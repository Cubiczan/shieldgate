import { getAuthZedClient, isAuthZedConfigured, v1 } from "./authzed-client";
import { withTimeout, isResilienceError } from "./resilience";
export { type UserRole, type AuthZDecision, AUTHZED_SCHEMA, ROLES } from "./authz-types";
import type { UserRole, AuthZDecision } from "./authz-types";

/** Per-call deadline for SpiceDB gRPC checks. Breach -> AuthZUnavailableError. */
const SPICEDB_TIMEOUT_MS = 2000;

/**
 * Raised when SpiceDB is configured but the authorization decision could not be
 * obtained (timeout / transport error). Routes should translate this into a 503
 * rather than silently degrading to simulation, which would be a fail-open.
 */
export class AuthZUnavailableError extends Error {
  constructor(message: string, readonly cause?: unknown) {
    super(message);
    this.name = "AuthZUnavailableError";
  }
}

// ---------- Real SpiceDB permission checks ----------

async function spicedbCheckPermission(
  resourceType: string,
  resourceId: string,
  permission: string,
  subjectType: string,
  subjectId: string
): Promise<{ allowed: boolean; debug?: string }> {
  const client = getAuthZedClient();

  const resource = v1.ObjectReference.create({
    objectType: resourceType,
    objectId: resourceId,
  });
  const subject = v1.SubjectReference.create({
    object: v1.ObjectReference.create({
      objectType: subjectType,
      objectId: subjectId,
    }),
  });

  const request = v1.CheckPermissionRequest.create({
    resource,
    permission,
    subject,
    consistency: v1.Consistency.create({
      requirement: {
        oneofKind: "fullyConsistent",
        fullyConsistent: true,
      },
    }),
  });

  const { promises } = client;
  const response = await withTimeout(
    promises.checkPermission(request),
    SPICEDB_TIMEOUT_MS,
    `SpiceDB checkPermission ${resourceType}:${resourceId}#${permission}`,
  );

  const allowed =
    response.permissionship ===
    v1.CheckPermissionResponse_Permissionship.HAS_PERMISSION;

  return { allowed };
}

async function spicedbCheckToolPermission(
  role: UserRole,
  toolName: string,
  index?: string
): Promise<AuthZDecision> {
  const timestamp = new Date().toISOString();
  const userId = `${role}_user`;

  try {
    const toolCheck = await spicedbCheckPermission(
      "splunk_tool",
      toolName,
      "execute",
      "user",
      userId
    );

    if (!toolCheck.allowed) {
      return {
        allowed: false,
        reason: `SpiceDB DENY: user '${userId}' cannot execute '${toolName}'`,
        policy: "least_privilege",
        timestamp,
        source: "spicedb",
      };
    }

    if (index) {
      const indexCheck = await spicedbCheckPermission(
        "splunk_index",
        index,
        "read",
        "user",
        userId
      );

      if (!indexCheck.allowed) {
        return {
          allowed: false,
          reason: `SpiceDB DENY: user '${userId}' does not have access to index '${index}'`,
          policy: "index_isolation",
          timestamp,
          source: "spicedb",
        };
      }

      if (toolName === "splunk_run_query") {
        const queryCheck = await spicedbCheckPermission(
          "splunk_index",
          index,
          "query",
          "user",
          userId
        );

        if (!queryCheck.allowed) {
          return {
            allowed: false,
            reason: `SpiceDB DENY: user '${userId}' has read but not query permission on index '${index}'`,
            policy: "read_only_access",
            timestamp,
            source: "spicedb",
          };
        }
      }
    }

    const constraint = TOOL_CONSTRAINTS[role]?.[toolName];
    return {
      allowed: true,
      reason: constraint || "Permission granted by SpiceDB policy",
      policy: constraint ? "conditional_allow" : "full_allow",
      timestamp,
      source: "spicedb",
    };
  } catch (error) {
    // SpiceDB is configured but unreachable/slow. Do NOT silently fall back to
    // simulation — that would fail-open the authorization decision. Surface a
    // typed error so the route can return 503.
    const detail = isResilienceError(error) && error.kind === "timeout" ? "timed out" : "failed";
    console.error(`[AuthZed] SpiceDB tool check ${detail}:`, error);
    throw new AuthZUnavailableError(`SpiceDB authorization check ${detail}`, error);
  }
}

async function spicedbCheckIndexPermission(
  role: UserRole,
  index: string,
  permission: "read" | "query"
): Promise<AuthZDecision> {
  const timestamp = new Date().toISOString();
  const userId = `${role}_user`;

  try {
    const result = await spicedbCheckPermission(
      "splunk_index",
      index,
      permission,
      "user",
      userId
    );

    return {
      allowed: result.allowed,
      reason: result.allowed
        ? `SpiceDB ALLOW: user '${userId}' has '${permission}' on index '${index}'`
        : `SpiceDB DENY: user '${userId}' lacks '${permission}' on index '${index}'`,
      policy: "index_isolation",
      timestamp,
      source: "spicedb",
    };
  } catch (error) {
    const detail = isResilienceError(error) && error.kind === "timeout" ? "timed out" : "failed";
    console.error(`[AuthZed] SpiceDB index check ${detail}:`, error);
    throw new AuthZUnavailableError(`SpiceDB authorization check ${detail}`, error);
  }
}

// Constraints are metadata not stored in SpiceDB — they enrich ALLOW decisions
const TOOL_CONSTRAINTS: Record<string, Record<string, string>> = {
  soc_tier1: {
    splunk_run_query:
      "Limited SPL only (no subsearches, no eval with eval expressions)",
  },
  sre: {
    splunk_run_query: "Observability and prod indexes only",
    splunk_get_alerts: "Observability alerts only",
  },
  contractor: {
    splunk_ai_assistant: "Results are redacted",
  },
  ai_agent: {
    splunk_run_query: "Requires human approval for remediation queries",
  },
};

// ---------- Simulation fallback (when AUTHZED_API_KEY not set) ----------

const INDEX_PERMISSIONS: Record<UserRole, Record<string, string[]>> = {
  soc_tier1: {
    security: ["read"],
    observability: [],
    compliance: ["read"],
    hr: [],
    prod: [],
  },
  soc_tier2: {
    security: ["read", "query"],
    observability: ["read"],
    compliance: ["read", "query"],
    hr: [],
    prod: [],
  },
  sre: {
    security: [],
    observability: ["read", "query"],
    compliance: [],
    hr: [],
    prod: ["read", "query"],
  },
  contractor: {
    security: ["read"],
    observability: [],
    compliance: [],
    hr: [],
    prod: [],
  },
  ai_agent: {
    security: ["read"],
    observability: ["read"],
    compliance: ["read"],
    hr: [],
    prod: ["read"],
  },
};

const TOOL_PERMISSIONS: Record<
  UserRole,
  Record<string, { allowed: boolean; constraint?: string }>
> = {
  soc_tier1: {
    splunk_run_query: { allowed: true, constraint: "Limited SPL only (no subsearches, no eval with eval expressions)" },
    splunk_get_indexes: { allowed: true },
    splunk_get_index_detail: { allowed: true },
    splunk_search_history: { allowed: true },
    splunk_get_alerts: { allowed: true },
    splunk_describe: { allowed: true },
    splunk_ai_assistant: { allowed: true },
    splunk_get_kv_store: { allowed: false },
    splunk_list_inputs: { allowed: false },
    splunk_get_dashboard: { allowed: true },
    splunk_get_lookup: { allowed: false },
  },
  soc_tier2: {
    splunk_run_query: { allowed: true },
    splunk_get_indexes: { allowed: true },
    splunk_get_index_detail: { allowed: true },
    splunk_search_history: { allowed: true },
    splunk_get_alerts: { allowed: true },
    splunk_describe: { allowed: true },
    splunk_ai_assistant: { allowed: true },
    splunk_get_kv_store: { allowed: true },
    splunk_list_inputs: { allowed: true },
    splunk_get_dashboard: { allowed: true },
    splunk_get_lookup: { allowed: true },
  },
  sre: {
    splunk_run_query: { allowed: true, constraint: "Observability and prod indexes only" },
    splunk_get_indexes: { allowed: true },
    splunk_get_index_detail: { allowed: true },
    splunk_search_history: { allowed: true },
    splunk_get_alerts: { allowed: true, constraint: "Observability alerts only" },
    splunk_describe: { allowed: true },
    splunk_ai_assistant: { allowed: true },
    splunk_get_kv_store: { allowed: false },
    splunk_list_inputs: { allowed: true },
    splunk_get_dashboard: { allowed: true },
    splunk_get_lookup: { allowed: false },
  },
  contractor: {
    splunk_run_query: { allowed: false, constraint: "Contractors cannot execute ad-hoc queries" },
    splunk_get_indexes: { allowed: true },
    splunk_get_index_detail: { allowed: false },
    splunk_search_history: { allowed: false },
    splunk_get_alerts: { allowed: false },
    splunk_describe: { allowed: true },
    splunk_ai_assistant: { allowed: true, constraint: "Results are redacted" },
    splunk_get_kv_store: { allowed: false },
    splunk_list_inputs: { allowed: false },
    splunk_get_dashboard: { allowed: false },
    splunk_get_lookup: { allowed: false },
  },
  ai_agent: {
    splunk_run_query: { allowed: true, constraint: "Requires human approval for remediation queries" },
    splunk_get_indexes: { allowed: true },
    splunk_get_index_detail: { allowed: true },
    splunk_search_history: { allowed: true },
    splunk_get_alerts: { allowed: true },
    splunk_describe: { allowed: true },
    splunk_ai_assistant: { allowed: true },
    splunk_get_kv_store: { allowed: true },
    splunk_list_inputs: { allowed: true },
    splunk_get_dashboard: { allowed: true },
    splunk_get_lookup: { allowed: true },
  },
};

function simCheckToolPermission(
  role: UserRole,
  toolName: string,
  index?: string
): AuthZDecision {
  const timestamp = new Date().toISOString();
  const toolPerms = TOOL_PERMISSIONS[role]?.[toolName];

  if (!toolPerms || !toolPerms.allowed) {
    const reason =
      toolPerms?.constraint ||
      `Role '${role}' is not authorized to execute '${toolName}'`;
    return { allowed: false, reason, policy: "least_privilege", timestamp, source: "simulation" };
  }

  if (index) {
    const indexPerms = INDEX_PERMISSIONS[role]?.[index];
    if (!indexPerms || indexPerms.length === 0) {
      return {
        allowed: false,
        reason: `Role '${role}' does not have access to index '${index}'. Per SpiceDB policy, index membership is required.`,
        policy: "index_isolation",
        timestamp,
        source: "simulation",
      };
    }

    if (toolName === "splunk_run_query" && !indexPerms.includes("query")) {
      return {
        allowed: false,
        reason: `Role '${role}' has read but not query permission on index '${index}'${toolPerms.constraint ? ". " + toolPerms.constraint : ""}`,
        policy: "read_only_access",
        timestamp,
        source: "simulation",
      };
    }
  }

  const extras: string[] = [];
  if (toolPerms.constraint) extras.push(toolPerms.constraint);

  return {
    allowed: true,
    reason: extras.length > 0 ? extras.join(". ") : "Permission granted by role policy",
    policy: toolPerms.constraint ? "conditional_allow" : "full_allow",
    timestamp,
    source: "simulation",
  };
}

function simCheckIndexPermission(
  role: UserRole,
  index: string,
  permission: "read" | "query"
): AuthZDecision {
  const timestamp = new Date().toISOString();
  const perms = INDEX_PERMISSIONS[role]?.[index] || [];

  if (!perms.includes(permission)) {
    return {
      allowed: false,
      reason: `Role '${role}' does not have '${permission}' permission on index '${index}'`,
      policy: "index_isolation",
      timestamp,
      source: "simulation",
    };
  }

  return {
    allowed: true,
    reason: `Role '${role}' has '${permission}' access to index '${index}'`,
    policy: "index_isolation",
    timestamp,
    source: "simulation",
  };
}

// ---------- Public API (routes unchanged) ----------

export async function checkToolPermission(
  role: UserRole,
  toolName: string,
  index?: string
): Promise<AuthZDecision> {
  if (isAuthZedConfigured()) {
    return spicedbCheckToolPermission(role, toolName, index);
  }
  return simCheckToolPermission(role, toolName, index);
}

export async function checkIndexPermission(
  role: UserRole,
  index: string,
  permission: "read" | "query"
): Promise<AuthZDecision> {
  if (isAuthZedConfigured()) {
    return spicedbCheckIndexPermission(role, index, permission);
  }
  return simCheckIndexPermission(role, index, permission);
}

export function getRolePermissions(role: UserRole) {
  return {
    tools: TOOL_PERMISSIONS[role] || {},
    indexes: INDEX_PERMISSIONS[role] || {},
  };
}

