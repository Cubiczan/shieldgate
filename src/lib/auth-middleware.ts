import { NextResponse } from 'next/server';
import type { UserRole } from './authz-types';
import { importJWK, jwtVerify, type JWTPayload } from 'jose';
import { AuthZUnavailableError } from './authz';

// ─── Types ───────────────────────────────────────────────────────────────────

export interface AuthenticatedRequest extends Request {
  /** Role extracted from the verified JWT */
  authRole: UserRole;
  /** Subject (user id) extracted from the verified JWT */
  authUserId: string;
}

// ─── Valid roles whitelist ───────────────────────────────────────────────────

const VALID_ROLES = new Set<string>([
  'soc_tier1',
  'soc_tier2',
  'sre',
  'contractor',
  'ai_agent',
]);

// ─── Dev-only bypass (ONLY when AUTH_DISABLED=true) ──────────────────────────
// This exists solely to avoid breaking local development before a real
// login flow is wired up.  MUST remain disabled in production.

const isAuthDisabled = process.env.AUTH_DISABLED === 'true';

// ─── JWKS / secret helpers ──────────────────────────────────────────────────

let verificationKey: Uint8Array | null = null;

function getVerificationKey(): Uint8Array {
  if (verificationKey) return verificationKey;

  const secret = process.env.JWT_SECRET;
  if (!secret) {
    throw new Error(
      'JWT_SECRET environment variable is not set. ' +
      'Set it in .env.local or pass AUTH_DISABLED=true for local dev only.',
    );
  }

  verificationKey = new TextEncoder().encode(secret);
  return verificationKey;
}

// ─── Core: verify a Bearer token and return its claims ──────────────────────

export async function verifyToken(
  token: string,
): Promise<{ role: UserRole; userId: string }> {
  const key = getVerificationKey();
  const { payload } = await jwtVerify(token, key);

  const role = payload.role as string;
  const userId = (payload.sub as string) || 'unknown';

  if (!role || !VALID_ROLES.has(role)) {
    throw new Error(
      `Invalid role "${role}" in token. Allowed: ${[...VALID_ROLES].join(', ')}`,
    );
  }

  return { role: role as UserRole, userId };
}

// ─── Extract token from request ─────────────────────────────────────────────

function extractBearerToken(request: Request): string | null {
  const header = request.headers.get('Authorization');
  if (!header || !header.startsWith('Bearer ')) return null;
  return header.slice(7).trim();
}

// ─── Public routes (no auth required) ──────────────────────────────────────

const PUBLIC_PATHS = new Set(['/api']);

function isPublicPath(pathname: string): boolean {
  return PUBLIC_PATHS.has(pathname);
}

// ─── Default role for dev bypass ────────────────────────────────────────────

const DEV_DEFAULT_ROLE: UserRole = 'soc_tier1';

// ─── Middleware wrapper for API route handlers ──────────────────────────────
//
// Usage in a route file:
//
//   import { withAuth } from '@/lib/auth-middleware';
//
//   export const GET = withAuth(async (request) => {
//     const role = request.authRole;  // guaranteed to be a valid UserRole
//     const userId = request.authUserId;
//     // ... handler logic
//   });
//
// The wrapper returns 401 if no valid token is provided (or AUTH_DISABLED
// is not set), and 403 if the token is malformed / has an invalid role.

type RouteHandler = (
  request: AuthenticatedRequest,
) => Promise<Response> | Response;

// Invoke the wrapped handler, translating an AuthZUnavailableError (SpiceDB
// timeout / transport failure) into a 503 instead of letting it fail-open or
// surface as an opaque 500.
async function runHandler(
  handler: RouteHandler,
  request: AuthenticatedRequest,
): Promise<Response> {
  try {
    return await handler(request);
  } catch (err) {
    if (err instanceof AuthZUnavailableError) {
      return NextResponse.json(
        { error: 'AUTHZ_UNAVAILABLE', reason: err.message },
        { status: 503 },
      );
    }
    throw err;
  }
}

export function withAuth(handler: RouteHandler): RouteHandler {
  return async (request: Request): Promise<Response> => {
    const { pathname } = new URL(request.url);

    // Skip auth for public paths
    if (isPublicPath(pathname)) {
      return runHandler(handler, request as AuthenticatedRequest);
    }

    // ── Dev bypass (danger: never enable in production) ──────────────────
    if (isAuthDisabled) {
      const role = DEV_DEFAULT_ROLE;
      const userId = 'dev_user';
      const augmented = Object.assign(request, { authRole: role, authUserId: userId });
      return runHandler(handler, augmented);
    }

    // ── Normal auth flow ──────────────────────────────────────────────────
    try {
      const token = extractBearerToken(request);

      if (!token) {
        return NextResponse.json(
          { error: 'UNAUTHORIZED', reason: 'Missing or invalid Authorization header. Expected: Bearer <token>' },
          { status: 401 },
        );
      }

      const { role, userId } = await verifyToken(token);
      const augmented = Object.assign(request, { authRole: role, authUserId: userId });
      return runHandler(handler, augmented);
    } catch (err) {
      const message = err instanceof Error ? err.message : 'Authentication failed';
      return NextResponse.json(
        { error: 'UNAUTHORIZED', reason: message },
        { status: 401 },
      );
    }
  };
}

// ─── Utility: extract role from a NextRequest (for query-param routes) ──────
// DEPRECATED – prefer `withAuth` wrapper which attaches authRole directly.

export function getRoleFromRequest(request: AuthenticatedRequest): UserRole {
  return request.authRole;
}
