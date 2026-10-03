# ShieldGate — Lean 4 verification notes

## Scope choice (read this first)

This repo is a mixed monorepo (finflowrl, metal-monitor, courtvision-ai,
greenverify-ai, battery-erp, assorted skills), but the product actually named
**ShieldGate** is the root Next.js/TypeScript app: a least-privilege
authorization gateway between AI agents/humans and Splunk, built from two
layers — an AuthZed/SpiceDB **ReBAC** layer (`src/lib/authz.ts`) and a
**CHP (Consensus Hardening Protocol) gate** (`src/lib/chp.ts`). That gate
core is what is modelled here, in `Gate.lean` (Lean 4.34.1, core library
only, no Mathlib; compiles with plain `~/.elan/bin/lean Gate.lean`, exit 0;
no `sorry`/`admit`/custom axioms — `#print axioms` on headline theorems
shows at most the standard `propext`/`Quot.sound`).

Modelled:

- `src/lib/authz.ts` — the simulation ReBAC (both permission tables
  transcribed exactly, both sim decision functions) and the *decision
  structure* of the SpiceDB path (the SpiceDB service itself is external;
  what the code guarantees is which oracle answers it requires).
- `src/lib/chp.ts` — R0 gate, incident lifecycle/forward transitions, both
  reviews (`reviewQuery`, `reviewIncidentTransition`), foundation scoring
  (`assessQueryExecution`, `assessIncidentTransition`), the human-lock
  verdict (`humanLockVerdict`), third-party confirmation
  (`SocChpGate.confirm`), and ledger integrity (`checkIntegrity`).
- Route composition facts from `src/app/api/splunk/query/route.ts`
  (results returned iff verdict ≠ `refused`) and
  `src/app/api/incidents/route.ts` (transition applied iff `lock.locked`).

Not modelled: JWT/auth middleware (`src/lib/auth-middleware.ts`), the
Splunk clients (but see Finding 7 — an execution-layer gap the gate cannot
see), JSON/timestamps/reason strings, the INVESTIGATIVE_SPL regex (an
opaque boolean), SHA-256 (an opaque function `H`), string trimming
(represented by "nonempty after trim" booleans). Scores/counts are `Nat`
(event counts are list lengths in the code, so non-negative).

## Theorem → source mapping

All line ranges are in `src/lib/authz.ts` / `src/lib/chp.ts` unless a route
file is named.

### ReBAC — simulation (`authz.ts`)

| Theorem | Source | Property |
|---|---|---|
| `simCheckIndex_iff` | `simCheckIndexPermission`, ll. 366–393 | Index check is exactly membership in `INDEX_PERMISSIONS` (ll. 207–243) |
| `hr_no_access` | ll. 207–243 | No role has any permission on index `hr` |
| `sim_tool_unknown_denied` | `simCheckToolPermission`, ll. 316–364 | Deny-by-default: tool absent from `TOOL_PERMISSIONS` (ll. 245–314) ⇒ deny |
| `contractor_no_query` | l. 297 + ll. 334–341 | Contractor's `splunk_run_query` entry is `allowed: false` ⇒ always denied |
| `tier1_query_security_denied`, `tier1_query_unpinned_allowed` | ll. 209–215, 347–355 | Tier-1 `security` grant is read-only: pinned query denied, unpinned allowed |
| `tier2_query_security_allowed` | ll. 217–226 | Tier-2 holds `query` on `security` |
| `sre_query_security_denied`, `sre_query_observability_allowed` | ll. 228–234 | SRE has no `security` access at all; full query on `observability` |
| `aiagent_query_prod_denied`, `aiagent_query_unpinned_allowed` | ll. 236–242 | AI agent's `prod` grant is read-only — tool check and index check genuinely differ |
| `sim_tool_index_monotone` | ll. 343–363 | Pinning an index can only restrict: indexed ALLOW ⇒ unpinned ALLOW |

### ReBAC — SpiceDB structure (`authz.ts` ll. 69–152)

| Theorem | Property |
|---|---|
| `spicedb_requires_tool` | ALLOW ⇒ tool `execute` check passed |
| `spicedb_requires_read` | ALLOW with an index pinned ⇒ index `read` check passed |
| `spicedb_requires_query` | ALLOW for `splunk_run_query` with an index pinned ⇒ index `query` check passed |

Errors/timeouts throw `AuthZUnavailableError` and routes answer 503 —
there is no ALLOW-on-error path in the code (fail-closed, verified by
reading, not modelled as a theorem).

### R0 gate + lifecycle (`chp.ts`)

| Theorem | Source | Property |
|---|---|---|
| `r0_pass_iff`, `r0_any_fatal_halts` | `evaluateR0Gate`, ll. 83–100 | PROCEED iff all four criteria pass; any failure halts |
| `forward_table` | `INCIDENT_LIFECYCLE` l. 165, `isForwardTransition` ll. 175–179 | On the status allowlist, exactly six forward pairs — including `open → closed` (skipping stages is allowed; reversal/no-op is not) |
| `forward_closed_terminal` | ll. 165–179 | `closed` is terminal |
| `forward_noop` | ll. 175–179 | No-op transitions are never forward |
| `forward_unknown_left`, `forward_unknown_right` | ll. 165–179 | Unknown/malformed statuses cannot move in either direction — no silent pass-through |
| `lifecycle_le`, `mem_statusAllowlist` | ll. 165, 201 | Ranks are bounded by 3; allowlist membership is boolean-decidable as in the code |

### Reviews (`chp.ts`)

| Theorem | Source | Property |
|---|---|---|
| `query_proceed_iff` | `reviewQuery`, ll. 376–420 | PROCEED is exactly: ReBAC ∧ SPL nonempty ∧ (context ∨ incident id) ∧ index pinned ∧ index known ∧ (context ∨ investigative SPL). (The code's `scoped` conjunct `SOC_SPL_RESULT_CAP > 0` is dropped — the cap is the constant 200, l. 151, so it is vacuous.) |
| `query_no_regrant` | ll. 378–390 | ReBAC deny ⇒ REFUSED with `evaluation = null`; CHP never re-grants |
| `transition_proceed_iff` | `reviewIncidentTransition`, ll. 422–465 | PROCEED is exactly: ReBAC ∧ incident exists ∧ target ∈ allowlist ∧ actor ∈ `INCIDENT_WRITE_ROLES` ∧ strictly forward move |
| `transition_no_regrant` | ll. 428–440 | Same no-regrant property for transitions |

### Foundation scoring (`chp.ts` ll. 467–540; floor l. 146, cap l. 151)

| Theorem | Property |
|---|---|
| `query_score_cases` | A query score is always exactly 40, 70, or 100 (40 guardrails are added unconditionally) |
| `query_score_floor_iff` | Score ≥ 70 iff bounded result (`1 ≤ eventCount ≤ 200`, **both bounds inclusive**, code `>= 1 && <= SOC_SPL_RESULT_CAP`) or corroborated |
| `query_score_subfloor_iff` | Score < 70 iff neither points block was earned (score is then 40) |
| `query_score_hundred_iff` | Score = 100 iff both blocks earned |
| `transition_score_full` | Existing incident + forward move ⇒ (100, no fatal) |
| `transition_score_contradiction` | Existing incident + non-forward move ⇒ (70, **fatal**) — scores *at* the floor, so only the fatal flag refuses it |
| `transition_fatal_iff` | Fatal ⟺ a status exists and the move is not forward |
| `transition_score_absent` | No incident ⇒ (40, no fatal) |

### Human lock (`humanLockVerdict`, `chp.ts` ll. 542–609)

| Theorem | Property |
|---|---|
| `verdict_fatal_refused` | Fatal ⇒ refused outright, before floor/confirmer checks — no confirmer can wave a contradiction through |
| `verdict_selfCertified_iff` | Via = `self_certified` ⟺ no fatal ∧ no lock needed |
| `verdict_confirmedBy_iff` | Via = `confirmed_by` ⟺ no fatal ∧ lock needed ∧ `confirmed_by` present ∧ **actor** ≠ `ai_agent` |
| `verdict_ledger_iff` | Via = `ledger` ⟺ no fatal ∧ lock needed ∧ no `confirmed_by` ∧ valid LOCKED ledger record |
| `verdict_locked_routes` | Locked ⇒ exactly those two routes; always lock-needed and non-fatal |
| `ai_cannot_self_confirm` | An AI actor supplying `confirmed_by` is refused (ll. 562–571) |
| `floor_boundary_exact`, `floor_boundary_below` | Lock test is `score < 70` (l. 550): exactly **70 passes**, 69 locks |
| `transition_always_needs_lock` | With REQUIRE_HUMAN_LOCK on, **every** transition-kind action needs a lock, at any score |
| `review_verdict_divergence` | Same non-destructive transition: review reports `humanLockRequired = false` (l. 461) while the verdict computes `needsLock = true` |

### Counterexamples (proved, not conjectured)

| Theorem | What it exhibits |
|---|---|
| `counterexample_sre_names_confirmer` | An `sre` actor — a write role but **not** an eligible confirmer (`eligibleConfirmerRoles`, ll. 189–191: transitions → `soc_tier2` only) — locks a transition by putting any non-empty string in `confirmed_by`. `humanLockVerdict` receives no confirmer role and never checks eligibility; the only check is that the *actor* isn't `ai_agent`. |
| `route_deadlock` | With `SHIELDGATE_REQUIRE_HUMAN_LOCK` off, a transition verdict is `self_certified`; the verdict function returns before consulting `confirmed_by`/ledger, and the incidents route applies only `locked` verdicts — so **no request can ever apply an incident transition** in that configuration. The query route proceeds on the identical verdict. |
| `confirm_self_confirmation` | `confirm` (ll. 671–711) accepts the decision's own actor as confirmer: it takes no confirmer identity distinct from the free-text name, and the decisions route (`src/app/api/chp/decisions/route.ts`) defaults that name to the caller's own user id and takes it from the request body otherwise. "Third-party" is a docstring claim, not a check. |
| `confirm_any_status` | `confirm` never checks the prior status is `PROVISIONAL_LOCK`: a HALT record confirms to LOCKED just as well. (Latent — routes only record PROVISIONAL_LOCK/LOCKED.) |
| `integrity_forgeable` | `checkIntegrity` (ll. 288–296) is an **unkeyed** SHA-256 equality plus structure-only envelope validation (ll. 121–137: BEGIN/END markers with matching ids; content unbound). For every forged body `b`, storing digest `H b` passes. The check detects corruption, not forgery. |

### `confirm` — positive properties (`chp.ts` ll. 671–711)

| Theorem | Property |
|---|---|
| `confirm_unknown` | Unknown decision id ⇒ rejected |
| `confirm_tampered_rejected` | Integrity-invalid latest record ⇒ rejected **even if it claims LOCKED** — the integrity check (ll. 676–680) precedes the idempotence check (ll. 682–684) |
| `confirm_idempotent` | Confirming a valid LOCKED record returns it unchanged, appends nothing. ⚠️ Corollary (by the check order, visible in the model): the idempotent return also precedes the eligibility and blank-name checks, so an *ineligible* role — even `ai_agent` — confirming an already-LOCKED decision gets a successful LOCKED response |
| `confirm_ineligible_rejected` | Non-LOCKED + ineligible role ⇒ rejected, state unchanged. Eligibility is exact: queries → `soc_tier1`/`soc_tier2`; transitions → `soc_tier2` only (ll. 189–197) |
| `confirm_success` | On success the appended record is LOCKED, carries the confirmer name, and `supersedes` the prior body digest (ll. 693–708) |

## Findings / discrepancies / risks

1. **Two-stage lock disagreement (proved: `review_verdict_divergence`,
   `transition_always_needs_lock`).** `reviewIncidentTransition` reports
   `humanLockRequired = destructive(target) ∧ flag`, but
   `humanLockVerdict` recomputes need from the action *kind*: with the
   flag on (default; off only when the env var is exactly `"0"`), every
   incident transition needs a lock, including non-destructive ones the
   review cleared. Neither route consults the review's field, so the
   review value is dead weight that misdescribes the system's behaviour.

2. **Route-level deadlock (proved: `route_deadlock`).** With the flag
   off, transitions self-certify at the verdict but the incidents route
   (`src/app/api/incidents/route.ts` ll. 132–157) applies only `locked`
   verdicts and records PROVISIONAL_LOCK + 403 otherwise. The repo's own
   test (`tests/chp.test.ts`, human-lock section) exercises the gate
   class directly and expects the self-certified verdict — the route
   composition that turns it into a permanent 403 is untested.

3. **Inline `confirmed_by` is naming, not confirming (proved:
   `counterexample_sre_names_confirmer`).** Any non-AI actor role locks
   any gated action by supplying any non-empty `confirmed_by` string;
   confirmer eligibility (`eligibleConfirmerRoles`) is enforced only on
   the decisions-API path (`confirm`), not inline. The guard that does
   exist checks the *actor's* role against `ai_agent`, not the
   confirmer's identity.

4. **Self-confirmation through the decisions API (proved:
   `confirm_self_confirmation`).** Nothing in `confirm` or the decisions
   route binds the confirmer to a different principal than the actor;
   the route takes `confirmed_by` from the request body and only
   defaults it to the JWT subject when the body value is empty.

5. **Ledger reuse across actors and repeats.** Decision ids bind no
   actor: query ids hash `[spl, index, incidentId, incidentContext]`,
   transition ids are `soc-incident-{incidentId}-{targetStatus}` (no
   source status, no actor). The verdict's ledger path checks only the
   record for that id (valid, LOCKED, has a confirmer) — so one LOCKED
   record can release later, different actors' actions with the same id,
   and repeated transitions to the same target.

6. **The query executes before the lock verdict.** In
   `src/app/api/splunk/query/route.ts` the Splunk search runs *before*
   the foundation pass and human-lock verdict; on lock refusal the
   results are withheld (403) but the search already ran. Also: a
   `self_certified` response returns results while still reporting
   `session_status: "PROVISIONAL_LOCK"`, and on real-Splunk failure the
   route silently falls back to the simulator.

7. **Execution layer diverges from the checked index (read-only finding;
   outside the gate model).** `runSplunkQuery`
   (`src/lib/splunk-client.ts`) never puts the authorized `index`
   argument into the search — the SPL string is executed essentially as
   supplied, so SPL-embedded index selection can diverge from the index
   the ReBAC/CHP layers checked. The simulator
   (`src/lib/splunk-sim.ts`, `simulateSplunkQuery` l. 100) is more
   lenient still: an unknown or missing pinned index returns events from
   **all** indexes (l. 111) instead of none. Compounding this, the query
   route's `indexKnown` is `isSplunkConfigured() || SPLUNK_INDEXES.some(…)`
   — with Splunk configured, *any* index string counts as "known" at the
   CHP layer.

8. **Ungrounded incident references pass.** `reviewQuery` uses only
   `Boolean(incidentId)` for grounding and never resolves the id; a
   query citing a nonexistent incident, with investigative SPL and a
   bounded result, reaches score 70 and is released (follows from
   `query_proceed_iff` + `query_score_floor_iff`).

9. **Tool constraints are decorative (read-only finding).** `TOOL_CONSTRAINTS`
   (`authz.ts` l. 188) only enriches ALLOW reasons/policies
   (`conditional_allow`); nothing in `src/` enforces the constraint
   strings against the SPL — e.g. tier-1's "Limited SPL only (no
   subsearches…)" and the AI agent's "Requires human approval for
   remediation queries" are never checked. In the SpiceDB path,
   constraints come from the role's own table by construction.

10. **Incidents route has no ReBAC check.** It validates the caller's
    role and the status against its own allowlists, then calls the gate
    with `rebacAllowed: true` — despite the "ReBAC first" framing,
    SpiceDB is never consulted on this path. (The gate-side property
    `transition_no_regrant` therefore relies on the route's own checks.)

11. **Assessor quirks worth knowing.** Both assessors add the 40
    guardrail points unconditionally (they trust R0 ran);
    `assessIncidentTransition`'s fatal branch is unreachable through the
    incidents route with consistent inputs (the review already required
    the same forward condition), yet the route checks `assessment.fatal`
    separately anyway; an incident whose status is the empty string
    scores 70 with no fatal in the assessor (empty string is falsy)
    while the review refuses it — the review masks the quirk.

12. **Ledger mechanics.** JSONL append via `appendFileSync`;
    `DecisionLedger.readAll` throws on a corrupt line rather than
    skipping it (good — no silent skip); entries are not hash-chained
    to each other (only `confirm` sets `supersedes` to the prior body
    digest); `get` returns the latest record for an id, which is all
    the model needed.

13. **Standing dev bypass (out of model scope, flagged).**
    `AUTH_DISABLED=true` in `src/lib/auth-middleware.ts` bypasses auth
    entirely and assigns role `soc_tier1` / user `dev_user`, gated only
    by an environment variable.
