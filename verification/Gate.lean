/-
  ShieldGate — Lean 4 model of the authorization / CHP gate core
  ==============================================================

  Source: the root Next.js app of this monorepo (the subprojects —
  finflowrl, metal-monitor, courtvision-ai, … — are separate products
  and are NOT modelled here).

  Modelled, following the CODE (not the docs):

  * `src/lib/authz.ts`
      - the simulation ReBAC: `simCheckToolPermission` (ll. 316–364) and
        `simCheckIndexPermission` (ll. 366–393) over the concrete tables
        `TOOL_PERMISSIONS` (ll. 245–314) and `INDEX_PERMISSIONS`
        (ll. 207–243);
      - the SpiceDB decision *structure* of `spicedbCheckToolPermission`
        (ll. 69–152): the conjunction of oracle answers the code requires
        (the SpiceDB service itself is external and not modelled).

  * `src/lib/chp.ts` — the CHP gate:
      - `evaluateR0Gate` (ll. 83–100);
      - `SocChpGate.reviewQuery` (ll. 376–420) and
        `reviewIncidentTransition` (ll. 422–465), incl. the incident
        lifecycle `INCIDENT_LIFECYCLE` / `isForwardTransition`
        (ll. 164–179);
      - foundation scoring `assessQueryExecution` (ll. 467–501) and
        `assessIncidentTransition` (ll. 503–540), floor `GENERAL_FLOOR`
        = 70 (l. 146), result cap `SOC_SPL_RESULT_CAP` = 200 (l. 151);
      - `humanLockVerdict` (ll. 542–609);
      - `SocChpGate.confirm` (ll. 671–711) over the decision ledger,
        abstracted to the *latest* record for one decision id — the only
        thing `DecisionLedger.get` (ll. 259–267) and `confirm` consult;
      - ledger integrity `checkIntegrity` (ll. 288–296): an *unkeyed*
        SHA-256 digest comparison, with the hash abstracted as `H`.

  * Route composition (simple boolean combinations in the routes):
      - `src/app/api/splunk/query/route.ts` — results are returned iff
        the lock verdict is not `refused`;
      - `src/app/api/incidents/route.ts` (ll. 132–157) — the transition
        is applied iff `lock.locked`, i.e. iff the verdict came via
        `confirmed_by` or `ledger`; there is no self-certified path.

  Abstracted away: timestamps, reason strings, JSON bodies, the
  INVESTIGATIVE_SPL regex (an opaque boolean), string trimming
  (`confirmedBy` / `index` / `spl` are represented by "nonempty after
  trim" booleans), SHA-256 (an opaque function `H`), floating point
  (scores and counts are `Nat`; event counts are list lengths in the
  code, hence non-negative).
-/

namespace ShieldGate

/-! ## Roles (`src/lib/authz-types.ts` ll. 1–6, authz.ts tables) -/

inductive Role where
  | socTier1 | socTier2 | sre | contractor | aiAgent
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Boolean membership for string lists (the code's `Array.includes` /
    `Set.has` over string collections). -/
def memB (xs : List String) (a : String) : Bool := xs.any (fun x => x = a)

theorem memB_iff {xs : List String} {a : String} : memB xs a = true ↔ a ∈ xs := by
  simp [memB, List.any_eq_true]

/-! ## Simulation ReBAC (`src/lib/authz.ts`)

`INDEX_PERMISSIONS` (ll. 207–243): role ↦ index ↦ permission list.
An index absent from a role's record yields `[]` here; the code reads
`undefined` and denies, which the empty list reproduces in both sim
functions. -/

def indexPerms : Role → String → List String
  | .socTier1, idx =>
      if idx = "security" then ["read"]
      else if idx = "compliance" then ["read"] else []
  | .socTier2, idx =>
      if idx = "security" then ["read", "query"]
      else if idx = "observability" then ["read"]
      else if idx = "compliance" then ["read", "query"] else []
  | .sre, idx =>
      if idx = "observability" then ["read", "query"]
      else if idx = "prod" then ["read", "query"] else []
  | .contractor, idx =>
      if idx = "security" then ["read"] else []
  | .aiAgent, idx =>
      if idx = "security" then ["read"]
      else if idx = "observability" then ["read"]
      else if idx = "compliance" then ["read"]
      else if idx = "prod" then ["read"] else []

/-- `TOOL_PERMISSIONS` (ll. 245–314) as an association list per role:
    tool ↦ (allowed, has-constraint?). Tools absent from a role's record
    are denied by the code (`!toolPerms`), so absence means `none`. -/
def toolTable : Role → List (String × Bool × Bool)
  | .socTier1 =>
      [ ("splunk_run_query", true, true), ("splunk_get_indexes", true, false),
        ("splunk_get_index_detail", true, false), ("splunk_search_history", true, false),
        ("splunk_get_alerts", true, false), ("splunk_describe", true, false),
        ("splunk_ai_assistant", true, false), ("splunk_get_kv_store", false, false),
        ("splunk_list_inputs", false, false), ("splunk_get_dashboard", true, false),
        ("splunk_get_lookup", false, false) ]
  | .socTier2 =>
      [ ("splunk_run_query", true, false), ("splunk_get_indexes", true, false),
        ("splunk_get_index_detail", true, false), ("splunk_search_history", true, false),
        ("splunk_get_alerts", true, false), ("splunk_describe", true, false),
        ("splunk_ai_assistant", true, false), ("splunk_get_kv_store", true, false),
        ("splunk_list_inputs", true, false), ("splunk_get_dashboard", true, false),
        ("splunk_get_lookup", true, false) ]
  | .sre =>
      [ ("splunk_run_query", true, true), ("splunk_get_indexes", true, false),
        ("splunk_get_index_detail", true, false), ("splunk_search_history", true, false),
        ("splunk_get_alerts", true, true), ("splunk_describe", true, false),
        ("splunk_ai_assistant", true, false), ("splunk_get_kv_store", false, false),
        ("splunk_list_inputs", true, false), ("splunk_get_dashboard", true, false),
        ("splunk_get_lookup", false, false) ]
  | .contractor =>
      [ ("splunk_run_query", false, true), ("splunk_get_indexes", true, false),
        ("splunk_get_index_detail", false, false), ("splunk_search_history", false, false),
        ("splunk_get_alerts", false, false), ("splunk_describe", true, false),
        ("splunk_ai_assistant", true, true), ("splunk_get_kv_store", false, false),
        ("splunk_list_inputs", false, false), ("splunk_get_dashboard", false, false),
        ("splunk_get_lookup", false, false) ]
  | .aiAgent =>
      [ ("splunk_run_query", true, true), ("splunk_get_indexes", true, false),
        ("splunk_get_index_detail", true, false), ("splunk_search_history", true, false),
        ("splunk_get_alerts", true, false), ("splunk_describe", true, false),
        ("splunk_ai_assistant", true, false), ("splunk_get_kv_store", true, false),
        ("splunk_list_inputs", true, false), ("splunk_get_dashboard", true, false),
        ("splunk_get_lookup", true, false) ]

def findTool : List (String × Bool × Bool) → String → Option (Bool × Bool)
  | [], _ => none
  | (n, a, c) :: rest, t => if n = t then some (a, c) else findTool rest t

/-- The `allowed` component of `simCheckToolPermission`
    (authz.ts ll. 316–364). -/
def simCheckTool (role : Role) (tool : String) (index : Option String) : Bool :=
  match findTool (toolTable role) tool with
  | none => false
  | some (false, _) => false
  | some (true, _) =>
      match index with
      | none => true
      | some idx =>
          let perms := indexPerms role idx
          if perms.isEmpty then false
          else if tool = "splunk_run_query" && !perms.contains "query" then false
          else true

/-- The `allowed` component of `simCheckIndexPermission`
    (authz.ts ll. 366–393). -/
def simCheckIndex (role : Role) (idx perm : String) : Bool :=
  memB (indexPerms role idx) perm

/-! ### Simulation theorems -/

/-- Index checks are exactly table membership. -/
theorem simCheckIndex_iff {r : Role} {i p : String} :
    simCheckIndex r i p = true ↔ p ∈ indexPerms r i :=
  memB_iff

/-- No role has any permission on the `hr` index, for any permission. -/
theorem hr_no_access (r : Role) (p : String) : simCheckIndex r "hr" p = false := by
  cases r <;> rfl

/-- Deny by default: a tool absent from the role's table is denied. -/
theorem sim_tool_unknown_denied {r : Role} {t : String} {i : Option String}
    (h : findTool (toolTable r) t = none) : simCheckTool r t i = false := by
  simp [simCheckTool, h]

/-- Contractors can never run queries, with or without an index
    (table entry `allowed: false`, authz.ts l. 297). -/
theorem contractor_no_query (i : Option String) :
    simCheckTool .contractor "splunk_run_query" i = false := by
  cases i <;> rfl

/-- Tier 1 may run the query tool in the abstract, but its `security`
    grant is read-only, so a query pinned to `security` is denied
    (ll. 209–215 + 347–355). -/
theorem tier1_query_security_denied :
    simCheckTool .socTier1 "splunk_run_query" (some "security") = false := rfl

theorem tier1_query_unpinned_allowed :
    simCheckTool .socTier1 "splunk_run_query" none = true := rfl

/-- Tier 2 holds `query` on `security`: allowed. -/
theorem tier2_query_security_allowed :
    simCheckTool .socTier2 "splunk_run_query" (some "security") = true := rfl

/-- SRE: no access at all to `security`; full query on `observability`. -/
theorem sre_query_security_denied :
    simCheckTool .sre "splunk_run_query" (some "security") = false := rfl

theorem sre_query_observability_allowed :
    simCheckTool .sre "splunk_run_query" (some "observability") = true := rfl

/-- The AI agent's `prod` grant is read-only: the *tool* is allowed but
    a query pinned to `prod` is denied — tool and index checks differ. -/
theorem aiagent_query_prod_denied :
    simCheckTool .aiAgent "splunk_run_query" (some "prod") = false := rfl

theorem aiagent_query_unpinned_allowed :
    simCheckTool .aiAgent "splunk_run_query" none = true := rfl

/-- Pinning an index can only restrict the tool decision: an indexed
    ALLOW implies the unpinned ALLOW. -/
theorem sim_tool_index_monotone {r : Role} {t : String} {i : String}
    (h : simCheckTool r t (some i) = true) : simCheckTool r t none = true := by
  cases hf : findTool (toolTable r) t with
  | none => simp [simCheckTool, hf] at h
  | some p =>
      obtain ⟨a, c⟩ := p
      cases a with
      | false => simp [simCheckTool, hf] at h
      | true => simp [simCheckTool, hf]

/-! ## SpiceDB decision structure (`spicedbCheckToolPermission`, ll. 69–152)

The service is external; what the *code* guarantees is the shape of the
composition: ALLOW requires the tool check, and — when an index is
pinned — the index `read` check, and additionally the `query` check
for `splunk_run_query`. On any error the function throws
`AuthZUnavailableError` (fail-closed; routes answer 503), so there is
no ALLOW-on-error path in the code. -/

def spicedbToolDecision (toolOK readOK queryOK hasIndex isRunQuery : Bool) : Bool :=
  toolOK && (!hasIndex || (readOK && (!isRunQuery || queryOK)))

theorem spicedb_requires_tool {t r q hi iq : Bool}
    (h : spicedbToolDecision t r q hi iq = true) : t = true := by
  cases t <;> simp [spicedbToolDecision] at h ⊢

theorem spicedb_requires_read {t r q iq : Bool}
    (h : spicedbToolDecision t r q true iq = true) : r = true := by
  cases r <;> simp [spicedbToolDecision] at h ⊢

theorem spicedb_requires_query {t r q : Bool}
    (h : spicedbToolDecision t r q true true = true) : q = true := by
  cases q <;> simp [spicedbToolDecision] at h ⊢

/-! ## The R0 gate (`evaluateR0Gate`, chp.ts ll. 83–100)

PROCEED (modelled here as `r0Pass`) iff every criterion is `pass`; any
`fatal` criterion — or, indeed, any non-pass — halts. At every call
site in chp.ts each criterion is itself derived from a boolean
condition, so the three-valued status is faithfully a conjunction. -/

structure Criteria where
  solvable : Bool
  scopedB : Bool
  valid : Bool
  worthIt : Bool
  deriving DecidableEq, Repr

def r0Pass (c : Criteria) : Bool := c.solvable && c.scopedB && c.valid && c.worthIt

theorem r0_pass_iff (c : Criteria) :
    r0Pass c = true ↔
      c.solvable = true ∧ c.scopedB = true ∧ c.valid = true ∧ c.worthIt = true := by
  simp [r0Pass, Bool.and_eq_true, and_assoc]

theorem r0_any_fatal_halts {c : Criteria} (h : c.solvable = false ∨ c.scopedB = false ∨
    c.valid = false ∨ c.worthIt = false) : r0Pass c = false := by
  rcases h with h | h | h | h <;> simp [r0Pass, h]

/-! ## Incident lifecycle (chp.ts ll. 164–211)

`INCIDENT_LIFECYCLE` is a rank map (l. 165); an unknown status —
including the code's `""` default for a missing `from` — has no rank,
and `isForwardTransition` (ll. 175–179) is then false. -/

def lifecycle (s : String) : Option Nat :=
  if s = "open" then some 0
  else if s = "investigating" then some 1
  else if s = "resolved" then some 2
  else if s = "closed" then some 3
  else none

def forward (frm target : String) : Bool :=
  match lifecycle frm, lifecycle target with
  | some a, some b => a < b
  | _, _ => false

def destructive (target : String) : Bool := target = "resolved" || target = "closed"

def statusAllowlist : List String := ["open", "investigating", "resolved", "closed"]

theorem mem_statusAllowlist {s : String} :
    memB statusAllowlist s = true ↔ s ∈ statusAllowlist := memB_iff

theorem lifecycle_le {s : String} {n : Nat} (h : lifecycle s = some n) : n ≤ 3 := by
  have e : ∀ m : Nat, lifecycle s = some m → m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
    intro m hm
    by_cases h1 : s = "open"
    · subst h1
      exact Or.inl (Option.some.inj (show some 0 = some m from hm)).symm
    by_cases h2 : s = "investigating"
    · subst h2
      exact Or.inr (Or.inl (Option.some.inj (show some 1 = some m from hm)).symm)
    by_cases h3 : s = "resolved"
    · subst h3
      exact Or.inr (Or.inr (Or.inl (Option.some.inj (show some 2 = some m from hm)).symm))
    by_cases h4 : s = "closed"
    · subst h4
      exact Or.inr (Or.inr (Or.inr (Option.some.inj (show some 3 = some m from hm)).symm))
    · have hnone : lifecycle s = none := by simp [lifecycle, h1, h2, h3, h4]
      rw [hnone] at hm
      simp at hm
  rcases e n h with rfl | rfl | rfl | rfl <;> omega

/-- The complete forward table on the allowlist: exactly the six
    strictly-increasing pairs — note `open → closed` *skips* two
    stages and is still forward — and nothing else. -/
theorem forward_table {f t : String} (hf : f ∈ statusAllowlist) (ht : t ∈ statusAllowlist) :
    forward f t = true ↔
      (f = "open" ∧ (t = "investigating" ∨ t = "resolved" ∨ t = "closed")) ∨
      (f = "investigating" ∧ (t = "resolved" ∨ t = "closed")) ∨
      (f = "resolved" ∧ t = "closed") := by
  simp only [statusAllowlist, List.mem_cons, List.mem_nil_iff, or_false] at hf ht
  rcases hf with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
    decide

/-- `closed` is terminal: no forward move out of it. -/
theorem forward_closed_terminal (t : String) : forward "closed" t = false := by
  cases ht : lifecycle t with
  | none => simp [forward, ht]
  | some v =>
      have hv := lifecycle_le ht
      have h3 : lifecycle "closed" = some 3 := rfl
      simp [forward, ht, h3, show ¬ (3 < v) by omega]

/-- A no-op "transition" is never forward — worth_it fails. -/
theorem forward_noop (s : String) : forward s s = false := by
  cases hs : lifecycle s <;> simp [forward, hs, Nat.lt_irrefl]

/-- Unknown statuses cannot move in either direction (no silent
    pass-through of malformed lifecycle states). -/
theorem forward_unknown_left {s t : String} (h : lifecycle s = none) :
    forward s t = false := by simp [forward, h]

theorem forward_unknown_right {s t : String} (h : lifecycle t = none) :
    forward s t = false := by
  cases hs : lifecycle s <;> simp [forward, hs, h]

/-! ## The two reviews

Boolean form of `reviewQuery` (ll. 376–420) and
`reviewIncidentTransition` (ll. 422–465): PROCEED is exactly the
ReBAC decision *and* R0 passing on the derived criteria. Inputs:

* `rebac` — the ReBAC layer's `allowed`;
* `splNE`, `ctxNE` — SPL / incident-context nonempty after trim;
* `hasId` — an incident id was supplied (its existence is NOT checked);
* `idxPinned` — a nonempty index (the code defaults a missing index to
  `"security"`, l. 384, so a pinned index is in fact always present);
* `idxKnown` — caller-computed "index exists in this Splunk"
  (`indexKnownForGate`, query route l. 69);
* `inv` — the INVESTIGATIVE_SPL regex matched.

The code's `scoped` conjunct `SOC_SPL_RESULT_CAP > 0` is dropped: the
cap is the constant 200 (l. 151), so the conjunct is vacuously true. -/

def queryProceed (rebac splNE ctxNE hasId idxPinned idxKnown inv : Bool) : Bool :=
  rebac && (splNE && (ctxNE || hasId)) && idxPinned && idxKnown && (ctxNE || inv)

theorem query_proceed_iff {r s c h p k v : Bool} :
    queryProceed r s c h p k v = true ↔
      r = true ∧ s = true ∧ (c = true ∨ h = true) ∧ p = true ∧ k = true ∧
        (c = true ∨ v = true) := by
  cases r <;> cases s <;> cases c <;> cases h <;> cases p <;> cases k <;> cases v <;>
    decide

/-- CHP never re-grants: a ReBAC deny is a REFUSED review, full stop. -/
theorem query_no_regrant {s c h p k v : Bool} :
    queryProceed false s c h p k v = false := rfl

def writeRoles : List Role := [.socTier2, .sre, .aiAgent]

def memRole (xs : List Role) (r : Role) : Bool := xs.any (fun x => x = r)

theorem memRole_iff {xs : List Role} {r : Role} :
    memRole xs r = true ↔ r ∈ xs := by
  simp [memRole, List.any_eq_true]

/-- Boolean form of `reviewIncidentTransition` (ll. 422–465). Inputs:
    `ex` — the incident resolved (non-null); `sc` — target in the
    status allowlist; `va` — actor in INCIDENT_WRITE_ROLES;
    `frm` — the incident's current status. -/
def transitionProceed (rebac ex : Bool) (target : String) (actor : Role)
    (frm : Option String) : Bool :=
  rebac && ex && memB statusAllowlist target && memRole writeRoles actor &&
    (match frm with | some f => forward f target | none => false)

theorem transition_proceed_iff {r e : Bool} {t : String} {a : Role} {f : Option String} :
    transitionProceed r e t a f = true ↔
      r = true ∧ e = true ∧ t ∈ statusAllowlist ∧ a ∈ writeRoles ∧
        (match f with | some s => forward s t = true | none => False) := by
  cases f with
  | none => simp [transitionProceed]
  | some s =>
      simp only [transitionProceed, Bool.and_eq_true, memB_iff, memRole_iff, and_assoc]

theorem transition_no_regrant {e : Bool} {t : String} {a : Role} {f : Option String} :
    transitionProceed false e t a f = false := rfl

/-- What `reviewIncidentTransition` *reports* as `humanLockRequired`
    on PROCEED (l. 461): destructive target ∧ the operator flag. -/
def reviewHumanLockRequired (target : String) (requireHumanLock : Bool) : Bool :=
  destructive target && requireHumanLock

/-! ## Foundation scoring (`assessQueryExecution` ll. 467–501,
`assessIncidentTransition` ll. 503–540)

Deterministic adversary, out of 100: 40 guardrails (added
*unconditionally* by both assessors — they trust that R0 already ran),
30 bounded result, 30 state corroboration; total capped at 100 (the
cap never binds: the components sum to at most 100). The floor is
`GENERAL_FLOOR = 70` and the lock test is `score < 70`, so exactly 70
passes. -/

def boundedQ (eventCount : Nat) : Bool := 1 ≤ eventCount && eventCount ≤ 200

def queryScore (eventCount : Nat) (corroborated : Bool) : Nat :=
  min (40 + (if boundedQ eventCount then 30 else 0) +
    (if corroborated then 30 else 0)) 100

theorem query_score_cases (ec : Nat) (c : Bool) :
    queryScore ec c = 40 ∨ queryScore ec c = 70 ∨ queryScore ec c = 100 := by
  by_cases hb : boundedQ ec = true <;> by_cases hc : c = true <;>
    simp [queryScore, hb, hc]

/-- The floor, exactly: a query self-certifies (score ≥ 70) iff it
    earned the bounded-result points or the corroboration points. -/
theorem query_score_floor_iff (ec : Nat) (c : Bool) :
    70 ≤ queryScore ec c ↔ boundedQ ec = true ∨ c = true := by
  by_cases hb : boundedQ ec = true <;> by_cases hc : c = true <;>
    simp [queryScore, hb, hc]

theorem query_score_subfloor_iff (ec : Nat) (c : Bool) :
    queryScore ec c < 70 ↔ boundedQ ec = false ∧ c = false := by
  by_cases hb : boundedQ ec = true <;> by_cases hc : c = true <;>
    simp [queryScore, hb, hc]

theorem query_score_hundred_iff (ec : Nat) (c : Bool) :
    queryScore ec c = 100 ↔ boundedQ ec = true ∧ c = true := by
  by_cases hb : boundedQ ec = true <;> by_cases hc : c = true <;>
    simp [queryScore, hb, hc]

/-- Transition assessment, returned as (score, fatal). `frm` is the
    incident's status when the incident resolved (and the status string
    is non-empty — an empty status is falsy in the code and behaves
    like `none` here); `ex` is whether the incident resolved at all.
    `fatal` is the state-contradiction flag: set exactly when a status
    exists but the move is not forward. -/
def transitionScore (ex : Bool) (frm : Option String) (target : String) : Nat × Bool :=
  let boundedPts := if ex then 30 else 0
  let corrPts := match frm with
    | some f => if forward f target then 30 else 0
    | none => 0
  let fatal := match frm with
    | some f => !forward f target
    | none => false
  (min (40 + boundedPts + corrPts) 100, fatal)

theorem transition_score_full {f t : String} (h : forward f t = true) :
    transitionScore true (some f) t = (100, false) := by
  simp [transitionScore, h]

theorem transition_score_contradiction {f t : String} (h : forward f t = false) :
    transitionScore true (some f) t = (70, true) := by
  simp [transitionScore, h]

/-- A contradiction scores *at* the floor (70) yet is fatal — the
    fatal flag, checked first in `humanLockVerdict`, is the only thing
    that refuses it. -/
theorem transition_fatal_iff {ex : Bool} {f t : String} :
    (transitionScore ex (some f) t).2 = true ↔ forward f t = false := by
  simp [transitionScore]

theorem transition_score_absent :
    transitionScore false none "resolved" = (40, false) := rfl

/-! ## The human lock (`humanLockVerdict` ll. 542–609)

`ledgerLocked` abstracts the code's ledger lookup (ll. 583–594): a
latest record for the decision id that is integrity- and
envelope-valid, has status LOCKED, and carries a `confirmed_by`.
`cbPresent` abstracts `confirmedBy && confirmedBy.trim()` — *any*
non-empty name string; the function receives no confirmer identity or
role, which is the point of `counterexample_sre_names_confirmer`. -/

inductive Kind where
  | query | transition
  deriving DecidableEq, BEq, Repr

inductive Via where
  | confirmedBy | ledger | selfCertified | refused
  deriving DecidableEq, BEq, Repr

structure Verdict where
  locked : Bool
  via : Via
  deriving DecidableEq, Repr

/-- `needsLock` (ll. 550–551): sub-floor, or — for the transition
    *kind* — whenever REQUIRE_HUMAN_LOCK is on. Note the code binds
    `destructive := kind === "incident_transition"` here, NOT the
    review's target-based destructive flag. -/
def needsLock (kind : Kind) (score : Nat) (requireHumanLock : Bool) : Bool :=
  score < 70 || (match kind with | .transition => requireHumanLock | .query => false)

def humanLockVerdict (kind : Kind) (fatal : Bool) (score : Nat)
    (requireHumanLock : Bool) (cbPresent : Bool) (actor : Role)
    (ledgerLocked : Bool) : Verdict :=
  if fatal then ⟨false, .refused⟩
  else if !needsLock kind score requireHumanLock then ⟨false, .selfCertified⟩
  else if cbPresent then
    if actor = .aiAgent then ⟨false, .refused⟩ else ⟨true, .confirmedBy⟩
  else if ledgerLocked then ⟨true, .ledger⟩
  else ⟨false, .refused⟩

/-- A state contradiction is refused outright — before the floor,
    before any confirmer: no confirmer can wave it through. -/
theorem verdict_fatal_refused (k : Kind) (s : Nat) (rhl cb l : Bool) (a : Role) :
    humanLockVerdict k true s rhl cb a l = ⟨false, .refused⟩ := rfl

theorem verdict_selfCertified_iff {k : Kind} {f : Bool} {s : Nat}
    {rhl cb l : Bool} {a : Role} :
    (humanLockVerdict k f s rhl cb a l).via = .selfCertified ↔
      f = false ∧ needsLock k s rhl = false := by
  by_cases hf : f = true <;> by_cases hn : needsLock k s rhl = true <;>
    by_cases hc : cb = true <;> by_cases ha : a = .aiAgent <;>
    by_cases hl : l = true <;>
    simp [humanLockVerdict, hf, hn, hc, ha, hl]

theorem verdict_confirmedBy_iff {k : Kind} {f : Bool} {s : Nat}
    {rhl cb l : Bool} {a : Role} :
    (humanLockVerdict k f s rhl cb a l).via = .confirmedBy ↔
      f = false ∧ needsLock k s rhl = true ∧ cb = true ∧ a ≠ .aiAgent := by
  by_cases hf : f = true <;> by_cases hn : needsLock k s rhl = true <;>
    by_cases hc : cb = true <;> by_cases ha : a = .aiAgent <;>
    by_cases hl : l = true <;>
    simp [humanLockVerdict, hf, hn, hc, ha, hl]

theorem verdict_ledger_iff {k : Kind} {f : Bool} {s : Nat}
    {rhl cb l : Bool} {a : Role} :
    (humanLockVerdict k f s rhl cb a l).via = .ledger ↔
      f = false ∧ needsLock k s rhl = true ∧ cb = false ∧ l = true := by
  by_cases hf : f = true <;> by_cases hn : needsLock k s rhl = true <;>
    by_cases hc : cb = true <;> by_cases ha : a = .aiAgent <;>
    by_cases hl : l = true <;>
    simp [humanLockVerdict, hf, hn, hc, ha, hl]

/-- Locked implies one of exactly two routes — a named `confirmed_by`
    (by a non-AI *actor*; the confirmer is never authenticated here) or
    a valid LOCKED ledger record — and always a lock was needed and no
    fatal was present. -/
theorem verdict_locked_routes {k : Kind} {f : Bool} {s : Nat}
    {rhl cb l : Bool} {a : Role}
    (h : (humanLockVerdict k f s rhl cb a l).locked = true) :
    f = false ∧ needsLock k s rhl = true ∧
      ((cb = true ∧ a ≠ .aiAgent) ∨ (cb = false ∧ l = true)) := by
  by_cases hf : f = true
  · simp [humanLockVerdict, hf] at h
  have hf' : f = false := by
    cases f
    · rfl
    · exact (hf rfl).elim
  by_cases hn : needsLock k s rhl = true
  · by_cases hc : cb = true
    · by_cases ha : a = .aiAgent
      · simp [humanLockVerdict, hf, hn, hc, ha] at h
      · exact ⟨hf', hn, Or.inl ⟨hc, ha⟩⟩
    · by_cases hl : l = true
      · exact ⟨hf', hn, Or.inr ⟨by simpa using hc, hl⟩⟩
      · simp [humanLockVerdict, hf, hn, hc, hl] at h
  · simp [humanLockVerdict, hf, hn] at h

/-- An AI principal supplying `confirmed_by` is refused — self-approval
    is the one confirmer check the inline path does make
    (ll. 562–571). -/
theorem ai_cannot_self_confirm {k : Kind} {s : Nat} {rhl l : Bool}
    (h : needsLock k s rhl = true) :
    humanLockVerdict k false s rhl true .aiAgent l = ⟨false, .refused⟩ := by
  simp [humanLockVerdict, h]

/-- Floor boundary: the test is `score < 70`, so exactly 70 does NOT
    need a lock (self-certifies) and 69 does. -/
theorem floor_boundary_exact : needsLock .query 70 false = false := rfl
theorem floor_boundary_below : needsLock .query 69 false = true := rfl

/-- Under REQUIRE_HUMAN_LOCK, EVERY incident transition needs a lock at
    the verdict — even a full-score, non-destructive one — because the
    verdict keys on the action *kind*, not the target status. -/
theorem transition_always_needs_lock (s : Nat) :
    needsLock .transition s true = true := by
  simp [needsLock]

/-- …whereas the review stage reports `humanLockRequired = false` for
    the same non-destructive transition. The two stages disagree; the
    review's field is never consulted by either route. -/
theorem review_verdict_divergence :
    reviewHumanLockRequired "investigating" true = false ∧
      needsLock .transition 100 true = true :=
  ⟨rfl, transition_always_needs_lock 100⟩

/-- Roles eligible to confirm via the decisions API
    (`eligibleConfirmerRoles`, chp.ts ll. 189–191). -/
def eligibleRoles : Kind → List Role
  | .transition => [.socTier2]
  | .query => [.socTier1, .socTier2]

/-- COUNTEREXAMPLE — naming is not confirming. An `sre` actor (a write
    role, but NOT an eligible confirmer for transitions) locks a
    destructive transition by putting any non-empty string in
    `confirmed_by`: `humanLockVerdict` never receives a confirmer role
    and never checks eligibility. The eligibility check exists only in
    `confirm` (the decisions API path). -/
theorem counterexample_sre_names_confirmer :
    humanLockVerdict .transition false 100 true true .sre false =
      ⟨true, .confirmedBy⟩ ∧
    memRole (eligibleRoles .transition) .sre = false :=
  ⟨rfl, rfl⟩

/-! ## Route composition

Query route (`api/splunk/query/route.ts`): results are returned for
via ∈ {confirmed_by, ledger, self_certified}; only `refused` withholds
them (403). Incidents route (`api/incidents/route.ts` ll. 132–157):
the transition is applied iff `lock.locked` — self-certification is
treated exactly like refusal. -/

def queryReturnsResults (v : Verdict) : Bool := v.via != .refused

def incidentApplies (v : Verdict) : Bool := v.locked

/-- COUNTEREXAMPLE — the incidents route deadlocks when
    REQUIRE_HUMAN_LOCK is off. A full-score, non-fatal transition
    self-certifies (the repo's own test expects exactly this verdict),
    the verdict function returns before ever consulting `confirmed_by`
    or the ledger, and the route applies only `locked` verdicts — so
    NO request, with or without a confirmer or a LOCKED ledger record,
    can ever apply an incident transition in that configuration. The
    query route proceeds on the very same verdict. -/
theorem route_deadlock (cb l : Bool) (a : Role) :
    humanLockVerdict .transition false 100 false cb a l = ⟨false, .selfCertified⟩ ∧
      incidentApplies ⟨false, .selfCertified⟩ = false ∧
      queryReturnsResults ⟨false, .selfCertified⟩ = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## Third-party confirmation (`SocChpGate.confirm`, ll. 671–711)

Modelled over the latest record for a single decision id (what
`ledger.get` returns and all `confirm` consults). Check order, as in
the code: unknown id → integrity/envelope → already LOCKED
(idempotent return) → confirmer-role eligibility → non-empty name →
append LOCKED. Notably absent: any check that the confirmer differs
from the original actor, and any check that the prior status is
PROVISIONAL_LOCK specifically. -/

inductive SessionStatus where
  | exploring | provisionalLock | locked | reframeRequired | halt
  deriving DecidableEq, BEq, Repr

structure LatestRecord where
  kind : Kind
  status : SessionStatus
  integrityValid : Bool
  envelopeValid : Bool
  confirmedBy : Option String
  supersedes : Option String
  actorId : String
  digest : String
  deriving DecidableEq, Repr

inductive ConfirmOutcome where
  | rejected | idempotent | accepted
  deriving DecidableEq, Repr

def confirm (latest : Option LatestRecord) (name : String) (nameNonempty : Bool)
    (role : Role) : Option LatestRecord × ConfirmOutcome :=
  match latest with
  | none => (none, .rejected)
  | some prior =>
      if !prior.integrityValid || !prior.envelopeValid then (some prior, .rejected)
      else if prior.status = .locked then (some prior, .idempotent)
      else if !memRole (eligibleRoles prior.kind) role then (some prior, .rejected)
      else if !nameNonempty then (some prior, .rejected)
      else (some { prior with status := .locked, confirmedBy := some name, supersedes := some prior.digest }, .accepted)

theorem confirm_unknown (n : String) (ne : Bool) (r : Role) :
    confirm none n ne r = (none, .rejected) := rfl

/-- A tampered latest record is rejected even if it claims LOCKED —
    the integrity check precedes the idempotence check (ll. 676–680
    before ll. 682–684). -/
theorem confirm_tampered_rejected {p : LatestRecord} (h : p.integrityValid = false)
    (n : String) (ne : Bool) (r : Role) :
    confirm (some p) n ne r = (some p, .rejected) := by
  simp [confirm, h]

/-- Idempotence: confirming an already-LOCKED (valid) decision returns
    it unchanged and appends nothing. -/
theorem confirm_idempotent {p : LatestRecord} (hi : p.integrityValid = true)
    (he : p.envelopeValid = true) (hs : p.status = .locked)
    (n : String) (ne : Bool) (r : Role) :
    confirm (some p) n ne r = (some p, .idempotent) := by
  simp [confirm, hi, he, hs]

/-- An ineligible confirmer role is rejected, state unchanged — for
    transitions only `soc_tier2` may confirm (ll. 686–690). -/
theorem confirm_ineligible_rejected {p : LatestRecord} {r : Role}
    (hi : p.integrityValid = true) (he : p.envelopeValid = true)
    (hs : p.status ≠ .locked) (hr : memRole (eligibleRoles p.kind) r = false)
    (n : String) (ne : Bool) :
    confirm (some p) n ne r = (some p, .rejected) := by
  simp [confirm, hi, he, hs, hr]

/-- Success: the appended record is LOCKED, carries the confirmer's
    name, and supersedes the prior body digest (ll. 693–708). -/
theorem confirm_success {p : LatestRecord} {r : Role}
    (hi : p.integrityValid = true) (he : p.envelopeValid = true)
    (hs : p.status ≠ .locked) (hr : memRole (eligibleRoles p.kind) r = true)
    (n : String) :
    confirm (some p) n true r =
      (some { p with status := .locked, confirmedBy := some n, supersedes := some p.digest }, .accepted) := by
  simp [confirm, hi, he, hs, hr]

/-- COUNTEREXAMPLE — self-confirmation via the decisions API. Every
    check in `confirm` passes when the confirmer is the decision's own
    actor: the function takes no confirmer identity distinct from the
    free-text name, and the decisions route even defaults the name to
    the caller's own user id. "Third-party validation" is a comment,
    not a check. -/
theorem confirm_self_confirmation :
    confirm (some { kind := .transition, status := .provisionalLock,
                    integrityValid := true, envelopeValid := true,
                    confirmedBy := none, supersedes := none,
                    actorId := "u1", digest := "d0" })
        "u1" true .socTier2 =
      (some { kind := .transition, status := .locked,
              integrityValid := true, envelopeValid := true,
              confirmedBy := some "u1", supersedes := some "d0",
              actorId := "u1", digest := "d0" }, .accepted) := rfl

/-- COUNTEREXAMPLE — `confirm` never checks that the prior status is
    PROVISIONAL_LOCK (its docstring's claim): a HALT record locks just
    as well. (Routes only ever record PROVISIONAL_LOCK/LOCKED, so this
    is latent — but the gate function itself admits it.) -/
theorem confirm_any_status :
    confirm (some { kind := .query, status := .halt,
                    integrityValid := true, envelopeValid := true,
                    confirmedBy := none, supersedes := none,
                    actorId := "u2", digest := "d1" })
        "boss" true .socTier1 =
      (some { kind := .query, status := .locked,
              integrityValid := true, envelopeValid := true,
              confirmedBy := some "boss", supersedes := some "d1",
              actorId := "u2", digest := "d1" }, .accepted) := rfl

/-! ## Ledger integrity (`checkIntegrity`, ll. 288–296)

`integrity_valid` is an *unkeyed* SHA-256 equality: digest of body vs
the digest stored beside it in the same file. With `H` abstract: -/

def integrityValid (H : String → String) (body stored : String) : Bool :=
  decide (H body = stored)

/-- The check detects *corruption* (body changed, digest not) but not
    *forgery*: anyone who can write the ledger line can recompute the
    digest over a forged body and pass. Formally, the acceptance
    predicate is satisfiable for every body. -/
theorem integrity_forgeable (H : String → String) (b : String) :
    integrityValid H b (H b) = true := by
  simp [integrityValid]

end ShieldGate
