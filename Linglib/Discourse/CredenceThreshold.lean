import Linglib.Discourse.SpeechAct.Basic
import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.CommonGround
import Mathlib.Data.Rat.Defs

/-!
# Credence-Threshold Assertion

[lauer-2013]

A credence-gated model of assertion: a proposition is assertable when
the speaker's credence exceeds a context-dependent threshold.
Lauer-adjacent in motivation but **not** the central [lauer-2013]
contribution.

## ⚠ Naming history (was `Lauer.lean`)

This file was previously named `Lauer.lean` but its content is a
credence-threshold model, not [lauer-2013]'s headline doxastic /
preferential commitment split. The actual Lauer 2013 framework is
substrate-supported elsewhere:

- The doxastic / preferential force distinction lives in
  `Discourse/Commitment.lean` as `CommitmentForce` (with
  `.doxastic` and `.preferential` cases).
- Krifka-style commitment spaces consume it via
  `Discourse/CommitmentSpace.lean` (the `force` parameter on
  `IndexedWeightedCommitment.commit/refuse` and the
  `toDoxasticContextSet` / `toPreferentialContextSet` projections).
- The [condoravdi-lauer-2012] imperative-as-PEP study lives in
  `Studies/CondoravdiLauer2012.lean`.

## Key properties of this file

- **Credence function**: the speaker's subjective probability over
  worlds (rational-valued, matching RSA's `worldPrior`)
- **Assertability threshold**: a credence threshold above which
  assertion is licensed (matching RSA's `alpha` parameter)
- **Bridge to RSA**: credence maps to RSA's `worldPrior`, threshold
  maps to the rationality parameter

Closest to Stalnaker in structure (no explicit commitment/belief
separation), but adds a probabilistic dimension that the bare CommonGround
model lacks.

-/

namespace Discourse.CredenceThreshold

open Discourse.Commitment (CommitmentSlate)
open CommonGround (ContextSet)

-- ════════════════════════════════════════════════════
-- § 1. Credence Functions
-- ════════════════════════════════════════════════════

/-- A credence function: the speaker's subjective probability
    assignment to propositions.

    Rational-valued (ℚ) for exact computation, matching RSA convention.
    The function takes a proposition and returns a probability in [0,1]. -/
structure Credence (W : Type*) where
  /-- Probability assignment for a proposition (given as a list of
      proposition-probability pairs). -/
  prob : List (Set W × ℚ)
  /-- Default credence for propositions not in the list. -/
  defaultProb : ℚ := 1/2

namespace Credence

variable {W : Type*}

/-- Look up the credence for a proposition. -/
def lookup (c : Credence W) (p : Set W) [BEq (Set W)] : ℚ :=
  match c.prob.find? (λ ⟨q, _⟩ => q == p) with
  | some ⟨_, v⟩ => v
  | none => c.defaultProb

/-- Uninformative credence: equal probability for everything. -/
def uniform : Credence W := ⟨[], 1/2⟩

end Credence

-- ════════════════════════════════════════════════════
-- § 2. Lauer State
-- ════════════════════════════════════════════════════

/-- Lauer's discourse state: speaker credence + assertability threshold
    + history of assertions.

    The threshold is context-dependent: formal contexts (courtrooms)
    have higher thresholds than casual conversation. -/
structure State (W : Type*) where
  /-- Speaker's credence function -/
  credence : Credence W
  /-- Assertability threshold (credence must exceed this) -/
  threshold : ℚ := 9/10
  /-- List of asserted propositions (for tracking) -/
  asserted : CommitmentSlate W

namespace State

variable {W : Type*}

/-- Initial state: uniform credence, default threshold, no assertions. -/
def empty : State W :=
  ⟨Credence.uniform, 9/10, CommitmentSlate.empty⟩

/-- Assert a proposition: add it to the asserted list.

    Assertability is a precondition (the speaker SHOULD have credence ≥
    threshold), but the operation succeeds regardless — modeling that
    assertion can occur even when the norm is violated (as in lying). -/
def assert (s : State W) (p : Set W) : State W :=
  { s with asserted := s.asserted.add p }

/-- Check if a proposition is assertable (credence ≥ threshold). -/
def assertable (s : State W) (p : Set W) [BEq (Set W)] : Prop :=
  s.credence.lookup p ≥ s.threshold

instance (s : State W) (p : Set W) [BEq (Set W)] : Decidable (assertable s p) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- Context set: worlds compatible with all asserted propositions. -/
def contextSet (s : State W) : ContextSet W :=
  λ w => s.asserted.toContextSet w

/-- Stability: always stable (no table mechanism). -/
def isStable (_ : State W) : Prop := True

instance (s : State W) : Decidable (isStable s) :=
  inferInstanceAs (Decidable True)

end State

-- ════════════════════════════════════════════════════
-- § 3. Bridge to RSA
-- ════════════════════════════════════════════════════

/-!
## RSA Correspondence

Lauer's probabilistic model maps naturally to RSA parameters:

| Lauer | RSA | Role |
|-------|-----|------|
| `credence` | `worldPrior` | probability over worlds |
| `threshold` | `alpha` | rationality / commitment level |
| `asserted` | utterance history | discourse context |

The mapping is conceptual, not formal: RSA's `worldPrior` is a
distribution over worlds (P(w)), while Lauer's credence is a
probability over propositions (P(p)). The connection is:

    P_Lauer(p) = Σ_{w: p(w)} P_RSA(w)

This lifts RSA's world-level prior to Lauer's proposition-level credence.
-/

/-- Always stable (no pending issues mechanism). -/
theorem always_stable {W : Type*} (s : State W) :
    State.isStable s := trivial

-- ════════════════════════════════════════════════════
-- HasContextSet instance
-- ════════════════════════════════════════════════════

open CommonGround in
/-- Credence-threshold states project to a context set via the
    asserted-list intersection (`contextSet`). The credence + threshold
    machinery gates *which* assertions can occur; once asserted, the
    propositional contribution to the context set is the same as
    Stalnakerian narrowing. -/
instance {W : Type*} : HasContextSet (State W) W where
  toContextSet := State.contextSet

open CommonGround in
/-- Credence-threshold states instantiate `HasAssertion`: the credence and
    threshold machinery gates the *felicity* of asserting (the sincerity
    norm), but the effect of an assertion on the context set is exactly
    Stalnakerian narrowing — including for norm-violating assertions
    (lying), which update the context set all the same. -/
instance instHasAssertion {W : Type*} :
    CommonGround.HasAssertion (State W) W where
  initial := State.empty
  assert s p := s.assert p
  toContextSet_initial :=
    Set.eq_univ_of_forall fun _ _ hq => absurd hq List.not_mem_nil
  toContextSet_assert s p := by
    ext w
    rw [Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h p List.mem_cons_self⟩
    · rintro ⟨hs, hp⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hs q hq

end Discourse.CredenceThreshold
