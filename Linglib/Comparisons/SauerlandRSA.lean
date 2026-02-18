/-
# Sauerland-RSA Correspondence

Formalizes the connection between Sauerland (2004)'s epistemic implicature
framework and RSA's probabilistic reasoning.

## Sauerland's Framework

Sauerland distinguishes:
- **Primary implicatures**: ¬Kψ ("speaker doesn't know ψ")
- **Secondary implicatures**: K¬ψ ("speaker knows ¬ψ")

Secondary implicatures are derived from primary ones via an additional
"competence" assumption: the speaker either knows ψ or knows ¬ψ.

Key insight: Secondary K¬ψ is blocked if it contradicts the assertion
or the primary implicatures.

## RSA Framework

RSA computes:
- L0(w|u): literal interpretation (uniform over consistent worlds)
- S1(u|w): speaker utility (proportional to L0^α)
- L1(w|u): pragmatic interpretation (Bayesian update on S1)

## Main Results

**Theorem (Primary Correspondence)**:
ψ has primary implicature ¬Kψ iff L1 assigns positive probability to ¬ψ worlds.

**Theorem (Categorical-Graded Distinction)**:
Sauerland derives categorical K¬(A∧B) for disjunction.
RSA derives graded dispreference: P(both) << P(onlyA).
The categorical result is the limit as α → ∞.

**Theorem (Blocking Correspondence)**:
Secondary K¬ψ is blocked in Sauerland iff RSA's L1 assigns positive
probability to ψ-worlds (due to interaction with other alternatives).

## Status

RSA evaluation infrastructure (RSA.Eval.L1_world, boolToRat, getScore) has been
removed. Epistemic logic framework (EpistemicState, knows, possible, duality,
blocking), domain types (DisjWorld, DisjUtterance, disjMeaning), and structural
theorems are preserved. RSA L1 computation (disjL1, p_both) and graded
exclusivity theorems remain with `sorry` for future reimplementation.

## References

- Sauerland, U. (2004). Scalar implicatures in complex sentences. L&P 27:367-391.
- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in language games.
- Goodman, N. D. & Frank, M. C. (2016). Pragmatic language interpretation as probabilistic inference.
-/

import Linglib.Core.Proposition
import Mathlib.Data.Rat.Defs

namespace SauerlandRSA

open Core.Proposition


/--
An epistemic state represents what the speaker knows.
We model this as a set of worlds the speaker considers possible.
-/
structure EpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's knowledge -/
  possible : List W
  /-- Non-empty (speaker knows something is true) -/
  nonempty : possible ≠ []

/--
K operator: speaker knows φ iff φ is true in all epistemically possible worlds.
-/
def knows {W : Type*} (e : EpistemicState W) (φ : BProp W) : Bool :=
  e.possible.all φ

/--
P operator: speaker considers φ possible.
-/
def possible {W : Type*} (e : EpistemicState W) (φ : BProp W) : Bool :=
  e.possible.any φ

/--
Helper: ¬(!b) = true iff b = true
-/
private theorem not_not_eq_true (b : Bool) : ((!b) ≠ true) ↔ (b = true) := by
  cases b <;> decide

/--
Helper: (!b) = true iff b = false
-/
private theorem not_eq_true_iff (b : Bool) : ((!b) = true) ↔ (b = false) := by
  cases b <;> decide

/--
Standard epistemic duality: ¬K¬φ ↔ Pφ
-/
theorem duality {W : Type*} (e : EpistemicState W) (φ : BProp W) :
    (knows e (λ w => !φ w) = false) ↔ (possible e φ = true) := by
  simp only [knows, possible, Bool.eq_false_iff, ne_eq, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h
    push_neg at h
    obtain ⟨w, hw, hneg⟩ := h
    use w, hw
    exact (not_not_eq_true (φ w)).mp hneg
  · intro ⟨w, hw, hφ⟩ h
    have hneg := h w hw
    rw [not_eq_true_iff] at hneg
    rw [hφ] at hneg
    contradiction


/--
A scalar scenario specifies an assertion and its alternatives.
-/
structure ScalarScenario (W : Type*) where
  /-- The asserted proposition -/
  assertion : BProp W
  /-- The scalar alternatives (stronger propositions) -/
  alternatives : List (BProp W)

/--
Primary implicature: speaker doesn't know the stronger alternative.
-/
def hasPrimaryImplicature {W : Type*} (S : ScalarScenario W) (e : EpistemicState W)
    (ψ : BProp W) : Prop :=
  ψ ∈ S.alternatives ∧ knows e ψ = false

/--
Secondary implicature: speaker knows the alternative is false.
-/
def hasSecondaryImplicature {W : Type*} (e : EpistemicState W) (ψ : BProp W) : Prop :=
  knows e (λ w => !ψ w) = true

/--
Key insight: if ψ is possible, then K¬ψ is blocked.
-/
theorem secondary_blocked_if_possible {W : Type*} (e : EpistemicState W) (ψ : BProp W) :
    possible e ψ = true → knows e (λ w => !ψ w) = false := by
  intro hpos
  simp only [possible, List.any_eq_true] at hpos
  simp only [knows, Bool.eq_false_iff, ne_eq, List.all_eq_true]
  obtain ⟨w, hw, hψ⟩ := hpos
  intro h
  have hneg := h w hw
  rw [not_eq_true_iff] at hneg
  rw [hψ] at hneg
  contradiction


/--
Worlds for the disjunction scenario: A∨B with 4 possible truth combinations.
-/
inductive DisjWorld where
  | neither : DisjWorld  -- ¬A ∧ ¬B
  | onlyA : DisjWorld    -- A ∧ ¬B
  | onlyB : DisjWorld    -- ¬A ∧ B
  | both : DisjWorld     -- A ∧ B
  deriving DecidableEq, BEq, Repr, Inhabited

open DisjWorld

/-- Proposition A is true -/
def propA : BProp DisjWorld
  | onlyA | both => true
  | _ => false

/-- Proposition B is true -/
def propB : BProp DisjWorld
  | onlyB | both => true
  | _ => false

/-- A ∨ B -/
def propAorB : BProp DisjWorld
  | neither => false
  | _ => true

/-- A ∧ B -/
def propAandB : BProp DisjWorld
  | both => true
  | _ => false


/--
**Theorem (Primary-Possibility Correspondence)**:

Sauerland: ¬Kψ (speaker doesn't know ψ)
RSA: P(¬ψ worlds) > 0 (positive probability on ¬ψ worlds)

These are equivalent when the epistemic state corresponds to the support
of the probability distribution.
-/
theorem primary_possibility_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : BProp W) :
    (knows e ψ = false) → (possible e (λ w => !ψ w) = true) := by
  intro h
  simp only [knows, Bool.eq_false_iff, ne_eq, List.all_eq_true] at h
  simp only [possible, List.any_eq_true]
  push_neg at h
  obtain ⟨w, hw, hψ⟩ := h
  use w, hw
  -- hψ : ψ w ≠ true means ψ w = false
  -- We need to show (!ψ w) = true, i.e., ψ w = false
  rw [not_eq_true_iff]
  cases hψw : ψ w
  · rfl
  · exact absurd hψw hψ

/--
**Theorem (Blocking Correspondence)**:
Secondary K¬ψ is blocked when Pψ holds.
-/
theorem blocking_correspondence {W : Type*}
    (e : EpistemicState W) (ψ : BProp W) :
    possible e ψ = true → ¬hasSecondaryImplicature e ψ := by
  intro hpos hsec
  simp only [hasSecondaryImplicature] at hsec
  have := secondary_blocked_if_possible e ψ hpos
  rw [hsec] at this
  contradiction


/-- Utterances for disjunction scenario -/
inductive DisjUtterance where
  | AorB  -- "A or B"
  | A     -- "A"
  | B     -- "B"
  | AandB -- "A and B"
  deriving DecidableEq, BEq, Repr, Inhabited

open DisjUtterance

/-- Literal semantics for disjunction utterances -/
def disjMeaning : DisjUtterance → DisjWorld → Bool
  | .AorB, .neither => false
  | .AorB, _ => true
  | .A, .onlyA => true
  | .A, .both => true
  | .A, _ => false
  | .B, .onlyB => true
  | .B, .both => true
  | .B, _ => false
  | .AandB, .both => true
  | .AandB, _ => false


/-!
## RSA Graded Exclusivity (Stubs)

RSA evaluation infrastructure (RSA.Eval.L1_world, boolToRat, getScore) has been
removed. The RSA L1 computation (disjL1) and graded exclusivity theorems
need reimplementation with the new RSAConfig framework.

The key results to reimplement:
- `rsa_disjunction_graded_exclusivity`: L1("A or B") assigns higher probability
  to exclusive worlds (onlyA, onlyB) than inclusive (both)
- `rsa_both_has_positive_probability`: RSA assigns positive (but lower)
  probability to "both" world (unlike Sauerland's categorical K¬(A∧B))
- `p_both_decreases_with_alpha`: As α increases, P(both) decreases,
  approaching Sauerland's categorical framework in the limit
- `sauerland_is_rsa_limit`: Sauerland's categorical framework is the α → ∞
  limit of RSA
-/


/-
## Main Results

1. **Primary implicature ¬Kψ** corresponds to L1 assigning positive
   probability to ¬ψ worlds.

2. **Secondary implicature K¬ψ** in Sauerland corresponds to a *graded*
   dispreference in RSA: L1 assigns lower (but positive) probability
   to ψ worlds.

3. **Blocking** occurs when possibility implicatures force positive
   probability on worlds that would otherwise be excluded.

4. For disjunction, RSA correctly derives:
   - Graded exclusivity: P(both) < P(onlyA) = P(onlyB)
   - The categorical limit: as α → ∞, P(both) → 0

## The Key Difference: Categorical vs. Graded

| Sauerland | RSA |
|-----------|-----|
| K¬(A∧B) categorical | P(both) < P(onlyA) graded |
| PA categorical | P(onlyA) > 0 |
| Competence assumed | Emerges from α |

RSA's graded predictions better match empirical judgment data,
while Sauerland's categorical framework captures the logical structure.
-/

end SauerlandRSA
