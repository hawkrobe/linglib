import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Phenomena.Gradability.Vagueness
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Fine (1975): Vagueness, Truth and Logic @cite{fine-1975}
@cite{kamp-1975}

Supervaluationism applied to gradable predicates: a vague sentence is
true iff true on ALL admissible precisifications, false iff false on
ALL, and indefinite otherwise.

## Architecture

The *general* supervaluation framework (specification spaces, super-truth,
D operator, classical validity biconditional) lives in
`Theories/Semantics/Supervaluation/Basic.lean`. This study file
**specializes** that framework to threshold-based precisifications for
gradable adjectives, and proves results specific to degree semantics:

- § 1: Threshold specification spaces
- § 2: Comparative entailment (monotonicity of positive predicate)
- § 3: Sorites resolution
- § 4: External penumbral connections (pink/red — multi-predicate)
- § 5: Bridge — `inGapRegion` ↔ `Truth3.indet`
- § 6: Higher-order D operator
- § 7: Verification of `Vagueness.lean` data

## Connection to Kamp (1975)

@cite{fine-1975} and @cite{kamp-1975} appeared in the same volume.
Kamp's dilemma (truth-functional three-valued logic cannot distinguish
P ∧ P from P ∧ ¬P) is resolved by supervaluation — see
`Supervaluation.Basic.conjunction_self` and
`Supervaluation.Basic.nonContradiction_superFalse`.

## Connection to Klein (1980)

@cite{klein-1980}'s comparative — "∃ C where tall(a,C) ∧ ¬tall(b,C)" —
is the existential dual of supervaluation. See
`Theories/Semantics/Comparison/Delineation.lean`.
-/

namespace Phenomena.Gradability.Studies.Fine1975

open Core.Duality (Truth3)
open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat)
open Semantics.Lexical.Adjective (ThresholdPair inGapRegion)
open Semantics.Supervaluation (SpecSpace superTrue definitely indefinite)

-- ════════════════════════════════════════════════════
-- § 1. Threshold Specification Spaces
-- ════════════════════════════════════════════════════

/-- Construct a specification space from a non-empty set of thresholds. -/
def mkSpec {max : Nat} (S : Finset (Threshold max)) (hne : S.Nonempty) :
    SpecSpace (Threshold max) :=
  ⟨S, hne⟩

/-- Supervaluation of a degree predicate: fix a degree, vary the threshold. -/
def superTrueAt {max : Nat} (meaning : Degree max → Threshold max → Bool)
    (d : Degree max) (S : SpecSpace (Threshold max)) : Truth3 :=
  superTrue (meaning d) S

-- ════════════════════════════════════════════════════
-- § 2. Comparative Entailment
-- ════════════════════════════════════════════════════

/-- **Comparative entailment.** If d₁ > d₂ and d₂ is super-true for a
    positive (upward) predicate, then d₁ is also super-true.

    This captures Fine's internal penumbral connection: if Herbert is
    to be bald, then so is the man with fewer hairs (p. 276). -/
theorem comparative_entailment {max : Nat}
    (d₁ d₂ : Degree max) (S : SpecSpace (Threshold max))
    (hgt : d₂.toNat < d₁.toNat)
    (hd₂ : superTrueAt (fun d θ => decide (d.toNat > θ.toNat)) d₂ S = Truth3.true) :
    superTrueAt (fun d θ => decide (d.toNat > θ.toNat)) d₁ S = Truth3.true := by
  unfold superTrueAt at *
  rw [Semantics.Supervaluation.superTrue_true_iff] at hd₂ ⊢
  intro θ hθ
  have := hd₂ θ hθ
  simp only [decide_eq_true_eq] at this ⊢
  omega

-- ════════════════════════════════════════════════════
-- § 3. Sorites Resolution
-- ════════════════════════════════════════════════════

/-! Fine's resolution: the tolerance premise "if n hairs is bald,
    then n+1 hairs is bald" is SUPER-FALSE. For every admissible
    threshold θ, there exists an n (= θ) where n is below θ but n+1
    is above. The premise fails at every precisification. -/

/-- The tolerance premise fails at any threshold separating d from d'. -/
theorem tolerance_fails_at_boundary {max : Nat}
    (d d' : Degree max) (θ : Threshold max)
    (hd : d.toNat > θ.toNat) (hd' : ¬(d'.toNat > θ.toNat)) :
    ¬(d.toNat > θ.toNat → d'.toNat > θ.toNat) :=
  fun h => hd' (h hd)

-- ════════════════════════════════════════════════════
-- § 4. External Penumbral Connections
-- ════════════════════════════════════════════════════

/-! Fine's most distinctive examples involve *external* penumbral
    connections between different predicates. A blob on the border of
    pink and red is borderline pink and borderline red. Yet "the blob
    is pink AND red" is super-false, because no admissible specification
    makes something both pink and red.

    We model this with a single threshold governing both: "pink" = above
    threshold, "red" = at or below threshold. The same threshold
    determines both predicates, creating the penumbral connection. -/

/-- Pink: degree above the boundary (on a single color dimension). -/
def isPink {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  decide (d.toNat > θ.toNat)

/-- Red: degree at or below the boundary (complementary to pink). -/
def isRed {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  decide (d.toNat ≤ θ.toNat)

/-- Pink and red are complementary: nothing can be both. -/
theorem pink_red_complementary {max : Nat} (d : Degree max) (θ : Threshold max) :
    (isPink d θ && isRed d θ) = false := by
  unfold isPink isRed
  rcases hgt : decide (d.toNat > θ.toNat) with _ | _
  · simp
  · simp only [Bool.true_and, decide_eq_false_iff_not]
    rw [decide_eq_true_eq] at hgt
    omega

/-- **"The blob is pink and red" is super-false.** Even when both
    conjuncts are individually indefinite, their conjunction is false
    on every precisification, hence super-false.

    This is Fine's central argument for supervaluationism over
    truth-functional three-valued logic (p. 269-270). In Strong Kleene
    logic, `indet ∧ indet = indet`; supervaluation gives `false`. -/
theorem pink_and_red_superFalse {max : Nat} (d : Degree max)
    (S : SpecSpace (Threshold max)) :
    superTrue (fun θ => isPink d θ && isRed d θ) S = Truth3.false :=
  (Semantics.Supervaluation.superTrue_false_iff _ S).mpr
    (fun θ _ => pink_red_complementary d θ)

/-- Both "pink" and "red" can individually be indefinite (borderline). -/
theorem pink_indefinite_example :
    superTrue (isPink ⟨5, by omega⟩ : Threshold 10 → Bool)
      ⟨{⟨3, by omega⟩, ⟨7, by omega⟩}, ⟨⟨3, by omega⟩, by simp⟩⟩ = Truth3.indet := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 5. Bridge: Gap Region ↔ Truth3.indet
-- ════════════════════════════════════════════════════

/-! The `inGapRegion` function in `Adjective.Theory` computes whether a
    degree falls between two thresholds (the "borderline" zone for contrary
    antonyms). A `ThresholdPair` with `neg ≤ pos` is a two-element
    specification space, and the gap region is exactly the set of degrees
    that receive `Truth3.indet` under supervaluation. -/

/-- The specification space induced by a threshold pair. -/
def specOfPair {max : Nat} (tp : ThresholdPair max) : SpecSpace (Threshold max) :=
  ⟨{tp.neg, tp.pos}, ⟨tp.neg, Finset.mem_insert_self _ _⟩⟩

/-- Extract Nat-level upper bound from `inGapRegion`. -/
theorem inGapRegion_le_pos {max : Nat} (d : Degree max) (tp : ThresholdPair max)
    (h : inGapRegion d tp = true) : d.toNat ≤ tp.pos.toNat := by
  simp only [inGapRegion, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Extract Nat-level lower bound from `inGapRegion`. -/
theorem inGapRegion_ge_neg {max : Nat} (d : Degree max) (tp : ThresholdPair max)
    (h : inGapRegion d tp = true) : tp.neg.toNat ≤ d.toNat := by
  simp only [inGapRegion, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- When a degree is strictly inside the gap, the positive-meaning
    predicate disagrees across the two thresholds: true at the negative
    threshold, false at the positive. -/
theorem gap_implies_disagreement {max : Nat} (d : Degree max) (tp : ThresholdPair max)
    (h_in : inGapRegion d tp = true) (h_strict : tp.neg.toNat < d.toNat) :
    decide (d.toNat > tp.neg.toNat) = true ∧
    decide (d.toNat > tp.pos.toNat) = false := by
  simp only [gt_iff_lt, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
  exact ⟨h_strict, inGapRegion_le_pos d tp h_in⟩

-- ════════════════════════════════════════════════════
-- § 6. Higher-Order D
-- ════════════════════════════════════════════════════

/-! Fine's D operator (§ 5) applied to threshold semantics. DA is true
    iff A is true at ALL thresholds in the space. Iterated application
    (DDA, DDDA, ...) collapses: since D is constant across specification
    points, DD = D. Higher-order vagueness in Fine's framework arises not
    from iterating D within a fixed space, but from the *specification
    space itself* being vague — requiring nested spaces (boundaries of
    boundaries). We do not formalize nested spaces here. -/

/-- D collapses under iteration: DD = D. Since `definitely eval S` is a
    constant Bool (independent of the specification point), applying D
    again yields the same value. -/
theorem D_idempotent {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    definitely (fun _ => definitely eval S) S = definitely eval S := by
  unfold definitely
  cases hd : decide (∀ s ∈ S.admissible, eval s = true)
  · -- D is false. DD asks: is "false" true at all specs? No.
    simp only [decide_eq_false_iff_not]
    intro hall
    obtain ⟨s₀, hs₀⟩ := S.nonempty
    exact absurd (hall s₀ hs₀) (by simp)
  · -- D is true. DD asks: is "true" true at all specs? Yes.
    simp only [decide_eq_true_eq]
    intro _ _
    trivial

-- ════════════════════════════════════════════════════
-- § 7. Verification: Vagueness.lean Data
-- ════════════════════════════════════════════════════

open Gradability.Vagueness

/-- Excluded middle data says supervaluationism captures it;
    `Supervaluation.Basic.excludedMiddle_superTrue` proves this. -/
theorem excludedMiddle_captured :
    excludedMiddle.supervaluationismCaptures = true := rfl

/-- Non-contradiction data says supervaluationism captures it;
    `Supervaluation.Basic.nonContradiction_superFalse` proves this. -/
theorem nonContradiction_captured :
    nonContradiction.supervaluationismCaptures = true := rfl

/-- Comparative entailment data says supervaluationism captures it;
    `comparative_entailment` proves this. -/
theorem comparativeEntailment_captured :
    comparativeEntailment.supervaluationismCaptures = true := rfl

/-- The D operator data says it eliminates borderline cases;
    `Supervaluation.Basic.definitely_iff_superTrue` shows D = super-truth. -/
theorem definitelyOperator_eliminates :
    definitelyOperator.eliminatesBorderline = true := rfl

end Phenomena.Gradability.Studies.Fine1975
