import Linglib.Core.Logic.Truth3
import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Phenomena.Gradability.Vagueness
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Fine (1975): Vagueness, Truth and Logic @cite{fine-1975}

Supervaluationism: a vague sentence is true iff true on ALL admissible
precisifications, false iff false on ALL, and indefinite otherwise.

## Core Insight

A precisification of a vague gradable predicate is a choice of threshold.
A **specification space** is a set of admissible thresholds — the different
ways the predicate could be made precise. Super-truth is universal
quantification over this set, mapping Bool-valued threshold semantics
to three-valued (`Truth3`) outputs.

## Structure

- § 1: Specification spaces and the supervaluation operator
- § 2: The D (definitely) operator
- § 3: Penumbral connection theorems (§ 2 of the paper, pp. 270–271)
- § 4: Sorites resolution (§ 4, pp. 285–286)
- § 5: Bridge — `inGapRegion` ↔ `Truth3.indet`

## Scope

Fine's framework is fully general: specification spaces are partially
ordered sets of precisifications for arbitrary vague predicates. We
specialize to the case of gradable predicates with threshold-based
precisifications (`Finset (Threshold max)`), which connects directly to
linglib's `Degree`/`Threshold` types and the RSA models (e.g.,
`LassiterGoodman2017.lean`).

## Connection to Klein (1980)

@cite{klein-1980}'s comparative — "∃ C where tall(a,C) ∧ ¬tall(b,C)" —
can be seen as the existential dual of supervaluation: Klein quantifies
existentially over comparison classes; Fine quantifies universally over
thresholds. (Neither paper states this connection explicitly.) See
`Theories/Semantics/Degree/Frameworks/Klein.lean`.
-/

namespace Phenomena.Gradability.Studies.Fine1975

open Core.Duality (Truth3)
open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat)
open Semantics.Lexical.Adjective (ThresholdPair inGapRegion)

-- ════════════════════════════════════════════════════
-- § 1. Specification Spaces & Supervaluation
-- ════════════════════════════════════════════════════

/-- A specification space: the set of admissible precisifications for a
    vague predicate. Each element is a threshold — one way of drawing
    the boundary. -/
abbrev SpecSpace (max : Nat) := Finset (Threshold max)

/-- Supervaluation operator. Maps a Bool-valued predicate (parameterized
    by threshold) to a three-valued truth value:
    - `tt` if true at ALL thresholds in the space
    - `ff` if false at ALL thresholds in the space
    - `unk` if true at some and false at others (the borderline case)

    Uses decidable bounded quantification over Finset.
    Empty specification spaces yield `tt` (vacuous universal). -/
def superTrue {max : Nat} (p : Threshold max → Bool) (S : SpecSpace max) : Truth3 :=
  if ∀ θ ∈ S, p θ = true then Truth3.true
  else if ∀ θ ∈ S, p θ = false then Truth3.false
  else Truth3.indet

/-- Supervaluation of a degree predicate: fix a degree, vary the threshold. -/
def superTrueAt {max : Nat} (meaning : Degree max → Threshold max → Bool)
    (d : Degree max) (S : SpecSpace max) : Truth3 :=
  superTrue (meaning d) S

-- ════════════════════════════════════════════════════
-- § 2. The D (Definitely) Operator
-- ════════════════════════════════════════════════════

/-- The definitely operator (@cite{fine-1975}, § 5, p. 287).
    DA is true iff A is true at all admissible precisifications.
    This is the `tt` case of supervaluation — D projects the
    "super-true" component. Analogous to necessity in S5. -/
def definitely {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) : Bool :=
  decide (∀ θ ∈ S, p θ = true)

/-- The indefiniteness operator: IA ≡ ¬DA ∧ ¬D¬A.
    A is indefinite iff it is neither definitely true nor definitely false
    — i.e., true at some precisifications and false at others. -/
def indefinite {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) : Bool :=
  !definitely p S && !definitely (fun θ => !p θ) S

theorem definitely_iff_supertrue {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) :
    definitely p S = true ↔ superTrue p S = Truth3.true := by
  unfold definitely superTrue
  constructor
  · intro h; rw [decide_eq_true_eq] at h; exact if_pos h
  · intro h
    by_contra hc; rw [decide_eq_true_eq] at hc
    rw [if_neg hc] at h; split at h <;> cases h

/-- The indefiniteness operator corresponds to `Truth3.indet` under
    supervaluation: A is indefinite iff it is neither super-true nor
    super-false. Requires non-empty S to exclude the vacuous case. -/
theorem indefinite_iff_superunk {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) (hne : S.Nonempty) :
    indefinite p S = true ↔ superTrue p S = Truth3.indet := by
  unfold indefinite definitely superTrue
  simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  constructor
  · intro ⟨hnt, hnf⟩
    rw [if_neg hnt, if_neg hnf]
  · intro h
    constructor
    · intro hall; rw [if_pos hall] at h; cases h
    · intro hall
      have hnt : ¬(∀ θ ∈ S, p θ = true) := by
        obtain ⟨θ₀, hθ₀⟩ := hne
        intro ht; have := hall θ₀ hθ₀; rw [ht θ₀ hθ₀] at this; simp at this
      rw [if_neg hnt, if_pos hall] at h; cases h

-- ════════════════════════════════════════════════════
-- § 3. Penumbral Connection Theorems
-- ════════════════════════════════════════════════════

/-! Penumbral connections are logical relationships that hold even in the
    borderline region. Fine coined the term (p. 270) and argued that
    supervaluationism is the only framework that captures them all.

    Below, `p` is a Bool-valued predicate parameterized by threshold —
    e.g., `fun θ => d.toNat > θ.toNat` for "tall at degree d". -/

/-- **Excluded middle is super-true.** P ∨ ¬P is true on every
    precisification (each threshold makes P either true or false),
    so it is true on ALL — i.e., super-true.

    @cite{fine-1975}, § 3: the super-truth theory "covers all cases
    of penumbral connection" (p. 278). -/
theorem excluded_middle_supertrue {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) :
    superTrue (fun θ => p θ || !p θ) S = Truth3.true := by
  unfold superTrue
  exact if_pos (fun θ _ => by cases p θ <;> simp)

/-- **Non-contradiction is super-false.** P ∧ ¬P is false on every
    precisification, so it is false on ALL — i.e., super-false.

    Requires non-empty specification space (Fine assumes at least one
    admissible precisification exists). -/
theorem non_contradiction_superfalse {max : Nat} (p : Threshold max → Bool)
    (S : SpecSpace max) (hne : S.Nonempty) :
    superTrue (fun θ => p θ && !p θ) S = Truth3.false := by
  unfold superTrue
  have hnt : ¬(∀ θ ∈ S, (p θ && !p θ) = true) := by
    obtain ⟨θ₀, hθ₀⟩ := hne
    intro hall; have := hall θ₀ hθ₀; cases p θ₀ <;> simp at this
  have haf : ∀ θ ∈ S, (p θ && !p θ) = false := by
    intro θ _; cases p θ <;> simp
  rw [if_neg hnt, if_pos haf]

/-- **Comparative entailment.** If d₁ > d₂ and d₂ is super-true for a
    positive (upward) predicate, then d₁ is also super-true.

    This captures Fine's internal penumbral connection: if Herbert is
    to be bald, then so is the man with fewer hairs (p. 276). -/
theorem comparative_entailment {max : Nat}
    (d₁ d₂ : Degree max) (S : SpecSpace max)
    (hgt : d₂.toNat < d₁.toNat)
    (hd₂ : superTrueAt (fun d θ => decide (d.toNat > θ.toNat)) d₂ S = Truth3.true) :
    superTrueAt (fun d θ => decide (d.toNat > θ.toNat)) d₁ S = Truth3.true := by
  unfold superTrueAt superTrue at *
  have h : ∀ θ ∈ S, decide (d₂.toNat > θ.toNat) = true := by
    by_contra hc; push_neg at hc
    obtain ⟨θ, hθ, hv⟩ := hc
    have : ¬(∀ θ ∈ S, decide (d₂.toNat > θ.toNat) = true) :=
      fun h => hv (h θ hθ)
    rw [if_neg this] at hd₂; split at hd₂ <;> cases hd₂
  have h₁ : ∀ θ ∈ S, decide (d₁.toNat > θ.toNat) = true := by
    intro θ hθ; have := h θ hθ; simp only [decide_eq_true_eq] at this ⊢; omega
  exact if_pos h₁

-- ════════════════════════════════════════════════════
-- § 4. Sorites Resolution
-- ════════════════════════════════════════════════════

/-! Fine's resolution (§ 4, pp. 285–286): the tolerance premise
    "if n hairs is bald, then n+1 hairs is bald" is SUPER-FALSE.
    For every admissible threshold θ, there exists an n (namely n = θ)
    where n is below θ but n+1 is above. The premise fails at every
    precisification, so it fails under supervaluation.

    We prove the finite version: on a discrete scale, the universal
    tolerance step "∀ θ ∈ S, (meaning d θ → meaning d' θ)" fails
    when d is above some threshold and d' is below it. -/

/-- The tolerance premise fails at any threshold that separates d from d'.
    If d is "tall" at θ but d' is not, the tolerance step from d to d'
    is falsified at θ. -/
theorem tolerance_fails_at_boundary {max : Nat}
    (d d' : Degree max) (θ : Threshold max)
    (hd : d.toNat > θ.toNat) (hd' : ¬(d'.toNat > θ.toNat)) :
    ¬(d.toNat > θ.toNat → d'.toNat > θ.toNat) :=
  fun h => hd' (h hd)

-- ════════════════════════════════════════════════════
-- § 5. Bridge: Gap Region ↔ Truth3.indet
-- ════════════════════════════════════════════════════

/-! The `inGapRegion` function in `Adjective.Theory` computes whether a
    degree falls between two thresholds (the "borderline" zone for contrary
    antonyms). A `ThresholdPair` with `neg ≤ pos` is a two-element
    specification space `{neg, pos}`, and the gap region is exactly the
    set of degrees that receive `Truth3.indet` under supervaluation.

    This makes the implicit connection between the adjective theory's
    computational concept and the Kleene truth-value concept explicit. -/

/-- The specification space induced by a threshold pair: the two thresholds
    that bound the gap region. -/
def specOfPair {max : Nat} (tp : ThresholdPair max) : SpecSpace max :=
  {tp.neg, tp.pos}

-- TODO: gap_implies_disagreement — prove that inGapRegion d tp = true
-- implies d > neg but d ≤ pos (as threshold values), yielding
-- disagreement across the two precisifications in specOfPair tp.
-- The proof requires unwinding the Threshold → Degree coercion
-- (via Fin.castSucc) and the LE instance on Degree.

-- ════════════════════════════════════════════════════
-- § 6. Verification: Vagueness.lean Data
-- ════════════════════════════════════════════════════

/-! The `Vagueness.lean` data file records that supervaluationism captures
    all four penumbral connections. Fine1975's theorems prove this: -/

open Gradability.Vagueness

/-- Excluded middle data says supervaluationism captures it;
    `excluded_middle_supertrue` proves this. -/
theorem excludedMiddle_captured :
    excludedMiddle.supervaluationismCaptures = true := rfl

/-- Non-contradiction data says supervaluationism captures it;
    `non_contradiction_superfalse` proves this. -/
theorem nonContradiction_captured :
    nonContradiction.supervaluationismCaptures = true := rfl

/-- Comparative entailment data says supervaluationism captures it;
    `comparative_entailment` proves this. -/
theorem comparativeEntailment_captured :
    comparativeEntailment.supervaluationismCaptures = true := rfl

/-- The D operator data says it eliminates borderline cases;
    `definitely_iff_supertrue` shows D = super-truth. -/
theorem definitelyOperator_eliminates :
    definitelyOperator.eliminatesBorderline = true := rfl

-- ════════════════════════════════════════════════════
-- § 7. Classical Validity (§ 4, p. 283)
-- ════════════════════════════════════════════════════

/-! @cite{fine-1975}'s central logical result (§ 4, pp. 283–284):
    the super-truth theory yields classical logic. A formula is
    super-valid (true in all specification spaces) iff classically valid
    (true in all classical models). This is because each complete
    specification is a classical model.

    We prove one direction: classical tautologies are super-valid.
    The converse requires a model-theoretic argument beyond our scope. -/

/-- A classical tautology (true at every threshold) is super-true
    in every specification space. -/
theorem classical_tautology_supervalid {max : Nat}
    (p : Threshold max → Bool)
    (htaut : ∀ θ, p θ = true) (S : SpecSpace max) :
    superTrue p S = Truth3.true := by
  unfold superTrue
  exact if_pos (fun θ _ => htaut θ)

end Phenomena.Gradability.Studies.Fine1975
