import Linglib.Core.PrivativePair
import Linglib.Core.Constraint.OT.Basic
import Linglib.Theories.Semantics.Presupposition.PhiFeatures

/-!
# Maximize Presupposition
@cite{heim-1991}

Maximize Presupposition (MP) is a pragmatic principle: among competing
expressions with the same assertive content, use the one with the
strongest *satisfied* presupposition.

## Three formulations unified

This module provides a general, domain-agnostic formulation of MP and
connects it to existing domain-specific implementations:

1. **OT formulation** (`mpConstraintOf`): MP as a `NamedConstraint C`
   parameterized by a presuppositional strength function. Violation
   count = maxStrength − strength(c). Wang2023's `mpConstraint` is
   an instance (`phiMP`).

2. **Structural alternatives** (`violatesMP` in
   `Theories.Semantics.Alternatives.Structural`): MP defined over
   syntactic trees, parametric in an
   `Alternatives.AlternativeSource (Tree C W)`. The classical Katzir
   2007 source is `katzirSource lex`; the indirect-alternative source
   `Alternatives.Indirect.indirectFrom`
   (@cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025})
   competes with unpronounceable Katzir witnesses (e.g. *les deux NP*
   competes with the silent *tous les NP.dual* via the Indirect
   Alternative construction). Bridge to the OT formulation is
   conceptual: both enforce "prefer the strongest presupposition"
   but over different candidate-generation mechanisms.

3. **IC/FP/MP ranking** (`PragConstraint.MP` in
   `Pragmatics.Implicature.Presuppositions`): MP as a
   violable constraint ranked below IC (Internal Coherence) and FP
   (Felicity Presupposition). Describes MP's position in the
   constraint hierarchy for presupposition obligatoriness
   (@cite{wang-2025}).

## Core abstraction

MP competition requires three ingredients:

1. A **candidate set** — forms that can fill the same syntactic position
2. A **presuppositional strength measure** — `strength : C → Nat`
3. A **same-assertion condition** — all candidates have identical
   at-issue content (e.g., `phiPresup_same_assertion`)

MP penalizes failure to maximize strength: candidates with weaker
presuppositions incur more violations. The key structural property:
MP is *antagonistic* to markedness constraints, which penalize
strength directly (`mp_reverses_markedness`).

## Architecture

- §1: Abstract MP and markedness constraints (`mpConstraintOf`, `markednessPenalty`)
- §2: Structural properties (reversal, dominance)
- §3: Phi-feature instance (`phiMP`)
- §4: Presuppositional strict total order on well-formed cells
-/

set_option autoImplicit false

namespace Semantics.Presupposition.MaximizePresupposition

open Core (PrivativePair)
open Core.Constraint.OT (NamedConstraint ConstraintFamily mkTableau
              mkTableau_optimal_zero_first mkTableau_optimal_mem)
open Core.Constraint.Evaluation
open Semantics.Presupposition.PhiFeatures

-- ============================================================================
-- §1  Abstract MP and Markedness Constraints
-- ============================================================================

/-!
## §1: Abstract Constraints

Two generic constraint constructors, parameterized by a presuppositional
strength function `strength : C → Nat`:

- **`mpConstraintOf`**: penalizes failure to maximize presupposition.
  Violation count = `maxStrength - strength c`.
- **`markednessPenalty`**: penalizes presuppositional strength directly.
  Violation count = `strength c`.

These are antagonistic: for any candidate `c`, `mpConstraintOf.eval c +
markednessPenalty.eval c = maxStrength` (when `strength c ≤ maxStrength`).
-/

/-- Build an MP constraint from a presuppositional strength function.
    Violation count = `maxStrength - strength c`: maximal presupposition
    → 0 violations, weaker presupposition → more. -/
def mpConstraintOf {C : Type} (maxStrength : Nat)
    (strength : C → Nat) : NamedConstraint C :=
  { name := "MP!"
  , family := .faithfulness
  , eval := fun c => maxStrength - strength c }

/-- A markedness constraint penalizing presuppositional strength.
    Violation count = `strength c`: stronger presupposition → more
    violations. This is the generic form of Wang2023's `todConstraint`
    (Taboo of Directness). -/
def markednessPenalty {C : Type}
    (strength : C → Nat) : NamedConstraint C :=
  { name := "Markedness"
  , family := .markedness
  , eval := strength }

/-- Violation counts sum to maxStrength for any candidate whose
    strength does not exceed the maximum. -/
theorem mp_markedness_complementary {C : Type} (maxStrength : Nat)
    (strength : C → Nat) (c : C) (h : strength c ≤ maxStrength) :
    (mpConstraintOf maxStrength strength).eval c +
    (markednessPenalty strength).eval c = maxStrength := by
  simp only [mpConstraintOf, markednessPenalty]; omega

-- ============================================================================
-- §2  Structural Properties
-- ============================================================================

/-!
## §2: Structural Properties

The core algebraic facts about MP and markedness as OT constraints.
These hold for any candidate type and strength function.
-/

/-- MP assigns 0 violations to the maximally presupposing candidate. -/
theorem mp_zero_at_max {C : Type} (maxStrength : Nat) (strength : C → Nat)
    (c : C) (hMax : strength c = maxStrength) :
    (mpConstraintOf maxStrength strength).eval c = 0 := by
  simp [mpConstraintOf, hMax]

/-- Markedness assigns 0 violations to the minimally presupposing
    candidate. -/
theorem markedness_zero_at_min {C : Type} (strength : C → Nat)
    (c : C) (hMin : strength c = 0) :
    (markednessPenalty strength).eval c = 0 := by
  simp [markednessPenalty, hMin]

/-- **MP and markedness impose opposite orderings**: fewer MP violations
    ↔ more markedness violations. This is the general form of Wang2023's
    `tod_reverses_mp`. -/
theorem mp_reverses_markedness {C : Type} (maxStrength : Nat)
    (strength : C → Nat) (c₁ c₂ : C)
    (h₁ : strength c₁ ≤ maxStrength) (h₂ : strength c₂ ≤ maxStrength) :
    (markednessPenalty strength).eval c₁ < (markednessPenalty strength).eval c₂ ↔
    (mpConstraintOf maxStrength strength).eval c₁ >
    (mpConstraintOf maxStrength strength).eval c₂ := by
  simp only [markednessPenalty, mpConstraintOf]; omega

/-- **MP dominant → strongest wins**: when MP is the top-ranked constraint,
    all optimal candidates have maximal presuppositional strength.
    Proof via `optimal_zero_first` — a max-strength candidate has 0 MP
    violations, forcing all winners to have 0 as well. -/
theorem mp_selects_strongest {C : Type} [DecidableEq C] (candidates : List C)
    (maxStrength : Nat) (strength : C → Nat)
    (rest : List (NamedConstraint C))
    (hNE : candidates ≠ [])
    (hBound : ∀ c ∈ candidates, strength c ≤ maxStrength)
    (hExists : ∃ c₀ ∈ candidates, strength c₀ = maxStrength) :
    ∀ c ∈ (mkTableau candidates
      (mpConstraintOf maxStrength strength :: rest) hNE).optimal,
      strength c = maxStrength := by
  intro c hc
  have hZero := mkTableau_optimal_zero_first candidates
    (mpConstraintOf maxStrength strength) rest hNE
    (by obtain ⟨c₀, hm, hs⟩ := hExists
        exact ⟨c₀, hm, mp_zero_at_max maxStrength strength c₀ hs⟩) c hc
  have hcBound := hBound c (mkTableau_optimal_mem candidates _ hNE c hc)
  simp only [mpConstraintOf] at hZero; omega

/-- **Markedness dominant → weakest wins**: when a markedness constraint
    is the top-ranked constraint, all optimal candidates have zero
    presuppositional strength. This is the general form of Wang2023's
    `tod_mp_only_minimal`. -/
theorem markedness_selects_weakest {C : Type} [DecidableEq C] (candidates : List C)
    (strength : C → Nat)
    (rest : List (NamedConstraint C))
    (hNE : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, strength c₀ = 0) :
    ∀ c ∈ (mkTableau candidates
      (markednessPenalty strength :: rest) hNE).optimal,
      strength c = 0 := by
  intro c hc
  have hZero := mkTableau_optimal_zero_first candidates
    (markednessPenalty strength) rest hNE
    (by obtain ⟨c₀, hm, hs⟩ := hExists
        exact ⟨c₀, hm, markedness_zero_at_min strength c₀ hs⟩) c hc
  simp only [markednessPenalty] at hZero; exact hZero

-- ============================================================================
-- §3  Phi-Feature Instance
-- ============================================================================

/-!
## §3: Phi-Feature Instance

The phi-feature system (`PrivativePair` with `presupStrength = specLevel`)
is a canonical instance of MP competition:

- **Candidates**: well-formed `PrivativePair` cells (3 cells)
- **Strength**: `presupStrength` (= `specLevel`: 0, 1, or 2)
- **maxStrength**: 2 (= `PrivativePair.maximal.specLevel`)
- **Same assertion**: `phiPresup_same_assertion` — all cells have
  identical (trivially true) at-issue content

This section defines `phiMP` (the instantiation) and proves bridges
connecting the general theorems to `phiPresup`.
-/

/-- The phi-feature MP constraint: `mpConstraintOf` instantiated with
    `presupStrength` over `PrivativePair`. -/
def phiMP : NamedConstraint PrivativePair :=
  mpConstraintOf PrivativePair.maximal.specLevel presupStrength

/-- `phiMP` evaluates to `maxSpec - presupStrength`. -/
theorem phiMP_eval (c : PrivativePair) :
    phiMP.eval c = PrivativePair.maximal.specLevel - presupStrength c := rfl

/-- The phi-feature markedness constraint: `markednessPenalty` instantiated
    with `presupStrength`. This is the generic form of ToD. -/
def phiMarkedness : NamedConstraint PrivativePair :=
  markednessPenalty presupStrength

/-- `phiMarkedness` evaluates to `presupStrength`. -/
theorem phiMarkedness_eval (c : PrivativePair) :
    phiMarkedness.eval c = presupStrength c := rfl

/-- Phi-feature competitors satisfy the **same-assertion condition**:
    all cells of `phiPresup` have identical (trivially true) at-issue
    content. This is the prerequisite for MP to apply — if assertions
    differed, the competition would be at-issue (scalar implicature),
    not presuppositional. -/
theorem phi_same_assertion {E : Type*} (innerP outerP : E → Prop) :
    ∀ c₁ c₂ : PrivativePair, ∀ x : E,
      (phiPresup innerP outerP c₁).assertion x ↔
      (phiPresup innerP outerP c₂).assertion x :=
  fun c₁ c₂ x => phiPresup_same_assertion innerP outerP c₁ c₂ x

/-- Phi-feature competitors satisfy the **presuppositional nesting**
    condition: stronger presupposition → smaller domain. This ensures
    the strength ordering corresponds to genuine set-theoretic
    containment of presuppositional domains. -/
theorem phi_strength_nesting {E : Type*} {innerP outerP : E → Prop}
    (hContain : ∀ x, innerP x → outerP x)
    {c₁ c₂ : PrivativePair}
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true)
    (hSpec : presupStrength c₁ ≥ presupStrength c₂) (x : E)
    (h : (phiPresup innerP outerP c₁).defined x) :
    (phiPresup innerP outerP c₂).defined x :=
  phiPresup_nesting hContain hw₁ hw₂ hSpec x h

/-- MP over phi-features selects the maximal (most marked) cell when
    it is among the candidates. Instantiation of `mp_selects_strongest`
    to `PrivativePair`.

    This is the normal-speech pattern: absent any politeness or
    context-sensitivity constraint, MP forces use of the form with the
    strongest presupposition (SG over PL, 1st over 3rd, DEF over INDEF).
    @cite{sauerland-2003} derives the preference for singular from
    exactly this principle. -/
theorem phi_mp_selects_maximal (candidates : List PrivativePair)
    (rest : List (NamedConstraint PrivativePair))
    (hNE : candidates ≠ [])
    (hWF : ∀ c ∈ candidates, c.wellFormed = true)
    (hMax : PrivativePair.maximal ∈ candidates) :
    ∀ c ∈ (mkTableau candidates (phiMP :: rest) hNE).optimal,
      presupStrength c = PrivativePair.maximal.specLevel :=
  mp_selects_strongest candidates _ presupStrength rest hNE
    (fun c hc => wellFormed_specLevel_le_two c (hWF c hc))
    ⟨.maximal, hMax, rfl⟩

/-- MP and markedness reverse each other over phi-features.
    This is the algebraic core of `tod_reverses_mp` in `Wang2023`. -/
theorem phi_mp_reverses_markedness (c₁ c₂ : PrivativePair)
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true) :
    phiMarkedness.eval c₁ < phiMarkedness.eval c₂ ↔
    phiMP.eval c₁ > phiMP.eval c₂ :=
  mp_reverses_markedness _ presupStrength c₁ c₂
    (wellFormed_specLevel_le_two c₁ hw₁)
    (wellFormed_specLevel_le_two c₂ hw₂)

-- ============================================================================
-- §4  Presuppositional Strict Total Order
-- ============================================================================

/-!
## §4: `presupWeakerThan` is a Strict Total Order

`presupWeakerThan` (defined in `PhiFeatures`) inherits the strict total
order structure of `<` on `Nat` via `specLevel`. We prove the standard
order-theoretic properties on well-formed cells.

The key non-trivial result is **totality**: distinct well-formed cells
always have different specLevels (`specLevel_injective_wf`), so
`presupWeakerThan` is a strict linear order on the 3-element set of
well-formed cells.
-/

/-- `specLevel` is injective on well-formed cells: two well-formed cells
    with the same specLevel are identical. This follows from the three
    well-formed cells having specLevels 0, 1, 2 — all distinct. -/
theorem specLevel_injective_wf (a b : PrivativePair)
    (ha : a.wellFormed = true) (hb : b.wellFormed = true)
    (h : a.specLevel = b.specLevel) : a = b := by
  rcases PrivativePair.classification a ha with rfl | rfl | rfl <;>
    rcases PrivativePair.classification b hb with rfl | rfl | rfl <;>
    first | rfl | simp_all [PrivativePair.spec_maximal,
      PrivativePair.spec_intermediate, PrivativePair.spec_minimal]

/-- `presupWeakerThan` is irreflexive. -/
theorem presupWeakerThan_irrefl (c : PrivativePair) :
    presupWeakerThan c c = false := by
  simp [presupWeakerThan]

/-- `presupWeakerThan` is transitive. -/
theorem presupWeakerThan_trans (a b c : PrivativePair)
    (h₁ : presupWeakerThan a b = true)
    (h₂ : presupWeakerThan b c = true) :
    presupWeakerThan a c = true := by
  simp only [presupWeakerThan, decide_eq_true_eq] at *; omega

/-- `presupWeakerThan` is asymmetric. -/
theorem presupWeakerThan_asymm (a b : PrivativePair)
    (h : presupWeakerThan a b = true) :
    presupWeakerThan b a = false := by
  simp only [presupWeakerThan, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega

/-- `presupWeakerThan` is total on well-formed cells: for distinct
    well-formed cells, either `a < b` or `b < a`. -/
theorem presupWeakerThan_total (a b : PrivativePair)
    (ha : a.wellFormed = true) (hb : b.wellFormed = true) (hne : a ≠ b) :
    presupWeakerThan a b = true ∨ presupWeakerThan b a = true := by
  simp only [presupWeakerThan, decide_eq_true_eq]
  have hne' : a.specLevel ≠ b.specLevel :=
    fun h => hne (specLevel_injective_wf a b ha hb h)
  omega

/-- `presupStrongerThan` is the converse of `presupWeakerThan`. -/
theorem strongerThan_iff_not_weakerOrEq (a b : PrivativePair) :
    presupStrongerThan a b = true ↔ presupWeakerThan b a = true := by
  simp [presupStrongerThan, presupWeakerThan, decide_eq_true_eq]

/-- The presuppositional strength ordering is determined by `specLevel`:
    `a` is strictly weaker than `b` iff `a.specLevel < b.specLevel`. -/
theorem strength_iff_specLevel (a b : PrivativePair) :
    presupWeakerThan a b = true ↔ a.specLevel < b.specLevel := by
  simp [presupWeakerThan, decide_eq_true_eq]

end Semantics.Presupposition.MaximizePresupposition
