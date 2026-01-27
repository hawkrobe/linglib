/-
# Scale Semantics: Theory-Specific Content

Formal semantic structures for scalar implicature phenomena.
Connects to data in `Phenomena/ScalarImplicatures/`.

## Contents

1. **HornScale**: Semantic structure for Horn scales (some/all, or/and, etc.)
2. **HurfordSemantic**: For Hurford's constraint analysis
3. **SinghSemantic**: For Singh's asymmetry analysis
4. **Concrete scales**: QuantWorld, ConnWorld, ModalWorld with worked proofs

## Key References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Hurford, J. (1974). Exclusive or inclusive disjunction.
- Singh, R. (2008). On the interpretation of disjunction.
- Fox & Spector (2018). Economy and embedded exhaustification.
-/

import Linglib.Theories.NeoGricean.Exhaustivity

namespace NeoGricean.ScaleSemantics

open NeoGricean.Exhaustivity

-- ============================================================================
-- PART 1: Horn Scale Structure
-- ============================================================================

/--
A Horn scale with semantic content.

The key property: `stronger` entails `weaker` but not vice versa.
This asymmetry drives scalar implicatures via exhaustification.
-/
structure HornScale (World : Type*) where
  /-- Name of the scale -/
  name : String
  /-- The weaker scalar term (e.g., "some") -/
  weakerTerm : String
  /-- The stronger scalar term (e.g., "all") -/
  strongerTerm : String
  /-- Semantic denotation of weaker term -/
  weaker : Prop' World
  /-- Semantic denotation of stronger term -/
  stronger : Prop' World
  /-- Stronger entails weaker -/
  entailment : stronger ⊆ₚ weaker
  /-- Weaker does NOT entail stronger (non-trivial scale) -/
  nonTrivial : ¬(weaker ⊆ₚ stronger)

/--
Alternative set for a Horn scale: {weaker, stronger}.
-/
def HornScale.alts {World : Type*} (s : HornScale World) : Set (Prop' World) :=
  {s.weaker, s.stronger}

-- ============================================================================
-- PART 2: Hurford Semantic Structure
-- ============================================================================

/--
Semantic structure for a Hurford configuration.
Allows proving when exhaustification rescues the violation.
-/
structure HurfordSemantic (World : Type*) where
  /-- First disjunct meaning -/
  disjunctA : Prop' World
  /-- Second disjunct meaning -/
  disjunctB : Prop' World
  /-- The entailment that creates the violation -/
  entailment : (disjunctA ⊆ₚ disjunctB) ∨ (disjunctB ⊆ₚ disjunctA)
  /-- Alternative set for exhaustification -/
  alts : Set (Prop' World)

/--
A Hurford violation is rescued iff after exhaustifying the weaker disjunct,
the entailment no longer holds.

Since the structure tracks that either A⊆B or B⊆A, rescue means
exhaustification breaks whichever entailment held.
-/
def HurfordSemantic.isRescued {World : Type*} (h : HurfordSemantic World) : Prop :=
  (¬(exhIE h.alts h.disjunctA ⊆ₚ h.disjunctB)) ∨ (¬(exhIE h.alts h.disjunctB ⊆ₚ h.disjunctA))

-- ============================================================================
-- PART 3: Singh Semantic Structure
-- ============================================================================

/--
Semantic structure for Singh configurations.
-/
structure SinghSemantic (World : Type*) where
  /-- Weaker disjunct meaning -/
  weaker : Prop' World
  /-- Stronger disjunct meaning -/
  stronger : Prop' World
  /-- Stronger entails weaker -/
  entailment : stronger ⊆ₚ weaker
  /-- Alternative set -/
  alts : Set (Prop' World)
  /-- Is weaker mentioned first? -/
  weakerFirst : Bool

/--
Fox & Spector's prediction: weak-first is felicitous because exh(weak)
can break the entailment to strong.
-/
def SinghSemantic.exhBreaksEntailment {World : Type*} (s : SinghSemantic World) : Prop :=
  ¬(exhIE s.alts s.weaker ⊆ₚ s.stronger)

/--
The asymmetry: felicitous iff (weak-first AND exh breaks entailment).
Strong-first can't be rescued because exh(strong) is vacuous.
-/
def SinghSemantic.predictedFelicitous {World : Type*} (s : SinghSemantic World) : Prop :=
  s.weakerFirst ∧ s.exhBreaksEntailment

-- ============================================================================
-- PART 4: SOME/ALL SCALE
-- ============================================================================

/-- Worlds for quantifier scale: number satisfying predicate (0 to 3). -/
abbrev QuantWorld := Fin 4

/-- "Some Ps are Q" = at least one. -/
def someQ : Prop' QuantWorld := fun w => w.val ≥ 1

/-- "All Ps are Q" = all three. -/
def allQ : Prop' QuantWorld := fun w => w.val = 3

/-- All entails some. -/
theorem all_entails_some : allQ ⊆ₚ someQ := by
  intro w h
  simp only [allQ] at h
  simp only [someQ, h]
  decide

/-- Some does not entail all. -/
theorem some_not_entails_all : ¬(someQ ⊆ₚ allQ) := by
  intro h
  have : allQ ⟨1, by omega⟩ := h ⟨1, by omega⟩ (by simp [someQ])
  simp [allQ] at this

/-- The some/all Horn scale with semantic content. -/
def someAllScale : HornScale QuantWorld :=
  { name := "Quantifiers (some/all)"
  , weakerTerm := "some"
  , strongerTerm := "all"
  , weaker := someQ
  , stronger := allQ
  , entailment := all_entails_some
  , nonTrivial := some_not_entails_all
  }

-- ============================================================================
-- PART 5: OR/AND SCALE
-- ============================================================================

/-- Worlds for connective scale. -/
inductive ConnWorld where
  | neither | onlyA | onlyB | both
  deriving DecidableEq, Repr

/-- "A or B" (inclusive). -/
def orConn : Prop' ConnWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True

/-- "A and B". -/
def andConn : Prop' ConnWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True

/-- And entails or. -/
theorem and_entails_or : andConn ⊆ₚ orConn := by
  intro w h
  cases w <;> simp [andConn, orConn] at h ⊢

/-- Or does not entail and. -/
theorem or_not_entails_and : ¬(orConn ⊆ₚ andConn) := by
  intro h
  have : andConn .onlyA := h .onlyA (by simp [orConn])
  simp [andConn] at this

/-- The or/and Horn scale with semantic content. -/
def orAndScale : HornScale ConnWorld :=
  { name := "Connectives (or/and)"
  , weakerTerm := "or"
  , strongerTerm := "and"
  , weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , nonTrivial := or_not_entails_and
  }

-- ============================================================================
-- PART 6: POSSIBLE/NECESSARY SCALE
-- ============================================================================

/-- Worlds for modal scale: accessibility relation outcomes. -/
inductive ModalWorld where
  | none    -- no accessible world has P
  | some    -- some but not all accessible worlds have P
  | all     -- all accessible worlds have P
  deriving DecidableEq, Repr

/-- "Possibly P" = at least one accessible world has P. -/
def possibleP : Prop' ModalWorld
  | .none => False
  | .some => True
  | .all => True

/-- "Necessarily P" = all accessible worlds have P. -/
def necessaryP : Prop' ModalWorld
  | .none => False
  | .some => False
  | .all => True

/-- Necessary entails possible. -/
theorem necessary_entails_possible : necessaryP ⊆ₚ possibleP := by
  intro w h
  cases w <;> simp [necessaryP, possibleP] at h ⊢

/-- Possible does not entail necessary. -/
theorem possible_not_entails_necessary : ¬(possibleP ⊆ₚ necessaryP) := by
  intro h
  have : necessaryP .some := h .some (by simp [possibleP])
  simp [necessaryP] at this

/-- The possible/necessary Horn scale. -/
def possibleNecessaryScale : HornScale ModalWorld :=
  { name := "Modals (possible/necessary)"
  , weakerTerm := "possible"
  , strongerTerm := "necessary"
  , weaker := possibleP
  , stronger := necessaryP
  , entailment := necessary_entails_possible
  , nonTrivial := possible_not_entails_necessary
  }

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Structures Provided

| Structure | Purpose |
|-----------|---------|
| `HornScale World` | Scale with semantic content |
| `HurfordSemantic World` | Hurford disjunction semantics |
| `SinghSemantic World` | Singh asymmetry semantics |

## Concrete Scales

| Scale | World Type | Weaker | Stronger |
|-------|------------|--------|----------|
| `someAllScale` | `QuantWorld` | some | all |
| `orAndScale` | `ConnWorld` | or | and |
| `possibleNecessaryScale` | `ModalWorld` | possible | necessary |

## Usage

Theory files (e.g., `ClassicExamples.lean`, `FoxSpector2018.lean`) import this
and prove predictions. Phenomena files contain theory-neutral data.
-/

end NeoGricean.ScaleSemantics
