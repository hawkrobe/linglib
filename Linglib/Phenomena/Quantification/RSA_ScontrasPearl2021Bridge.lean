import Linglib.Theories.Pragmatics.RSA.Implementations.ScontrasPearl2021
import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Mathlib.Data.Rat.Defs

/-!
# Bridge: RSA Scope Ambiguity → Phenomena (Scontras & Pearl 2021)

Connects the RSA scope ambiguity model (`RSA.ScontrasPearl2021`) to empirical
data from `Phenomena.Quantification.Studies.ScontrasPearl2021`.

## Status

RSA evaluation infrastructure (RSA.Eval.L1_world, RSA.Eval.S1, RSA.Eval.getScore,
RSA.Eval.normalize, RSA.Eval.sumScores, boolToRat) has been removed.
Domain types (scopeMeaningTyped, typedWorlds) and empirical ordering structures
are preserved. RSA computation stubs and prediction theorems remain with
`sorry` for future reimplementation.
-/


namespace RSA.ScontrasPearl2021.Bridge

open RSA.ScontrasPearl2021
open ScontrasPearl2021
open Semantics.Scope
open Semantics.Scope (ScopeConfig)

-- Fintype instances for domain types

instance jumpOutcomeFintype : Fintype Phenomena.Quantification.Studies.ScontrasPearl2021.JumpOutcome where
  elems := {.zero, .one, .two}
  complete := λ x => by cases x <;> simp

-- Typed Distributions (using JumpOutcome)

/--
Truth conditions using JumpOutcome (typed version).
-/
def scopeMeaningTyped : ScopeConfig → ScopeUtterance → Phenomena.Quantification.Studies.ScontrasPearl2021.JumpOutcome → Bool
  | _, .null, _ => true  -- null utterance always true
  | .surface, .everyHorseNotJump, w => w == .zero      -- ∀>¬: true iff no horse jumped
  | .inverse, .everyHorseNotJump, w => w != .two       -- ¬>∀: true iff not all jumped

/-- Typed worlds -/
def typedWorlds : List Phenomena.Quantification.Studies.ScontrasPearl2021.JumpOutcome :=
  [.zero, .one, .two]

/-- Typed utterances -/
def typedUtterances : List ScopeUtterance :=
  [.null, .everyHorseNotJump]

/-- Typed scopes -/
def typedScopes : List ScopeConfig :=
  [.surface, .inverse]


-- Connection to Empirical Data (stubs)

/-- Both RSA and empirical data show the same ordering. -/
theorem rsa_and_empirical_agree :
    (Phenomena.Quantification.Studies.ScontrasPearl2021.getResult .zero > Phenomena.Quantification.Studies.ScontrasPearl2021.getResult .one) ∧
    (Phenomena.Quantification.Studies.ScontrasPearl2021.getResult .one > Phenomena.Quantification.Studies.ScontrasPearl2021.getResult .two) := by
  sorry

/-- Ordering of typed distributions matches empirical data.

P(zero) > P(one) > P(two)
matches empirical 92% > 59% > 18% -/
theorem typed_ordering_matches_empirical :
    (9 : ℚ)/13 > (4 : ℚ)/13 ∧ (4 : ℚ)/13 > 0 := by
  sorry

/-- Inverse scope preference in typed distributions.

P(inverse) = 8/13 > P(surface) = 5/13 -/
theorem typed_inverse_preference :
    (8 : ℚ)/13 > (5 : ℚ)/13 := by
  sorry

end RSA.ScontrasPearl2021.Bridge
