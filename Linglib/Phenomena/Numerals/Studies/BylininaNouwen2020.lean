import Linglib.Theories.Semantics.Numerals.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Data.Rat.Defs

/-!
# @cite{bylinina-nouwen-2020}: Lower-Bound Bare Numerals + RSA Derive Exact Readings
@cite{bylinina-nouwen-2020} @cite{horn-1972}

@cite{bylinina-nouwen-2020} survey the two camps on bare-numeral semantics:
the lower-bound view (`bare n` = `≥n`; @cite{horn-1972}) and the exact view
(`bare n` = `=n`). Under the lower-bound camp, the exact reading must arise
*pragmatically*. This study formalises that derivation: a standard
L0→S1→L1 RSA cascade with bare numerals over a 0–3 cardinality domain
strengthens "two" from `≥2` to peak at `w=2`, and analogously for "one".

The construction reuses the `LowerBound.meaning` semantics from
`Theories/Semantics/Quantification/Numerals/Semantics.lean` via a small
finite domain wrapper (`NCard`, `NUtt`) suited to `rsa_predict` reification.
The `lbNuttMeaning_eq_lowerBound` grounding theorem witnesses that the
inlined meaning is the same one defined there.
-/

namespace BylininaNouwen2020

open Semantics.Numerals

-- ============================================================================
-- § 1: Finite domain wrappers for `rsa_predict` reification
-- ============================================================================

/-- Cardinality worlds 0–3 as a finite enum (suits `rsa_predict`). -/
inductive NCard where
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Repr, Fintype

def NCard.toNat : NCard → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3

/-- Bare-numeral utterances under consideration. -/
inductive NUtt where
  | one | two | three
  deriving DecidableEq, Repr, Fintype

def NUtt.toBareNumeral : NUtt → BareNumeral
  | .one => .one | .two => .two | .three => .three

/-- Lower-bound meaning inlined for reification: `n ≥ k`. Avoids the
    `maxMeaning` indirection that would defeat `rsa_predict`'s definitional
    unfolder. The grounding theorem below shows it agrees with
    `LowerBound.meaning`. -/
def lbNuttMeaning : NUtt → NCard → Bool
  | .one,   w => w.toNat ≥ 1
  | .two,   w => w.toNat ≥ 2
  | .three, w => w.toNat ≥ 3

/-- The inlined meaning agrees with `LowerBound.meaning` from
    `Numerals.Basic`. -/
theorem lbNuttMeaning_eq_lowerBound (u : NUtt) (w : NCard) :
    lbNuttMeaning u w = LowerBound.meaning u.toBareNumeral w.toNat := by
  cases u <;> cases w <;> rfl

-- ============================================================================
-- § 2: RSA configuration with belief-based S1
-- ============================================================================

open RSA Real in
/-- Standard belief-based RSA over bare numerals with `≥` semantics:
    `S1` rates worlds by `L0^α` (here α = 1). The cascade is what
    @cite{bylinina-nouwen-2020} call "scalar implicature in the
    lower-bound camp". -/
noncomputable def lbNumeralCfg : RSAConfig NUtt NCard where
  Latent := Unit
  meaning _ _ u w := if lbNuttMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 3: RSA strengthens "two" and "one" to their exact readings
-- ============================================================================

/-- Under lower-bound semantics, RSA strengthens "two" from `≥2` to the
    exact reading: `L1` assigns more probability to `w = 2` than `w = 3`. -/
theorem lb_rsa_strengthens_two :
    lbNumeralCfg.L1 .two .c2 > lbNumeralCfg.L1 .two .c3 := by rsa_predict

/-- Same effect for "one": `L1("one", w = 1) > L1("one", w = 2)`. -/
theorem lb_rsa_strengthens_one :
    lbNumeralCfg.L1 .one .c1 > lbNumeralCfg.L1 .one .c2 := by rsa_predict

/-- "Three" trivially peaks at `w = 3` (the only `≥3`-compatible world in
    the 0–3 range). -/
theorem lb_three_peaked :
    lbNumeralCfg.L1 .three .c3 > lbNumeralCfg.L1 .three .c2 := by rsa_predict

end BylininaNouwen2020
