import Linglib.Theories.Semantics.Numerals.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Data.Rat.Defs

/-!
# @cite{kennedy-2015}: Kennedy Alternative Sets through RSA
@cite{kennedy-2015}

@cite{kennedy-2015}'s alternative sets for modified numerals — replacing
the traditional Horn scale `⟨1, 2, 3, …⟩` with sets like
`{bare 3, more than 3, at least 3}` (lower-bound) and
`{bare 3, fewer than 3, at most 3}` (upper-bound) — through standard RSA
L1 reasoning. Under bilateral (exact) bare-numeral semantics, RSA
predicts:

- **Class B (`≥`, `≤`)**: ignorance implicatures at the boundary —
  hearing "at least 3" pushes probability *above* the boundary; "at most 3"
  pushes it *below*.
- **Class A (`>`, `<`)**: the boundary is excluded semantically, so no
  competition with the bare numeral arises.
- **Bare numerals**: peaked under exact semantics.

Domain: cardinality 0–5 to fit `rsa_predict` reification cleanly.
-/

namespace Kennedy2015

open Semantics.Numerals

-- ============================================================================
-- § 1: Cardinality and alternative sets for n = 3
-- ============================================================================

/-- Cardinality worlds 0–5 (wider than `BylininaNouwen2020.NCard` because
    Class A "more than 3" needs `w = 4` to be non-trivial). -/
inductive KCard where
  | c0 | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Repr, Fintype

def KCard.toNat : KCard → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4 | .c5 => 5

/-- Lower-bound alternatives for `n = 3`: `{bare 3, more than 3, at least 3}`. -/
inductive KLowerUtt where
  | bare3 | moreThan3 | atLeast3
  deriving DecidableEq, Repr, Fintype

/-- Lower-bound alternative meanings, inlined for `rsa_predict`. -/
def kLowerMeaning : KLowerUtt → KCard → Bool
  | .bare3,     w => w.toNat == 3
  | .moreThan3, w => w.toNat > 3
  | .atLeast3,  w => w.toNat ≥ 3

/-- Upper-bound alternatives for `n = 3`: `{bare 3, fewer than 3, at most 3}`. -/
inductive KUpperUtt where
  | bare3 | fewerThan3 | atMost3
  deriving DecidableEq, Repr, Fintype

/-- Upper-bound alternative meanings, inlined for `rsa_predict`. -/
def kUpperMeaning : KUpperUtt → KCard → Bool
  | .bare3,      w => w.toNat == 3
  | .fewerThan3, w => w.toNat < 3
  | .atMost3,    w => w.toNat ≤ 3

-- ============================================================================
-- § 2: RSA configurations (bilateral bare semantics, belief-based S1)
-- ============================================================================

open RSA Real in
/-- Lower-bound Kennedy alternatives through RSA L1. -/
noncomputable def kennedyLowerCfg : RSAConfig KLowerUtt KCard where
  Latent := Unit
  meaning _ _ u w := if kLowerMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

open RSA Real in
/-- Upper-bound Kennedy alternatives through RSA L1. -/
noncomputable def kennedyUpperCfg : RSAConfig KUpperUtt KCard where
  Latent := Unit
  meaning _ _ u w := if kUpperMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 3: Lower-bound predictions (Class A excludes; Class B competes + strengthens)
-- ============================================================================

/-- Class B competition at the boundary: "bare 3" beats "at least 3" at
    `w = 3`. A speaker who knew exactly 3 would have used the more
    informative "bare 3", so a listener hearing "at least 3" infers
    `w ≥ 4` is more likely. -/
theorem classB_competition_at_boundary :
    kennedyLowerCfg.L1 .bare3 .c3 > kennedyLowerCfg.L1 .atLeast3 .c3 := by rsa_predict

/-- Class A excludes the boundary: "more than 3" is false at `w = 3`,
    so `L1(w=4 | "more than 3") > L1(w=3 | "more than 3")`. -/
theorem classA_no_competition_at_boundary :
    kennedyLowerCfg.L1 .moreThan3 .c4 > kennedyLowerCfg.L1 .moreThan3 .c3 := by rsa_predict

/-- Bare numeral is peaked under exact semantics:
    `L1("bare 3", w = 3) > L1("bare 3", w = 4)`. -/
theorem bare_peaked_with_kennedy_alternatives :
    kennedyLowerCfg.L1 .bare3 .c3 > kennedyLowerCfg.L1 .bare3 .c4 := by rsa_predict

/-- Class B strengthened above bare: `L1("at least 3", w = 4) > L1("at least 3", w = 3)`.
    Hearing "at least 3" pushes probability above the boundary. -/
theorem classB_strengthened_above_bare :
    kennedyLowerCfg.L1 .atLeast3 .c4 > kennedyLowerCfg.L1 .atLeast3 .c3 := by rsa_predict

-- ============================================================================
-- § 4: Upper-bound predictions (mirror image)
-- ============================================================================

/-- Upper Class B competition at the boundary. -/
theorem upper_classB_competition :
    kennedyUpperCfg.L1 .bare3 .c3 > kennedyUpperCfg.L1 .atMost3 .c3 := by rsa_predict

/-- Upper Class A excludes the boundary: "fewer than 3" is false at `w = 3`. -/
theorem upper_classA_no_competition :
    kennedyUpperCfg.L1 .fewerThan3 .c2 > kennedyUpperCfg.L1 .fewerThan3 .c3 := by rsa_predict

/-- Upper Class B strengthened below bare: hearing "at most 3" pushes
    probability below the boundary (mirror of `classB_strengthened_above_bare`). -/
theorem upper_classB_strengthened_below_bare :
    kennedyUpperCfg.L1 .atMost3 .c2 > kennedyUpperCfg.L1 .atMost3 .c3 := by rsa_predict

-- ============================================================================
-- § 5: Grounding — inlined meanings agree with `maxMeaning`
-- ============================================================================

/-- Lower Kennedy meanings agree with the `maxMeaning` family. -/
theorem kLowerMeaning_eq_maxMeaning (u : KLowerUtt) (w : KCard) :
    kLowerMeaning u w = match u with
      | .bare3 => maxMeaning .eq 3 w.toNat
      | .moreThan3 => maxMeaning .gt 3 w.toNat
      | .atLeast3 => maxMeaning .ge 3 w.toNat := by
  cases u <;> cases w <;> rfl

/-- Upper Kennedy meanings agree with the `maxMeaning` family. -/
theorem kUpperMeaning_eq_maxMeaning (u : KUpperUtt) (w : KCard) :
    kUpperMeaning u w = match u with
      | .bare3 => maxMeaning .eq 3 w.toNat
      | .fewerThan3 => maxMeaning .lt 3 w.toNat
      | .atMost3 => maxMeaning .le 3 w.toNat := by
  cases u <;> cases w <;> rfl

end Kennedy2015
