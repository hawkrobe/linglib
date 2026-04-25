import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

/-!
# Syllogistic substrate: types

Theory-neutral types for the Aristotelian syllogistic fragment.

The four Aristotelian quantifiers (`AristQuant`: A/I/O/E = all/some/someNot/no)
applied to three terms (A, B, C) generate the classical syllogism: two
quantified premises sharing a middle term B, plus a conclusion relating A and C.
The state space is the 7 non-empty regions of a three-circle Venn diagram —
the empty region {¬A, ¬B, ¬C} is excluded since it does not affect quantifier
truth conditions.

Used by:
- `Theories.Semantics.Quantification.Syllogistic.Basic` for the semantics
- `Phenomena.Quantification.Studies.TesslerTenenbaumGoodman2022` and any
  future Bayesian/RSA/mental-models paper formalisation
-/

namespace Semantics.Quantification.Syllogistic

-- ============================================================================
-- §1. Aristotelian Quantifiers (A/I/O/E square)
-- ============================================================================

/-- The four Aristotelian quantifiers. Names follow the medieval mnemonic:
    A = `all` (universal affirmative), I = `some` (particular affirmative),
    O = `someNot` (particular negative), E = `no` (universal negative). -/
inductive AristQuant where
  | all | some | someNot | no
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Venn Diagram Regions
-- ============================================================================

/-- The 7 non-empty regions of a three-circle (A, B, C) Venn diagram.
    The empty region {¬A, ¬B, ¬C} is excluded because it does not affect
    quantifier truth conditions for any A/I/O/E form. -/
inductive Region where
  | A | B | C | AB | AC | BC | ABC
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A Venn state: which regions are populated. 2⁷ = 128 possible states. -/
abbrev VennState := Region → Bool

/-- Region predicate: does region r have property A? -/
def hasA : Region → Bool | .A | .AB | .AC | .ABC => true | _ => false

/-- Region predicate: does region r have property B? -/
def hasB : Region → Bool | .B | .AB | .BC | .ABC => true | _ => false

/-- Region predicate: does region r have property C? -/
def hasC : Region → Bool | .C | .AC | .BC | .ABC => true | _ => false

-- ============================================================================
-- §3. Syllogisms and Conclusions
-- ============================================================================

/-- A syllogism is a pair of quantified premises sharing middle term B.

    `order1AB = true` means premise 1 is "Q₁ A-B"; false means "Q₁ B-A".
    `order2BC = true` means premise 2 is "Q₂ B-C"; false means "Q₂ C-B".

    The four combinations of orderings give the four classical *figures*:
    - Figure 1: A-B, B-C   (`order1AB = true,  order2BC = true`)
    - Figure 2: B-A, B-C   (`order1AB = false, order2BC = true`)
    - Figure 3: A-B, C-B   (`order1AB = true,  order2BC = false`)
    - Figure 4: B-A, C-B   (`order1AB = false, order2BC = false`)

    With 4 quantifier choices per premise, this gives 4 × 2 × 4 × 2 = 64 syllogisms. -/
structure Syllogism where
  q1 : AristQuant
  order1AB : Bool
  q2 : AristQuant
  order2BC : Bool
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 9 possible conclusions: 4 quantifiers × 2 term orders + NVC ("nothing
    follows"). NVC is the explicit response that no Aristotelian conclusion
    is warranted — modeled semantically as the vacuous utterance. -/
inductive Conclusion where
  | allAC | allCA
  | someAC | someCA
  | someNotAC | someNotCA
  | noAC | noCA
  | nvc
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Does the conclusion use A→C term order (vs C→A)? Used by figural-bias
    parameterisations that prefer one term order based on the syllogism's figure. -/
def Conclusion.isAC : Conclusion → Bool
  | .allAC | .someAC | .someNotAC | .noAC => true
  | _ => false

/-- Short label for display (Aristotelian medieval letter codes:
    A = universal affirmative, I = particular affirmative,
    E = universal negative, O = particular negative). -/
def Conclusion.short : Conclusion → String
  | .allAC => "Aac" | .allCA => "Aca"
  | .someAC => "Iac" | .someCA => "Ica"
  | .someNotAC => "Oac" | .someNotCA => "Oca"
  | .noAC => "Eac" | .noCA => "Eca"
  | .nvc => "NVC"

end Semantics.Quantification.Syllogistic
