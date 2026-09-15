import Linglib.Syntax.Mereological.Basic
import Linglib.Data.Examples.WangSun2026

/-!
# Wang & Sun (2026): Detaching Mandarin Classifiers from Nouns

This file formalizes [wang-sun-2026]'s account of three restrictions on Mandarin classifier
phrases in [adger-2025]'s mereological syntax. A classifier is not a projection of the noun but
an object of its own: it subjoins to Q as Q's 1-part, and the numeral is Q's 2-part.
Dimensionality then leaves no room at Q, so a degree-modified adjective cannot sit between the
numeral and the classifier (`q_full`, `subjoin_modifier_q`) although it subjoins to the
classifier, which has only the noun as a part (`subjoin_modifier_cl`). The classifier spells
out collectively with Q along Q's complementation line (`compLine_q`), so classifier and noun
cannot be dislocated without the numeral. The particle *de* reroutes the noun to D and the
classifier phrase through a modifier in D's second dimension, taking the classifier out of D's
1-part chain (`not_clVisible_numClDeN`); visibility from D is the paper's structural correlate
of the sortal reading of a classifier and its absence of the mensural one (`reading`). A
pre-nominal modifier in D's second dimension fills D, so a wh-numeral has nowhere to subjoin on
its way out (`subjoin_num_modNumClN`).

## Implementation notes

Structures are `MereologicalSyntax.SynObj` trees over the labels of the paper's spell-out
diagrams, and the predictions are decided on them. The paper's examples are in
`Data.Examples.WangSun2026`.

## TODO

* The article is paywalled and was not checked; the example numbers are carried over from the
  earlier version of this file and are unverified.

## References

* [wang-sun-2026]
* [adger-2025]
-/

namespace WangSun2026

open MereologicalSyntax

/-! ### Structures -/

/-- A classifier with its noun as 1-part. -/
def cl : SynObj := .sub₁ .Cl (.leaf .N)

/-- Q with the classifier as 1-part and the numeral as 2-part. -/
def q : SynObj := .sub₁₂ .Q cl (.leaf .Num)

/-- *yī zhāng zhuōzi* 'a table': Q is D's 1-part. -/
def numClN : SynObj := .sub₁ .D q

/-- *hěn dà de* 'very big': a degree phrase under Mod, the spell-out of *de*. -/
def modifier : SynObj := .sub₁ .Mod (.sub₁₂ .Deg (.leaf .A) (.leaf .Adv))

/-- *yī zhāng hěn dà de zhuōzi*: the modifier is the classifier's 2-part. -/
def numClModN : SynObj :=
  .sub₁ .D (.sub₁₂ .Q (.sub₁₂ .Cl (.leaf .N) modifier) (.leaf .Num))

/-- *hěn dà de yī zhāng zhuōzi*: the modifier is D's 2-part. -/
def modNumClN : SynObj := .sub₁₂ .D q modifier

/-- *sān bēi de jiǔ* 'three glassfuls of liquor': the noun is D's 1-part, and the numeral
phrase with a bare classifier sits under Mod as D's 2-part. -/
def numClDeN : SynObj :=
  .sub₁₂ .D (.leaf .N) (.sub₁ .Mod (.sub₁₂ .Q (.leaf .Cl) (.leaf .Num)))

/-- *sān kē duō* 'three (units) more': a numeral phrase with a bare classifier as the 1-part of
a degree predicate, with no noun at all. -/
def numClPred : SynObj :=
  .sub₁ .Pred (.sub₁₂ .Deg (.sub₁₂ .Q (.leaf .Cl) (.leaf .Num)) (.leaf .A))

/-! ### Modification -/

/-- Q has both parts, so nothing more subjoins to it. -/
theorem q_full : q.isFull = true := rfl

theorem subjoin_modifier_q : subjoin modifier q = none := rfl

/-- The classifier has room for a modifier as its 2-part. -/
theorem subjoin_modifier_cl : subjoin modifier cl = some (.sub₁₂ .Cl (.leaf .N) modifier) := rfl

/-! ### Dislocation -/

/-- The classifier lies on Q's complementation line, so it spells out with Q, whose 2-part
is the numeral. -/
theorem compLine_q : q.compLine = [.Q, .Cl, .N] := rfl

/-- The classifier phrase of `numClPred` contains no noun. -/
theorem not_containsLabel_n_numClPred : numClPred.containsLabel .N = false := rfl

/-! ### Visibility and the reading of a classifier -/

/-- Whether the classifier lies in D's 1-part chain. -/
abbrev ClVisible (d : SynObj) : Prop := labelInOnePartChain .Cl d = true

theorem clVisible_numClN : ClVisible numClN := rfl

theorem clVisible_numClModN : ClVisible numClModN := rfl

theorem clVisible_modNumClN : ClVisible modNumClN := rfl

theorem clVisible_numClPred : ClVisible numClPred := rfl

/-- With *de* the classifier is reached from D only across dimensions, so it is invisible. -/
theorem not_clVisible_numClDeN : ¬ ClVisible numClDeN := by decide

/-- The noun is visible from D with or without *de*. -/
theorem nVisible_numClN : labelInOnePartChain .N numClN = true := rfl

theorem nVisible_numClDeN : labelInOnePartChain .N numClDeN = true := rfl

/-- A classifier denotes a concrete object or an abstract unit. -/
inductive Reading
  | sortal
  | mensural
  deriving DecidableEq

/-- The reading of the classifier at a nominal: sortal when visible from D, mensural
otherwise. -/
def reading (d : SynObj) : Reading := if ClVisible d then .sortal else .mensural

theorem reading_numClN : reading numClN = .sortal := rfl

theorem reading_numClDeN : reading numClDeN = .mensural := by decide

theorem reading_numClModN : reading numClModN = .sortal := rfl

theorem reading_modNumClN : reading modNumClN = .sortal := rfl

/-! ### Wh-extraction -/

/-- Without a pre-nominal modifier D has room for the wh-numeral. -/
theorem subjoin_num_numClN : (subjoin (.leaf .Num) numClN).isSome = true := rfl

/-- A pre-nominal modifier fills D, and the wh-numeral cannot subjoin. -/
theorem subjoin_num_modNumClN : subjoin (.leaf .Num) modNumClN = none := rfl

end WangSun2026
