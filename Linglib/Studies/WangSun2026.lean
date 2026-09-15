import Linglib.Syntax.Mereological.Basic
import Linglib.Syntax.Mereological.AngularLocality

/-!
# Wang and Sun (2026): Detaching Mandarin Classifiers from Nouns

This file formalizes [wang-sun-2026]'s account of three restrictions on Mandarin classifier
phrases in [adger-2025]'s mereological syntax. A classifier is not a projection of the noun but
an object of its own, (7a): it subjoins to Q as Q's 1-part, the numeral is Q's 2-part, and the
noun, if present, is the classifier's 1-part, (7b), (26). Dimensionality then leaves no room at
Q, so a degree-modified adjective cannot sit between the numeral and the classifier, (29a)
(`q_full`, `subjoin_modifier_q`), although it subjoins to the classifier as its 2-part, (28a)
(`subjoin_modifier_cl`), or to D, (28b). The classifier spells out with Q along Q's
complementation line, (26b) (`compLine_q`), so the classifier and the noun cannot be dislocated
without the numeral. The particle *de* realises Mod, (7c): with *de* after the classifier the
quantity phrase is the 1-part of a Mod that is D's 2-part, and the classifier is reached from D
only across dimensions, (34)–(35) (`not_clVisible_numClDeN`). Visibility from D is the paper's
structural correlate of the sortal reading, glasses as entities, against the mensural reading,
glassfuls, (33) (`reading`). A second *de*-modifier cannot subjoin to the filled D, (37a)
(`subjoin_modifier_numClDeN`). In the measure use the classifier has no noun and Q is the
2-part of Deg, (45) (`not_containsLabel_n_numClPred`, `compLine_numClPred`).

Extraction runs by Angular Locality, (40), on the clausal structure of (41): the object D is
the 2-part of O, and O, v and Asp are the 1-part chain of C. A wh-numeral first subjoins to D
and from there to C, (41) (`wh_numeral`); with a *de*-modifier in D's 2-part the numeral can
neither subjoin to D nor reach C directly, (39b), (42) (`wh_numeral_modifier`). Topicalisation
of the whole D reaches C at once, (43c) (`topic_d`); the noun must subjoin to D first, stranding
the numeral and classifier, (43d) (`topic_n`), which a modifier as the classifier's 2-part
permits, (44a) (`topic_n_modifier_cl`), and a modifier as D's 2-part blocks, (44b)
(`topic_n_modifier_d`).

## Implementation notes

* Phrase-internal structure uses the trees `MereologicalSyntax.SynObj`, whose Subjoin has no
  object identity; the paper's derivations by subjunction of an object already in place use
  `MereologicalSyntax.Parthood` on the nodes of (41), with Mod a leaf and the internal structure
  of the modifier, (27), omitted.
* Linearisation, (7e), and the collective spell-out of Q with Cl are not represented; the
  adjacency of the numeral and the classifier is stated as Dimensionality at Q, which is what
  the paper derives it from, and the ban on modifiers between D and Num, (31), is not derived.
* The topicalisation of the whole D in (43c) is proved for the structure without a modifier.

## References

* [wang-sun-2026]
* [adger-2025]
-/

namespace WangSun2026

open MereologicalSyntax MereologicalSyntax.Parthood

/-! ### Structures, (26)–(28), (34), (45) -/

/-- A classifier with its noun as 1-part. -/
def cl : SynObj := .sub₁ .Cl (.leaf .N)

/-- Q with the classifier as 1-part and the numeral as 2-part, (26b). -/
def q : SynObj := .sub₁₂ .Q cl (.leaf .Num)

/-- *yī zhāng zhuōzi* 'a table', (26): Q is D's 1-part. -/
def numClN : SynObj := .sub₁ .D q

/-- *hěn dà de* 'very big', (27): a degree phrase under Mod, the spell-out of *de*. -/
def modifier : SynObj := .sub₁ .Mod (.sub₁₂ .Deg (.leaf .A) (.leaf .Adv))

/-- *yī zhāng hěn dà de zhuōzi*, (28a): the modifier is the classifier's 2-part. -/
def numClModN : SynObj :=
  .sub₁ .D (.sub₁₂ .Q (.sub₁₂ .Cl (.leaf .N) modifier) (.leaf .Num))

/-- *hěn dà de yī zhāng zhuōzi*, (28b): the modifier is D's 2-part. -/
def modNumClN : SynObj := .sub₁₂ .D q modifier

/-- Q with a bare classifier and the numeral, with no noun. -/
def qBare : SynObj := .sub₁₂ .Q (.leaf .Cl) (.leaf .Num)

/-- *sān bēi de jiǔ* 'three glassfuls of liquor', (34b): the noun is D's 1-part, and the
quantity phrase sits under Mod as D's 2-part. -/
def numClDeN : SynObj := .sub₁₂ .D (.leaf .N) (.sub₁ .Mod qBare)

/-- *duō sān kē* 'three (units) more', (45b): the quantity phrase with a bare classifier is the
2-part of Deg, whose 1-part is the adjective, under the predicate object. -/
def numClPred : SynObj := .sub₁ .Pred (.sub₁₂ .Deg (.leaf .A) qBare)

/-! ### Modification, (28)–(29), (37) -/

/-- Q has both parts, so nothing more subjoins to it, (29a). -/
theorem q_full : q.isFull = true := rfl

theorem subjoin_modifier_q : subjoin modifier q = none := rfl

/-- The classifier has room for a modifier as its 2-part, (28a). -/
theorem subjoin_modifier_cl : subjoin modifier cl = some (.sub₁₂ .Cl (.leaf .N) modifier) := rfl

/-- With *de* after the classifier D is full, so a second *de*-modifier cannot subjoin to it,
(37a). -/
theorem subjoin_modifier_numClDeN : subjoin modifier numClDeN = none := rfl

/-! ### Spell-out lines, (26b), (45b) -/

/-- The classifier lies on Q's complementation line, so it spells out with Q, whose 2-part is
the numeral, (26b). -/
theorem compLine_q : q.compLine = [.Q, .Cl, .N] := rfl

/-- The classifier of the measure use has no noun, (45a). -/
theorem not_containsLabel_n_numClPred : numClPred.containsLabel .N = false := rfl

/-- Pred, Deg and the adjective spell out together, (45b); the quantity phrase is off the
line. -/
theorem compLine_numClPred : numClPred.compLine = [.Pred, .Deg, .A] := rfl

/-! ### Visibility and the reading of a classifier, (33)–(36) -/

/-- Whether the classifier lies in D's 1-part chain. -/
abbrev ClVisible (d : SynObj) : Prop := labelInOnePartChain .Cl d = true

theorem clVisible_numClN : ClVisible numClN := rfl

theorem clVisible_numClModN : ClVisible numClModN := rfl

theorem clVisible_modNumClN : ClVisible modNumClN := rfl

/-- With *de* the classifier is reached from D only across dimensions, (35b), so it is
invisible. -/
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

/-! ### Extraction by Angular Locality, (39)–(44) -/

/-- The objects of the clausal structure (41): the clausal spine, the object D with its
quantity phrase, a modifier, and the agent. -/
inductive Node
  | C | Asp | v | O | V | D | Q | Cl | N | Num | Mod | Agent
  deriving DecidableEq, Fintype, Repr

/-- *Sān gè píngguǒ, Zhāngsān chī-le* before topicalisation, (43): D is the 2-part of O, O the
1-part of v, v of Asp, Asp of C, with the agent Asp's 2-part. -/
def clause : Parthood Node where
  onePart
    | .C => some .Asp | .Asp => some .v | .v => some .O | .O => some .V
    | .D => some .Q | .Q => some .Cl | .Cl => some .N | _ => none
  twoPart | .Asp => some .Agent | .O => some .D | .Q => some .Num | _ => none

/-- `clause` with a modifier as the classifier's 2-part, (39a), (44a). -/
def clauseModCl : Parthood Node :=
  { clause with twoPart := Function.update clause.twoPart .Cl (some .Mod) }

/-- `clause` with a modifier as D's 2-part, (39b), (44b). -/
def clauseModD : Parthood Node :=
  { clause with twoPart := Function.update clause.twoPart .D (some .Mod) }

/-- `clauseModCl` after the wh-numeral subjoins to D, (41). -/
def clauseModClNum : Parthood Node :=
  { clauseModCl with twoPart := Function.update clauseModCl.twoPart .D (some .Num) }

/-- `clause` after the noun subjoins to D, (43d). -/
def clauseN : Parthood Node :=
  { clause with twoPart := Function.update clause.twoPart .D (some .N) }

/-- `clauseModCl` after the noun subjoins to D, (44a). -/
def clauseModClN : Parthood Node :=
  { clauseModCl with twoPart := Function.update clauseModCl.twoPart .D (some .N) }

/-- O reaches C along the 1-part chain O, v, Asp, C. -/
private theorem o_nPart_c (P : Parthood Node) (h : P.onePart = clause.onePart) :
    P.NPart .one .O .C :=
  .tail (b := .Asp) (.tail (b := .v) (.single (by show P.onePart _ = _; rw [h]; rfl))
    (by show P.onePart _ = _; rw [h]; rfl)) (by show P.onePart _ = _; rw [h]; rfl)

/-- A wh-numeral is the 2-part of Q, the 1-part of D, so it subjoins to D; as D's 2-part it is
part of O, the 1-part of C, and subjoins to C, (41). It cannot reach C directly. -/
theorem wh_numeral :
    ¬ clauseModCl.CanSubjoin .Num .C ∧ clauseModCl.CanSubjoin .Num .D ∧
      clauseModCl.subjoin .Num .D = some clauseModClNum ∧ clauseModClNum.CanSubjoin .Num .C :=
  ⟨not_canSubjoin_of_not_nPart_two (S := {.D, .Q, .Cl, .N, .Num, .Mod}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .Q) (by decide) (by decide)).1 h).elim (by decide)
          (not_nPart_of_unique (n := .one) (u := .D) (by decide) (by decide) _),
    ⟨.Q, .inr (.single (by decide)), .single (by decide)⟩,
    by decide,
    ⟨.O, .inr (.tail (b := .D) (.single (by decide)) (by decide)), o_nPart_c _ rfl⟩⟩

/-- With a modifier as D's 2-part, Angular Locality still admits the wh-numeral at D but
Dimensionality refuses it, and C is out of reach, (42). -/
theorem wh_numeral_modifier :
    clauseModD.CanSubjoin .Num .D ∧ clauseModD.subjoin .Num .D = none ∧
      ¬ clauseModD.CanSubjoin .Num .C :=
  ⟨⟨.Q, .inr (.single (by decide)), .single (by decide)⟩,
    subjoin_eq_none_of_full rfl rfl,
    not_canSubjoin_of_not_nPart_two (S := {.D, .Q, .Cl, .N, .Num, .Mod}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .Q) (by decide) (by decide)).1 h).elim (by decide)
          (not_nPart_of_unique (n := .one) (u := .D) (by decide) (by decide) _)⟩

/-- The whole D, the 2-part of O, subjoins to C, (43c). -/
theorem topic_d : clause.CanSubjoin .D .C :=
  ⟨.O, .inr (.single (by decide)), o_nPart_c _ rfl⟩

/-- The noun, in D's first dimension, is no part of O and cannot reach C; it subjoins to D as
D's 2-part, becomes part of O, and reaches C, stranding the numeral and classifier, (43d). -/
theorem topic_n :
    ¬ clause.CanSubjoin .N .C ∧ clause.CanSubjoin .N .D ∧
      clause.subjoin .N .D = some clauseN ∧ clauseN.CanSubjoin .N .C :=
  ⟨not_canSubjoin_of_not_nPart_two (S := {.D, .Q, .Cl, .N, .Num}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (not_nPart_of_unique (n := .one) (u := .Cl) (by decide) (by decide) _),
    ⟨.Q, .inl (.tail (b := .Cl) (.single (by decide)) (by decide)), .single (by decide)⟩,
    by decide,
    ⟨.O, .inr (.tail (b := .D) (.single (by decide)) (by decide)), o_nPart_c _ rfl⟩⟩

/-- A modifier as the classifier's 2-part leaves D's 2-part free, and the noun topicalises,
(44a). -/
theorem topic_n_modifier_cl :
    clauseModCl.subjoin .N .D = some clauseModClN ∧ clauseModClN.CanSubjoin .N .C :=
  ⟨by decide, ⟨.O, .inr (.tail (b := .D) (.single (by decide)) (by decide)), o_nPart_c _ rfl⟩⟩

/-- A modifier as D's 2-part fills D, and the noun can neither subjoin to it nor reach C,
(44b). -/
theorem topic_n_modifier_d :
    clauseModD.subjoin .N .D = none ∧ ¬ clauseModD.CanSubjoin .N .C :=
  ⟨subjoin_eq_none_of_full rfl rfl,
    not_canSubjoin_of_not_nPart_two (S := {.D, .Q, .Cl, .N, .Num, .Mod}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (not_nPart_of_unique (n := .one) (u := .Cl) (by decide) (by decide) _)⟩

end WangSun2026
