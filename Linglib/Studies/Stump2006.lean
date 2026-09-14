import Linglib.Data.Forms.Stump2006
import Linglib.Morphology.Paradigm.Linkage
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-!
# Stump (2006): Heteroclisis and Paradigm Linkage

This file formalizes [stump-2006]'s paradigm-linkage account of heteroclisis, the property
of a lexeme whose paradigm contains forms built on stems of two or more inflection classes.
A content cell is realized by a form cell of one of the lexeme's stems, and which stem is
fixed by rules of paradigm linkage: the universal default routes every cell to the root,
and language-specific rules override it in narrower contexts, routing cells to a
coradical, a stem differing from the root in form or in class. The Czech nouns of the
paper's Tables 1, 6 and 8 are read from the forms data (`attested`): PRAMEN inflects
soft-masculine in the singular and hard-masculine in the plural, PŘEDSEDA hard-feminine in
the singular except for the dative and locative, and SLUHA also soft-masculine in the
locative plural. The endings of the declensions are read off their exemplars (`ending`),
the rules of paradigm linkage select a stem for each cell (`stemFor`), and the resulting
linkage on the substrate's `Morphology.Linkage` realizes every attested form
(`realize_matches_tables`). PRAMEN's two stems differ in class alone, so the paradigm is
heteroclite without form suppletion (`pramen_heteroclite`, `pramen_form_invariant`), which
the paper defends as a kind of stem alternation, and heteroclisis entails suppletion in that
sense (`Linkage.IsHeteroclite.isSuppletive`). Sanskrit HR̥D(AYA), built on *hr̥daya* in the
direct cases and *hr̥d* elsewhere, is heteroclite because of genuine stem suppletion
(`hrd_heteroclite_and_form_suppletive`).

The paper's constraint on heteroclisis rests on the degree of correlation of an inflectional
category with the class split, the sum over the category's values of the largest number of
cells with that value in one class, over the number of cells (`degree`). A category with
degree one is an absolute correlate and a heteroclite paradigm with an absolute correlate is
cloven, otherwise fractured, and a category exceeding every other is the maximal
correlate. Computed from the linkage, PRAMEN is cloven with number its absolute
correlate, and PŘEDSEDA and SLUHA are fractured with number their maximal correlate
(`pramen_cloven`, `predseda_fractured`, `sluha_fractured`, `number_maximal`), the
paper's figures of 1, .86 and .79 for number against .5, .64 and .57 for case.

## Implementation notes

The rules are the paper's (5), (14), (15) and (17), ordered by specificity as the paper
does under Pāṇini's principle, and the soft-masculine coradical of SLUHA is the palatalized
stem its rule of stem inference supplies. Animate and inanimate hard-masculine nouns
take their endings from FILOSOF and MOST respectively, the alternative dative and locative
endings the tables list for FILOSOF being left aside as the paper does for coradicals. The
privileged category restriction, that every rule assigning a coradical to a Czech noun is
sensitive to number, holds of the three rules by inspection and is not stated as a theorem
over a space of rules. The Sanskrit paradigm keeps the direct/oblique abstraction, since its
consonant-stem endings involve sandhi the forms data does not segment.

## References

* [stump-2006]
* [stump-2001]
-/

namespace Stump2006

open Morphology Data.Forms

/-! ### Cells, declensions and the attested forms -/

/-- The seven Czech cases, in the tables' row order. -/
inductive Case
  | nom
  | gen
  | dat
  | acc
  | voc
  | loc
  | ins
  deriving DecidableEq, Fintype, Repr

/-- The code of a case in the forms data. -/
def Case.code : Case → String
  | .nom => "nom" | .gen => "gen" | .dat => "dat" | .acc => "acc"
  | .voc => "voc" | .loc => "loc" | .ins => "ins"

/-- Grammatical number. -/
inductive Num
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

def Num.code : Num → String
  | .sg => "sg"
  | .pl => "pl"

/-- A content cell: case and number, gender held constant. -/
structure CzCell where
  case : Case
  num : Num
  deriving DecidableEq, Repr

instance : Fintype CzCell :=
  Fintype.ofEquiv (Case × Num) ⟨λ p => ⟨p.1, p.2⟩, λ c => (c.case, c.num), λ _ => rfl, λ _ => rfl⟩

/-- The Czech nouns of Tables 1, 6 and 8. -/
inductive CzNoun
  | pokoj
  | pramen
  | most
  | zena
  | predseda
  | filosof
  | sluha
  deriving DecidableEq, Fintype, Repr

/-- The parameter naming the lexeme in the forms data. -/
def CzNoun.paramId : CzNoun → String
  | .pokoj => "room" | .pramen => "spring" | .most => "bridge" | .zena => "woman"
  | .predseda => "president" | .filosof => "philosopher" | .sluha => "servant"

/-- The attested form of a cell, as segments, read from the tables. -/
def attested (l : CzNoun) (σ : CzCell) : List String :=
  ((Forms.all.find? λ f => f.parameterId == l.paramId && f.column? "Case" == some σ.case.code &&
    f.column? "Number" == some σ.num.code).map Form.segments).getD []

/-- The three declensions the tables juxtapose. -/
inductive Decl
  | softMasc
  | hardMasc
  | hardFem
  deriving DecidableEq, Fintype, Repr

/-- The ending of a declension at a cell, read off its exemplar: POKOJ for the soft-masculine,
MOST and FILOSOF for the inanimate and animate hard-masculine, ŽENA for the hard-feminine. -/
def ending : Decl → Bool → CzCell → List String
  | .softMasc, _, σ => (attested .pokoj σ).drop 5
  | .hardMasc, false, σ => (attested .most σ).drop 4
  | .hardMasc, true, σ => (attested .filosof σ).drop 7
  | .hardFem, _, σ => (attested .zena σ).drop 3

/-- The stem inventory of the tables' lexemes. Two stems may share their segments and differ
in declension, the class-distinct form-identical alternants of the paper: PRAMEN's and
PŘEDSEDA's coradicals, and SLUHA's hard-masculine coradical. -/
inductive Stem
  | pokoj
  | most
  | pramenSoft
  | pramenHard
  | zen
  | filosof
  | predsedFem
  | predsedMasc
  | sluhFem
  | sluhMasc
  | sluz
  deriving DecidableEq, Fintype, Repr

/-- A stem's segments. -/
def Stem.segments : Stem → List String
  | .pokoj => ["p", "o", "k", "o", "j"]
  | .most => ["m", "o", "s", "t"]
  | .pramenSoft | .pramenHard => ["p", "r", "a", "m", "e", "n"]
  | .zen => ["ž", "e", "n"]
  | .filosof => ["f", "i", "l", "o", "s", "o", "f"]
  | .predsedFem | .predsedMasc => ["p", "ř", "e", "d", "s", "e", "d"]
  | .sluhFem | .sluhMasc => ["s", "l", "u", "h"]
  | .sluz => ["s", "l", "u", "z"]

/-- A stem's declension, the projection heteroclisis is stated along. -/
def Stem.decl : Stem → Decl
  | .pokoj | .pramenSoft | .sluz => .softMasc
  | .most | .pramenHard | .filosof | .predsedMasc | .sluhMasc => .hardMasc
  | .zen | .predsedFem | .sluhFem => .hardFem

/-- Whether a stem inflects as animate. -/
def Stem.animate : Stem → Bool
  | .pokoj | .most | .pramenSoft | .pramenHard => false
  | _ => true

/-- The realization of a form cell: the stem's segments and its own declension's ending. -/
def czRealize (z : Stem) (σ : CzCell) : List String := z.segments ++ ending z.decl z.animate σ

/-! ### Lexical entries and the rules of paradigm linkage -/

/-- A lexeme's stipulated stems and class memberships: its root, its hard-masculine and
soft-masculine coradicals if any, and whether it belongs to the PRAMEN class of the paper's
(14) and the PŘEDSEDA subclass of (15). -/
structure Entry where
  root : Stem
  hardMascCoradical : Option Stem := none
  softMascCoradical : Option Stem := none
  pramenClass : Bool := false
  predsedaSubclass : Bool := false
  deriving DecidableEq, Repr

/-- The entries: PRAMEN's coradical is class-distinct and form-identical to its root;
PŘEDSEDA's and SLUHA's roots are hard-feminine with hard-masculine coradicals; SLUHA's
soft-masculine coradical is the palatalized stem of the paper's rule (18). -/
def entry : CzNoun → Entry
  | .pokoj => ⟨.pokoj, none, none, false, false⟩
  | .most => ⟨.most, none, none, false, false⟩
  | .pramen => ⟨.pramenSoft, some .pramenHard, none, true, false⟩
  | .zena => ⟨.zen, none, none, false, false⟩
  | .filosof => ⟨.filosof, none, none, false, false⟩
  | .predseda => ⟨.predsedFem, some .predsedMasc, none, true, true⟩
  | .sluha => ⟨.sluhFem, some .sluhMasc, some .sluz, true, true⟩

/-- The stem a cell's form correspondent is built on, by the rules of paradigm linkage in order
of specificity: (17) routes the locative plural to the soft-masculine coradical, (14) the
plural of the PRAMEN class and (15) the dative and locative singular of the PŘEDSEDA subclass
to the hard-masculine coradical, and the universal default (5) every other cell to the root. -/
def stemFor (e : Entry) (σ : CzCell) : Stem :=
  match σ.num, σ.case, e.softMascCoradical, e.hardMascCoradical with
  | .pl, .loc, some s, _ => s
  | .pl, _, _, some s => if e.pramenClass then s else e.root
  | .sg, .dat, _, some s | .sg, .loc, _, some s => if e.predsedaSubclass then s else e.root
  | _, _, _, _ => e.root

/-- The linkage of the Czech nouns: each cell to the stem its rules select, properties
preserved. -/
def czLinkage : Linkage CzNoun Stem CzCell where
  stems l σ := {stemFor (entry l) σ}
  pm _ σ := σ

/-- The rules of paradigm linkage realize every form of Tables 1, 6 and 8. -/
theorem realize_matches_tables :
    ∀ (l : CzNoun) (σ : CzCell), czLinkage.realize czRealize l σ = {(attested l σ, σ)} := by
  decide

/-! ### Heteroclisis and suppletion -/

/-- The declension realizing a cell of a lexeme. -/
def cellClass (l : CzNoun) (σ : CzCell) : Decl := (stemFor (entry l) σ).decl

/-- A lexeme is heteroclite when its cells draw on two declensions. -/
def Heteroclite (l : CzNoun) : Prop := ∃ σ τ, cellClass l σ ≠ cellClass l τ

instance (l : CzNoun) : Decidable (Heteroclite l) := inferInstanceAs (Decidable (∃ _ _, _))

/-- PRAMEN, PŘEDSEDA and SLUHA are heteroclite; the exemplars are not. -/
theorem heteroclite_iff : ∀ l, Heteroclite l ↔ l = .pramen ∨ l = .predseda ∨ l = .sluha := by
  decide

/-- The linkage is heteroclite along the class projection. -/
theorem pramen_heteroclite : czLinkage.IsHeteroclite Stem.decl := by decide

/-- PRAMEN's stems are phonologically constant: heteroclisis without form suppletion. -/
theorem pramen_form_invariant :
    ∀ σ, (stemFor (entry .pramen) σ).segments = (entry .pramen).root.segments := by
  decide

/-- The class split makes the linkage suppletive in the broad sense: two stems, the paper's
kind of stem alternation. -/
theorem stem_alternation : czLinkage.IsSuppletive := pramen_heteroclite.isSuppletive

/-! ### The constraint on heteroclisis -/

/-- The correlation count of an inflectional category `A` with the class split of a lexeme's
paradigm: for each value of the category, the largest number of cells carrying it that
inflect in one declension, summed. -/
def degreeNum {V : Type*} [Fintype V] [DecidableEq V] (l : CzNoun) (A : CzCell → V) : ℕ :=
  ∑ v : V, Finset.univ.sup λ d : Decl =>
    (Finset.univ.filter λ σ : CzCell => A σ = v ∧ cellClass l σ = d).card

/-- The degree of correlation: the count over the number of cells. -/
def degree {V : Type*} [Fintype V] [DecidableEq V] (l : CzNoun) (A : CzCell → V) : ℚ :=
  degreeNum l A / Fintype.card CzCell

/-- The inflectional categories of a Czech noun. -/
inductive Category
  | number
  | case
  deriving DecidableEq, Fintype, Repr

/-- The correlation count of a category. -/
def degreeNumOf : Category → CzNoun → ℕ
  | .number, l => degreeNum l CzCell.num
  | .case, l => degreeNum l CzCell.case

/-- The degree of correlation of a category. -/
def degreeOf (c : Category) (l : CzNoun) : ℚ := degreeNumOf c l / Fintype.card CzCell

theorem card_czCell : Fintype.card CzCell = 14 := by decide

/-- A category is an absolute correlate of a paradigm's heteroclisis when its degree is one,
that is, its count is the number of cells. -/
def IsAbsoluteCorrelate (c : Category) (l : CzNoun) : Prop :=
  degreeNumOf c l = Fintype.card CzCell

instance (c : Category) (l : CzNoun) : Decidable (IsAbsoluteCorrelate c l) :=
  inferInstanceAs (Decidable (_ = _))

theorem isAbsoluteCorrelate_iff (c : Category) (l : CzNoun) :
    IsAbsoluteCorrelate c l ↔ degreeOf c l = 1 := by
  rw [IsAbsoluteCorrelate, degreeOf, card_czCell, div_eq_one_iff_eq (by norm_num)]
  exact Nat.cast_inj.symm

/-- A category is the maximal correlate when its degree exceeds every other category's. -/
def IsMaximalCorrelate (c : Category) (l : CzNoun) : Prop :=
  ∀ c', c' ≠ c → degreeNumOf c' l < degreeNumOf c l

instance (c : Category) (l : CzNoun) : Decidable (IsMaximalCorrelate c l) :=
  inferInstanceAs (Decidable (∀ _, _ → _))

/-- A cloven paradigm: heteroclite with an absolute correlate. -/
def IsCloven (l : CzNoun) : Prop := Heteroclite l ∧ ∃ c, IsAbsoluteCorrelate c l

instance (l : CzNoun) : Decidable (IsCloven l) := inferInstanceAs (Decidable (_ ∧ ∃ _, _))

/-- A fractured paradigm: heteroclite with no absolute correlate. -/
def IsFractured (l : CzNoun) : Prop := Heteroclite l ∧ ∀ c, ¬ IsAbsoluteCorrelate c l

instance (l : CzNoun) : Decidable (IsFractured l) := inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- PRAMEN's number correlation is perfect and its case correlation one half. -/
theorem pramen_degrees : degreeOf .number .pramen = 1 ∧ degreeOf .case .pramen = 1 / 2 := by
  simp only [degreeOf, card_czCell, show degreeNumOf .number .pramen = 14 by decide,
    show degreeNumOf .case .pramen = 7 by decide]
  norm_num

/-- PŘEDSEDA: the plural and five of the seven singular cells align with number. -/
theorem predseda_degrees :
    degreeOf .number .predseda = 6 / 7 ∧ degreeOf .case .predseda = 9 / 14 := by
  simp only [degreeOf, card_czCell, show degreeNumOf .number .predseda = 12 by decide,
    show degreeNumOf .case .predseda = 9 by decide]
  norm_num

/-- SLUHA: the locative plural breaks the plural's alignment as well. -/
theorem sluha_degrees : degreeOf .number .sluha = 11 / 14 ∧ degreeOf .case .sluha = 4 / 7 := by
  simp only [degreeOf, card_czCell, show degreeNumOf .number .sluha = 11 by decide,
    show degreeNumOf .case .sluha = 8 by decide]
  norm_num

theorem pramen_cloven : IsCloven .pramen ∧ IsAbsoluteCorrelate .number .pramen := by decide

theorem predseda_fractured : IsFractured .predseda := by decide

theorem sluha_fractured : IsFractured .sluha := by decide

/-- Number is the maximal correlate of each heteroclite paradigm, the paper's (38) for Czech:
the category that is the absolute correlate of the cloven paradigm is the maximal correlate
of the fractured ones. -/
theorem number_maximal : ∀ l, Heteroclite l → IsMaximalCorrelate .number l := by decide

/-! ### Sanskrit HR̥D(AYA): heteroclisis riding on stem suppletion (Table 4)

Direct cases (nominative, vocative, accusative) are built on *hr̥daya*, oblique cases on
*hr̥d*; the a-stem follows the neuter a-stem declension, the consonant stem the neuter
consonant-stem declension. Cells are abstracted to the direct/oblique split. -/

/-- The direct/oblique case-class split. -/
inductive CaseClass
  | direct
  | oblique
  deriving DecidableEq, Fintype, Repr

/-- The two Sanskrit neuter declensions involved. -/
inductive SktDecl
  | aStem
  | consStem
  deriving DecidableEq, Fintype, Repr

/-- HR̥D(AYA)'s two suppletive stems. -/
inductive SktStem
  | hrdaya
  | hrd
  deriving DecidableEq, Fintype, Repr

/-- Stem forms. -/
def SktStem.form : SktStem → String
  | .hrdaya => "hr̥daya"
  | .hrd => "hr̥d"

/-- Stem class: the a-stem declines as an a-stem, the consonant stem as a consonant stem. -/
def SktStem.decl : SktStem → SktDecl
  | .hrdaya => .aStem
  | .hrd => .consStem

/-- The single lexeme HR̥D(AYA). -/
inductive SktNoun
  | hrdaya
  deriving DecidableEq, Fintype, Repr

/-- The suppletive linkage: direct cells on *hr̥daya*, oblique on *hr̥d*. -/
def sktLinkage : Linkage SktNoun SktStem CaseClass where
  stems _ σ := match σ with | .direct => {.hrdaya} | .oblique => {.hrd}
  pm _ σ := σ

/-- HR̥D(AYA) is heteroclite and form-suppletive: its heteroclisis is an effect of the stem
suppletion, in contrast with PRAMEN. -/
theorem hrd_heteroclite_and_form_suppletive :
    sktLinkage.IsHeteroclite SktStem.decl ∧ ¬ sktLinkage.InvariantAlong SktStem.form :=
  ⟨by decide, by decide⟩

end Stump2006
