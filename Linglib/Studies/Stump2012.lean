import Linglib.Data.Forms.Stump2012
import Linglib.Morphology.Paradigm.Linkage
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Stump (2012): The Formal and Functional Architecture of Inflectional Morphology

This file formalizes [stump-2012-mmm8]'s architecture of inflection, in which a lexeme's
content paradigm is linked to the form paradigms of its stems, and its account of
noncanonical inflection as deviation from canonical paradigm linkage. Canonical linkage is
total, stem-invariant, injective and property-preserving, the axes of the substrate's
`Morphology.Linkage.IsCanonical`, and the Breton inflecting preposition HERVEZ is the
paper's canonical witness (`hervez_isCanonical`). Each noncanonical phenomenon deviates on
one axis: Latin COEPISSE lacks present-system stems and is defective without being
suppletive (`coepisse_defective_not_suppletive`), Latin BELLUM shares form correspondents
between the nominative and the accusative and between the dative and the ablative, the
directional and nondirectional syncretisms of the paper's rules (24) and (25)
(`bellum_nom_acc_syncretic`, `bellum_nom_acc_realize_eq`), deponent HORTĀRĪ has passive
form correspondents for its active content cells and none for its passive ones
(`hortari_unfaithful`, `hortari_defective`, `hortari_active_form_virtual`), the Hungarian
pronoun ÉN takes its oblique-case forms from case stems inflected for the pronoun's own
person and number, the functor-argument reversal of rule (37)
(`en_functor_argument_reversal`, `en_pm_lexeme_sensitive`), and Latin FERRE has two stems
in complementary distribution under the default rule alone, suppletive yet
property-preserving (`ferre_suppletive_yet_faithful`). The deviations compound: Old
Icelandic ÞURFA forms its present as a strong verb forms its past and its past on a weak
stem, deponent and suppletive at once (`thurfa_suppletive_and_unfaithful`).

The forms of the paper's examples are read from the forms data (`attested`). Where the
paper's realization follows from a stem and an ending, the ending is read off an exemplar:
COEPISSE's perfect endings are FERRE's (`coepisse_perfect_realized`), and HORTĀRĪ's
passive endings are LAUDĀRE's, which realize the deponent's active content cells
(`hortari_realizes_hortor`, `depon_vs_regular`).

## Implementation notes

The merged dative/ablative form cell of rule (25) is represented by the dative, with both
content cells mapped there. Deponent HORTĀRĪ's stem is taken as the segments before the
personal ending, as is LAUDĀRE's, so that the endings are shared. The Hungarian pronoun's
direct-case forms and the full Old Icelandic paradigm of (44) are not represented; the
paper's discussion of the later Latin active *hortābat* as an exploratory expression is
described only in the docstring of the virtual form cell.

## References

* [stump-2012-mmm8]
* [hippisley-2010]
-/

namespace Stump2012

open Morphology Data.Forms

/-- The attested form with the given parameter and column values, as segments. -/
def attested (pid : String) (cols : List (String × String)) : List String :=
  ((Forms.all.find? λ f => f.parameterId == pid &&
    cols.all λ c => f.column? c.1 == some c.2).map Form.segments).getD []

/-- Person-number agreement, the six cells shared across the Latin verb paradigms. -/
inductive Agr
  | s1
  | s2
  | s3
  | p1
  | p2
  | p3
  deriving DecidableEq, Fintype, Repr

/-- The agreement code in the forms data. -/
def Agr.code : Agr → String
  | .s1 => "s1" | .s2 => "s2" | .s3 => "s3" | .p1 => "p1" | .p2 => "p2" | .p3 => "p3"

/-- The Latin tense-system split: present-system versus perfect-system cells. -/
inductive System
  | pres
  | perf
  deriving DecidableEq, Fintype, Repr

def System.code : System → String
  | .pres => "pres"
  | .perf => "perf"

/-! ### Breton HERVEZ: the canonical baseline -/

section Breton

/-- The inflecting preposition HERVEZ 'according to'. -/
inductive HervezLex
  | hervez
  deriving DecidableEq, Fintype, Repr

/-- Its sole stem. -/
inductive HervezStem
  | hervez
  deriving DecidableEq, Fintype, Repr

/-- HERVEZ's linkage: one stem, identity property mapping, the canonical pattern of the
paper's (14). -/
def hervezLinkage : Linkage HervezLex HervezStem Agr := Linkage.canonical λ _ => .hervez

/-- HERVEZ is canonical on all four axes. -/
theorem hervez_isCanonical : hervezLinkage.IsCanonical := Linkage.canonical_isCanonical _

end Breton

/-! ### Latin COEPISSE: defectiveness -/

section Coepisse

inductive CoepLex
  | coepisse
  deriving DecidableEq, Fintype, Repr

inductive CoepStem
  | coep
  deriving DecidableEq, Fintype, Repr

/-- A Latin verb content cell: a tense system and an agreement feature. -/
structure SysCell where
  sys : System
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype SysCell :=
  Fintype.ofEquiv (System × Agr) ⟨λ p => ⟨p.1, p.2⟩, λ c => (c.sys, c.agr), λ _ => rfl, λ _ => rfl⟩

/-- COEPISSE's linkage, the stem specification (18): `coep` on perfect-system cells, no stem
on present-system cells. -/
def coepisseLinkage : Linkage CoepLex CoepStem SysCell where
  stems _ σ := match σ.sys with | .perf => {.coep} | .pres => ∅
  pm _ σ := σ

/-- The perfect endings, read off FERRE's perfect forms of (41) after its stem `tul`. -/
def perfEnding (a : Agr) : List String :=
  (attested "carry" [("System", "perf"), ("Agr", a.code)]).drop 3

/-- The realization of a form cell of `coep`: the stem and the perfect ending. -/
def coepRealize : CoepStem → SysCell → List String
  | _, σ => ["c", "o", "e", "p"] ++ perfEnding σ.agr

/-- COEPISSE is defective: the present-system cells lack a stem. -/
theorem coepisse_defective : coepisseLinkage.IsDefective := ⟨.coepisse, ⟨.pres, .s1⟩, rfl⟩

/-- A present-system content cell has no realization. -/
theorem coepisse_present_no_realization :
    coepisseLinkage.realize coepRealize .coepisse ⟨.pres, .s3⟩ = ∅ := by decide

/-- Every perfect-system content cell realizes through its `coep` correspondent as the
paper's (17) lists, with FERRE's perfect endings. -/
theorem coepisse_perfect_realized (a : Agr) :
    coepisseLinkage.realize coepRealize .coepisse ⟨.perf, a⟩ =
      {(attested "begin" [("System", "perf"), ("Agr", a.code)], ⟨.perf, a⟩)} := by
  revert a; decide

/-- COEPISSE keeps a single stem, so it is stem-invariant. -/
theorem coepisse_stemInvariant : coepisseLinkage.IsStemInvariant := by
  intro _ _ _ z₁ z₂ _ _; cases z₁; cases z₂; rfl

/-- Defectiveness without suppletion: COEPISSE deviates on totality alone. -/
theorem coepisse_defective_not_suppletive :
    coepisseLinkage.IsDefective ∧ ¬ coepisseLinkage.IsSuppletive :=
  ⟨coepisse_defective, not_not.mpr coepisse_stemInvariant⟩

end Coepisse

/-! ### Latin BELLUM: syncretism -/

section Bellum

inductive BellumLex
  | bellum
  deriving DecidableEq, Fintype, Repr

inductive BellumStem
  | bell
  deriving DecidableEq, Fintype, Repr

inductive Case
  | nom
  | gen
  | dat
  | acc
  | abl
  deriving DecidableEq, Fintype, Repr

def Case.code : Case → String
  | .nom => "nom" | .gen => "gen" | .dat => "dat" | .acc => "acc" | .abl => "abl"

inductive Num
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

def Num.code : Num → String
  | .sg => "sg"
  | .pl => "pl"

/-- A BELLUM content cell: a case and a number. -/
structure BellumCell where
  case : Case
  num : Num
  deriving DecidableEq, Repr

instance : Fintype BellumCell :=
  Fintype.ofEquiv (Case × Num) ⟨λ p => ⟨p.1, p.2⟩, λ c => (c.case, c.num), λ _ => rfl, λ _ => rfl⟩

/-- The property mapping: the nominative to the accusative, the directional neuter syncretism
of rule (24), and the ablative to the dative representing the merged dative/ablative cell
of rule (25). -/
def bellumPm (σ : BellumCell) : BellumCell :=
  match σ.case with
  | .nom => { σ with case := .acc }
  | .abl => { σ with case := .dat }
  | _ => σ

/-- BELLUM's linkage: one stem, the syncretizing property mapping. -/
def bellumLinkage : Linkage BellumLex BellumStem BellumCell where
  stems _ _ := {.bell}
  pm _ σ := bellumPm σ

/-- The realizations of the form cells of `bell`, the paper's (22). -/
def bellRealize : BellumStem → BellumCell → List String
  | _, σ => attested "war" [("Case", σ.case.code), ("Number", σ.num.code)]

/-- Directional syncretism: the nominative and accusative singular share a form
correspondent. -/
theorem bellum_nom_acc_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.nom, .sg⟩, ⟨.acc, .sg⟩, by decide, by decide⟩

/-- Nondirectional syncretism: the dative and ablative singular share a form correspondent. -/
theorem bellum_dat_abl_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.dat, .sg⟩, ⟨.abl, .sg⟩, by decide, by decide⟩

/-- A shared form correspondent forces a shared realization: the nominative and accusative
singular both realize as *bellum*, the paper's (26). -/
theorem bellum_nom_acc_realize_eq :
    bellumLinkage.realize bellRealize .bellum ⟨.nom, .sg⟩ =
      bellumLinkage.realize bellRealize .bellum ⟨.acc, .sg⟩ :=
  bellumLinkage.realize_eq_of_corr_eq bellRealize (by decide)

/-- The nominative singular realizes through the accusative form cell. -/
theorem bellum_nom_realizes_acc :
    bellumLinkage.realize bellRealize .bellum ⟨.nom, .sg⟩ =
      {(attested "war" [("Case", "acc"), ("Number", "sg")], ⟨.acc, .sg⟩)} := by
  decide

/-- Syncretism is the failure of injectivity. -/
theorem bellum_not_injective : ¬ bellumLinkage.IsInjective :=
  bellumLinkage.isSyncretic_iff_not_isInjective.mp bellum_nom_acc_syncretic

end Bellum

/-! ### Latin HORTĀRĪ: deponency, defectiveness and virtual cells -/

section Hortari

inductive LatinVerb
  | hortari
  | laudare
  deriving DecidableEq, Fintype, Repr

inductive VerbStem
  | hort
  | laud
  deriving DecidableEq, Fintype, Repr

inductive Voice
  | active
  | passive
  deriving DecidableEq, Fintype, Repr

def Voice.code : Voice → String
  | .active => "act"
  | .passive => "pass"

/-- A finite content cell: a voice and an agreement feature. -/
structure VCell where
  voice : Voice
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype VCell :=
  Fintype.ofEquiv (Voice × Agr)
    ⟨λ p => ⟨p.1, p.2⟩, λ c => (c.voice, c.agr), λ _ => rfl, λ _ => rfl⟩

/-- The linkage of the two verbs: deponent HORTĀRĪ has a stem on its active cells only and
the voice-flipping property mapping of rule (29), the stem specification (30a); regular
LAUDĀRE is canonical, (30b). -/
def latinLinkage : Linkage LatinVerb VerbStem VCell where
  stems l σ := match l, σ.voice with
    | .hortari, .active => {.hort}
    | .hortari, .passive => ∅
    | .laudare, _ => {.laud}
  pm l σ := match l with
    | .hortari => { σ with voice := .passive }
    | .laudare => σ

/-- The personal endings, read off LAUDĀRE's forms of (28) after its stem. -/
def personalEnding (v : Voice) (a : Agr) : List String :=
  (attested "praise" [("Voice", v.code), ("Agr", a.code)]).drop 4

/-- The realization of a form cell: the stem and the ending of the form cell's voice. -/
def verbRealize : VerbStem → VCell → List String
  | .hort, τ => ["h", "o", "r", "t"] ++ personalEnding τ.voice τ.agr
  | .laud, τ => ["l", "a", "u", "d"] ++ personalEnding τ.voice τ.agr

/-- Deponency: the property mapping of HORTĀRĪ's active content cells is unfaithful, flipping
to passive. -/
theorem hortari_unfaithful : latinLinkage.IsUnfaithful := ⟨.hortari, ⟨.active, .s1⟩, by decide⟩

/-- Every active content cell of HORTĀRĪ has a passive form correspondent. -/
theorem hortari_active_realized_by_passive (a : Agr) :
    (latinLinkage.corr .hortari ⟨.active, a⟩).image (·.2.voice) = {.passive} := by
  revert a; decide

/-- The active content cells of HORTĀRĪ realize with LAUDĀRE's passive endings, as the
paper's (28) lists. -/
theorem hortari_realizes_hortor (a : Agr) :
    latinLinkage.realize verbRealize .hortari ⟨.active, a⟩ =
      {(attested "urge" [("Voice", "pass"), ("Agr", a.code)], ⟨.passive, a⟩)} := by
  revert a; decide

/-- The same active content cell: LAUDĀRE realizes through an active form cell, HORTĀRĪ
through a passive one. -/
theorem depon_vs_regular (a : Agr) :
    latinLinkage.realize verbRealize .laudare ⟨.active, a⟩ =
        {(attested "praise" [("Voice", "act"), ("Agr", a.code)], ⟨.active, a⟩)} ∧
      latinLinkage.realize verbRealize .hortari ⟨.active, a⟩ =
        {(attested "urge" [("Voice", "pass"), ("Agr", a.code)], ⟨.passive, a⟩)} := by
  revert a; decide

/-- Deponency compounds with defectiveness: the passive content cells of HORTĀRĪ lack a
stem. -/
theorem hortari_defective : latinLinkage.IsDefective := ⟨.hortari, ⟨.passive, .s1⟩, rfl⟩

/-- The active form cell of `hort` is virtual: no content cell corresponds to it, since
active content maps to passive form and passive content has no correspondent. The later
Latin active *hortābat*, as [hippisley-2010] describes, releases it. -/
theorem hortari_active_form_virtual : latinLinkage.IsVirtual (.hort, ⟨.active, .s1⟩) := by
  unfold Linkage.IsVirtual; decide

end Hortari

/-! ### Hungarian ÉN: functor-argument reversal -/

section Hungarian

/-- The personal pronouns ÉN '1sg' and TE '2sg'. -/
inductive Pron
  | en
  | te
  deriving DecidableEq, Fintype, Repr

/-- The oblique cases of (38) represented here. -/
inductive HuCase
  | dative
  | inessive
  | superessive
  deriving DecidableEq, Fintype, Repr

/-- The pronominal person-number properties the form cell carries. -/
inductive PersNum
  | p1sg
  | p2sg
  deriving DecidableEq, Fintype, Repr

def PersNum.code : PersNum → String
  | .p1sg => "p1sg"
  | .p2sg => "p2sg"

/-- A Hungarian property set: a content-side case or a form-side person-number set. -/
inductive HuProp
  | case (c : HuCase)
  | agr (pn : PersNum)
  deriving DecidableEq, Fintype, Repr

/-- The case postposition stems *nek*, *benn*, *rajt*. -/
inductive CaseStem
  | nek
  | benn
  | rajt
  deriving DecidableEq, Fintype, Repr

def CaseStem.pid : CaseStem → String
  | .nek => "nek"
  | .benn => "benn"
  | .rajt => "rajt"

/-- The stem selection of rule (37): the case picks the postpositional stem. -/
def enStems : Pron → HuProp → Finset CaseStem
  | _, .case .dative => {.nek}
  | _, .case .inessive => {.benn}
  | _, .case .superessive => {.rajt}
  | _, _ => ∅

/-- The property mapping computes the form property set from the lexeme, the
functor-argument reversal of (32) and (37). -/
def enPm : Pron → HuProp → HuProp
  | .en, _ => .agr .p1sg
  | .te, _ => .agr .p2sg

/-- ÉN's linkage: case-driven stem, lexeme-driven property mapping. -/
def enLinkage : Linkage Pron CaseStem HuProp where
  stems := enStems
  pm := enPm

/-- The inflected postpositions of (36). -/
def enRealize : CaseStem → HuProp → List String
  | z, .agr pn => attested z.pid [("PersNum", pn.code)]
  | _, _ => []

/-- The inessive of ÉN corresponds to the 1sg form cell of *benn*, the paper's (38). -/
theorem en_inessive_corr : enLinkage.corr .en (.case .inessive) = {(.benn, .agr .p1sg)} := by
  decide

/-- The correspondent's property set is the pronoun's, not the case's: the reversal is
unfaithful. -/
theorem en_functor_argument_reversal : enLinkage.IsUnfaithful := ⟨.en, .case .inessive, by decide⟩

/-- The property mapping consults the lexeme: ÉN and TE send the same inessive content cell to
different form property sets. -/
theorem en_pm_lexeme_sensitive :
    enLinkage.pm .en (.case .inessive) ≠ enLinkage.pm .te (.case .inessive) := by
  decide

/-- The inessive of ÉN and of TE realize as the first and second person forms of *benn*. -/
theorem inessive_realizes :
    enLinkage.realize enRealize .en (.case .inessive) =
        {(attested "benn" [("PersNum", "p1sg")], .agr .p1sg)} ∧
      enLinkage.realize enRealize .te (.case .inessive) =
        {(attested "benn" [("PersNum", "p2sg")], .agr .p2sg)} := by
  decide

end Hungarian

/-! ### Latin FERRE: suppletion under the default rule -/

section Ferre

inductive FerreLex
  | ferre
  deriving DecidableEq, Fintype, Repr

inductive FerreStem
  | fer
  | tul
  deriving DecidableEq, Fintype, Repr

/-- FERRE's linkage: the stem specification (42) gives two suppletive stems in complementary
distribution, and the default rule supplies the identity property mapping. -/
def ferreLinkage : Linkage FerreLex FerreStem SysCell where
  stems _ σ := match σ.sys with | .pres => {.fer} | .perf => {.tul}
  pm _ σ := σ

/-- FERRE is suppletive: the present- and perfect-system cells draw on different stems. -/
theorem ferre_suppletive : ferreLinkage.IsSuppletive := λ h =>
  absurd (h .ferre (σ₁ := ⟨.pres, .s1⟩) (σ₂ := ⟨.perf, .s1⟩) (z₁ := .fer) (z₂ := .tul)
    (by decide) (by decide)) (by decide)

/-- FERRE is property-preserving: with no override the default rule preserves the content
cell's property set. -/
theorem ferre_propertyPreserving : ferreLinkage.IsPropertyPreserving := λ _ _ => rfl

/-- Suppletive yet property-preserving: the two axes are independent. -/
theorem ferre_suppletive_yet_faithful :
    ferreLinkage.IsSuppletive ∧ ferreLinkage.IsPropertyPreserving :=
  ⟨ferre_suppletive, ferre_propertyPreserving⟩

end Ferre

/-! ### Old Icelandic ÞURFA: a compound deviation -/

section Thurfa

inductive ThurfaLex
  | thurfa
  deriving DecidableEq, Fintype, Repr

/-- The strong stem *þarf* and the weak stem *þurf*. -/
inductive ThurfaStem
  | strong
  | weak
  deriving DecidableEq, Fintype, Repr

inductive Tense
  | pres
  | past
  deriving DecidableEq, Fintype, Repr

/-- A ÞURFA content cell: a tense and an agreement feature. -/
structure TCell where
  tense : Tense
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype TCell :=
  Fintype.ofEquiv (Tense × Agr)
    ⟨λ p => ⟨p.1, p.2⟩, λ c => (c.tense, c.agr), λ _ => rfl, λ _ => rfl⟩

/-- ÞURFA's linkage, the paper's (45) and (46): the strong stem for the present and the weak
stem for the past, suppletion, and a property mapping sending every cell to the past, the
deponent tense. -/
def thurfaLinkage : Linkage ThurfaLex ThurfaStem TCell where
  stems _ σ := match σ.tense with | .pres => {.strong} | .past => {.weak}
  pm _ σ := { σ with tense := .past }

/-- The realizations of (46): the strong stem at a past form cell gives the present forms,
the weak stem the past forms. -/
def thurfaRealize : ThurfaStem → TCell → List String
  | .strong, τ => attested "need" [("Tense", "pres"), ("Agr", τ.agr.code)]
  | .weak, τ => attested "need" [("Tense", "past"), ("Agr", τ.agr.code)]

/-- ÞURFA is suppletive: present and past draw on different stems. -/
theorem thurfa_suppletive : thurfaLinkage.IsSuppletive := λ h =>
  absurd (h .thurfa (σ₁ := ⟨.pres, .s1⟩) (σ₂ := ⟨.past, .s1⟩) (z₁ := .strong) (z₂ := .weak)
    (by decide) (by decide)) (by decide)

/-- ÞURFA is unfaithful: a present content cell maps to a past form cell. -/
theorem thurfa_unfaithful : thurfaLinkage.IsUnfaithful := ⟨.thurfa, ⟨.pres, .s1⟩, by decide⟩

/-- The compound deviation: suppletion and deponent tense mapping in one linkage. -/
theorem thurfa_suppletive_and_unfaithful :
    thurfaLinkage.IsSuppletive ∧ thurfaLinkage.IsUnfaithful :=
  ⟨thurfa_suppletive, thurfa_unfaithful⟩

/-- The present content cell realizes as *þarf* through the strong stem at the past form
cell, and the past content cell as *þurfta* through the weak stem. -/
theorem thurfa_realizes :
    thurfaLinkage.realize thurfaRealize .thurfa ⟨.pres, .s1⟩ =
        {(attested "need" [("Tense", "pres"), ("Agr", "s1")], ⟨.past, .s1⟩)} ∧
      thurfaLinkage.realize thurfaRealize .thurfa ⟨.past, .s1⟩ =
        {(attested "need" [("Tense", "past"), ("Agr", "s1")], ⟨.past, .s1⟩)} := by
  decide

end Thurfa

end Stump2012
