import Linglib.Morphology.Paradigm.Linkage
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Stump 2012: canonical paradigm linkage and its deviations
[stump-2012-mmm8]

The four axes of canonical paradigm linkage of `Morphology/Paradigm/Linkage.lean`
([stump-2012-mmm8]), each anchored by the paper's own witness: a near-canonical
baseline and one deviation per axis, plus the two compound cases that show the
axes are independent. Content and form paradigms, the correspondence relation,
and the deviation typology are the paper's; the forms are transcribed from its
numbered tables.

* **Breton HERVEZ** (Table (2)) — the near-canonical baseline: total, stem-invariant,
  injective, property-preserving.
* **Latin COEPISSE** ((17)–(19)) — defectiveness: a present-system stem gap, yet a
  single stem, so defective without being suppletive.
* **Latin BELLUM** ((22)–(26)) — syncretism: neuter nominative patterning after the
  accusative (directional) and a merged dative/ablative cell (nondirectional).
* **Latin HORTĀRĪ** ((27)–(31), §4) — deponency: active content cells with passive
  form correspondents, compounded with defectiveness on the passive cells, and a
  virtual active form cell.
* **Hungarian ÉN** ((33)–(38)) — functor-argument reversal: a form correspondent's
  property set computed from the lexeme.
* **Latin FERRE** ((41)–(43)) — suppletion under the default rule: two stems in
  complementary distribution, yet property-preserving.
* **Old Icelandic ÞURFA** ((44)–(46)) — a compound deviation: suppletion and
  deponent tense mapping in one linkage.
-/

namespace Stump2012

open Morphology

/-- Person-number agreement, the six cells shared across the Latin verb paradigms. -/
inductive Agr | s1 | s2 | s3 | p1 | p2 | p3
  deriving DecidableEq, Fintype, Repr

/-- The Latin tense-system split: present-system versus perfect-system cells. -/
inductive System | pres | perf
  deriving DecidableEq, Fintype, Repr

/-! ### Breton HERVEZ: the near-canonical baseline (Table (2)) -/

section Breton

/-- The inflecting preposition HERVEZ 'according to'. -/
inductive HervezLex | hervez
  deriving DecidableEq, Fintype, Repr

/-- Its sole stem `hervez[Cl.1]`. -/
inductive HervezStem | hervez
  deriving DecidableEq, Fintype, Repr

/-- HERVEZ's linkage: one stem, identity property mapping — the canonical pattern.
Its realizations `hervezon, hervezout, hervezi, hervezomp, hervezo` are based on
the single stem with the content cell's own property set. -/
def hervezLinkage : Linkage HervezLex HervezStem Agr :=
  Linkage.canonical (fun _ => .hervez)

/-- HERVEZ is canonical on all four axes ([stump-2012-mmm8] Table (2)). -/
theorem hervez_isCanonical : hervezLinkage.IsCanonical :=
  Linkage.canonical_isCanonical _

theorem hervez_not_defective : ¬ hervezLinkage.IsDefective :=
  hervez_isCanonical.not_isDefective
theorem hervez_not_suppletive : ¬ hervezLinkage.IsSuppletive :=
  hervez_isCanonical.not_isSuppletive
theorem hervez_not_syncretic : ¬ hervezLinkage.IsSyncretic :=
  hervez_isCanonical.not_isSyncretic
theorem hervez_not_unfaithful : ¬ hervezLinkage.IsUnfaithful :=
  hervez_isCanonical.not_isUnfaithful

end Breton

/-! ### Latin COEPISSE: defectiveness ((17)–(19))

The present-system cells lack a stem, so they lack form correspondents and
realizations; the perfect-system cells have the stem `coep`. Defectiveness sits
in the stem specification, and COEPISSE keeps a single stem — defective without
being suppletive. -/

section Coepisse

inductive CoepLex | coepisse
  deriving DecidableEq, Fintype, Repr
inductive CoepStem | coep
  deriving DecidableEq, Fintype, Repr

/-- A COEPISSE content cell: a tense system and an agreement feature. -/
structure CoepCell where
  sys : System
  agr : Agr
  deriving DecidableEq, Fintype, Repr

/-- COEPISSE's linkage: `coep` on perfect-system cells, no stem on present-system
cells ([stump-2012-mmm8] (18)). -/
def coepisseLinkage : Linkage CoepLex CoepStem CoepCell where
  stem := fun _ σ => match σ.sys with | .perf => some .coep | .pres => none
  pm := fun _ σ => σ

/-- The perfect-system realizations `coepī, coepistī, coepit, coepimus,
coepistis, coepērunt` ([stump-2012-mmm8] (17)). -/
def coepRealize : CoepStem → CoepCell → String
  | _, σ => "coep" ++ (match σ.agr with
      | .s1 => "i" | .s2 => "isti" | .s3 => "it"
      | .p1 => "imus" | .p2 => "istis" | .p3 => "erunt")

/-- COEPISSE is defective: the present-system cells lack a stem ([stump-2012-mmm8]
§3.1). -/
theorem coepisse_defective : coepisseLinkage.IsDefective :=
  ⟨.coepisse, ⟨.pres, .s1⟩, rfl⟩

/-- A present-system content cell has no realization. -/
theorem coepisse_present_no_realization :
    coepisseLinkage.realize coepRealize .coepisse ⟨.pres, .s3⟩ = none := rfl

/-- A perfect-system content cell realizes through its `coep` correspondent
(`coepit`, 3sg). -/
theorem coepisse_perfect_realized :
    coepisseLinkage.realize coepRealize .coepisse ⟨.perf, .s3⟩
      = some ("coepit", ⟨.perf, .s3⟩) := rfl

/-- COEPISSE keeps a single stem, so it is stem-invariant. -/
theorem coepisse_stemInvariant : coepisseLinkage.IsStemInvariant := by
  intro _ _ _ z₁ z₂ _ _; cases z₁; cases z₂; rfl

/-- Defectiveness without suppletion: COEPISSE deviates on totality alone
([stump-2012-mmm8] §3.1). -/
theorem coepisse_defective_not_suppletive :
    coepisseLinkage.IsDefective ∧ ¬ coepisseLinkage.IsSuppletive :=
  ⟨coepisse_defective, not_not.mpr coepisse_stemInvariant⟩

end Coepisse

/-! ### Latin BELLUM: syncretism ((22)–(26))

Two content cells share a form correspondent. The neuter nominative patterns
after the accusative (directional), and the dative and ablative share one form
cell (nondirectional). The merged dative/ablative form cell is a coarsening of
the form-property space; it is modeled here by the dative as its representative,
with both content cells mapped there. -/

section Bellum

inductive BellumLex | bellum
  deriving DecidableEq, Fintype, Repr
inductive BellumStem | bell
  deriving DecidableEq, Fintype, Repr
inductive Case | nom | gen | dat | acc | abl
  deriving DecidableEq, Fintype, Repr
inductive Num | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- A BELLUM content cell: a case and a number. -/
structure BellumCell where
  case : Case
  num : Num
  deriving DecidableEq, Fintype, Repr

/-- The property mapping: nominative to accusative (directional neuter
syncretism, (24)) and ablative to dative as the merged `{dat/abl}` representative
(nondirectional, (25)). -/
def bellumPm (σ : BellumCell) : BellumCell :=
  match σ.case with
  | .nom => { σ with case := .acc }
  | .abl => { σ with case := .dat }
  | _ => σ

/-- BELLUM's linkage: one stem, the syncretizing property mapping. -/
def bellumLinkage : Linkage BellumLex BellumStem BellumCell where
  stem := fun _ _ => some .bell
  pm := fun _ σ => bellumPm σ

/-- The realizations `bellum, bellī, bellō, bella, bellōrum, bellīs` on the form
cells ([stump-2012-mmm8] (22)). -/
def bellRealize : BellumStem → BellumCell → String
  | _, σ => match σ.case, σ.num with
      | .acc, .sg => "bellum" | .gen, .sg => "belli" | .dat, .sg => "bello"
      | .acc, .pl => "bella" | .gen, .pl => "bellorum" | .dat, .pl => "bellis"
      | _, _ => "bell"

/-- Directional syncretism: nominative and accusative singular share a form
correspondent ([stump-2012-mmm8] (24)). -/
theorem bellum_nom_acc_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.nom, .sg⟩, ⟨.acc, .sg⟩, by decide, by decide, by decide⟩

/-- Nondirectional syncretism: dative and ablative singular share a form
correspondent ([stump-2012-mmm8] (25)). -/
theorem bellum_dat_abl_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.dat, .sg⟩, ⟨.abl, .sg⟩, by decide, by decide, by decide⟩

/-- The shared form correspondent forces a shared realization: nominative and
accusative singular both realize as `bellum` ([stump-2012-mmm8] (26)). -/
theorem bellum_nom_acc_realize_eq :
    bellumLinkage.realize bellRealize .bellum ⟨.nom, .sg⟩
      = bellumLinkage.realize bellRealize .bellum ⟨.acc, .sg⟩ :=
  bellumLinkage.realize_eq_of_corr_eq bellRealize (by decide)

theorem bellum_nom_realizes_bellum :
    bellumLinkage.realize bellRealize .bellum ⟨.nom, .sg⟩
      = some ("bellum", ⟨.acc, .sg⟩) := rfl

/-- Syncretism is the failure of injectivity. -/
theorem bellum_not_injective : ¬ bellumLinkage.IsInjective :=
  (bellumLinkage.isSyncretic_iff_not_isInjective).mp bellum_nom_acc_syncretic

end Bellum

/-! ### Latin HORTĀRĪ: deponency, defectiveness, and virtual cells ((27)–(31), §4)

The active content cells have passive form correspondents (deponency); the
passive content cells have none (defectiveness). No content cell corresponds to
an active form cell, so an active form cell is virtual — the seat of the
[stump-2012-mmm8] §4 point that later Latin *hortābat* releases by suppressing
the deponent override ([hippisley-2010]). -/

section Hortari

inductive HortariLex | hortari
  deriving DecidableEq, Fintype, Repr
inductive HortariStem | horta
  deriving DecidableEq, Fintype, Repr
inductive Voice | active | passive
  deriving DecidableEq, Fintype, Repr

/-- A HORTĀRĪ content cell: a voice and an agreement feature. -/
structure VCell where
  voice : Voice
  agr : Agr
  deriving DecidableEq, Fintype, Repr

/-- HORTĀRĪ's linkage: a stem on the active cells only, and the voice-flipping
property mapping ([stump-2012-mmm8] (29)–(30)). -/
def hortariLinkage : Linkage HortariLex HortariStem VCell where
  stem := fun _ σ => match σ.voice with | .active => some .horta | .passive => none
  pm := fun _ σ => { σ with voice := .passive }

/-- The passive-morphology realizations of the active content cells (`hortor,
…, hortantur`, (28)). -/
def hoRealize : HortariStem → VCell → String
  | _, σ => match σ.agr with
      | .s1 => "hortor" | .s2 => "hortaris" | .s3 => "hortatur"
      | .p1 => "hortamur" | .p2 => "hortamini" | .p3 => "hortantur"

/-- Deponency: the active content cells' property mapping is unfaithful, flipping
to passive ([stump-2012-mmm8] §3.3.1). -/
theorem hortari_unfaithful : hortariLinkage.IsUnfaithful :=
  ⟨.hortari, ⟨.active, .s1⟩, by decide⟩

/-- Every active content cell has a passive form correspondent. -/
theorem hortari_active_realized_by_passive (σ : VCell) :
    (hortariLinkage.corr .hortari ⟨.active, σ.agr⟩).map (·.2.voice) = some .passive :=
  rfl

/-- The active content cell `1sg` realizes as `hortor` through its passive
correspondent. -/
theorem hortari_realizes_hortor :
    hortariLinkage.realize hoRealize .hortari ⟨.active, .s1⟩
      = some ("hortor", ⟨.passive, .s1⟩) := rfl

/-- Deponency compounds with defectiveness: the passive content cells lack a
stem ([stump-2012-mmm8] (30a)). -/
theorem hortari_defective : hortariLinkage.IsDefective :=
  ⟨.hortari, ⟨.passive, .s1⟩, rfl⟩

/-- The active form cell `⟨horta, {1sg active}⟩` is virtual: no content cell
corresponds to it, since active content maps to passive form and passive content
has no correspondent ([stump-2012-mmm8] §4). -/
theorem hortari_active_form_virtual :
    hortariLinkage.IsVirtual (.horta, ⟨.active, .s1⟩) := by
  unfold Linkage.IsVirtual; decide

end Hortari

/-! ### Hungarian ÉN: functor-argument reversal ((33)–(38))

The form correspondent of a pronominal oblique-case cell pairs the case stem with
the pronoun's own person-number properties — `⟨f(σ), g(L)⟩` with the property set
computed from the lexeme ([stump-2012-mmm8] (37)). The inessive of ÉN '1sg' is
inflected as the 1sg form of the inessive stem `benn`. -/

section Hungarian

/-- The personal pronouns ÉN '1sg' and TE '2sg'. -/
inductive Pron | en | te
  deriving DecidableEq, Fintype, Repr

/-- The oblique cases marked by inflected postpositions. -/
inductive HuCase | dative | inessive | superessive
  deriving DecidableEq, Fintype, Repr

/-- The pronominal person-number properties the form cell carries. -/
inductive PersNum | p1sg | p2sg
  deriving DecidableEq, Fintype, Repr

/-- A Hungarian property set: either a content-side case or a form-side
person-number set. -/
inductive HuProp | case (c : HuCase) | agr (pn : PersNum)
  deriving DecidableEq, Fintype, Repr

/-- The case postposition stems `nek, benn, rajt`. -/
inductive CaseStem | nek | benn | rajt
  deriving DecidableEq, Fintype, Repr

/-- The stem selection: the case picks the postpositional stem ([stump-2012-mmm8]
(37)). -/
def enStem : Pron → HuProp → Option CaseStem
  | _, .case .dative => some .nek
  | _, .case .inessive => some .benn
  | _, .case .superessive => some .rajt
  | _, _ => none

/-- The property mapping computes the form property set from the *lexeme* — the
functor-argument reversal ([stump-2012-mmm8] (32), (37)). -/
def enPm : Pron → HuProp → HuProp
  | .en, _ => .agr .p1sg
  | .te, _ => .agr .p2sg

/-- ÉN's linkage: case-driven stem, lexeme-driven property mapping. -/
def enLinkage : Linkage Pron CaseStem HuProp where
  stem := enStem
  pm := enPm

/-- The realizations `nekem, bennem, rajtam` (1sg) and `neked, benned, rajtad`
(2sg) ([stump-2012-mmm8] (36)). -/
def enRealize : CaseStem → HuProp → String
  | .nek, .agr .p1sg => "nekem" | .nek, .agr .p2sg => "neked"
  | .benn, .agr .p1sg => "bennem" | .benn, .agr .p2sg => "benned"
  | .rajt, .agr .p1sg => "rajtam" | .rajt, .agr .p2sg => "rajtad"
  | _, _ => ""

/-- The inessive of ÉN corresponds to the 1sg form of `benn` ([stump-2012-mmm8]
(38)). -/
theorem en_inessive_corr :
    enLinkage.corr .en (.case .inessive) = some (.benn, .agr .p1sg) := rfl

/-- The correspondent's property set is the pronoun's, not the case's — the
reversal is unfaithful ([stump-2012-mmm8] (37)). -/
theorem en_functor_argument_reversal : enLinkage.IsUnfaithful :=
  ⟨.en, .case .inessive, by decide⟩

/-- The property mapping consults the lexeme: ÉN and TE send the same inessive
content cell to different form property sets. -/
theorem en_pm_lexeme_sensitive :
    enLinkage.pm .en (.case .inessive) ≠ enLinkage.pm .te (.case .inessive) := by
  decide

/-- The nekem/bennem row of (38): the dative and inessive of ÉN realize as
`nekem` and `bennem`. -/
theorem en_realizes_nekem_bennem :
    enLinkage.realize enRealize .en (.case .dative)
        = some ("nekem", .agr .p1sg) ∧
      enLinkage.realize enRealize .en (.case .inessive)
        = some ("bennem", .agr .p1sg) :=
  ⟨rfl, rfl⟩

end Hungarian

/-! ### Latin FERRE: suppletion under the default rule ((41)–(43))

Present-system cells take the stem `fer`, perfect-system cells the stem `tul`,
in complementary distribution under the default linkage rule — no override. The
linkage is suppletive yet property-preserving, showing the two axes are
independent. -/

section Ferre

inductive FerreLex | ferre
  deriving DecidableEq, Fintype, Repr
inductive FerreStem | fer | tul
  deriving DecidableEq, Fintype, Repr

/-- A FERRE content cell: a tense system and an agreement feature. -/
structure FerreCell where
  sys : System
  agr : Agr
  deriving DecidableEq, Fintype, Repr

/-- FERRE's linkage: two suppletive stems in complementary distribution, identity
property mapping ([stump-2012-mmm8] (42)). -/
def ferreLinkage : Linkage FerreLex FerreStem FerreCell where
  stem := fun _ σ => match σ.sys with | .pres => some .fer | .perf => some .tul
  pm := fun _ σ => σ

/-- The realizations `ferō, fers, fert, …` and `tulī, …, tulit, …`
([stump-2012-mmm8] (41)). -/
def ferRealize : FerreStem → FerreCell → String
  | .fer, σ => "fer" ++ (match σ.agr with
      | .s1 => "o" | .s2 => "s" | .s3 => "t"
      | .p1 => "imus" | .p2 => "tis" | .p3 => "unt")
  | .tul, σ => "tul" ++ (match σ.agr with
      | .s1 => "i" | .s2 => "isti" | .s3 => "it"
      | .p1 => "imus" | .p2 => "istis" | .p3 => "erunt")

/-- FERRE is suppletive: the present- and perfect-system cells draw on different
stems ([stump-2012-mmm8] §3.4). -/
theorem ferre_suppletive : ferreLinkage.IsSuppletive := fun h =>
  absurd (h .ferre (σ₁ := ⟨.pres, .s1⟩) (σ₂ := ⟨.perf, .s1⟩) rfl rfl) (by decide)

/-- FERRE is property-preserving: no override, the default rule preserves the
content cell's property set. -/
theorem ferre_propertyPreserving : ferreLinkage.IsPropertyPreserving :=
  fun _ _ => rfl

/-- The independence showcase: suppletive yet property-preserving
([stump-2012-mmm8] §3.4). -/
theorem ferre_suppletive_yet_faithful :
    ferreLinkage.IsSuppletive ∧ ferreLinkage.IsPropertyPreserving :=
  ⟨ferre_suppletive, ferre_propertyPreserving⟩

theorem ferre_present_realized :
    ferreLinkage.realize ferRealize .ferre ⟨.pres, .s3⟩
      = some ("fert", ⟨.pres, .s3⟩) := rfl
theorem ferre_perfect_realized :
    ferreLinkage.realize ferRealize .ferre ⟨.perf, .s3⟩
      = some ("tulit", ⟨.perf, .s3⟩) := rfl

end Ferre

/-! ### Old Icelandic ÞURFA: a compound deviation ((44)–(46))

A preterite-present verb forms its present as a strong verb forms its past
(deponent tense mapping) and its past with a separate weak stem (suppletion).
Suppletion and unfaithfulness coincide in a single linkage. -/

section Thurfa

inductive ThurfaLex | thurfa
  deriving DecidableEq, Fintype, Repr
inductive ThurfaStem | strong | weak
  deriving DecidableEq, Fintype, Repr
inductive Tense | pres | past
  deriving DecidableEq, Fintype, Repr

/-- A ÞURFA content cell: a tense and an agreement feature. -/
structure TCell where
  tense : Tense
  agr : Agr
  deriving DecidableEq, Fintype, Repr

/-- ÞURFA's linkage: the strong stem for the present, the weak stem for the past
(suppletion), and a property mapping sending every cell to the past
(deponent tense) ([stump-2012-mmm8] (45)–(46)). -/
def thurfaLinkage : Linkage ThurfaLex ThurfaStem TCell where
  stem := fun _ σ => match σ.tense with | .pres => some .strong | .past => some .weak
  pm := fun _ σ => { σ with tense := .past }

/-- ÞURFA is suppletive: present and past draw on different stems. -/
theorem thurfa_suppletive : thurfaLinkage.IsSuppletive := fun h =>
  absurd (h .thurfa (σ₁ := ⟨.pres, .s1⟩) (σ₂ := ⟨.past, .s1⟩) rfl rfl) (by decide)

/-- ÞURFA is unfaithful: the present content cell maps to a past form cell. -/
theorem thurfa_unfaithful : thurfaLinkage.IsUnfaithful :=
  ⟨.thurfa, ⟨.pres, .s1⟩, by decide⟩

/-- The compound deviation: suppletion and deponent tense mapping in one linkage
([stump-2012-mmm8] §3.4). -/
theorem thurfa_suppletive_and_unfaithful :
    thurfaLinkage.IsSuppletive ∧ thurfaLinkage.IsUnfaithful :=
  ⟨thurfa_suppletive, thurfa_unfaithful⟩

/-- The present content cell's form correspondent is the strong stem at the past
property set ([stump-2012-mmm8] (46)). -/
theorem thurfa_pres_corr :
    thurfaLinkage.corr .thurfa ⟨.pres, .s1⟩ = some (.strong, ⟨.past, .s1⟩) := rfl

/-- The past content cell's form correspondent is the weak stem at the past
property set ([stump-2012-mmm8] (46)). -/
theorem thurfa_past_corr :
    thurfaLinkage.corr .thurfa ⟨.past, .s1⟩ = some (.weak, ⟨.past, .s1⟩) := rfl

end Thurfa

end Stump2012
