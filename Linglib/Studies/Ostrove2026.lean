import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Fragments.Mixtec.SMPM.Basic
import Linglib.Syntax.Control.Head
import Linglib.Syntax.Control.Basic
import Linglib.Syntax.Control.Diagnostics
import Linglib.Studies.Landau2013
import Linglib.Studies.Allotey2021

/-!
# Ostrove (2026): Obligatorily Overt PRO in San Martín Peras Mixtec

This file formalizes the analysis in [ostrove-2026] of obligatory control in San Martín Peras
Mixtec, where the controlled subject must be an overt clitic pronoun. Embedded clauses come in
three types, finite, tensed subjunctive, and untensed subjunctive, distinguished by their
tense-aspect-mood morphology, by whether they admit a non-coreferential subject, and by
restructuring (`clause_types_distinguished`); the untensed subjunctives, the C-subjunctives
of [landau-2004], show the full obligatory-control signature and the other two types none of
it (`smpmProfile`, `isObligatory_iff`, `landauToSMPM`). The controlled subject is a genuine
pronoun rather than a copy: exempt anaphors reject quantified antecedents yet occur in
untensed subjunctives under quantified controllers, which refutes movement into the
controlled position (`smpm_refutes_movement`). The analysis is morphological: bound variables
are minimal pronouns ([kratzer-2009], [safir-2014], [landau-2015]) exponed by contextual
allomorphy, and the language lacks the null vocabulary item that yields PRO elsewhere, so the
elsewhere pronoun surfaces (`smpmInventory`, `smpm_overt_pro`); English, Quiegolani Zapotec,
Haitian, and SMPM then occupy four distinct cells of the syncretism typology (92)
(`syncretism_typology`). SMPM instantiates obligatory pronominal copy control, the type in
which overtness is unconditional, alongside Gã ([allotey-2021]) and Bùlì ([sulemana-2021])
(`CopyControlType`, `smpm_controlled_must_be_clitic`, `ga_patterns_with_smpm`), and the
tentative universal (54) that overt PRO entails the absence of pro-drop
(`smpm_satisfies_universal`).

## Implementation notes

Clause properties, the pronoun series, and the exempt-anaphor facts are read off the Mixtec
Fragment, and the control profile derives from the non-coreferential-subject property by the
same map as the Gã study. The logophoric and scope-sensitive types of pronominal copy
control, and the base-generation analysis of the control dependency itself, are described in
prose only.

## References

* [ostrove-2026]
* [landau-2004]
* [landau-2015]
* [kratzer-2009]
* [safir-2014]
* [polinsky-potsdam-2006]
* [allotey-2021]
* [sulemana-2021]
* [black-1994]
* [dechaine-manfredi-1994]
-/

namespace Ostrove2026

open Minimalist.MinimalPronoun
open scoped DistributedMorphology
open Control
open Mixtec.SMPM

/-! ### The clause typology (26) -/

/-- The three embedded clause types are pairwise distinguished by the properties of (26). -/
theorem clause_types_distinguished (c c' : EmbeddedClauseType) (h : c ≠ c') :
    clauseProperties c ≠ clauseProperties c' := by
  revert h; cases c <;> cases c' <;> decide

/-- The control signature of each clause type, from whether it admits a non-coreferential
subject, by the derivation of `Landau2013.ofNoncoreferential`. -/
def smpmProfile (c : EmbeddedClauseType) : Profile Landau2013.Clause74 :=
  Landau2013.ofNoncoreferential (clauseProperties c).noncoreferentialSubject

/-- Only untensed subjunctives are obligatory-control clauses: sloppy readings only under
ellipsis (33), exhaustive binding (37), and a local c-commanding antecedent (40), (44); the
other two types allow strict readings, non-exhaustive binding, and non-local antecedents. -/
theorem isObligatory_iff (c : EmbeddedClauseType) :
    (smpmProfile c).IsObligatory ↔ c = .untensedSubjunctive := by
  cases c <;> simp [smpmProfile, clauseProperties]

/-- The clause types on the finiteness scale of [landau-2004]: untensed subjunctives are
C-subjunctives and tensed ones F-subjunctives (§3). -/
def landauToSMPM : ClauseClass → EmbeddedClauseType
  | .cSubjunctive => .untensedSubjunctive
  | .fSubjunctive => .tensedSubjunctive
  | .finite => .finiteEmbedded

/-- The scale position of a clause type, from the Fragment's tense observables. -/
def smpmToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (clauseProperties c).unrestrictedTAM (clauseProperties c).independentTense

/-- SMPM realizes every position of the scale, unlike Gã (`Allotey2021.ga_no_fSubjunctive`). -/
theorem smpmToLandau_landauToSMPM (c : ClauseClass) : smpmToLandau (landauToSMPM c) = c := by
  cases c <;> rfl

/-! ### Against movement (§6) -/

/-- The occupants of the configurations (86) and (87): a quantified controller and the overt
controlled clitic that antecedes an exempt anaphor. -/
inductive Ex86Item where
  | quantifierDP
  | pronoun
  deriving DecidableEq

/-- The control dependency of (86) and (87), from the controller position to the embedded
clitic position. -/
def ex86Dependency : SetRel (Fin 2) (Fin 2) := {(0, 1)}

/-- The attested occupants of the two positions. -/
def ex86Occupant : Fin 2 → Ex86Item := λ p => if p = 0 then .quantifierDP else .pronoun

/-- Exempt anaphors reject quantified antecedents (78) yet are available in untensed
subjunctives under quantified controllers (86), (87), so the embedded position holds a
referential pronoun and not a copy of the quantifier: the dependency is not movement. -/
theorem smpm_refutes_movement : ¬ IsExhaustive ex86Occupant ex86Dependency :=
  not_isExhaustive_of_mismatch (P := (· = .quantifierDP)) rfl rfl (by decide)

/-! ### Minimal pronoun inventories (§7) -/

/-- English (94): a null item for controlled subjects, a reflexive for local binding, and the
pronoun elsewhere. -/
def englishInventory : MinPronInventory PronForm where
  items := [[.controlledSubject] ⟷ .null, [.locallyBound] ⟷ .reflexive]
  elsewhere := .pronoun

/-- Haitian Creole (96): a null item for controlled subjects and no reflexive item, reflexives
surfacing as pronouns ([dechaine-manfredi-1994]). -/
def haitianInventory : MinPronInventory PronForm where
  items := [[.controlledSubject] ⟷ .null]
  elsewhere := .pronoun

/-- SMPM (98): a reflexive item, *mí* with a clitic, and no null item. -/
def smpmInventory : MinPronInventory PronForm where
  items := [[.locallyBound] ⟷ .reflexive]
  elsewhere := .pronoun

/-- Quiegolani Zapotec ([black-1994]): no context-specific item at all. -/
def quiegolaniInventory : MinPronInventory PronForm where
  items := []
  elsewhere := .pronoun

/-- Overt PRO: the controlled subject of SMPM is the elsewhere pronoun, no item being more
specific for that context, where English's null item yields silent PRO. -/
theorem smpm_overt_pro :
    smpmInventory.controlForm = .pronoun ∧ englishInventory.controlForm = .null :=
  ⟨rfl, rfl⟩

/-- The syncretism table (92), each row derived from its inventory: whether the reflexive, the
controlled subject, and the bound variable share the referential pronoun's form. The four
languages occupy four distinct cells. -/
theorem syncretism_typology :
    syncretismFromInventory englishInventory = ⟨"", false, false, true⟩ ∧
      syncretismFromInventory quiegolaniInventory = ⟨"", true, true, true⟩ ∧
      syncretismFromInventory haitianInventory = ⟨"", true, false, true⟩ ∧
      syncretismFromInventory smpmInventory = ⟨"", false, true, true⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Copy control (§5) -/

/-- The four types of copy control, an overt element in the controlled position
([polinsky-potsdam-2006]): a full copy of the controller, or a pronoun that is overt in
attitude reports only, under scope-taking operators only, or unconditionally. -/
inductive CopyControlType where
  /-- San Lucas Quiaviní Zapotec, Copala Triqui. -/
  | fullCopy
  /-- Gengbe, Mandarin. -/
  | logophoricPronominal
  /-- Italian, Hungarian, European Portuguese, alternating with null PRO (60). -/
  | scopeSensitivePronominal
  /-- SMPM, Gã ([allotey-2021]), Bùlì ([sulemana-2021]). -/
  | obligatoryPronominal
  deriving DecidableEq

/-- The type in which overtness is unconditional. -/
def CopyControlType.UnconditionallyOvert : CopyControlType → Prop := (· = .obligatoryPronominal)

/-- SMPM's type: the controlled subject is a pronoun rather than a full copy (57), it is overt
outside attitude reports, and it cannot bear focus, so the scope-sensitive alternation with
null PRO is unavailable. -/
def smpmCopyControlType : CopyControlType := .obligatoryPronominal

/-- The clitic requirement (65), (67), from the Fragment through the deficiency order: the
controlled-subject class is strictly more deficient than every entry of the strong series. -/
theorem smpm_controlled_must_be_clitic :
    ∀ p ∈ strongSeries, ∀ s ∈ p.strength, controlledSubjectStrength < s :=
  controlledSubject_is_most_deficient

/-- Gã sits in SMPM's cell: the same controlled-subject realization, derived from the Gã
inventory of [allotey-2021], and the same pro-drop status. -/
theorem ga_patterns_with_smpm :
    Allotey2021.gaInventory.controlForm = smpmInventory.controlForm ∧
      Ga.allowsProDrop = allowsProDrop :=
  ⟨rfl, rfl⟩

/-! ### The implicational universal (54) -/

/-- SMPM instantiates the universal: overt PRO and no pro-drop. -/
theorem smpm_satisfies_universal : smpmInventory.OvertPROUniversal allowsProDrop :=
  λ _ => rfl

/-- English satisfies it vacuously, whatever its pro-drop status, since its PRO is null. -/
theorem english_satisfies_universal (proDrop : Bool) :
    englishInventory.OvertPROUniversal proDrop :=
  MinPronInventory.overtPROUniversal_of_controlForm_eq_null rfl proDrop

end Ostrove2026
