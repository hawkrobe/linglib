module

public import Linglib.Syntax.Minimalist.MinimalPronoun
public import Linglib.Fragments.Mixtec.SMPM.Pronouns
public import Linglib.Fragments.Mixtec.SMPM.Verbs
public import Linglib.Syntax.Control.Head
public import Linglib.Syntax.Control.Basic
public import Linglib.Syntax.Control.Diagnostics
public import Linglib.Studies.Landau2013
public import Linglib.Studies.Allotey2021

/-!
# Ostrove (2026): Obligatorily Overt PRO in San Martín Peras Mixtec

Ostrove argues that San Martín Peras Mixtec (SMPM) has obligatory control whose controlled
subject must be an overt clitic pronoun. Of its three embedded clause types, finite clauses,
tensed subjunctives and untensed subjunctives, only the untensed subjunctive shows Landau's
signature of obligatory control (`isObligatory_iff`). Exempt anaphors reject quantified
antecedents yet occur in untensed subjunctives under quantified controllers, so the controlled
subject is a pronoun rather than a copy left by movement (`smpm_refutes_movement`). The analysis
is morphological: bound variables are minimal pronouns realized by vocabulary items, and SMPM
lacks the null item that yields silent PRO elsewhere, so the elsewhere pronoun surfaces
(`smpm_overt_pro`, `syncretism_typology`). A tentative universal closes the argument: overt PRO
entails no pro-drop (`Universal54`).

## Implementation notes

The clause type of a complement is read off the fragment's verbs (`EmbeddedClauseType.ofFrame`):
indicative complements are finite, and irrealis ones are untensed exactly when the verb's reading
is controlled. The properties of (26) are the paper's summary (`shows`); deriving them from
example rows, as `Studies/Allotey2021` does for Gã, awaits a transcription of the examples.
Landau's calculus fits the three types only if the tensed subjunctive is `[+Agr]`
(`landau_predicts_control_iff`), which the paper does not discuss. The pro-drop status is the
paper's own 101A cell, as WALS does not sample the language. Example numbers follow the
manuscript version of the article.

## References

* [ostrove-2026]
* [landau-2004]
* [landau-2015]
* [kratzer-2009]
* [safir-2014]
* [cardinaletti-starke-1999]
* [polinsky-potsdam-2006]
* [allotey-2021]
* [wals-2013]
* [sulemana-2021]
* [black-1994]
* [dechaine-manfredi-1994]
-/

@[expose] public section

namespace Ostrove2026

open Minimalist.MinimalPronoun
open scoped DistributedMorphology
open Control
open Mixtec.SMPM

/-! ### The clause typology (26) -/

/-- The three embedded clause types of (26). -/
inductive EmbeddedClauseType where
  | finite
  | tensedSubjunctive
  | untensedSubjunctive
  deriving DecidableEq, Repr, Fintype

/-- A verb's complement frame is finite in the indicative coding and otherwise a subjunctive,
untensed exactly when the verb's reading of the frame is controlled (§3). -/
def EmbeddedClauseType.ofFrame (v : Verb) (fr : ArgumentFrame) : EmbeddedClauseType :=
  if Complement.Coding.indicative ∈ fr.codings then .finite
  else if ((v.reading? fr).bind (·.control)).isSome then .untensedSubjunctive
  else .tensedSubjunctive

/-- The fragment's controlled complements are exactly its untensed subjunctives: no finite
complement is controlled, not even that of *kònì* 'know', which also takes an untensed one. -/
theorem control_iff_untensed : ∀ v ∈ verbs, ∀ fr ∈ v.frames,
    ((v.reading? fr).bind (·.control)).isSome ↔
      EmbeddedClauseType.ofFrame v fr = .untensedSubjunctive := by
  decide

/-- The properties of (26), with the independent tense of (10), (16) and (17), which time
adverbs diagnose. -/
inductive Property where
  | unrestrictedTAM
  | independentTense
  | noncoreferentSubject
  | restructuring
  deriving DecidableEq, Repr, Fintype

/-- The properties each clause type shows, the checkmarks of (26) and the tense column.
*Kòni* 'want' is an exception to the restructuring column, letting a quantifier front out of
its tensed subjunctive (fn. 8). -/
def shows : EmbeddedClauseType → Finset Property
  | .finite => {.unrestrictedTAM, .independentTense, .noncoreferentSubject}
  | .tensedSubjunctive => {.independentTense, .noncoreferentSubject}
  | .untensedSubjunctive => {.restructuring}

/-- The properties of (26) distinguish the three clause types. -/
theorem shows_injective : Function.Injective shows := by decide

/-- The control signature of each clause type, from whether it admits a non-coreferent subject,
by the derivation of `Landau2013.ofNoncoreferential`. -/
def smpmProfile (c : EmbeddedClauseType) : Set Landau2013.Clause74 :=
  Landau2013.ofNoncoreferential (decide (.noncoreferentSubject ∈ shows c))

/-- Only untensed subjunctives are obligatory-control clauses: sloppy readings only under
ellipsis (33), exhaustive binding (37), and a local c-commanding antecedent (40), (44); the
other two types allow strict readings, non-exhaustive binding, and non-local antecedents. -/
theorem isObligatory_iff (c : EmbeddedClauseType) :
    smpmProfile c = Set.univ ↔ c = .untensedSubjunctive := by
  cases c <;> simp [smpmProfile, shows]

/-! ### Landau's scale -/

/-- The clause types on the finiteness scale of [landau-2004]: untensed subjunctives are
C-subjunctives and tensed ones F-subjunctives (§3). -/
def landauToSMPM : ClauseClass → EmbeddedClauseType
  | .cSubjunctive => .untensedSubjunctive
  | .fSubjunctive => .tensedSubjunctive
  | .finite => .finite

/-- The scale position of a clause type, from its TAM and tense properties. -/
def smpmToLandau (c : EmbeddedClauseType) : ClauseClass :=
  .ofFiniteness (decide (.unrestrictedTAM ∈ shows c)) (decide (.independentTense ∈ shows c))

/-- SMPM realizes every position of the scale, unlike Gã (`Allotey2021.ga_no_fSubjunctive`). -/
theorem smpmToLandau_landauToSMPM (c : ClauseClass) : smpmToLandau (landauToSMPM c) = c := by
  cases c <;> decide

/-- Landau's calculus predicts the control profile of every clause type exactly when the clauses
are `[+Agr]`: at `[−Agr]` it makes the tensed subjunctive, an F-subjunctive, obligatory control,
yet its subject may be disjoint from the matrix subject (18b). -/
theorem landau_predicts_control_iff (agr : Bool) :
    (∀ c, smpmProfile c = Set.univ ↔ (smpmToLandau c).HasOC agr) ↔ agr = true := by
  simp only [isObligatory_iff]
  cases agr <;> decide

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
def ex86Occupant : Fin 2 → Ex86Item := fun p ↦ if p = 0 then .quantifierDP else .pronoun

/-- Exempt anaphors reject quantified antecedents (78) yet are available in untensed
subjunctives under quantified controllers (86), (87), so the embedded position holds a
referential pronoun and not a copy of the quantifier: the dependency is not movement. -/
theorem smpm_refutes_movement : ¬ IsExhaustive ex86Occupant ex86Dependency :=
  not_isExhaustive_of_mismatch (P := (· = .quantifierDP)) rfl rfl (by decide)

/-! ### Minimal pronoun inventories (§7) -/

/-- English (94): a null item for controlled subjects, a reflexive for local binding, and the
pronoun elsewhere. -/
def englishInventory : Vocabulary Form where
  items := [[.controlledSubject] ⟷ .null, [.locallyBound] ⟷ .reflexive]
  elsewhere := .pronoun

/-- Haitian Creole (96): a null item for controlled subjects and no reflexive item, reflexives
surfacing as pronouns ([dechaine-manfredi-1994]). -/
def haitianInventory : Vocabulary Form where
  items := [[.controlledSubject] ⟷ .null]
  elsewhere := .pronoun

/-- SMPM (98): a reflexive item, *mí* with a clitic, and no null item. -/
def smpmInventory : Vocabulary Form where
  items := [[.locallyBound] ⟷ .reflexive]
  elsewhere := .pronoun

/-- Quiegolani Zapotec ([black-1994]): no context-specific item at all. -/
def quiegolaniInventory : Vocabulary Form where
  items := []
  elsewhere := .pronoun

/-- Overt PRO: no SMPM item is conditioned on the controlled subject, so it takes the
elsewhere pronoun (98), where English's null item yields silent PRO (94a). -/
theorem smpm_overt_pro :
    smpmInventory.controlForm = smpmInventory.elsewhere ∧ englishInventory.controlForm = .null :=
  ⟨Vocabulary.realize_eq_elsewhere (by decide), rfl⟩

/-- The analysis in general form: with the pronoun as its elsewhere form, a language has silent
PRO only through a null item for controlled subjects, which SMPM lacks. -/
theorem smpm_no_null_item : ∀ i ∈ smpmInventory.items, i.exponent ≠ .null := by decide

/-- The syncretism table (92), each row derived from its inventory: the contexts in which the
bound form is the referential pronoun's, whose own column is the elsewhere form itself. The four
languages occupy four distinct cells. -/
theorem syncretism_typology :
    englishInventory.syncretic = {.boundVariable} ∧
      quiegolaniInventory.syncretic = Finset.univ ∧
      haitianInventory.syncretic = {.locallyBound, .boundVariable} ∧
      smpmInventory.syncretic = {.controlledSubject, .boundVariable} := by
  decide

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

/-- SMPM's type: the controlled subject is a pronoun rather than a full copy (57), it is overt
outside attitude reports, and it cannot bear focus, so the scope-sensitive alternation with
null PRO is unavailable. -/
def smpmCopyControlType : CopyControlType := .obligatoryPronominal

/-- A controlled subject is of the clitic class of [cardinaletti-starke-1999], since non-clitic
forms, strengthened *mí =rà* among them, are ungrammatical there (67); the subject of a tensed
subjunctive may be non-clitic (68). -/
def controlledSubjectStrength : Pronoun.Strength := .clitic

/-- The pronouns that can be a controlled subject are exactly the clitics, none of which bears
focus (65), (66): the overt subject is not the focused pronoun of scope-sensitive copy
control. -/
theorem controlledSubject_iff_mem_clitics :
    ∀ p ∈ pronouns, p.strength = some controlledSubjectStrength ↔ p ∈ clitics := by
  decide

/-! ### The implicational universal (54) -/

/-- SMPM's cell of [wals-2013]'s 101A, which does not sample the language, is obligatory
subject pronouns, expletive and impersonal ones included (3). -/
def pronominalSubjects : Data.WALS.F101A.ExpressionOfPronominalSubjects :=
  .obligatoryPronounsInSubjectPosition

/-- A language with minimal-pronoun inventory `inv` and 101A cell `s` satisfies the
implicational universal (54) when overt PRO implies obligatory subject pronouns, that is, no
pro-drop. -/
def Universal54 (inv : Vocabulary Form)
    (s : Data.WALS.F101A.ExpressionOfPronominalSubjects) : Prop :=
  inv.controlForm ≠ .null → s = .obligatoryPronounsInSubjectPosition

/-- SMPM instantiates the universal: overt PRO and no pro-drop. -/
theorem smpm_universal54 : Universal54 smpmInventory pronominalSubjects := fun _ ↦ rfl

/-- English satisfies it vacuously, whatever its 101A cell, since its PRO is null. -/
theorem english_universal54 (s : Data.WALS.F101A.ExpressionOfPronominalSubjects) :
    Universal54 englishInventory s :=
  fun h ↦ absurd rfl h

/-- Gã sits in SMPM's cell: the same controlled-subject realization, derived from the Gã
inventory of [allotey-2021], and the same 101A cell. -/
theorem ga_patterns_with_smpm :
    Allotey2021.gaInventory.controlForm = smpmInventory.controlForm ∧
      Allotey2021.pronominalSubjects = pronominalSubjects :=
  ⟨rfl, rfl⟩

/-- Gã instantiates the universal ([allotey-2021]). -/
theorem ga_universal54 : Universal54 Allotey2021.gaInventory Allotey2021.pronominalSubjects :=
  fun _ ↦ rfl

/-- The universal has bite for Gã: under [wals-2013]'s coding of its subject markers as affixes
(`Allotey2021.wals_codes_affixes`) Gã violates it, so its instance rests on [allotey-2021]'s
analysis of the markers as pronouns. -/
theorem ga_violates_universal54_of_wals :
    ∀ s ∈ (Data.WALS.F101A.lookupISO "gaa").map (·.value),
      ¬ Universal54 Allotey2021.gaInventory s := by
  intro s hs h
  rw [Allotey2021.wals_codes_affixes, Option.mem_some_iff] at hs
  subst hs
  exact absurd (h (by rw [Allotey2021.ga_overt_pro]; decide)) (by decide)

end Ostrove2026
