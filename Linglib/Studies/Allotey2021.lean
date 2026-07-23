import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.NullSubject
import Linglib.Studies.Landau2015

/-!
# Allotey (2021): Overt Pronouns of Infinitival Predicates of Gã
[allotey-2021]

Western Papers in Linguistics / Cahiers linguistiques de Western 4.

Gã (Kwa, Niger-Congo; spoken in Greater Accra, Ghana) shows obligatory
control over the embedded subject of irrealis `ni`-clauses, where the
controlled subject is realized as an OVERT subject proclitic — null PRO
is ungrammatical. Under the [kratzer-2009] / [safir-2014] /
[landau-2015] minimal pronoun framework, Gã simply lacks a null
vocabulary item for the controlled subject position.

[allotey-2021] weighs two analyses of overt infinitival subjects — the
Long Distance Agree (LDA) Hypothesis of [szabolcsi-2009] and the
Movement Theory of Control (the derivation she illustrates from
[satik-2019]) — and adopts LDA: her analysis puts the matrix subject in
a Long-Distance relation with the embedded pronoun subject. The minimal
pronoun framework and LDA are compatible — LDA is the syntactic
mechanism that values the unvalued φ-features of the minimal pronoun in
the embedded subject position. We wire both perspectives in below.

## Core Contributions

1. **Three-way clause typology** distinguished by complementizer:
   `akɛ`-clauses (finite declarative), `kɛji`-clauses (finite
   conditional), `ni`-clauses (irrealis, OC).
2. **OC over an overt subject**: irrealis `ni`-clauses show the OC
   signature despite carrying an overt subject proclitic.
3. **Subject and object control** are both attested with `ni`-clause
   complements (subject-control: `tao` 'want' ex 2a, `hiɛ-ka-nɔ` 'hope'
   ex 16).
4. **Irrealis ≠ subjunctive**: Allotey argues that the high-tone marker
   on the embedded-clause subject pronoun is irrealis, not subjunctive
   (against the subjunctive classification in the Gã descriptive
   literature, [dakubu-2004], [campbell-2017]): it does not show the
   obviation that defines subjunctives (formalized below).
5. **Long Distance Agree analysis**: the embedded overt pronoun is a
   minimal pronoun whose φ-features are valued by LDA from the matrix
   controller ([szabolcsi-2009]).

## Out of scope

The paper also discusses Gã verbal negation and an analogy to French
V-movement past `pas` ([pollock-1989]). That analogy depends on
treating Gã `-ee` and `-ko` as a free Neg head (Pollock's diagnostic
crucially relies on negation occupying a fixed structural position
rather than being a verbal suffix). The morphological argument that
would license that step is outside Allotey's data, so we do not
formalize the V-to-T claim here.
-/

namespace Allotey2021

open Minimalist.MinimalPronoun
open Landau2015
open NullSubject (ProDropProfile)
open Ga (EmbeddedClauseType clauseProperties clauseComplementizer
                   complementizer_isFinite_eq_finiteFlag
                   Complementizer CTP)

/-! ### OC diagnostics — derived from clause properties -/

/-- OC signature derived from clause properties.

    A clause type that does not allow noncoreferential embedded
    subjects forces the full [landau-2013] OC signature; one
    that does allow them shows none. Per [allotey-2021], only
    `irrealisNi` falls in the former group.

    This is *derived* from `clauseProperties.noncoreferentialSubject`
    rather than stipulated per clause — changing the noncoreferential
    flag in `Fragments/Ga/Basic.lean` automatically propagates here. -/
def gaOCSignature (c : EmbeddedClauseType) : OCSignature :=
  if (clauseProperties c).noncoreferentialSubject then ocNone else ocFull

/-- The general derivation: lack of noncoreferential subjects iff OC. -/
theorem oc_iff_no_noncoreferential (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = !(clauseProperties c).noncoreferentialSubject := by
  cases c <;> rfl

/-- Universal: every Gã CTP whose complement is `irrealisNi` shows OC,
    and every CTP whose complement is finite does not. The clause type
    determines OC, regardless of the verb's own control type. -/
theorem oc_determined_by_clause_type (c : CTP) :
    (gaOCSignature c.selects).isOC = !(clauseComplementizer c.selects).isFinite := by
  cases h : c.selects <;> rfl

/-! ### Irrealis vs. subjunctive -/

/-- [allotey-2021] argues the high-tone marker on the embedded-clause
    pronoun is **irrealis**, not subjunctive (against the subjunctive
    classification of the Gã descriptive literature, [dakubu-2004],
    [campbell-2017]). Her diagnostic is obviation: Romance subjunctives
    force the embedded subject to be DISJOINT from the matrix subject,
    while Gã `ni`-clauses force coreference — the opposite. The fragment
    encodes only the coreference dimension, so we record the Gã half:
    `irrealisNi` requires a coreferential subject, which no obviative
    subjunctive allows. -/
theorem irrealisNi_forces_coreference :
    (clauseProperties .irrealisNi).noncoreferentialSubject = false := rfl

/-! ### Landau bridge -/

/-- Map Gã clause types to [landau-2004]'s finiteness scale.

    | Landau class    | Gã clause type   | OC? |
    |-----------------|------------------|-----|
    | C-subjunctive   | irrealisNi       | Yes |
    | finite          | finiteAke        | No  |
    | finite          | finiteKeji       | No  |

    Gã has no F-subjunctive correspondent: there is no morphologically
    distinct tensed-but-controlled clause class — `ni`-clauses are all
    irrealis and OC; `akɛ`/`kɛji`-clauses are all finite and non-OC. -/
def gaToLandau : EmbeddedClauseType → LandauClauseClass
  | .irrealisNi => .cSubjunctive
  | .finiteAke  => .finite
  | .finiteKeji => .finite

/-- Gã Agr status, derived from `clauseProperties.finiteComplementizer`.

    `irrealisNi` is `[−Agr]` in [landau-2015]'s sense — though it
    carries an overt subject proclitic, the proclitic is the realization
    of a minimal pronoun rather than independent agreement. The finite
    clause types are `[+Agr]`. -/
def gaAgr (c : EmbeddedClauseType) : Bool :=
  (clauseProperties c).finiteComplementizer

/-- Cross-check: `gaAgr` agrees with the complementizer's finiteness flag. -/
theorem gaAgr_eq_complementizer_isFinite (c : EmbeddedClauseType) :
    gaAgr c = (clauseComplementizer c).isFinite :=
  (complementizer_isFinite_eq_finiteFlag c).symm

/-- The Landau classification predicts Gã control properties for all
    three clause types, taking Agr status into account. -/
theorem landau_predicts_control (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = (gaToLandau c).hasOCWithAgr (gaAgr c) := by
  cases c <;> rfl

/-! ### Long-Distance Agree analysis (Allotey's syntactic mechanism) -/

/-- Long Distance Agree configuration ([szabolcsi-2009]): a matrix probe
    values an embedded goal's unvalued φ across a non-defective C. Folded
    in from the former single-consumer `Minimalist/LongDistanceAgree.lean`.
    The contentful dimension is `cIsDefectiveBlocker` — the cross-clausal
    locality that the `Probe`/defective-intervention vocabulary
    (`Studies/Halpert2019.lean`) derives rather than stipulates. -/
structure LDAConfig where
  /-- The probe (matrix v/T/Asp) carries valued φ-features. -/
  probeHasValuedPhi : Bool
  /-- The goal (embedded D head) carries unvalued φ-features. -/
  goalHasUnvaluedPhi : Bool
  /-- The intervening C head blocks LDA (is defective for it);
      `false` means transparent and LDA proceeds. -/
  cIsDefectiveBlocker : Bool
  deriving DecidableEq, Repr

/-- LDA is licensed iff probe and goal have the right feature profile and
    the intervening C is non-blocking. -/
def LDAConfig.licenses (cfg : LDAConfig) : Bool :=
  cfg.probeHasValuedPhi && cfg.goalHasUnvaluedPhi && !cfg.cIsDefectiveBlocker

/-- [allotey-2021]'s syntactic analysis: the embedded overt
    pronoun in a controlled `ni`-clause is a minimal pronoun whose
    unvalued φ-features are valued by Long Distance Agree from the
    matrix controller ([szabolcsi-2009]).

    The probe (matrix v/T) has valued φ; the goal (embedded D[uφ])
    has unvalued φ; the intervening `ni` C head is non-defective for
    LDA, so the dependency crosses a clause boundary. -/
def gaLDAConfig : LDAConfig where
  probeHasValuedPhi   := true
  goalHasUnvaluedPhi  := true
  cIsDefectiveBlocker := false

theorem ga_satisfies_LDA :
    LDAConfig.licenses gaLDAConfig = true := rfl

/-! ### Minimal pronoun inventory -/

open PronForm

/-- Gã vocabulary items: no null allomorph for controlled subjects.
    The controlled subject of an `irrealisNi` clause surfaces as the
    elsewhere (pronoun) form — i.e., the same subject proclitic used
    for referential pronouns. -/
def gaInventory : MinPronInventory PronForm where
  items := [ ⟨.locallyBound, .reflexive⟩ ]
  elsewhere := .pronoun

/-- Gã: controlled subjects are realized as overt subject proclitics
    (the elsewhere/pronoun form). The paper's central empirical
    observation. -/
theorem ga_overt_pro :
    gaInventory.controlForm = .pronoun := rfl

/-- Gã has reflexives distinct from referential pronouns. -/
theorem ga_has_reflexive :
    gaInventory.realize .locallyBound = .reflexive := rfl

/-! ### Pro-drop / overt-PRO universal -/

/-- Gã profile derived from fragment data and inventory. -/
def gaProfile : ProDropProfile :=
  { allowsProDrop := Ga.allowsProDrop
  , hasOvertPRO   := decide gaInventory.hasOvertPRO }

/-- Gã satisfies the pro-drop/overt-PRO implicational universal
    (`ProDropProfile.Satisfies`) — overt PRO + non-*pro*-drop means the
    consequent is true. -/
theorem ga_satisfies_universal : gaProfile.Satisfies := by decide

/-- Contrapositive concretization: were Gã *pro*-drop, it could not have
    overt PRO. The hypothesis is counterfactual (Gã is non-*pro*-drop), so
    this is a vacuous specialization of `prodrop_excludes_overt_pro`. -/
theorem ga_prodrop_would_exclude_overt_pro
    (h : gaProfile.allowsProDrop = true) :
    gaProfile.hasOvertPRO = false :=
  ProDropProfile.prodrop_excludes_overt_pro gaProfile ga_satisfies_universal h

end Allotey2021
