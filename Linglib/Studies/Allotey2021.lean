import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.NullSubject
import Linglib.Studies.Landau2015
import Linglib.Features.Complementation

/-!
# Allotey (2021): Overt Pronouns of Infinitival Predicates in Gã
[allotey-2021]

Western Papers in Linguistics / Cahiers linguistiques de Western 4.

Gã (Kwa, Niger-Congo; spoken in Greater Accra, Ghana) shows obligatory
control over the embedded subject of irrealis `ni`-clauses, where the
controlled subject is realized as an OVERT subject proclitic — null PRO
is ungrammatical. This is the same pattern [ostrove-2026] analyzes
for SMPM and [sulemana-2021] analyzes for Büli, and falls under the
[kratzer-2009] / [safir-2014] / [landau-2015] minimal
pronoun framework: Gã simply lacks a null vocabulary item for the
controlled subject position.

[allotey-2021] herself adopts [szabolcsi-2009]'s Long Distance
Agree (LDA) Hypothesis (building on [satik-2019]). The minimal
pronoun framework and LDA are compatible — LDA is the syntactic
mechanism that values the unvalued φ-features of the minimal pronoun
in the embedded subject position. We wire both perspectives in below.

## Core Contributions

1. **Three-way clause typology** distinguished by complementizer:
   `akɛ`-clauses (finite declarative), `kɛji`-clauses (finite
   conditional), `ni`-clauses (irrealis, OC).
2. **OC over an overt subject**: irrealis `ni`-clauses show the OC
   signature despite carrying an overt subject proclitic.
3. **Subject and object control** are both attested with `ni`-clause
   complements (subject-control: `tao` 'want', `hiɛ-kpa-nɔ` 'forget';
   object-control: `kenya` 'urge', `dai` 'force').
4. **Irrealis ≠ subjunctive**: Allotey argues against
   [dakubu-2004] and [campbell-2017], who classify the
   high-tone marker as subjunctive. The diagnostic she offers
   (controlled-clause obviation) is formalized below.
5. **Long Distance Agree analysis**: the embedded overt pronoun is a
   minimal pronoun whose φ-features are valued by LDA from the matrix
   controller ([szabolcsi-2009], [satik-2019]).
6. **Cross-linguistic pattern**: Gã joins SMPM and Büli as a third
   language with obligatory pronominal copy control under the
   [ostrove-2026] typology.

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
                   Complementizer Control CTP)

-- ════════════════════════════════════════════════════════════════
-- § 1: Clause Type Verification
-- ════════════════════════════════════════════════════════════════

theorem finiteAke_unrestricted_tam :
    (clauseProperties .finiteAke).unrestrictedTAM = true := rfl
theorem finiteKeji_unrestricted_tam :
    (clauseProperties .finiteKeji).unrestrictedTAM = true := rfl
theorem irrealisNi_restricted_tam :
    (clauseProperties .irrealisNi).unrestrictedTAM = false := rfl

theorem finiteAke_allows_noncoreferential :
    (clauseProperties .finiteAke).noncoreferentialSubject = true := rfl
theorem finiteKeji_allows_noncoreferential :
    (clauseProperties .finiteKeji).noncoreferentialSubject = true := rfl
theorem irrealisNi_no_noncoreferential :
    (clauseProperties .irrealisNi).noncoreferentialSubject = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 2: OC Diagnostics — derived from clauseProperties
-- ════════════════════════════════════════════════════════════════

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

theorem irrealisNi_is_OC :
    (gaOCSignature .irrealisNi).isOC = true := rfl

theorem finiteAke_not_OC :
    (gaOCSignature .finiteAke).isOC = false := rfl

theorem finiteKeji_not_OC :
    (gaOCSignature .finiteKeji).isOC = false := rfl

/-- The general derivation: lack of noncoreferential subjects iff OC. -/
theorem oc_iff_no_noncoreferential (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = !(clauseProperties c).noncoreferentialSubject := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 3: Irrealis vs. Subjunctive Diagnostic
-- ════════════════════════════════════════════════════════════════

/-- A clause type passes the **subjunctive diagnostic** iff it permits
    a noncoreferential embedded subject. Romance subjunctives display
    obviation effects (the embedded subject must NOT corefer with the
    matrix subject) — i.e., they license noncoreference. An irrealis
    OC clause license the opposite: obligatory coreference.

    [allotey-2021] argues that the high-tone marker on Gã verbs
    is **irrealis**, not subjunctive (contra [dakubu-2004],
    [campbell-2017]). The diagnostic below confirms her claim
    on the noncoreference test: `irrealisNi` fails the subjunctive
    diagnostic. -/
def isSubjunctiveLike (c : EmbeddedClauseType) : Bool :=
  (clauseProperties c).noncoreferentialSubject

theorem irrealisNi_not_subjunctive :
    isSubjunctiveLike .irrealisNi = false := rfl

theorem finiteAke_subjunctive_test_passes :
    isSubjunctiveLike .finiteAke = true := rfl

theorem finiteKeji_subjunctive_test_passes :
    isSubjunctiveLike .finiteKeji = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § 4: Landau Bridge
-- ════════════════════════════════════════════════════════════════

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

/-- Cross-check: `gaAgr` agrees with the complementizer's finiteness flag,
    via `complementizer_isFinite_eq_finiteFlag`. -/
theorem gaAgr_eq_complementizer_isFinite (c : EmbeddedClauseType) :
    gaAgr c = (clauseComplementizer c).isFinite := by
  unfold gaAgr
  rw [complementizer_isFinite_eq_finiteFlag]

/-- The Landau classification predicts Gã control properties for all
    three clause types, taking Agr status into account. -/
theorem landau_predicts_control (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = (gaToLandau c).hasOCWithAgr (gaAgr c) := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 5: Per-Verb Control Verification
-- ════════════════════════════════════════════════════════════════

open Ga (tao kpleno kpang hiekpano nye kenya laka dai wa kee)

/-- Each subject-control verb selects an `irrealisNi` clause whose
    OC signature is the full one. -/
theorem tao_OC      : (gaOCSignature tao.selects).isOC      = true := rfl
theorem hiekpano_OC : (gaOCSignature hiekpano.selects).isOC = true := rfl
theorem nye_OC      : (gaOCSignature nye.selects).isOC      = true := rfl
theorem kpleno_OC   : (gaOCSignature kpleno.selects).isOC   = true := rfl
theorem kpang_OC    : (gaOCSignature kpang.selects).isOC    = true := rfl

/-- Each object-control verb selects an `irrealisNi` clause whose
    OC signature is the full one. -/
theorem kenya_OC : (gaOCSignature kenya.selects).isOC = true := rfl
theorem laka_OC  : (gaOCSignature laka.selects).isOC  = true := rfl
theorem dai_OC   : (gaOCSignature dai.selects).isOC   = true := rfl
theorem wa_OC    : (gaOCSignature wa.selects).isOC    = true := rfl

/-- The finite-complement verb does not show OC. -/
theorem kee_no_OC : (gaOCSignature kee.selects).isOC = false := rfl

/-- Universal: every Gã CTP whose complement is `irrealisNi` shows OC,
    and every CTP whose complement is finite does not. The clause type
    determines OC, regardless of the verb's own control flavor. -/
theorem oc_determined_by_clause_type (c : CTP) :
    (gaOCSignature c.selects).isOC = !(clauseComplementizer c.selects).isFinite := by
  cases h : c.selects <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 6: Long-Distance Agree Analysis (Allotey's syntactic mechanism)
-- ════════════════════════════════════════════════════════════════

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
    matrix controller ([szabolcsi-2009], [satik-2019]).

    The probe (matrix v/T) has valued φ; the goal (embedded D[uφ])
    has unvalued φ; the intervening `ni` C head is non-defective for
    LDA, so the dependency crosses a clause boundary. -/
def gaLDAConfig : LDAConfig where
  probeHasValuedPhi   := true
  goalHasUnvaluedPhi  := true
  cIsDefectiveBlocker := false

theorem ga_satisfies_LDA :
    LDAConfig.licenses gaLDAConfig = true := rfl

/-- Bridge: the LDA configuration is exactly what's required to value
    the φ-features of a minimal pronoun in the embedded subject position.
    This is the syntactic mechanism that complements the morphological
    minimal-pronoun analysis (Section 7). -/
theorem ga_LDA_implies_OC :
    LDAConfig.licenses gaLDAConfig = true →
    (gaOCSignature .irrealisNi).isOC = true := by
  intro _; rfl

-- ════════════════════════════════════════════════════════════════
-- § 7: Minimal Pronoun Inventory
-- ════════════════════════════════════════════════════════════════

open PronForm

/-- Gã vocabulary items.

    Like SMPM and Büli: lacks a null allomorph for controlled subjects.
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

-- ════════════════════════════════════════════════════════════════
-- § 8: Pro-Drop / Overt-PRO Universal ([ostrove-2026] 54)
-- ════════════════════════════════════════════════════════════════

/-- Gã profile derived from fragment data and inventory. -/
def gaProfile : ProDropProfile :=
  { allowsProDrop := Ga.allowsProDrop
  , hasOvertPRO   := decide gaInventory.hasOvertPRO }

/-- Gã satisfies the implicational universal — overt PRO + non-*pro*-drop
    means the consequent is true. -/
theorem ga_satisfies_universal : gaProfile.Satisfies := by decide

/-- Contrapositive concretization: were Gã *pro*-drop, it could not have
    overt PRO. The hypothesis is counterfactual (Gã is non-*pro*-drop), so
    this is a vacuous specialization of `prodrop_excludes_overt_pro`. -/
theorem ga_prodrop_would_exclude_overt_pro
    (h : gaProfile.allowsProDrop = true) :
    gaProfile.hasOvertPRO = false :=
  ProDropProfile.prodrop_excludes_overt_pro gaProfile ga_satisfies_universal h

-- ════════════════════════════════════════════════════════════════
-- § 9: Noonan Complementation Bridge
-- ════════════════════════════════════════════════════════════════

/-- Map Gã clause types to [noonan-2007]'s complement typology.

    All three Gã clause types are "balanced" in Noonan's sense: they
    are inflected for TAM and carry overt subject morphology. There is
    no "deranked" (infinitival/nominalized/participial) complement
    type in Gã.

    - `finiteAke` → indicative (full TAM, free reference)
    - `finiteKeji` → indicative (full TAM, free reference; conditional flavor)
    - `irrealisNi` → subjunctive (irrealis only, obligatory coreference)

    Note: Noonan's `subjunctive` category is the typological-typology
    label for "finite irrealis-marked complement"; it is *not* the
    generative-grammar subjunctive Allotey is arguing against
    (cf. `irrealisNi_not_subjunctive` above). The Noonan label and the
    Dakubu/Campbell label happen to share a word but track different
    properties. -/
def gaToNoonan : EmbeddedClauseType → NoonanCompType
  | .finiteAke  => .indicative
  | .finiteKeji => .indicative
  | .irrealisNi => .subjunctive

end Allotey2021
