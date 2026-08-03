/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Ga.Predicates
import Linglib.Syntax.Minimalist.MinimalPronoun
import Linglib.Syntax.Control.Basic
import Linglib.Syntax.Control.CopyControl
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Features.Complementation

/-!
# Allotey (2021): Overt Pronouns of Infinitival Predicates of Gã

This file formalizes [allotey-2021]. Gã (Kwa; ISO gaa) shows obligatory
control over the embedded subject of irrealis `ni`-clauses, and the
controlled subject must be an overt subject proclitic — null PRO is
ungrammatical. Allotey argues that the embedded control clauses are
non-finite irrealis clauses rather than subjunctives (against the
descriptive tradition of [dakubu-2004], [campbell-2017], and
[korsah-2017]), that the
overt pronoun is a subject in Spec TP valued by Long Distance Agree
from the matrix controller ([szabolcsi-2009]) and lexicalized to host
the obligatory irrealis high tone, that the Movement Theory of Control
([hornstein-1999]) does not extend to the Gã data, and that
[satik-2019]'s left-periphery-bound pronoun does not fully extend
either: the Gã pronoun φ-covaries with its controller, while Ewe *yè*
is form-invariant.

## Main results

- `overt_pronoun_matches_pro`: the overt pronoun and OC PRO agree on
  all eight diagnostics of the paper's Table 2 (§3.7).
- `isOC_eq_not_isFinite`, `control_iff_selects_ni`: OC status and
  `ni`-frame selection both ride on the finiteness split.
- `marker_iff_irrealis_frame`, `realis_frame_only_under_realization`:
  the irrealis marker tracks the complement frame, not the verb;
  implicatives alternate into realis frames exactly when the complement
  is entailed realized (§5.2.3, including negated ex 117a).
- `landau_predicts_control`: [landau-2004]'s scale predicts the control
  facts for ANY Agr value — Gã has no F-subjunctive
  (`ga_no_fSubjunctive`) and no φ-agreement (§4.4).
- `ldaReaches_eq_isOC`, `ni_projects_no_focus`, `npi_patterns_with_lda`:
  LDA blocking as a [keine-2020]-style horizon at the strong C head
  ([rizzi-1997]); focus fronting and NPI licensing pattern with it.
- `control_realization_unique`: Table 4 — the control clause's
  subject-only tone profile is unique among the five irrealis contexts.
- `null_pro_impossible`, `ga_overt_pro`: overt PRO from the
  tone-hosting requirement (p. 28) and the absence of a null item.
- `ga_supports_basegeneration`: the lexical-copy diagnostic supports
  base-generation over movement.
- `ga_satisfies_universal`: Gã instantiates the overt-PRO →
  no-*pro*-drop universal.

The verb-movement/negation-placement diagnostic (§5.5.5, after
[pollock-1989]) and §6's negation-position subjecthood argument (exx
123–125) are not formalized — both need phrase-structure substrate;
the finiteness split the former diagnoses is carried by the clause
typology, and §6.1's no-agreement premise surfaces as
`landau_predicts_control`'s Agr-independence. §5.5.2's tonal asymmetry
(exx 110–112) is carried at the clause level by
`marker_iff_irrealis_frame`.

## References

* [D. Allotey, *Overt Pronouns of Infinitival Predicates of Gã*][allotey-2021]
-/

namespace Allotey2021

open Minimalist
open Minimalist.MinimalPronoun
open Control
open Ga

/-! ### Table 2: the overt pronoun has the OC signature

[landau-2013]'s OC diagnostics, applied twice (§§3.3–3.4): to OC PRO
(the signature itself) and to the Gã overt pronoun. Both columns of
Table 2 (p. 24) are transcribed; their agreement is the paper's §3
deliverable. -/

/-- The eight diagnostic properties of [allotey-2021]'s Table 2. -/
inductive OCDiagnostic where
  /-- Must be c-commanded by its antecedent (exx 45–46) -/
  | cCommandedByAntecedent
  /-- Allows a long-distance antecedent (exx 47–49) -/
  | longDistanceAntecedent
  /-- Sloppy reading only under ellipsis (exx 50–52) -/
  | sloppyOnly
  /-- Interpreted as a bound variable -/
  | boundVariable
  /-- Bears φ-features -/
  | hasPhiFeatures
  /-- Must be read *de se* (ex 53; [chierchia-1990]'s diagnostic) -/
  | obligatoryDeSe
  /-- Occurs under subject control (exx 34–43) -/
  | subjectControl
  /-- Occurs under object control (exx 54–59) -/
  | objectControl
  deriving DecidableEq, Repr

/-- Table 2's OC-PRO column ([landau-2013]'s signature). -/
def ocPRO : OCDiagnostic → Bool
  | .cCommandedByAntecedent => true
  | .longDistanceAntecedent => false
  | .sloppyOnly             => true
  | .boundVariable          => true
  | .hasPhiFeatures         => true
  | .obligatoryDeSe         => true
  | .subjectControl         => true
  | .objectControl          => true

/-- Table 2's overt-pronoun column (Allotey's observations,
    §§3.3.1–3.3.7, 3.4). -/
def overtPronoun : OCDiagnostic → Bool
  | .cCommandedByAntecedent => true
  | .longDistanceAntecedent => false
  | .sloppyOnly             => true
  | .boundVariable          => true
  | .hasPhiFeatures         => true
  | .obligatoryDeSe         => true
  | .subjectControl         => true
  | .objectControl          => true

/-- §3.7: "PRO and the *overt* pronoun share all properties" — the two
    Table 2 columns agree on every diagnostic. -/
theorem overt_pronoun_matches_pro (d : OCDiagnostic) :
    overtPronoun d = ocPRO d := by
  cases d <;> rfl

/-! ### OC diagnostics by clause type

The OC signature is derived from the fragment's
`clauseProperties.noncoreferentialSubject` via
`OCSignature.ofNoncoreferential` (the same derivation as
`Ostrove2026.smpmOCSignature`): a clause type that bars
noncoreferential embedded subjects forces the full [landau-2013]
signature, and only `irrealisNi` does. -/

/-- The OC signature of a Gã clause type, from its noncoreference flag. -/
def gaOCSignature (c : EmbeddedClauseType) : OCSignature :=
  .ofNoncoreferential (clauseProperties c).noncoreferentialSubject

/-- OC status is read off the complementizer's finiteness. -/
theorem isOC_eq_not_isFinite (c : EmbeddedClauseType) :
    (gaOCSignature c).isOC = !(clauseComplementizer c).isFinite := by
  cases c <;> rfl

/-- A verb has a `ni`-frame exactly when it is a control verb:
    C-selection (§5.5.1) and control-hood (§§3.4–3.5) coincide across
    the attested inventory. -/
theorem control_iff_selects_ni :
    ∀ v ∈ gaCTPs, .irrealisNi ∈ v.selects ↔ v.control ≠ .none := by
  decide

/-! ### The irrealis marker across complement frames

§§5.2.3, 5.3.5, 5.5.3: within the irrealis `ni`-clause the marker's
high tone on the subject is constant — affirmative (exx 43, 100) or
negated (ex 117a), implicative matrix or not (exx 89c–d, 102–103). What
implicativity governs is *frame choice*: a positive implicative under
affirmation entails its complement realized, and exactly then the verb
alternates into a realis frame (`akɛ` + past, ex 89a, or the bare
complement, ex 89b), where the irrealis marker is impossible. (True
subjunctive complements, ex 105, mark both sites — see Table 4 below —
and fall outside this table.) -/

/-- One attested complement configuration: the matrix verb, the
    complement's complementizer (`none` for the bare frame of ex 89b),
    the matrix polarity, and whether the embedded subject carries the
    irrealis marker. -/
structure MarkerDatum where
  verb : CTP
  comp : Option Complementizer
  matrixAffirmative : Bool
  markerPresent : Bool
  deriving DecidableEq, Repr

/-- Whether the datum's frame is the irrealis `ni`-clause. -/
def MarkerDatum.irrealisFrame (d : MarkerDatum) : Bool :=
  d.comp == some .ni

/-- The attested marker data (exx 89a–d, 100, 102–103, 117a). -/
def irrealisMarkerData : List MarkerDatum :=
  [ ⟨kai,      some .ake, true,  false⟩   -- 89a  realis 'remember that'
  , ⟨nye,      none,      true,  false⟩   -- 89b  bare realis complement
  , ⟨kpleno,   some .ni,  true,  true⟩    -- 89c  *mi/má
  , ⟨kpang,    some .ni,  true,  true⟩    -- 89d  *mi/má
  , ⟨tao,      some .ni,  true,  true⟩    -- 100  má (also exx 34, 88)
  , ⟨hiekpano, some .ni,  true,  true⟩    -- 102–103  ó, é
  , ⟨kai,      some .ni,  false, true⟩ ]  -- 117a é under matrix negation

/-- The marker tracks the clause frame, not the verb: present exactly
    in the irrealis `ni`-frame (Table 4's subject-site row). -/
theorem marker_iff_irrealis_frame :
    ∀ d ∈ irrealisMarkerData, d.markerPresent = d.irrealisFrame := by
  decide

/-- §5.2.3's implicative asymmetry at the correct grain: a realis frame
    — where the marker is impossible — occurs only where the complement
    is entailed realized, i.e. under an affirmative positive
    implicative. Non-implicatives cannot trade the `ni`-frame for a
    realis one (exx 89c–d: *mi), and a negated implicative reverts to
    the irrealis frame (ex 117a). -/
theorem realis_frame_only_under_realization :
    ∀ d ∈ irrealisMarkerData, d.irrealisFrame = false →
      d.verb.implicative = some .positive ∧ d.matrixAffirmative = true := by
  decide

/-! ### Landau bridge

`ni`-clauses are untensed (exx 118–119) and the finite complements
tensed, so the scale positions derive from the fragment's TAM
observables. Contrast SMPM (`Studies/Ostrove2026.lean`), whose tensed
subjunctives fill the F-subjunctive cell Gã leaves empty. -/

/-- Gã clause types on [landau-2004]'s finiteness scale, via
    `ClauseClass.ofFiniteness`. The label is a scale position, not a
    mood-morphology claim: §5.2 argues at length that these clauses are
    *not* subjunctives (Table 4; obviation, exx 90–92) — they are
    untensed irrealis clauses, which is the C-subjunctive cell. -/
def gaToLandau (c : EmbeddedClauseType) : Control.ClauseClass :=
  .ofFiniteness (clauseProperties c).unrestrictedTAM
    (clauseProperties c).independentTense

/-- Gã occupies a proper sub-part of the scale: no clause type is a
    tensed-but-controlled F-subjunctive. -/
theorem ga_no_fSubjunctive (c : EmbeddedClauseType) :
    gaToLandau c ≠ .fSubjunctive := by
  cases c <;> decide

/-- The Landau classification predicts the Gã control facts for ANY
    Agr value: Gã lacks the one scale position that reads the Agr bit
    (`ga_no_fSubjunctive`), and has no φ-agreement to ground a value
    anyway — "there is no agreement marked on the verb" (§4.4, exx
    79–81), in finite and non-finite clauses alike (§6.1). The control
    system rides on `[±T]` alone. -/
theorem landau_predicts_control (c : EmbeddedClauseType) (agr : Bool) :
    (gaOCSignature c).isOC = (gaToLandau c).hasOCWithAgr agr := by
  cases c <;> cases agr <;> rfl

/-! ### Long-Distance Agree and CP strength

The matrix φ-probe values the embedded minimal pronoun across `ni`
([szabolcsi-2009], exx 60–62). What separates the crossable from the
blocking complementizers is CP strength ([rizzi-1997], §5.5.1): `akɛ`
and `kɛji` head strong CPs — a full C-domain, with focus fronting (exx
107–108) — while `ni` heads a weak CP projecting only Fin (no focus, no
independent tense, ex 109). Encoded as a [keine-2020]-style horizon:
the search terminates at a strong C head, so the opacity is clause
*size*, not intervention — no φ-goal status is attributed to the
complementizer (contrast `Studies/Halpert2019.lean`, where the blocking
CP is a genuine φ-goal absorbing the probe, a commitment [allotey-2021]
does not make for Gã). -/

/-- Projected heads of a `c`-headed complement: the strong CPs project
    the full C-domain, the weak CP `ni` only Fin. -/
def clauseSpine (c : Complementizer) : List Cat :=
  if c.isFinite then [.V, .v, .T, .Fin, .Foc, .C] else [.V, .v, .T, .Fin]

/-- The matrix φ-probe: a T-probe whose horizon is the strong C head. -/
def ldaProbe : Probe.Profile := ⟨.T, some .C⟩

/-- LDA reaches into a `c`-headed complement. -/
def ldaReaches (c : Complementizer) : Bool :=
  ldaProbe.transparentToLabel (clauseSpine c)

/-- LDA crosses `ni` and is blocked by `akɛ`/`kɛji`. -/
theorem ldaReaches_eq_not_isFinite (c : Complementizer) :
    ldaReaches c = !c.isFinite := by
  cases c <;> rfl

/-- The probe reaches the embedded subject in exactly the OC clause
    types. -/
theorem ldaReaches_eq_isOC (c : EmbeddedClauseType) :
    ldaReaches (clauseComplementizer c) = (gaOCSignature c).isOC := by
  cases c <;> rfl

/-- The weak-CP content of the spines: `ni` projects no focus field,
    the finite complementizers do (exx 107–108) — the formal core of
    the strong/weak asymmetry. -/
theorem ni_projects_no_focus :
    Cat.Foc ∉ clauseSpine .ni ∧ Cat.Foc ∈ clauseSpine .ake := by
  decide

/-- NPI licensing (§5.5.3) patterns with LDA: matrix negation licenses
    an embedded NPI across exactly the complementizers the φ-probe
    crosses (exx 115–117). -/
theorem npi_patterns_with_lda (c : EmbeddedClauseType) :
    (clauseProperties c).npiTransparent = ldaReaches (clauseComplementizer c) := by
  cases c <;> rfl

/-! ### Against the rival derivations

§3.6.2: under movement ([hornstein-1999]) the pronounced embedded
element is a copy of the matrix DP, predicting an embedded lexical DP
where Gã allows only a pronoun (exx 42b, 64) — so control is
base-generated (`Derivation.eq_supportedBy_of_predicts` makes the
supported derivation unique). §3.6.3: [satik-2019]'s Ewe
left-periphery-bound pronoun *yè* is form-invariant, while the Gã
controlled proclitic φ-covaries with its controller (exx 37–39), so the
LPBP analysis "cannot be fully adopted" for Gã (p. 24). -/

/-- Gã forbids embedded lexical-DP copies (exx 42b, 64). -/
def gaEmbeddedLexicalCopyAvailable : Bool := false

/-- The derivation the lexical-copy observation supports. -/
def gaControlDerivation : Derivation :=
  Derivation.supportedBy .embeddedLexicalCopy gaEmbeddedLexicalCopyAvailable

/-- Control is base-generated: movement predicts the lexical-DP copy Gã
    forbids. -/
theorem ga_supports_basegeneration :
    gaControlDerivation = .baseGeneration := rfl

/-- The controlled form φ-covaries: distinct controller persons select
    distinct proclitics (exx 37–39: *o*, *nyɛ*, *amɛ*) — the datum that
    blocks a form-invariant left-periphery-bound pronoun for Gã. -/
theorem controlled_form_covaries :
    subjectProclitic .first .singular ≠ subjectProclitic .second .singular := by
  decide

/-! ### Table 4: the irrealis marker's realization sites

Gã has both a true subjunctive — irrealis doubled, high tone on pronoun
AND verb (exx 85–87) — and a bare irrealis. Table 4 (p. 36) records
where the marker's high tone and its vowel segment surface across the
five `[−REALIS]` contexts. The embedded-control profile (subject tone
only) is unique, so the control clause is neither a subjunctive
(§5.2.2, ex 88: *ná) nor a future (§5.3.5, ex 101: *baa-). -/

/-- The five `[−REALIS]` contexts of Table 4. -/
inductive IrrealisContext where
  | subjunctive
  | imperative
  | conditional
  | future
  | embeddedControl
  deriving DecidableEq, Repr

/-- Where the irrealis marker is realized in a context: as a high tone
    on the subject pronominal, as a high tone on the verb, and as the
    vowel segment `a`. -/
structure IrrealisRealization where
  subjectTone : Bool
  verbTone : Bool
  vowelSegment : Bool
  deriving DecidableEq, Repr

/-- Table 4 (exx 85–87 subjunctive; 93–94 imperative; 97 conditional;
    95–96 future; 100–103 embedded control). -/
def irrealisRealization : IrrealisContext → IrrealisRealization
  | .subjunctive     => ⟨true,  true,  true⟩
  | .imperative      => ⟨true,  true,  true⟩
  | .conditional     => ⟨false, false, true⟩
  | .future          => ⟨false, false, true⟩
  | .embeddedControl => ⟨true,  false, false⟩

/-- The embedded-control realization profile is unique among the five
    irrealis contexts — Table 4's argument that the control clause is
    its own irrealis category. -/
theorem control_realization_unique (c : IrrealisContext) :
    irrealisRealization c = irrealisRealization .embeddedControl →
      c = .embeddedControl := by
  cases c <;> decide

/-- In particular the control clause lacks the subjunctive's doubled
    realization (§5.2.2). -/
theorem control_not_subjunctive :
    irrealisRealization .embeddedControl ≠ irrealisRealization .subjunctive := by
  decide

/-! ### Deriving overt PRO

Allotey's explanation (§4.3, pp. 28, 45): the control clause
obligatorily realizes the irrealis high tone on its subject (Table 4),
the marker has no segmental exponent of its own there
(`Ga.TAM.exponent`), and a tone needs a segmental host — so the
controlled subject cannot be silent. -/

/-- A tonal exponent needs a segmental host: the null form has no
    segments to carry the irrealis high tone; overt forms do. -/
def _root_.Minimalist.MinimalPronoun.PronForm.hostsTone : PronForm → Bool
  | .null      => false
  | .pronoun   => true
  | .reflexive => true

/-- An inventory is usable for Gã's controlled subject only if the form
    it inserts there can host the obligatory irrealis tone (Table 4's
    embedded-control row). -/
def HostsControlTone (inv : MinPronInventory PronForm) : Prop :=
  (irrealisRealization .embeddedControl).subjectTone = true →
    inv.controlForm.hostsTone = true

/-- Null PRO is impossible in Gã: an inventory whose controlled-subject
    form is null cannot host the obligatory subject-site irrealis
    tone. -/
theorem null_pro_impossible (inv : MinPronInventory PronForm)
    (h : inv.controlForm = .null) : ¬ HostsControlTone inv :=
  fun hc => by simpa [PronForm.hostsTone, h] using hc rfl

/-! ### Minimal pronoun inventory -/

/-- Gã vocabulary items: reflexive when locally bound, pronoun
    elsewhere — crucially, no null item. (The reflexive item is
    required by the syncretism row [ostrove-2026] assigns Gã;
    UNVERIFIED: [allotey-2021] itself never discusses Gã reflexives —
    check [campbell-2017] for the form.) -/
def gaInventory : MinPronInventory PronForm where
  items := [⟨.locallyBound, .reflexive⟩]
  elsewhere := .pronoun

/-- The Gã inventory meets the tone-hosting requirement. -/
theorem ga_hostsControlTone : HostsControlTone gaInventory :=
  fun _ => rfl

/-- Controlled subjects surface as overt proclitics — the central
    empirical observation, with its explanation: no null item exists
    (`null_pro_impossible` shows one would be unusable), so the
    elsewhere pronoun applies. -/
theorem ga_overt_pro : gaInventory.controlForm = .pronoun := rfl

/-- The locally-bound context realizes the reflexive item. -/
theorem ga_has_reflexive :
    gaInventory.realize .locallyBound = .reflexive := rfl

/-! ### Typological placement -/

/-- Gã complements in [noonan-2007]'s typology: the finite clauses are
    indicative; the `ni`-clause is the infinitive — §5.6's own term for
    the bare-root complement ("I am going to call the bare root or
    citation form of the verb the infinitive form"). -/
def gaToNoonan : EmbeddedClauseType → NoonanCompType
  | .finiteAke  => .indicative
  | .finiteKeji => .indicative
  | .irrealisNi => .infinitive

/-- The control complement is reduced (deranked) in Noonan's terms —
    the paper's non-finiteness thesis in typological vocabulary. -/
theorem ni_complement_reduced :
    (gaToNoonan .irrealisNi).isReduced = true := rfl

/-- Gã instantiates [ostrove-2026]'s universal (overt PRO → no
    *pro*-drop): its controlled subjects are overt and the fragment's
    pro-drop flag is false. -/
theorem ga_satisfies_universal :
    gaInventory.OvertPROUniversal Ga.allowsProDrop :=
  fun _ => rfl

end Allotey2021
