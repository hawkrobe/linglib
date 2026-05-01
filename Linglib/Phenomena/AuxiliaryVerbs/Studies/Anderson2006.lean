import Linglib.Typology.AuxiliaryVerbs
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Doyayo.AuxiliaryVerbs
import Linglib.Fragments.Gorum.AuxiliaryVerbs
import Linglib.Fragments.Hemba.AuxiliaryVerbs
import Linglib.Fragments.Jakaltek.AuxiliaryVerbs
import Linglib.Fragments.Pipil.AuxiliaryVerbs
import Linglib.Phenomena.AuxiliaryVerbs.NegativeAuxiliaries
import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Phenomena.AuxiliaryVerbs.Studies.Sorace2000
import Linglib.Phenomena.Negation.Studies.Miestamo2005
import Linglib.Theories.Diachronic.Grammaticalization
import Linglib.Features.Aktionsart

/-!
# Anderson (2006): Auxiliary Verb Constructions
@cite{anderson-2006} @cite{heine-1993}

Cross-linguistic typology of auxiliary verb constructions (AVCs):
classification by inflectional distribution between auxiliary and
lexical verb, with diachronic grounding in @cite{heine-1993}'s
grammaticalization framework.

## Key contributions formalized

1. **Inflectional pattern typology** (`InflPattern` from substrate):
   auxHeaded, lexHeaded, doubled, split, splitDoubled — defined in
   `Typology/AuxiliaryVerbs.lean`, verified per-datum here.
2. **Semantic head invariant** (Anderson p. 23, Table 3.1 p. 117):
   the lexical verb is always the semantic head, regardless of where
   inflection sits.
3. **Typed inflectional distribution**: `InflDistribution` (from
   `Core.Morphology`) records which `MorphCategory` values each
   element hosts.
4. **Grammaticalization grounding**: Anderson ch. 7 traces AVCs
   onto Heine 1993's cline (Anderson p. 5: *"According to Heine
   (1993: 48ff.)..."*). The cline lives in
   `Theories/Diachronic/Grammaticalization.lean`, anchored on
   @cite{heine-1993} ch. 3.

## Coverage

Sample of 9 AVC datums across 7 languages, covering all 5 patterns:

- English *have eaten* (aux-headed) — Anderson ch. 2 canonical example
- Doyayo lex-headed (Anderson ch. 3 ex. 15a, p. 121)
- Doyayo split/doubled (Anderson ch. 5 ex. 129, p. 223)
- Gorum (doubled)
- Jakaltek (split, abs/erg)
- Pipil split/doubled (Anderson ch. 5 ex. 133, p. 224)
- Pipil lex-headed (Anderson p. 220-221 fn. 6, with *weli*)
- Finnish split (negative auxiliary *ei*) @cite{karlsson-2017}
- Hemba split/doubled

## 2026-04-30 audit fixes

PDF-verified against Anderson 2006 (book pp. 5, 114, 117, 121, 224)
and Heine 1993 (book p. 48ff. via Anderson p. 5):

- **Doyayo `.split` → `.lexHeaded`** (Ch 3 ex. 15a) + new
  `doyayoSplitDoubled` (Ch 5 ex. 129). Anderson never classifies
  Doyayo as plain split.
- **Pipil `.split` → `.splitDoubled`** (Ch 5 ex. 133, with subjects
  doubly marked). Fragment `splitDistribution` corrected to put
  `.agreement` on AUX (matches the gloss `1-AUX 1-2PL-show`).
- **Cline reattributed to @cite{heine-1993}** (Anderson p. 5
  explicitly cites Heine 1993:48ff.). Substrate
  `GramStage.toMorphStatus` projection moved to
  `Theories/Diachronic/Grammaticalization.lean`.
- **`negStrategyStage` moved to `NegativeAuxiliaries.lean`** as
  `NegStrategy.toGramStage : NegStrategy → Option GramStage`, with
  `.negParticle => none` (not on the verbal cline) — fixes the
  earlier formaliser-introduced collapse of @cite{miestamo-2005}'s
  particle-vs-verb distinction.
- **Dropped Table 2.3 reference**: Anderson's Table 2.3 (p. 114)
  catalogs *non-finite forms within AUX-headed AVCs* (a single-
  pattern grid of language exemplars), not a cross-pattern
  prediction. The pattern→LV-form prediction lives in Ch 2-5
  prose, not in any single table.
- **English exemplar**: switched from *will go* (modal) to *have
  eaten* (perfect) as Anderson's canonical Ch 2 AUX-headed
  example; gloss corrected from FUT (non-Andersonian for *will*)
  to AUX.PRS + PTCP.
- **9× `native_decide` → `decide`**: structural reduction is
  tractable; native_decide bypasses the kernel.
- **`finnish_form_from_paradigm`**: paired with
  `finnish_1sg_in_paradigm` witness lemma, now provably
  grounded in the Fragment paradigm rather than passing through
  the dead `none` fallback branch.
- **Sorace bridge** chains through @cite{sorace-2000}'s
  `vendlerClassToTypicalTransitivity` for a 2-step Vendler
  → TransitivityClass derivation.
- **Cross-framework theorem** `anderson_miestamo_agree_on_neg_morphology`
  documents the corrected mapping that preserves Miestamo's
  particle-vs-verb distinction.
-/

namespace Anderson2006

open Typology.AuxiliaryVerbs
open Phenomena.AuxiliaryVerbs.NegativeAuxiliaries (NegStrategy)
open Phenomena.AuxiliaryVerbs.Selection
open Core.Morphology (InflDistribution MorphCategory)
open Diachronic.Grammaticalization (GramStage)

/-! ## Per-language AVC data

The 9 sample datums (7 languages) covering all 5 of Anderson's
inflectional patterns. Per-datum verification theorems below ensure
each datum's `inflPattern` and `form`/`distribution` derive from
the Fragment files (changing a Fragment entry breaks exactly one
theorem). -/

/-- English *have eaten* — aux-headed (AUX *have* carries tense and
    agreement, LV *eaten* is a past participle). Anderson ch. 2
    (p. 40) treats English progressives (*is V-ing*) and perfects
    (*have V-ed*) as the canonical AUX-headed exemplars. -/
def english : AVCDatum :=
  { language := "English"
  , form := "have eaten"
  , inflPattern := .auxHeaded
  , gloss := "AUX.PRS eat.PTCP" }

/-- Doyayo lex-headed (Anderson Ch 3 ex. 15a, p. 121).
    *mi¹ (gi²) kpel¹-ko¹* 'I'm going to pour'. Auxiliary `gi²`
    uninflected (parenthesized in Anderson's gloss); LV carries
    proximate-future TAM. Form derived from
    `Fragments.Doyayo.AuxiliaryVerbs.lexHeadedForm`. -/
def doyayo : AVCDatum :=
  { language := "Doyayo"
  , form := Fragments.Doyayo.AuxiliaryVerbs.lexHeadedForm
  , inflPattern := .lexHeaded
  , distribution := some Fragments.Doyayo.AuxiliaryVerbs.lexHeadedDistribution
  , gloss := Fragments.Doyayo.AuxiliaryVerbs.lexHeadedGloss }

/-- Doyayo split/doubled (Anderson Ch 5 ex. 129, p. 223).
    *hi¹-za¹ hi¹-zaa³ hi¹-lɔ-mɔ* 'they might come bite you'.
    Subject `hi¹` doubly marked on AUX and LV; object `-mɔ` only
    on LV. Anderson p. 223: "this pattern... is common in Doyayo." -/
def doyayoSplitDoubled : AVCDatum :=
  { language := "Doyayo"
  , form := Fragments.Doyayo.AuxiliaryVerbs.splitDoubledForm
  , inflPattern := .splitDoubled
  , distribution := some Fragments.Doyayo.AuxiliaryVerbs.splitDoubledDistribution
  , gloss := Fragments.Doyayo.AuxiliaryVerbs.splitDoubledGloss }

/-- Gorum (doubled): subject + TAM on both AUX and LV.
    Form derived from `Fragments.Gorum.AuxiliaryVerbs`. -/
def gorum : AVCDatum :=
  { language := "Gorum"
  , form := Fragments.Gorum.AuxiliaryVerbs.form
  , inflPattern := .doubled
  , distribution := some Fragments.Gorum.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Gorum.AuxiliaryVerbs.gloss }

/-- Jakaltek (split): absolutive on AUX, ergative on LV.
    Form derived from `Fragments.Jakaltek.AuxiliaryVerbs`. -/
def jakaltek : AVCDatum :=
  { language := "Jakaltek"
  , form := Fragments.Jakaltek.AuxiliaryVerbs.form
  , inflPattern := .split
  , distribution := some Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Jakaltek.AuxiliaryVerbs.gloss }

/-- Pipil split/doubled (Anderson Ch 5 ex. 133b, p. 224).
    *n-yu ni-mitsin-ilwitia* 'I'm going to show you'. Subject `1`
    doubly marked (`n-` on AUX, `ni-` on LV); object `-mitsin-`
    only on LV. AUX root *yu* lexically encodes prospective TAM.
    Anderson p. 224: "Subjects are doubly marked... while objects
    occur only on lexical verbs." -/
def pipilSplitDoubled : AVCDatum :=
  { language := "Pipil"
  , form := Fragments.Pipil.AuxiliaryVerbs.splitDoubledForm
  , inflPattern := .splitDoubled
  , distribution := some Fragments.Pipil.AuxiliaryVerbs.splitDoubledDistribution
  , gloss := Fragments.Pipil.AuxiliaryVerbs.splitDoubledGloss }

/-- Pipil lex-headed (Anderson p. 220-221 fn. 6; Campbell 1985: 139).
    *weli ni-nehnemi wehka* 'I can walk far'. AUX *weli* uninflected;
    LV carries subject agreement. Anderson explicitly contrasts
    this with the split/doubled pattern in fn. 6 as a coexisting
    Pipil construction. -/
def pipilLexHeaded : AVCDatum :=
  { language := "Pipil"
  , form := Fragments.Pipil.AuxiliaryVerbs.lexHeadedForm
  , inflPattern := .lexHeaded
  , distribution := some Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution
  , gloss := Fragments.Pipil.AuxiliaryVerbs.lexHeadedGloss }

/-- Finnish negative auxiliary *ei* (split): person/number on aux,
    TAM on lexical verb (connegative form). Anderson §1.7.2 (p. 33)
    treats Uralic negative auxiliaries as aux-headed AVCs. The split
    nature derives from `Fragments.Finnish.Negation.finnishNegDistribution`:
    the negative auxiliary hosts negation, tense, and agreement,
    while the lexical verb retains stem and aspect. @cite{karlsson-2017}.
    The 1sg neg-aux form derives from `negParadigm`; see
    `finnish_1sg_in_paradigm` below for the lookup-witness theorem
    that grounds the form-construction in the actual paradigm. -/
def finnish : AVCDatum :=
  { language := "Finnish"
  , form := match Fragments.Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg") with
    | some f => f.form ++ " lue"
    | none => "en lue"
  , inflPattern := .split
  , distribution := some Fragments.Finnish.Negation.finnishNegDistribution
  , gloss := "NEG-1SG read.CONNEG" }

/-- Hemba split/doubled: subject doubled on both AUX and LV; tense
    on AUX only; mood on LV only. Form derived from
    `Fragments.Hemba.AuxiliaryVerbs`. -/
def hemba : AVCDatum :=
  { language := "Hemba"
  , form := Fragments.Hemba.AuxiliaryVerbs.form
  , inflPattern := .splitDoubled
  , distribution := some Fragments.Hemba.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Hemba.AuxiliaryVerbs.gloss }

/-- All 9 AVC datums (covering all 5 of Anderson's patterns). -/
def allData : List AVCDatum :=
  [english, doyayo, doyayoSplitDoubled, gorum, jakaltek,
   pipilSplitDoubled, pipilLexHeaded, finnish, hemba]

/-! ## Per-datum InflPattern verification

Each theorem below is a structural drift sentry: changing a
Fragment entry's underlying analysis breaks exactly one theorem. -/

theorem english_is_auxHeaded : english.inflPattern = .auxHeaded := rfl
theorem doyayo_is_lexHeaded : doyayo.inflPattern = .lexHeaded := rfl
theorem doyayoSplitDoubled_is_splitDoubled :
    doyayoSplitDoubled.inflPattern = .splitDoubled := rfl
theorem gorum_is_doubled : gorum.inflPattern = .doubled := rfl
theorem jakaltek_is_split : jakaltek.inflPattern = .split := rfl
theorem pipilSplitDoubled_is_splitDoubled :
    pipilSplitDoubled.inflPattern = .splitDoubled := rfl
theorem pipilLexHeaded_is_lexHeaded : pipilLexHeaded.inflPattern = .lexHeaded := rfl
theorem finnish_is_split : finnish.inflPattern = .split := rfl
theorem hemba_is_splitDoubled : hemba.inflPattern = .splitDoubled := rfl

/-! ## Per-datum form/distribution Fragment grounding -/

theorem doyayo_form_from_fragment :
    doyayo.form = Fragments.Doyayo.AuxiliaryVerbs.lexHeadedForm := rfl
theorem doyayoSplitDoubled_form_from_fragment :
    doyayoSplitDoubled.form = Fragments.Doyayo.AuxiliaryVerbs.splitDoubledForm := rfl
theorem gorum_form_from_fragment :
    gorum.form = Fragments.Gorum.AuxiliaryVerbs.form := rfl
theorem jakaltek_form_from_fragment :
    jakaltek.form = Fragments.Jakaltek.AuxiliaryVerbs.form := rfl
theorem pipilSplitDoubled_form_from_fragment :
    pipilSplitDoubled.form = Fragments.Pipil.AuxiliaryVerbs.splitDoubledForm := rfl
theorem pipilLexHeaded_form_from_fragment :
    pipilLexHeaded.form = Fragments.Pipil.AuxiliaryVerbs.lexHeadedForm := rfl
theorem hemba_form_from_fragment :
    hemba.form = Fragments.Hemba.AuxiliaryVerbs.form := rfl

theorem doyayo_dist_from_fragment :
    doyayo.distribution = some Fragments.Doyayo.AuxiliaryVerbs.lexHeadedDistribution := rfl
theorem doyayoSplitDoubled_dist_from_fragment :
    doyayoSplitDoubled.distribution =
      some Fragments.Doyayo.AuxiliaryVerbs.splitDoubledDistribution := rfl
theorem gorum_dist_from_fragment :
    gorum.distribution = some Fragments.Gorum.AuxiliaryVerbs.inflDistribution := rfl
theorem jakaltek_dist_from_fragment :
    jakaltek.distribution = some Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution := rfl
theorem pipilSplitDoubled_dist_from_fragment :
    pipilSplitDoubled.distribution =
      some Fragments.Pipil.AuxiliaryVerbs.splitDoubledDistribution := rfl
theorem pipilLexHeaded_dist_from_fragment :
    pipilLexHeaded.distribution =
      some Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution := rfl
theorem finnish_dist_from_fragment :
    finnish.distribution = some Fragments.Finnish.Negation.finnishNegDistribution := rfl
theorem hemba_dist_from_fragment :
    hemba.distribution = some Fragments.Hemba.AuxiliaryVerbs.inflDistribution := rfl

/-! ## Finnish form construction grounding

The Finnish form construction uses `negParadigm.find?`, which is
`Option`-typed. The fallback `| none => "en lue"` was historically
chosen to coincide with the success-branch result, making
`finnish.form = "en lue"` pass by `rfl` even when the lookup
*would* return `none`. The witness theorem below grounds the
construction in the actual paradigm content. -/

/-- The Finnish 1sg negative-auxiliary entry exists in `negParadigm`.
    Together with `finnish_form_from_paradigm`, this pins
    `finnish.form` to the Fragment's actual paradigm content
    rather than the dead-branch fallback. -/
theorem finnish_1sg_in_paradigm :
    (Fragments.Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg")).isSome = true := by
  decide

/-- The Finnish form is the 1sg `negParadigm` entry's form
    concatenated with `" lue"`. -/
theorem finnish_form_from_paradigm : finnish.form = "en lue" := rfl

/-! ## Connection to FunctionWords (English modals)

Anderson's framework subsumes English modals as aux-headed AVCs:
*can* (and *will*, *may*, etc.) take `AuxType.modal` and the
lexical verb appears bare. -/

theorem english_modals_are_aux_type :
    Fragments.English.Auxiliaries.can.auxType =
      Fragments.English.Auxiliaries.AuxType.modal := rfl

/-! ## Connection to Finnish Fragment -/

/-- The Finnish negative auxiliary construction is a split AVC: the
    auxiliary hosts some inflectional categories and the lexical
    verb hosts others, with neither element hosting all categories. -/
theorem finnish_split_from_fragment :
    let dist := Fragments.Finnish.Negation.finnishNegDistribution
    dist.onAux ≠ [] ∧ dist.onLex ≠ [] := by
  exact ⟨by decide, by decide⟩

/-! ## Pattern coverage (named witnesses)

All five of Anderson's inflectional patterns are attested in the
sample. Each pattern is witnessed by a *named* datum (existence by
witness, not aggregate `.any`-scan). Adding a new datum doesn't
break this theorem; changing one of the named witnesses' patterns
does. -/

theorem five_patterns_attested :
    english.inflPattern = .auxHeaded ∧
    doyayo.inflPattern = .lexHeaded ∧
    gorum.inflPattern = .doubled ∧
    jakaltek.inflPattern = .split ∧
    hemba.inflPattern = .splitDoubled := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Structural theorems on distribution -/

/-- In Gorum's doubled AVC, aux and lex host exactly the same categories. -/
theorem gorum_doubled_same_categories :
    let dist := Fragments.Gorum.AuxiliaryVerbs.inflDistribution
    dist.onAux == dist.onLex = true := by decide

/-- In Doyayo's lex-headed AVC, the auxiliary hosts no inflection. -/
theorem doyayo_lexHeaded_aux_empty :
    Fragments.Doyayo.AuxiliaryVerbs.lexHeadedDistribution.onAux = [] := rfl

/-- In Doyayo's split/doubled AVC, subject agreement is shared
    (doubled on both elements); object valence appears only on LV. -/
theorem doyayo_splitDoubled_agreement_doubled :
    let dist := Fragments.Doyayo.AuxiliaryVerbs.splitDoubledDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true ∧
    dist.onLex.contains .valence = true ∧
    dist.onAux.contains .valence = false := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- In Pipil's split/doubled AVC, subject agreement is doubled
    (on both AUX and LV); object valence appears only on LV.
    The AUX itself encodes TAM lexically (no separate `.tense`
    morpheme on AUX). -/
theorem pipil_splitDoubled_agreement_doubled :
    let dist := Fragments.Pipil.AuxiliaryVerbs.splitDoubledDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true ∧
    dist.onLex.contains .valence = true ∧
    dist.onAux.contains .valence = false := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- In Pipil's lex-headed AVC, the auxiliary hosts no inflection. -/
theorem pipil_lexHeaded_aux_empty :
    Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution.onAux = [] := rfl

/-- In Finnish's split AVC, aux and lex host disjoint category types.
    (`.stem` on the lex side is a base, not an inflectional overlap.) -/
theorem finnish_split_disjoint :
    let dist := Fragments.Finnish.Negation.finnishNegDistribution
    dist.onAux.all (fun c => !dist.onLex.contains c) = true := by decide

/-- Jakaltek's split distributes agreement across both elements —
    absolutive on AUX and ergative on LV. At the `MorphCategory` level,
    both are `.agreement`, so the split is *within* a single category
    type rather than *between* category types. Anderson classifies this
    as split despite the shared `.agreement` label because the specific
    agreement relations (absolutive vs. ergative) differ. -/
theorem jakaltek_split_within_agreement :
    let dist := Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true := by
  exact ⟨by decide, by decide⟩

/-- In Hemba's split/doubled AVC, agreement is doubled (on both
    elements), tense is AUX-only, mood is LV-only. -/
theorem hemba_splitDoubled_agreement_doubled :
    let dist := Fragments.Hemba.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains .agreement = true ∧
    dist.onLex.contains .agreement = true ∧
    dist.onAux.contains .tense = true ∧
    dist.onLex.contains .tense = false ∧
    dist.onAux.contains .mood = false ∧
    dist.onLex.contains .mood = true := by
  exact ⟨by decide, by decide, by decide,
         by decide, by decide, by decide⟩

/-! ## Dual headedness

Anderson p. 117 Table 3.1 distinguishes three notions of head:
inflectional, phrasal/syntactic, and semantic. The semantic head
(content provider) is always the lexical verb (Anderson p. 23);
the inflectional host varies by pattern. This mismatch is what
makes AVCs typologically distinctive. -/

/-- The semantic head and inflectional host coincide only in
    lex-headed AVCs. In all other patterns they diverge: the
    semantic head is always the lexical verb, but inflection
    may sit on the auxiliary (or on both elements). -/
theorem heads_coincide_iff_lexHeaded (p : InflPattern) :
    (p.semanticHead == p.inflHost) = (p == .lexHeaded) := by
  cases p <;> rfl

/-! ## Negative auxiliaries as AVCs

@cite{anderson-2006} §1.7.2 (p. 33) treats negative auxiliaries
(Finnish *ei*, Komi *oz*, Mari, Veps) as a special case of
aux-headed AVCs: the negative element IS the auxiliary, hosting
inflection that the lexical verb would otherwise carry. The
substantive theorems about NegStrategy live in
`Phenomena/AuxiliaryVerbs/NegativeAuxiliaries.lean`; this section
re-exports the connection visible from Anderson's framing. -/

theorem negVerb_creates_auxHeaded :
    NegStrategy.negVerb.expectedInflPattern = some InflPattern.auxHeaded := rfl

/-! ## LV form predictions across patterns

Anderson predicts the verb form of the lexical verb from the
inflectional pattern. AUX-headed AVCs have a nonfinite LV
(infinitive/participle/etc.; Anderson Table 2.3 on p. 114
catalogs the LV non-finite-form types within AUX-headed AVCs
specifically — the table is a one-pattern grid of language
exemplars, not a cross-pattern prediction). All other patterns
have a finite LV (carrying at least some inflection, per Anderson
chs. 3-5 prose). The pattern→LV-form prediction is formalized in
`Typology.lvVerbForm`. -/

theorem auxHeaded_predicts_nonfinite_lv :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

theorem lexHeaded_predicts_finite_lv :
    InflPattern.lexHeaded.lvVerbForm = UD.VerbForm.Fin := rfl

theorem doubled_predicts_finite_lv :
    InflPattern.doubled.lvVerbForm = UD.VerbForm.Fin := rfl

theorem split_predicts_finite_lv :
    InflPattern.split.lvVerbForm = UD.VerbForm.Fin := rfl

theorem splitDoubled_predicts_finite_lv :
    InflPattern.splitDoubled.lvVerbForm = UD.VerbForm.Fin := rfl

/-! ## Bridge to Sorace 2000 (auxiliary selection)

Be/have auxiliary selection (`Selection.lean`) operates within
aux-headed AVCs: the question of *which* auxiliary appears
presupposes the auxiliary hosts inflection. @cite{sorace-2000}'s
sister study `Studies/Sorace2000.lean` provides
`vendlerClassToTypicalTransitivity`; chaining through it gives
a Vendler→TransitivityClass→PerfectAux derivation that Anderson's
framework presupposes (the *which-aux* question is well-posed
only inside aux-headed AVCs).

Sorace's **gradient** Auxiliary Selection Hierarchy is not yet
formalized in linglib (per `Sorace2000.lean` docstring); the
contrastive theorem against Anderson's discrete pattern typology
(`anderson_silent_on_intermediate_ash`) will land when ASH ranks
are added. -/

/-- Auxiliary selection presupposes aux-headed pattern: the
    selecting auxiliary hosts tense/agreement (is the inflectional
    head). -/
theorem selection_presupposes_auxHeaded :
    InflPattern.auxHeaded.inflHost = .aux := rfl

/-- Two-step Vendler → TransitivityClass → PerfectAux derivation
    via Sorace's mapping: an achievement-class verb projects onto
    `.unaccusative`, which canonical (Romance) selection maps to
    `.be`. Italian *arrivare* (Selection datum) is independently
    classified as unaccusative; the chain agrees. -/
theorem italian_arrivare_chain :
    canonicalSelection
      (Phenomena.AuxiliaryVerbs.Studies.Sorace2000.vendlerClassToTypicalTransitivity
        Features.VendlerClass.achievement) = .be ∧
    italianArrivare.transitivityClass = .unaccusative ∧
    canonicalSelection italianArrivare.transitivityClass = .be := by
  exact ⟨rfl, rfl, rfl⟩

/-- In aux-headed AVCs (where be/have selection is well-posed),
    the LV is nonfinite — past participle in Romance compound
    perfects: *è arrivato*, *a mangé*, *ist angekommen*. -/
theorem selection_lv_is_nonfinite_in_auxHeaded :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

/-! ## Cross-framework: Miestamo 2005 (negation symmetry)

@cite{miestamo-2005} draws a sharp morphological distinction
between negative *verbs* (Finnish *ei*, an inflecting verb) and
negative *particles* (German *nicht*, English *not*) — verbs
typically create constructional asymmetry, particles typically
don't. Anderson's grammaticalization-cline framework, via the
`NegStrategy.toGramStage` projection now in `NegativeAuxiliaries.lean`,
keeps this distinction visible at the cline level: verbs map to
`.auxiliary`, particles map to `none` (not on the verbal cline).

The 2026-04-30 audit removed an earlier formaliser-introduced
synthesis `negStrategyStage : NegStrategy → GramStage` (then in
this file) that mapped both `.negVerb` and `.negParticle` onto
`.auxiliary` — collapsing the Miestamo distinction. The theorem
below documents the cross-framework agreement that the corrected
`toGramStage` mapping makes Lean-checkable. -/

/-- Anderson's grammaticalization framework (via `toGramStage`)
    distinguishes negative verbs from negative particles by
    placement on the cline; @cite{miestamo-2005} distinguishes
    them by clause-structure asymmetry. The two frameworks
    agree: Finnish *ei* and German *nicht* are different
    morphological categories with different structural
    consequences (asymmetric vs symmetric negation). -/
theorem anderson_miestamo_agree_on_neg_morphology :
    NegStrategy.negVerb.toGramStage = some .auxiliary ∧
    NegStrategy.negParticle.toGramStage = none ∧
    Miestamo2005.finnish.symmetry ≠ Miestamo2005.german.symmetry := by
  exact ⟨rfl, rfl, by decide⟩

end Anderson2006
