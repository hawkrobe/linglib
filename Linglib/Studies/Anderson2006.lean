import Linglib.Syntax.AuxiliaryVerbs
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
import Linglib.Morphology.MorphRule
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Doyayo.AuxiliaryVerbs
import Linglib.Fragments.Gorum.AuxiliaryVerbs
import Linglib.Fragments.Hemba.AuxiliaryVerbs
import Linglib.Fragments.Jakaltek.AuxiliaryVerbs
import Linglib.Fragments.Pipil.AuxiliaryVerbs
import Linglib.Typology.Negation
import Linglib.Studies.Sorace2000
import Linglib.Studies.Miestamo2005
import Linglib.Morphology.Grammaticalization
import Linglib.Features.Aktionsart
import Linglib.Data.Examples.Anderson2006

/-!
# Anderson (2006): Auxiliary Verb Constructions
[anderson-2006] [heine-1993]

Cross-linguistic typology of auxiliary verb constructions (AVCs):
classification by inflectional distribution between auxiliary and
lexical verb, with diachronic grounding in [heine-1993]'s
grammaticalization framework.

## Key contributions formalized

1. **Inflectional pattern typology** (`InflPattern` from substrate):
   auxHeaded, lexHeaded, doubled, split, splitDoubled — defined in
   `Typology/AuxiliaryVerbs.lean`, verified per-datum here.
2. **Semantic head invariant** (Anderson p. 23, Table 3.1 p. 116):
   the lexical verb is always the semantic head, regardless of where
   inflection sits.
3. **Typed inflectional distribution**: `InflDistribution` (from
   `Morphology`) records which `MorphCategory` values each
   element hosts.
4. **Grammaticalization grounding**: Anderson ch. 7 traces AVCs
   onto Heine 1993's cline (Anderson p. 5: *"According to Heine
   (1993: 48ff.)..."*). The cline lives in
   `Morphology/Grammaticalization.lean`, anchored on
   [heine-1993] ch. 3.

## Coverage

Sample of 9 AVC datums across 7 languages, covering all 5 patterns:

- English *have eaten* (aux-headed) — Anderson ch. 2 canonical example
- Doyayo lex-headed (Anderson ch. 3 ex. 15a, p. 121)
- Doyayo split/doubled (Anderson ch. 5 ex. 129, p. 223)
- Gorum (doubled)
- Jakaltek (split, abs/erg)
- Pipil split/doubled (Anderson ch. 5 ex. 133, p. 224)
- Pipil lex-headed (Anderson ch. 3 ex. 49, p. 130, with *weli*)
- Finnish split (negative auxiliary *ei*) [karlsson-2017]
- Hemba split/doubled

## 2026-04-30 audit fixes

PDF-verified against Anderson 2006 (book pp. 5, 114, 116, 121, 224)
and Heine 1993 (book p. 48ff. via Anderson p. 5):

- **Doyayo `.split` → `.lexHeaded`** (Ch 3 ex. 15a) + new
  `doyayoSplitDoubled` (Ch 5 ex. 129). Anderson never classifies
  Doyayo as plain split.
- **Pipil `.split` → `.splitDoubled`** (Ch 5 ex. 133, with subjects
  doubly marked). Fragment `splitDistribution` corrected to put
  `.agreement` on AUX (matches the gloss `1-AUX 1-2PL-show`).
- **Cline reattributed to [heine-1993]** (Anderson p. 5
  explicitly cites Heine 1993:48ff.). Substrate
  `GramStage.toMorphStatus` projection moved to
  `Morphology/Grammaticalization.lean`.
- **`negStrategyStage`** is now `NegStrategy.toGramStage :
  NegStrategy → Option GramStage` (in `Typology/Negation.lean`), with
  `.negParticle => none` (not on the verbal cline) — fixes the
  earlier formaliser-introduced collapse of [miestamo-2005]'s
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
- **Sorace bridge** chains through [sorace-2000]'s
  `vendlerClassToTypicalTransitivity` for a 2-step Vendler
  → TransitivityClass derivation.
- **Cross-framework theorem** `anderson_miestamo_agree_on_neg_morphology`
  documents the corrected mapping that preserves Miestamo's
  particle-vs-verb distinction.
-/

namespace Anderson2006

open AuxiliaryVerbs
open Semantics.ArgumentStructure.AuxiliarySelection
open Typology.Negation (NegStrategy)

/-- A cross-linguistic AVC datum. Study-local: the `AuxiliaryVerbs` substrate
    classifies over `InflPattern`; this paper's per-language rows bundle the
    form/distribution/gloss with it. -/
structure AVCDatum where
  language : String
  form : String
  inflPattern : InflPattern
  distribution : Option Morphology.InflDistribution := none
  gloss : String := ""
  deriving Repr, BEq

/-! ## Per-language AVC data

The 9 sample datums (7 languages) covering all 5 of Anderson's
inflectional patterns. Per-datum verification theorems below ensure
each datum's `inflPattern` and `form`/`distribution` derive from
the Fragment files (changing a Fragment entry breaks exactly one
theorem). -/

/-- English *have eaten* — aux-headed (AUX *have* carries tense and
    agreement, LV *eaten* is a past participle). Anderson ch. 2
    (p. 40) describes the English perfect as AUX *have* with the LV
    in the *-ed* ~ *-en* form;
    the specific *have eaten* form is this file's instantiation of
    that pattern, not a verbatim Anderson example. -/
def english : AVCDatum :=
  { language := "English"
  , form := "have eaten"
  , inflPattern := .auxHeaded
  , gloss := "AUX.PRS eat.PTCP" }

/-- Doyayo lex-headed (Anderson Ch 3 ex. 15a, p. 121).
    *mi¹ (gi²) kpel¹-ko¹* 'I'm going to pour'. Auxiliary `gi²`
    parenthesized in Anderson's example, carrying only tonal subject
    person (Anderson p. 120); LV carries proximate TAM. Form derived from
    `Doyayo.AuxiliaryVerbs.lexHeadedForm`. -/
def doyayo : AVCDatum :=
  { language := "Doyayo"
  , form := Doyayo.AuxiliaryVerbs.lexHeadedForm
  , inflPattern := .lexHeaded
  , distribution := some Doyayo.AuxiliaryVerbs.lexHeadedDistribution
  , gloss := Doyayo.AuxiliaryVerbs.lexHeadedGloss }

/-- Doyayo split/doubled (Anderson Ch 5 ex. 129, p. 223).
    *hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ* 'they might come bite you'.
    Subject `hi¹` doubly marked on AUX and LV; object `-mɔ` only
    on LV. Anderson p. 223: "this pattern... is common in Doyayo." -/
def doyayoSplitDoubled : AVCDatum :=
  { language := "Doyayo"
  , form := Doyayo.AuxiliaryVerbs.splitDoubledForm
  , inflPattern := .splitDoubled
  , distribution := some Doyayo.AuxiliaryVerbs.splitDoubledDistribution
  , gloss := Doyayo.AuxiliaryVerbs.splitDoubledGloss }

/-- Gorum (doubled): subject + TAM on both AUX and LV.
    Form derived from `Gorum.AuxiliaryVerbs`. -/
def gorum : AVCDatum :=
  { language := "Gorum"
  , form := Gorum.AuxiliaryVerbs.form
  , inflPattern := .doubled
  , distribution := some Gorum.AuxiliaryVerbs.inflDistribution
  , gloss := Gorum.AuxiliaryVerbs.gloss }

/-- Jakaltek (split): absolutive on AUX, ergative on LV.
    Form derived from `Jakaltek.AuxiliaryVerbs`. -/
def jakaltek : AVCDatum :=
  { language := "Jakaltek"
  , form := Jakaltek.AuxiliaryVerbs.form
  , inflPattern := .split
  , distribution := some Jakaltek.AuxiliaryVerbs.inflDistribution
  , gloss := Jakaltek.AuxiliaryVerbs.gloss }

/-- Pipil split/doubled (Anderson Ch 5 ex. 133b, p. 224).
    *n-yu ni-mitsin-ilwitia* 'I'm going to show you'. Subject `1`
    doubly marked (`n-` on AUX, `ni-` on LV); object `-mitsin-`
    only on LV. AUX root *yu* lexically encodes prospective TAM.
    Anderson p. 224: "Subjects are doubly marked... while objects
    occur only on lexical verbs." -/
def pipilSplitDoubled : AVCDatum :=
  { language := "Pipil"
  , form := Pipil.AuxiliaryVerbs.splitDoubledForm
  , inflPattern := .splitDoubled
  , distribution := some Pipil.AuxiliaryVerbs.splitDoubledDistribution
  , gloss := Pipil.AuxiliaryVerbs.splitDoubledGloss }

/-- Pipil lex-headed (Anderson ch. 3 ex. 49, p. 130; Campbell 1985: 139).
    *weli ni-nehnemi wehka* 'CAP 1-walk far' 'I can walk far'.
    AUX *weli* uninflected; LV carries subject agreement. Anderson's
    fn. 6 (p. 221) separately documents lex-headed/split-doubled
    variation in the Pipil *progressive* — a different AVC from
    this capability construction. -/
def pipilLexHeaded : AVCDatum :=
  { language := "Pipil"
  , form := Pipil.AuxiliaryVerbs.lexHeadedForm
  , inflPattern := .lexHeaded
  , distribution := some Pipil.AuxiliaryVerbs.lexHeadedDistribution
  , gloss := Pipil.AuxiliaryVerbs.lexHeadedGloss }

/-- Finnish negative auxiliary *ei* (split): person/number on aux,
    TAM on lexical verb (connegative form). Anderson §1.7.2 (p. 33-34)
    presents negative auxiliaries as a family-level Uralic trait
    (with connegative-marked LV, exx. 44-48) and, across other
    families, as spanning multiple AVC patterns — Udihe and Neyo
    aux-headed, Kokota split, Kwerba lex-headed, 'Iipay doubled.
    Finnish *ei* itself is
    not classified by Anderson in §1.7.2 with a specific pattern label;
    the split classification here follows [karlsson-2017] §19.5
    where the connegative suffix on the LV is the load-bearing diagnostic.
    The split nature derives from `Finnish.Negation.finnishNegDistribution`:
    the negative auxiliary hosts negation, tense, and agreement, while
    the lexical verb retains stem and aspect.
    The 1sg neg-aux form derives from `negParadigm`; see the
    `finnish_1sg_form_eq` witness lemma for the strong pinning of
    the form-construction. Gloss style follows Anderson's Uralic
    convention (`Neg-1 read-conneg`). -/
def finnish : AVCDatum :=
  { language := "Finnish"
  , form := match Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg") with
    | some f => f.form ++ " lue"
    | none => "en lue"
  , inflPattern := .split
  , distribution := some Finnish.Negation.finnishNegDistribution
  , gloss := "Neg-1 read-conneg" }

/-- Hemba split/doubled: subject doubled on both AUX and LV; tense
    on AUX only; mood on LV only. Form derived from
    `Hemba.AuxiliaryVerbs`. -/
def hemba : AVCDatum :=
  { language := "Hemba"
  , form := Hemba.AuxiliaryVerbs.form
  , inflPattern := .splitDoubled
  , distribution := some Hemba.AuxiliaryVerbs.inflDistribution
  , gloss := Hemba.AuxiliaryVerbs.gloss }

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
    doyayo.form = Doyayo.AuxiliaryVerbs.lexHeadedForm := rfl
theorem doyayoSplitDoubled_form_from_fragment :
    doyayoSplitDoubled.form = Doyayo.AuxiliaryVerbs.splitDoubledForm := rfl
theorem gorum_form_from_fragment :
    gorum.form = Gorum.AuxiliaryVerbs.form := rfl
theorem jakaltek_form_from_fragment :
    jakaltek.form = Jakaltek.AuxiliaryVerbs.form := rfl
theorem pipilSplitDoubled_form_from_fragment :
    pipilSplitDoubled.form = Pipil.AuxiliaryVerbs.splitDoubledForm := rfl
theorem pipilLexHeaded_form_from_fragment :
    pipilLexHeaded.form = Pipil.AuxiliaryVerbs.lexHeadedForm := rfl
theorem hemba_form_from_fragment :
    hemba.form = Hemba.AuxiliaryVerbs.form := rfl

theorem doyayo_dist_from_fragment :
    doyayo.distribution = some Doyayo.AuxiliaryVerbs.lexHeadedDistribution := rfl
theorem doyayoSplitDoubled_dist_from_fragment :
    doyayoSplitDoubled.distribution =
      some Doyayo.AuxiliaryVerbs.splitDoubledDistribution := rfl
theorem gorum_dist_from_fragment :
    gorum.distribution = some Gorum.AuxiliaryVerbs.inflDistribution := rfl
theorem jakaltek_dist_from_fragment :
    jakaltek.distribution = some Jakaltek.AuxiliaryVerbs.inflDistribution := rfl
theorem pipilSplitDoubled_dist_from_fragment :
    pipilSplitDoubled.distribution =
      some Pipil.AuxiliaryVerbs.splitDoubledDistribution := rfl
theorem pipilLexHeaded_dist_from_fragment :
    pipilLexHeaded.distribution =
      some Pipil.AuxiliaryVerbs.lexHeadedDistribution := rfl
theorem finnish_dist_from_fragment :
    finnish.distribution = some Finnish.Negation.finnishNegDistribution := rfl
theorem hemba_dist_from_fragment :
    hemba.distribution = some Hemba.AuxiliaryVerbs.inflDistribution := rfl

/-! ## Finnish form construction grounding

The Finnish form construction uses `negParadigm.find?`, which is
`Option`-typed. The fallback `| none => "en lue"` was historically
chosen to coincide with the success-branch result, making
`finnish.form = "en lue"` pass by `rfl` even when the lookup
*would* return `none`. The witness theorem below grounds the
construction in the actual paradigm content. -/

/-- The Finnish 1sg negative-auxiliary entry exists in `negParadigm`. -/
theorem finnish_1sg_in_paradigm :
    (Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg")).isSome = true := by
  decide

/-- Strong pinning: the 1sg paradigm entry's form is exactly `"en"`.
    Together with `finnish_1sg_in_paradigm`, this pins `finnish.form`
    to the Fragment's actual paradigm content. A future change to
    `negParadigm` that altered the 1sg form (or removed the entry
    entirely) would break this theorem; the dead-branch `| none =>
    "en lue"` fallback in `finnish.form` cannot mask the change. -/
theorem finnish_1sg_form_eq :
    (Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg")).map (·.form)
      = some "en" := by
  decide

/-- The Finnish form is the 1sg `negParadigm` entry's form
    concatenated with `" lue"`. -/
theorem finnish_form_from_paradigm : finnish.form = "en lue" := rfl

/-! ## Connection to Finnish Fragment -/

/-- The Finnish negative auxiliary construction is a split AVC: the
    auxiliary hosts some inflectional categories and the lexical
    verb hosts others, with neither element hosting all categories. -/
theorem finnish_split_from_fragment :
    let dist := Finnish.Negation.finnishNegDistribution
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
    let dist := Gorum.AuxiliaryVerbs.inflDistribution
    dist.onAux == dist.onLex = true := by decide

/-- In Doyayo's lex-headed AVC, the auxiliary hosts ONLY tonal subject
    agreement (per Anderson p. 120), and the LV carries TAM. -/
theorem doyayo_lexHeaded_aux_agreement_only :
    Doyayo.AuxiliaryVerbs.lexHeadedDistribution.onAux = [.agreement .subj] ∧
    Doyayo.AuxiliaryVerbs.lexHeadedDistribution.onLex = [.tense] := by
  exact ⟨rfl, rfl⟩

/-- **Anderson Ch 5 §5.2 payoff (Doyayo)**: subject agreement is
    doubled across AUX and LV; object agreement appears on LV only.
    Now Lean-checkable directly via `Controller`-typed `.agreement`,
    rather than via the fragile list-length encoding the 0.230.578
    workaround used. -/
theorem doyayo_splitDoubled_subj_doubled_obj_lex_only :
    let dist := Doyayo.AuxiliaryVerbs.splitDoubledDistribution
    dist.onAux.contains (.agreement .subj) = true ∧
    dist.onLex.contains (.agreement .subj) = true ∧
    dist.onLex.contains (.agreement .obj) = true ∧
    dist.onAux.contains (.agreement .obj) = false := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **Anderson Ch 5 §5.2 payoff (Pipil)**: same generalization as
    Doyayo — subject doubled across AUX and LV, object on LV only.
    The AUX root *yu* itself encodes TAM lexically (no separate
    `.tense` morpheme on AUX). -/
theorem pipil_splitDoubled_subj_doubled_obj_lex_only :
    let dist := Pipil.AuxiliaryVerbs.splitDoubledDistribution
    dist.onAux.contains (.agreement .subj) = true ∧
    dist.onLex.contains (.agreement .subj) = true ∧
    dist.onLex.contains (.agreement .obj) = true ∧
    dist.onAux.contains (.agreement .obj) = false := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- In Pipil's lex-headed AVC, the auxiliary hosts no inflection. -/
theorem pipil_lexHeaded_aux_empty :
    Pipil.AuxiliaryVerbs.lexHeadedDistribution.onAux = [] := rfl

/-- In Finnish's split AVC, aux and lex host disjoint category types.
    (`.stem` on the lex side is a base, not an inflectional overlap.) -/
theorem finnish_split_disjoint :
    let dist := Finnish.Negation.finnishNegDistribution
    dist.onAux.all (fun c => !dist.onLex.contains c) = true := by decide

/-- **Anderson Ch 5 abs/erg payoff (Jakaltek)**: with role-typed
    agreement, the absolutive-on-AUX / ergative-on-LV split is now
    a category-level distinction (`.agreement .obj` vs `.agreement .subj`),
    not just a within-category meta-comment. -/
theorem jakaltek_abs_on_aux_erg_on_lex :
    let dist := Jakaltek.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains (.agreement .obj) = true ∧
    dist.onLex.contains (.agreement .subj) = true ∧
    dist.onAux.contains (.agreement .subj) = false ∧
    dist.onLex.contains (.agreement .obj) = false := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- In Hemba's split/doubled AVC, subject agreement is doubled (on both
    elements), tense is AUX-only, mood is LV-only. No object agreement
    in this construction. -/
theorem hemba_splitDoubled_agreement_doubled :
    let dist := Hemba.AuxiliaryVerbs.inflDistribution
    dist.onAux.contains (.agreement .subj) = true ∧
    dist.onLex.contains (.agreement .subj) = true ∧
    dist.onAux.contains .tense = true ∧
    dist.onLex.contains .tense = false ∧
    dist.onAux.contains .mood = false ∧
    dist.onLex.contains .mood = true := by
  exact ⟨by decide, by decide, by decide,
         by decide, by decide, by decide⟩

/-! ## Dual headedness

Anderson distinguishes three notions of head — inflectional,
phrasal/syntactic, and semantic (§1.4, pp. 22-24; Table 3.1 on
p. 116 tabulates the assignment for the lex-headed pattern). The
semantic head (content provider) is always the lexical verb
(Anderson p. 23: "It is the lexical verb"); the inflectional
host varies by pattern. This mismatch is what
makes AVCs typologically distinctive. -/

/-- The semantic head and inflectional host coincide only in
    lex-headed AVCs. In all other patterns they diverge: the
    semantic head is always the lexical verb, but inflection
    may sit on the auxiliary (or on both elements). -/
theorem heads_coincide_iff_lexHeaded (p : InflPattern) :
    (p.semanticHead == p.inflHost) = (p == .lexHeaded) := by
  cases p <;> rfl

/-! ## Negative auxiliaries as AVCs

[anderson-2006] §1.7.2 (p. 33-34) treats negative auxiliaries
across multiple AVC patterns: aux-headed in Udihe, Neyo; split in
Kokota; lex-headed in Kwerba; doubled in 'Iipay. The example rows
live in `Data/Examples/Anderson2006.json` (Komi (47a,b), Udihe (49),
Kwerba (52a,b), all verified against the book); each row's
`infl_pattern` feature records the book's classification where it
states one. The NegStrategy → InflPattern mapping lives in
`Typology/Negation.lean`: `NegStrategy.expectedInflPattern` encodes
the most common verbal-negator → aux-headed mapping, and the Kwerba
rows witness below that it is a tendency, not a law. -/

/-- Value of a row's `paperFeatures` key, if present. -/
private def featureOf (row : Data.Examples.LinguisticExample)
    (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- Udihe (49) *bi ei-mi sa:* is classified aux-headed by Anderson,
    and the strategy-level projection expects exactly that. -/
theorem udihe_negVerb_expects_auxHeaded :
    featureOf Examples.udihe_neg "infl_pattern" = some "auxHeaded" ∧
    NegStrategy.negVerb.expectedInflPattern = some .auxHeaded :=
  ⟨rfl, rfl⟩

/-- Kwerba (52a,b) shows a negative auxiliary in a *lex-headed* AVC
    (the lexical verb hosts the inflection), so the aux-headed
    expectation of `NegStrategy.expectedInflPattern` is defeasible —
    Anderson's own four-pattern list is the counterexample source. -/
theorem kwerba_negVerb_lexHeaded_counterexample :
    featureOf Examples.kwerba_neg_fut "infl_pattern" = some "lexHeaded" ∧
    NegStrategy.negVerb.expectedInflPattern ≠ some .lexHeaded :=
  ⟨rfl, by decide⟩

/-- The Komi tense alternation (47a,b) sits entirely on the negative
    auxiliary: same lexical verb token, different auxiliary form. -/
theorem komi_tense_on_aux :
    Examples.komi_neg_pres.glossedTokens.getLast? =
      Examples.komi_neg_past.glossedTokens.getLast? ∧
    Examples.komi_neg_pres.primaryText ≠ Examples.komi_neg_past.primaryText :=
  ⟨rfl, by decide⟩

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

Be/have auxiliary selection (`Typology/AuxiliaryVerbs.lean`) operates
within aux-headed AVCs: the question of *which* auxiliary appears
presupposes the auxiliary hosts inflection. [sorace-2000]'s
sister study `Studies/Sorace2000.lean` provides
`vendlerClassToTypicalTransitivity`; the quantified composition
with `canonicalSelection` is given below.

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

/-- Quantified Sorace bridge: composing `vendlerClassToTypicalTransitivity`
    with `canonicalSelection` yields `.be` exactly for achievements,
    `.have` elsewhere (Italian *è arrivato* instantiates the
    achievement case). Exposes the composition
    `canonicalSelection ∘ vendlerClassToTypicalTransitivity`
    as a single theorem rather than a hand-picked tuple. Falsifiable
    by changing either lookup. -/
theorem sorace_canonical_chain (v : Features.VendlerClass) :
    canonicalSelection
      (Sorace2000.vendlerClassToTypicalTransitivity v) =
        match v with
        | .achievement => .be
        | _ => .have := by
  cases v <;> rfl

/-! ## Cross-framework: Miestamo 2005 (negation morpheme classification)

[miestamo-2005] classifies negation strategies by morpheme
type (`NegMorphemeType`: `.auxVerb`, `.affix`, `.particle`, ...);
[anderson-2006] via [heine-1993]'s grammaticalization
framework places verbal negators on the cline at `.auxiliary` and
non-verbal negators off the cline (Anderson §1.7.2 covers only
verbal negators). The two frameworks classify by independently-
motivated criteria but, for the strategies linglib's
`NegStrategy` enum exposes, AGREE on which strategies are
"verbal": Anderson's `.toGramStage = some .auxiliary` is exactly
Miestamo's `.toNegMorphemeType = .auxVerb`.

Composition with [miestamo-2005]'s
`verbal_constructional_always_derived` (in
`Linglib/Studies/Miestamo2005.lean`) then
yields: any `NegStrategy` Anderson places at the auxiliary cline
stage, in any Miestamo datum showing constructional asymmetry,
has its asymmetry classified as `.derived` rather than
`.independent` — a falsifiable empirical prediction whose chain
runs Anderson's cline → Miestamo's morpheme type → Miestamo's
asymmetry source.

The earlier `anderson_miestamo_agree_on_neg_morphology` theorem
in this slot (0.230.573) was a stapled conjunction of three
independent facts; the meta-audit at 0.230.576 replaced it with
the quantified-equivalence shape below. -/

/-- Cross-framework equivalence: Anderson's grammaticalization-cline
    placement at `.auxiliary` and Miestamo's morpheme-type
    classification as `.auxVerb` partition the `NegStrategy` enum
    *identically*. Both frameworks classify exactly `.negVerb`
    (Finnish *ei*-style inflecting negators) as the verbal subtype.
    Falsifiable by changing either projection: a future split of
    `NegStrategy.negVerb` into Miestamo-style auxVerb-vs-doubleNeg
    subtypes would break this without breaking either projection
    individually. -/
theorem auxiliary_stage_iff_aux_verb_morpheme (s : NegStrategy) :
    s.toGramStage = some .auxiliary ↔ s.toNegMorphemeType = .auxVerb := by
  cases s <;> decide

end Anderson2006
