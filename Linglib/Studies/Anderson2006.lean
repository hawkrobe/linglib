import Mathlib.Data.Finset.Basic
import Linglib.Syntax.Category.Auxiliary.Constructions
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
import Linglib.Fragments.Finnish.Negation
import Linglib.Syntax.Negation
import Linglib.Studies.Sorace2000
import Linglib.Studies.Miestamo2005
import Linglib.Features.Grammaticalization
import Linglib.Features.Aktionsart
import Linglib.Data.Examples.Anderson2006

/-!
# Anderson (2006): Auxiliary Verb Constructions

An auxiliary verb construction pairs an auxiliary with a lexical verb, and
languages differ in where the inflection lands: on the auxiliary (English
*have eaten*), on the lexical verb (Doyayo), on both (Gorum), split between
them (Jakaltek puts absolutive agreement on the auxiliary and ergative on
the lexical verb), or split with some categories doubled (Pipil, Hemba).
The lexical verb stays the semantic head throughout, and that mismatch
between where meaning sits and where inflection sits is what makes AVCs
typologically distinctive. Chapter 7 places the constructions on
[heine-1993]'s grammaticalization cline.

Formalized here: nine datums across seven languages covering all five
patterns, each recording which categories the auxiliary and the lexical
verb host; the chapter 5 generalization that subject agreement doubles
while object agreement stays on the lexical verb; negative auxiliaries as
AVCs, with Kwerba as the counterexample to the verbal-negator
tendency; and the compositions with [sorace-2000]'s auxiliary selection
and [miestamo-2005]'s morpheme typology.

## References

* [anderson-2006], §1.4, §1.7.2, chs. 2–5, ch. 7
* [heine-1993], ch. 3
* [karlsson-2017], §19.5
-/
namespace Anderson2006

open AuxiliaryVerbs
open ArgumentStructure.AuxiliarySelection
open Syntax.Negation (Strategy)

/-! ### Inflectional distribution

Possessing a distribution is neutral on periphrasis-hood
([spencer-popova-2015] pp. 200, 204); the data is the raw material for
the distributed-exponence criterion. -/

open Morphology (MorphCategory)

/-- Which inflectional categories each element of an auxiliary verb
construction hosts. The category vocabulary is `MorphCategory`
([bybee-1985]'s relevance hierarchy); which pattern a distribution
realizes is `InflPattern`. -/
structure InflDistribution where
  onAux : Finset MorphCategory
  onLex : Finset MorphCategory
  deriving DecidableEq

/-- Doyayo lex-headed (ch. 3 ex. 15a, p. 121), *mi¹ (gi²) kpel¹-ko¹* 'I'm
going to pour': the auxiliary "partially encodes person of the subject
through the tone" (p. 120), the lexical verb carries TAM. -/
def doyayoLexHeadedDist : InflDistribution :=
  { onAux := {.agreement .subj}, onLex := {.tense} }

/-- Doyayo split/doubled (ch. 5 ex. 129, p. 223), *hi¹-za¹ hi¹-zaa¹³
hi¹-lɔ-mɔ* 'they might come bite you': the subject is marked on both
elements, the object only on the lexical verb. -/
def doyayoSplitDoubledDist : InflDistribution :=
  { onAux := {.agreement .subj}
  , onLex := {.agreement .subj, .agreement .obj} }

/-- Gorum doubled: subject agreement, tense and affectedness on both
elements. -/
def gorumDist : InflDistribution :=
  { onAux := {.agreement .subj, .tense, .voice}
  , onLex := {.agreement .subj, .tense, .voice} }

/-- Hemba split/doubled: agreement on both elements, tense on the
auxiliary, mood on the lexical verb. -/
def hembaDist : InflDistribution :=
  { onAux := {.agreement .subj, .tense}
  , onLex := {.agreement .subj, .mood} }

/-- Jakaltek split: aspect and absolutive agreement on the auxiliary,
ergative agreement on the lexical verb. -/
def jakaltekDist : InflDistribution :=
  { onAux := {.aspect, .agreement .obj}
  , onLex := {.agreement .subj} }

/-- Pipil lex-headed (ch. 3 ex. 49, p. 130; Campbell 1985: 139), *weli
ni-nehnemi wehka* 'I can walk far': the auxiliary *weli* is uninflected. -/
def pipilLexHeadedDist : InflDistribution :=
  { onAux := ∅, onLex := {.agreement .subj} }

/-- Pipil split/doubled (ch. 5 ex. 133b, p. 224), *n-yu ni-mitsin-ilwitia*
'I'm going to show you': "Subjects are doubly marked… while objects occur
only on lexical verbs". The auxiliary root *yu* carries prospective TAM
lexically, so no tense morpheme sits on it. -/
def pipilSplitDoubledDist : InflDistribution :=
  { onAux := {.agreement .subj}
  , onLex := {.agreement .subj, .agreement .obj} }

/-- Finnish negative AVC, *en lue* 'I do not read': the negative auxiliary
hosts negation, tense and agreement, the main verb the stem and aspect
(through the connegative). [anderson-2006] §1.7.2 presents Uralic negative
auxiliaries with connegative-marked lexical verbs without assigning
Finnish a pattern label; the split reading follows [karlsson-2017] §19.5,
where the connegative suffix is the diagnostic. -/
def finnishNegDist : InflDistribution :=
  { onAux := {.negation, .tense, .agreement .subj}
  , onLex := {.stem, .aspect} }

/-- The 1sg negative auxiliary with the connegative *lue*, read out of
`Finnish.Negation.negParadigm`; gloss `Neg-1 read-conneg`. -/
def finnishNegForm : String :=
  (Finnish.Negation.negParadigm.find?
    (fun f => f.person == 1 && f.number == "sg")).elim "" (·.form ++ " lue")

/-- The 1sg paradigm entry builds the form: a change to that entry leaves
`finnishNegForm` empty and breaks this. -/
theorem finnishNegForm_eq : finnishNegForm = "en lue" := rfl

/-- The Finnish distribution is consistent with [miestamo-2005]'s
    constructional A/Fin coding: categories split across the negative
    auxiliary and the main verb. -/
theorem finnish_split_confirms_constructional :
    finnishNegDist.onAux ≠ ∅ ∧ finnishNegDist.onLex ≠ ∅ ∧
    Miestamo2005.finnish.asymmetryDimensions.contains .constructional := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### The Finnish negative AVC -/

/-- The Finnish negative auxiliary construction is a split AVC: the
    auxiliary hosts some inflectional categories and the lexical
    verb hosts others, with neither element hosting all categories. -/
theorem finnish_split_from_fragment :
    finnishNegDist.onAux ≠ ∅ ∧ finnishNegDist.onLex ≠ ∅ := ⟨by decide, by decide⟩

/-! ### Where the inflection sits -/

/-- Doubled: the two elements host exactly the same categories. -/
theorem gorum_doubled_same_categories : gorumDist.onAux = gorumDist.onLex := by decide

/-- In Doyayo's lex-headed AVC, the auxiliary hosts ONLY tonal subject
    agreement (per Anderson p. 120), and the LV carries TAM. -/
theorem doyayo_lexHeaded_aux_agreement_only :
    doyayoLexHeadedDist.onAux = {.agreement .subj} ∧
    doyayoLexHeadedDist.onLex = {.tense} := ⟨rfl, rfl⟩

/-- Chapter 5 (Doyayo): subject agreement is doubled across auxiliary
    and lexical verb, while object agreement appears on the lexical verb
    only. -/
theorem doyayo_splitDoubled_subj_doubled_obj_lex_only :
    let dist := doyayoSplitDoubledDist
    MorphCategory.agreement .subj ∈ dist.onAux ∧
    MorphCategory.agreement .subj ∈ dist.onLex ∧
    MorphCategory.agreement .obj ∈ dist.onLex ∧
    MorphCategory.agreement .obj ∉ dist.onAux := by decide

/-- Chapter 5 (Pipil): the same generalization as Doyayo. The auxiliary
    root *yu* encodes TAM lexically, so no `.tense` morpheme sits on the
    auxiliary. -/
theorem pipil_splitDoubled_subj_doubled_obj_lex_only :
    let dist := pipilSplitDoubledDist
    MorphCategory.agreement .subj ∈ dist.onAux ∧
    MorphCategory.agreement .subj ∈ dist.onLex ∧
    MorphCategory.agreement .obj ∈ dist.onLex ∧
    MorphCategory.agreement .obj ∉ dist.onAux := by decide

/-- In Pipil's lex-headed AVC, the auxiliary hosts no inflection. -/
theorem pipil_lexHeaded_aux_empty : pipilLexHeadedDist.onAux = ∅ := rfl

/-- Split: the two elements host disjoint categories. (`.stem` on the
    lexical side is a base, not an inflectional overlap.) -/
theorem finnish_split_disjoint : Disjoint finnishNegDist.onAux finnishNegDist.onLex := by
  decide

/-- Chapter 5 (Jakaltek): absolutive agreement on the auxiliary,
    ergative on the lexical verb. -/
theorem jakaltek_abs_on_aux_erg_on_lex :
    let dist := jakaltekDist
    MorphCategory.agreement .obj ∈ dist.onAux ∧
    MorphCategory.agreement .subj ∈ dist.onLex ∧
    MorphCategory.agreement .subj ∉ dist.onAux ∧
    MorphCategory.agreement .obj ∉ dist.onLex := by decide

/-- In Hemba's split/doubled AVC, subject agreement is doubled (on both
    elements), tense is AUX-only, mood is LV-only. No object agreement
    in this construction. -/
theorem hemba_splitDoubled_agreement_doubled :
    let dist := hembaDist
    MorphCategory.agreement .subj ∈ dist.onAux ∧
    MorphCategory.agreement .subj ∈ dist.onLex ∧
    MorphCategory.tense ∈ dist.onAux ∧ MorphCategory.tense ∉ dist.onLex ∧
    MorphCategory.mood ∉ dist.onAux ∧ MorphCategory.mood ∈ dist.onLex := by decide

/-! ### Dual headedness

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

/-! ### Negative auxiliaries as AVCs

[anderson-2006] §1.7.2 (p. 33-34) treats negative auxiliaries
across multiple AVC patterns: aux-headed in Udihe, Neyo; split in
Kokota; lex-headed in Kwerba; doubled in 'Iipay. The example rows
live in `Data/Examples/Anderson2006.json` (Komi (47a,b), Udihe (49),
Kwerba (52a,b), all verified against the book); each row's
`infl_pattern` feature records the book's classification where it
states one. The Strategy → InflPattern mapping lives in
`Syntax/Negation.lean`: `Strategy.expectedInflPattern` encodes
the most common verbal-negator → aux-headed mapping, and the Kwerba
rows witness below that it is a tendency, not a law. -/

/-- Udihe (49) *bi ei-mi sa:* is classified aux-headed by Anderson,
    and the strategy-level projection expects exactly that. -/
theorem udihe_negVerb_expects_auxHeaded :
    Examples.udihe_neg.feature? "infl_pattern" = some "auxHeaded" ∧
    Strategy.negVerb.expectedInflPattern = some .auxHeaded :=
  ⟨rfl, rfl⟩

/-- Kwerba (52a,b) shows a negative auxiliary in a *lex-headed* AVC
    (the lexical verb hosts the inflection), so the aux-headed
    expectation of `Strategy.expectedInflPattern` is defeasible —
    Anderson's own four-pattern list is the counterexample source. -/
theorem kwerba_negVerb_lexHeaded_counterexample :
    Examples.kwerba_neg_fut.feature? "infl_pattern" = some "lexHeaded" ∧
    Strategy.negVerb.expectedInflPattern ≠ some .lexHeaded :=
  ⟨rfl, by decide⟩

/-- The Komi tense alternation (47a,b) sits entirely on the negative
    auxiliary: same lexical verb token, different auxiliary form. -/
theorem komi_tense_on_aux :
    Examples.komi_neg_pres.glossedTokens.getLast? =
      Examples.komi_neg_past.glossedTokens.getLast? ∧
    Examples.komi_neg_pres.primaryText ≠ Examples.komi_neg_past.primaryText :=
  ⟨rfl, by decide⟩

/-! ### Auxiliary selection

Be/have auxiliary selection (`Syntax/Category/Auxiliary/Constructions.lean`) operates
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

/-! ### Cross-framework: Miestamo's morpheme typology

[miestamo-2005] classifies negation strategies by morpheme
type (WALS Ch 112A: negative auxiliary verb, affix, particle, ...);
[anderson-2006] via [heine-1993]'s grammaticalization
framework places verbal negators on the cline at `.auxiliary` and
non-verbal negators off the cline (Anderson §1.7.2 covers only
verbal negators). The two frameworks classify by independently-
motivated criteria but, for the strategies linglib's
`Strategy` enum exposes, AGREE on which strategies are
"verbal": Anderson's `.toGramStage = some .auxiliary` is exactly
Miestamo's `.morphemeType = .negativeAuxiliaryVerb`.

Composition with [miestamo-2005]'s
`afin_verbal_implies_constructional` (in
`Linglib/Studies/Miestamo2005.lean`) then
yields: any `Strategy` Anderson places at the auxiliary cline
stage, in any Miestamo A/Fin datum, shows constructional
asymmetry — a falsifiable empirical prediction whose chain
runs Anderson's cline → Miestamo's morpheme type → Miestamo's
asymmetry dimension.
 -/

/-- Cross-framework equivalence: Anderson's grammaticalization-cline
    placement at `.auxiliary` and Miestamo's morpheme-type
    classification as `.auxVerb` partition the `Strategy` enum
    *identically*. Both frameworks classify exactly `.negVerb`
    (Finnish *ei*-style inflecting negators) as the verbal subtype.
    Falsifiable by changing either projection: a future split of
    `Strategy.negVerb` into Miestamo-style auxVerb-vs-doubleNeg
    subtypes would break this without breaking either projection
    individually. -/
theorem auxiliary_stage_iff_aux_verb_morpheme (s : Strategy) :
    s.toGramStage = some .auxiliary ↔ s.morphemeType = .negativeAuxiliaryVerb := by
  cases s <;> decide

end Anderson2006
