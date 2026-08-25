import Mathlib.Data.Finset.Basic
import Linglib.Syntax.Category.Auxiliary.Constructions
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
import Linglib.Fragments.Finnish.Negation
import Linglib.Syntax.Negation
import Linglib.Studies.Sorace2000
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

/-! ### Where the inflection is marked

Possessing a distribution is neutral on periphrasis-hood
([spencer-popova-2015] pp. 200, 204); the data is the raw material for
the distributed-exponence criterion. -/

open Morphology (MorphCategory)

/-- Which inflectional categories each element of an auxiliary verb
construction carries. The category vocabulary is `MorphCategory`
([bybee-1985]'s relevance hierarchy); the coarse question of which element
is the inflectional head is `InflPattern.inflHost`. -/
structure InflectionalMarking where
  onAux : Finset MorphCategory
  onLex : Finset MorphCategory
  deriving DecidableEq

/-- Doyayo lex-headed (`Examples.doyayo_lexheaded`): the auxiliary
"partially encodes person of the subject through the tone" (p. 120), the
lexical verb carries TAM. -/
def doyayoLexHeaded : InflectionalMarking :=
  { onAux := {.agreement .subj}, onLex := {.tense} }

/-- Doyayo split/doubled (`Examples.doyayo_splitdoubled`): the subject is
marked on both elements, the object only on the lexical verb. -/
def doyayoSplitDoubled : InflectionalMarking :=
  { onAux := {.agreement .subj}
  , onLex := {.agreement .subj, .agreement .obj} }

/-- Gorum doubled (`Examples.gorum_tiger`, `Examples.gorum_vigorously`):
subject agreement, tense and affectedness on both elements. -/
def gorumDoubled : InflectionalMarking :=
  { onAux := {.agreement .subj, .tense, .voice}
  , onLex := {.agreement .subj, .tense, .voice} }

/-- Hemba split/doubled (`Examples.hemba_progressive`): agreement on both
elements, tense on the auxiliary, mood on the lexical verb. -/
def hembaSplitDoubled : InflectionalMarking :=
  { onAux := {.agreement .subj, .tense}
  , onLex := {.agreement .subj, .mood} }

/-- Jakaltek split (`Examples.jakaltek_completive`): aspect and absolutive
agreement on the auxiliary, ergative agreement on the lexical verb. -/
def jakaltekSplit : InflectionalMarking :=
  { onAux := {.aspect, .agreement .obj}
  , onLex := {.agreement .subj} }

/-- Pipil lex-headed (`Examples.pipil_capability`): the capability
auxiliary *weli* is uninflected. -/
def pipilLexHeaded : InflectionalMarking :=
  { onAux := ∅, onLex := {.agreement .subj} }

/-- Pipil split/doubled (`Examples.pipil_progressive`): "Subjects are doubly
marked… while objects occur only on lexical verbs". The auxiliary root *yu*
carries prospective TAM lexically, so no tense morpheme sits on it. -/
def pipilSplitDoubled : InflectionalMarking :=
  { onAux := {.agreement .subj}
  , onLex := {.agreement .subj, .agreement .obj} }

/-- Finnish negative AVC, *en lue* 'I do not read': the negative auxiliary
hosts negation, tense and agreement, the main verb the stem and aspect
(through the connegative). [anderson-2006] §1.7.2 presents Uralic negative
auxiliaries with connegative-marked lexical verbs without assigning
Finnish a pattern label; the split reading follows [karlsson-2017] §19.5,
where the connegative suffix is the diagnostic. -/
def finnishNegative : InflectionalMarking :=
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

/-- The inflectional pattern Anderson assigns an example. -/
def parseInflPattern : String → Option InflPattern
  | "auxHeaded" => some .auxHeaded
  | "lexHeaded" => some .lexHeaded
  | "doubled" => some .doubled
  | "split" => some .split
  | "splitDoubled" => some .splitDoubled
  | _ => none

/-- The patterns Anderson's examples are classified as. -/
def attestedPatterns : List InflPattern :=
  Examples.all.filterMap fun e => (e.feature? "infl_pattern").bind parseInflPattern

/-- Anderson's examples instantiate every one of his five patterns. -/
theorem all_patterns_attested (p : InflPattern) : p ∈ attestedPatterns := by
  cases p <;> decide

/-- Chapter 5's generalization across the split/doubled languages: subject
agreement is doubled over both elements, while object agreement stays on
the lexical verb ("Subjects are doubly marked… while objects occur only on
lexical verbs", p. 224). -/
theorem splitDoubled_subj_doubled_obj_lex_only :
    ∀ d ∈ [doyayoSplitDoubled, pipilSplitDoubled],
      MorphCategory.agreement .subj ∈ d.onAux ∧
      MorphCategory.agreement .subj ∈ d.onLex ∧
      MorphCategory.agreement .obj ∈ d.onLex ∧
      MorphCategory.agreement .obj ∉ d.onAux := by decide

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

end Anderson2006
