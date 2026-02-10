import Linglib.Core.UD
import Linglib.Fragments.English.FunctionWords

/-!
# Auxiliary Verb Construction Typology (Anderson 2006)

Cross-linguistic classification of auxiliary verb constructions (AVCs) based on
how inflection distributes between auxiliary and lexical verb. Anderson's core
insight: the **semantic head is always the lexical verb**, but the
**inflectional host** varies across 5 macro-patterns.

## The Five Patterns

| Pattern | Infl Host | Example | LV Form |
|---------|-----------|---------|---------|
| Aux-headed | AUX | English *will go* | nonfinite |
| Lex-headed | LEX | Doyayo *mà jâ* | finite |
| Doubled | AUX+LEX | Gorum *kidis-t-an-a* | both agree |
| Split | AUX or LEX | Jakaltek *x-Ø-ach w-ilwi* | person on one, TAM on other |
| Split/doubled | AUX+LEX (split) | Pipil *ni-k-miktia-ya* | mixed |

## References

- Anderson, G. D. S. (2006). Auxiliary Verb Constructions. OUP.
- Huddleston, R. (1976). Some theoretical issues in the description of the
  English verb. *Lingua* 40:331-383.
-/

namespace Phenomena.AuxiliaryVerbs.Typology

/-! ## Core types -/

/-- Anderson's 5-way inflectional pattern typology for AVCs. -/
inductive InflPattern where
  /-- Inflection hosted on auxiliary; lexical verb is nonfinite.
      E.g., English *will go*, French *va manger*. -/
  | auxHeaded
  /-- Inflection hosted on lexical verb; auxiliary is grammaticalized.
      E.g., Doyayo *mà jâ* (AUX uninflected, LV carries TAM). -/
  | lexHeaded
  /-- Inflection appears on both auxiliary and lexical verb.
      E.g., Gorum *kidis-t-an-a* (agreement on both). -/
  | doubled
  /-- Inflection split between AUX and LV (different features on each).
      E.g., Jakaltek (person on AUX, TAM on LV). -/
  | split
  /-- Combination of split and doubled.
      E.g., Pipil *ni-k-miktia-ya* (subject on both, TAM split). -/
  | splitDoubled
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Which element(s) of an AVC bear a given property. -/
inductive AVCElement where
  | aux   -- auxiliary only
  | lex   -- lexical verb only
  | both  -- both auxiliary and lexical verb
  deriving DecidableEq, Repr, BEq

/-! ## Key functions -/

/-- The semantic head is always the lexical verb (Anderson's invariant). -/
def InflPattern.semanticHead (_ : InflPattern) : AVCElement := .lex

/-- Which element hosts inflection in each pattern. -/
def InflPattern.inflHost : InflPattern → AVCElement
  | .auxHeaded    => .aux
  | .lexHeaded    => .lex
  | .doubled      => .both
  | .split        => .both
  | .splitDoubled => .both

/-- Whether the inflectional head equals the phrasal head.
    In aux-headed and doubled patterns, inflection is on AUX (= phrasal head).
    In lex-headed, split, splitDoubled, they dissociate. -/
def InflPattern.inflEqualsPhrasal : InflPattern → Bool
  | .auxHeaded    => true
  | .doubled      => true
  | .lexHeaded    => false
  | .split        => false
  | .splitDoubled => false

/-! ## Cross-linguistic data -/

/-- A cross-linguistic AVC datum. -/
structure AVCDatum where
  language : String
  form : String
  inflPattern : InflPattern
  gloss : String := ""
  deriving Repr, BEq

/-- English *will go* — aux-headed (AUX carries tense, LV is bare infinitive). -/
def english : AVCDatum :=
  { language := "English"
  , form := "will go"
  , inflPattern := .auxHeaded
  , gloss := "FUT go.INF" }

/-- Doyayo *mà jâ* — lex-headed (AUX is bare particle, LV inflects). -/
def doyayo : AVCDatum :=
  { language := "Doyayo"
  , form := "mà jâ"
  , inflPattern := .lexHeaded
  , gloss := "AUX come.TAM" }

/-- Gorum — doubled (agreement copied onto both AUX and LV). -/
def gorum : AVCDatum :=
  { language := "Gorum"
  , form := "kidis-t-an-a"
  , inflPattern := .doubled
  , gloss := "AUX-AGR LV-AGR" }

/-- Jakaltek — split (person on AUX, TAM on LV). -/
def jakaltek : AVCDatum :=
  { language := "Jakaltek"
  , form := "x-Ø-ach w-ilwi"
  , inflPattern := .split
  , gloss := "ASP-3ABS-2ERG 1ERG-see" }

/-- Pipil — split/doubled (subject marking doubled, TAM on AUX only). -/
def pipil : AVCDatum :=
  { language := "Pipil"
  , form := "ni-k-miktia-ya"
  , inflPattern := .splitDoubled
  , gloss := "1SG-3SG-kill-IPFV" }

def allData : List AVCDatum := [english, doyayo, gorum, jakaltek, pipil]

/-! ## Invariant theorems -/

/-- Anderson's key insight: the semantic head is always the lexical verb,
    regardless of inflectional pattern. -/
theorem semantic_head_always_lex (p : InflPattern) :
    p.semanticHead = .lex := rfl

/-- In aux-headed AVCs, inflectional and phrasal headedness align. -/
theorem auxHeaded_no_dissociation :
    InflPattern.auxHeaded.inflEqualsPhrasal = true := rfl

/-- In lex-headed AVCs, inflectional and phrasal headedness dissociate. -/
theorem lexHeaded_dissociation :
    InflPattern.lexHeaded.inflEqualsPhrasal = false := rfl

/-! ## Bridge to UD -/

/-- Expected verb form of the lexical verb in each AVC pattern.
    Aux-headed: LV is nonfinite (infinitive/participle).
    Lex-headed: LV is finite (carries TAM).
    Doubled/split/splitDoubled: LV is finite (carries at least some inflection). -/
def InflPattern.lvVerbForm : InflPattern → UD.VerbForm
  | .auxHeaded    => .Inf
  | .lexHeaded    => .Fin
  | .doubled      => .Fin
  | .split        => .Fin
  | .splitDoubled => .Fin

/-- In aux-headed AVCs, the lexical verb is nonfinite. -/
theorem auxHeaded_lv_nonfinite :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

/-- In lex-headed AVCs, the lexical verb is finite. -/
theorem lexHeaded_lv_finite :
    InflPattern.lexHeaded.lvVerbForm = UD.VerbForm.Fin := rfl

/-! ## Bridge to FunctionWords -/
open Fragments.English.FunctionWords in
/-- English modals are aux-headed: they take AuxType.modal and the LV is bare. -/
theorem english_modals_are_aux_type :
    Fragments.English.FunctionWords.can.auxType = AuxType.modal := rfl

/-! ## Per-datum verification -/

theorem english_is_auxHeaded : english.inflPattern = .auxHeaded := rfl
theorem doyayo_is_lexHeaded : doyayo.inflPattern = .lexHeaded := rfl
theorem gorum_is_doubled : gorum.inflPattern = .doubled := rfl
theorem jakaltek_is_split : jakaltek.inflPattern = .split := rfl
theorem pipil_is_splitDoubled : pipil.inflPattern = .splitDoubled := rfl

end Phenomena.AuxiliaryVerbs.Typology
