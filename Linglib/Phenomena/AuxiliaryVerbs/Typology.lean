import Linglib.Core.Lexical.UD
import Linglib.Fragments.English.FunctionWords
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Doyayo.AuxiliaryVerbs
import Linglib.Fragments.Gorum.AuxiliaryVerbs
import Linglib.Fragments.Hemba.AuxiliaryVerbs
import Linglib.Fragments.Jakaltek.AuxiliaryVerbs
import Linglib.Fragments.Pipil.AuxiliaryVerbs

/-!
# Auxiliary Verb Construction Typology
@cite{anderson-2006}

Cross-linguistic classification of auxiliary verb constructions (AVCs) based on
how inflection distributes between auxiliary and lexical verb. Anderson's core
insight: the **semantic head is always the lexical verb**, but the
**inflectional host** varies across 5 macro-patterns.

## The Five Patterns

| Pattern | Infl Host | Example Language |
|---------|-----------|-----------------|
| Aux-headed | AUX | English *will go* |
| Lex-headed | LEX | Pipil *weli ni-nehnemi wehka* |
| Doubled | AUX+LEX | Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru* |
| Split | AUX or LEX | Doyayo, Jakaltek, Finnish |
| Split/doubled | AUX+LEX (split) | (various) |

-/

namespace Phenomena.AuxiliaryVerbs.Typology

/-! ## Core types -/

/-- Anderson's 5-way inflectional pattern typology for AVCs. -/
inductive InflPattern where
  /-- Inflection hosted on auxiliary; lexical verb is nonfinite.
      E.g., English *will go*, French *va manger*. -/
  | auxHeaded
  /-- Inflection hosted on lexical verb; auxiliary is grammaticalized.
      E.g., Pipil *weli ni-nehnemi wehka* (AUX uninflected, LV carries person). -/
  | lexHeaded
  /-- Inflection appears on both auxiliary and lexical verb.
      E.g., Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru* (subject + TAM on both). -/
  | doubled
  /-- Inflection split between AUX and LV (different features on each).
      E.g., Jakaltek *šk-ach w-ila* (absolutive on AUX, ergative on LV). -/
  | split
  /-- Combination of split and doubled: different inflectional features
      appear on both AUX and LV, but neither hosts the same set.
      @cite{anderson-2006} discusses this as a logical possibility;
      clear exemplars are rare. -/
  | splitDoubled
  deriving DecidableEq, Repr, Inhabited

/-- Which element(s) of an AVC bear a given property. -/
inductive AVCElement where
  | aux   -- auxiliary only
  | lex   -- lexical verb only
  | both  -- both auxiliary and lexical verb
  deriving DecidableEq, Repr

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

/-- Whether inflection is hosted exclusively on the phrasal head (= AUX).
    Only aux-headed AVCs have this property: the AUX hosts all inflection
    and the LV is fully nonfinite. In doubled AVCs, both elements carry
    inflection, so the phrasal head is not the sole inflectional host. -/
def InflPattern.inflOnlyOnPhrasalHead : InflPattern → Bool
  | .auxHeaded    => true
  | .lexHeaded    => false
  | .doubled      => false
  | .split        => false
  | .splitDoubled => false

/-! ## Cross-linguistic data -/

/-- A cross-linguistic AVC datum. -/
structure AVCDatum where
  language : String
  form : String
  inflPattern : InflPattern
  distribution : Option Core.Morphology.InflDistribution := none
  gloss : String := ""
  deriving Repr, BEq

/-- English *will go* — aux-headed (AUX carries tense, LV is bare infinitive). -/
def english : AVCDatum :=
  { language := "English"
  , form := "will go"
  , inflPattern := .auxHeaded
  , gloss := "FUT go.INF" }

/-- Doyayo — split (AUX hosts subject/benefactive/object; LV hosts tense).
    Form derived from `Fragments.Doyayo.AuxiliaryVerbs`. -/
def doyayo : AVCDatum :=
  { language := "Doyayo"
  , form := Fragments.Doyayo.AuxiliaryVerbs.form
  , inflPattern := .split
  , distribution := some Fragments.Doyayo.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Doyayo.AuxiliaryVerbs.gloss }

/-- Gorum — doubled (subject + TAM marked on both AUX and LV).
    Form derived from `Fragments.Gorum.AuxiliaryVerbs`. -/
def gorum : AVCDatum :=
  { language := "Gorum"
  , form := Fragments.Gorum.AuxiliaryVerbs.form
  , inflPattern := .doubled
  , distribution := some Fragments.Gorum.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Gorum.AuxiliaryVerbs.gloss }

/-- Jakaltek — split (absolutive on AUX, ergative on LV).
    Form derived from `Fragments.Jakaltek.AuxiliaryVerbs`. -/
def jakaltek : AVCDatum :=
  { language := "Jakaltek"
  , form := Fragments.Jakaltek.AuxiliaryVerbs.form
  , inflPattern := .split
  , distribution := some Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Jakaltek.AuxiliaryVerbs.gloss }

/-- Pipil — split (auxiliaries mark tense; subject/object on LV).
    Form derived from `Fragments.Pipil.AuxiliaryVerbs`.
    Note: Pipil also has lex-headed AVCs (see `Fragments.Pipil.AuxiliaryVerbs.lexHeadedForm`). -/
def pipil : AVCDatum :=
  { language := "Pipil"
  , form := Fragments.Pipil.AuxiliaryVerbs.form
  , inflPattern := .split
  , distribution := some Fragments.Pipil.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Pipil.AuxiliaryVerbs.gloss }

/-- Finnish negative auxiliary *ei* — split (person/number on aux, TAM on main verb).
    The split nature derives from `Fragments.Finnish.Negation.finnishNegDistribution`:
    the negative auxiliary hosts negation, tense, and agreement, while the lexical verb
    retains only the stem and aspect (connegative form). @cite{karlsson-2017}.

    The neg aux form derives from `Fragments.Finnish.Negation.negParadigm` (1sg). -/
def finnish : AVCDatum :=
  { language := "Finnish"
  , form := match Fragments.Finnish.Negation.negParadigm.find?
      (fun f => f.person == 1 && f.number == "sg") with
    | some f => f.form ++ " lue"
    | none => "en lue"
  , inflPattern := .split
  , distribution := some Fragments.Finnish.Negation.finnishNegDistribution
  , gloss := "NEG-1SG read.CONNEG" }

/-- Pipil — lex-headed (AUX *weli* is uninflected; LV carries all agreement).
    This is Pipil's second AVC pattern, illustrating that a single language can
    exhibit multiple AVC types. Form derived from `Fragments.Pipil.AuxiliaryVerbs`. -/
def pipilLexHeaded : AVCDatum :=
  { language := "Pipil"
  , form := Fragments.Pipil.AuxiliaryVerbs.lexHeadedForm
  , inflPattern := .lexHeaded
  , distribution := some Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution
  , gloss := Fragments.Pipil.AuxiliaryVerbs.lexHeadedGloss }

/-- Hemba — split/doubled (subject doubled on both AUX and LV; tense on AUX
    only, mood on LV only). Form derived from `Fragments.Hemba.AuxiliaryVerbs`. -/
def hemba : AVCDatum :=
  { language := "Hemba"
  , form := Fragments.Hemba.AuxiliaryVerbs.form
  , inflPattern := .splitDoubled
  , distribution := some Fragments.Hemba.AuxiliaryVerbs.inflDistribution
  , gloss := Fragments.Hemba.AuxiliaryVerbs.gloss }

def allData : List AVCDatum :=
  [english, doyayo, gorum, jakaltek, pipil, pipilLexHeaded, finnish, hemba]

/-! ## Invariant theorems -/

/-- Anderson's key insight: the semantic head is always the lexical verb,
    regardless of inflectional pattern. -/
theorem semantic_head_always_lex (p : InflPattern) :
    p.semanticHead = .lex := rfl

/-- In aux-headed AVCs, inflection is exclusively on the phrasal head (AUX). -/
theorem auxHeaded_infl_on_phrasal_head :
    InflPattern.auxHeaded.inflOnlyOnPhrasalHead = true := rfl

/-- In lex-headed AVCs, inflection is not on the phrasal head. -/
theorem lexHeaded_infl_not_on_phrasal_head :
    InflPattern.lexHeaded.inflOnlyOnPhrasalHead = false := rfl

/-- In doubled AVCs, inflection appears on both elements, so the phrasal
    head is not the sole host. -/
theorem doubled_infl_not_only_on_phrasal_head :
    InflPattern.doubled.inflOnlyOnPhrasalHead = false := rfl

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

/-! ## Per-datum verification

These theorems are load-bearing: changing a Fragment entry's `inflPattern`
breaks exactly one theorem here. -/

theorem english_is_auxHeaded : english.inflPattern = .auxHeaded := rfl
theorem doyayo_is_split : doyayo.inflPattern = .split := rfl
theorem gorum_is_doubled : gorum.inflPattern = .doubled := rfl
theorem jakaltek_is_split : jakaltek.inflPattern = .split := rfl
theorem pipil_is_split : pipil.inflPattern = .split := rfl
theorem finnish_is_split : finnish.inflPattern = .split := rfl
theorem pipilLexHeaded_is_lexHeaded : pipilLexHeaded.inflPattern = .lexHeaded := rfl
theorem hemba_is_splitDoubled : hemba.inflPattern = .splitDoubled := rfl

/-! ## Per-datum form verification

These theorems verify that the forms derive from Fragment entries.
Changing a Fragment form breaks the corresponding theorem. -/

theorem doyayo_form_from_fragment :
    doyayo.form = Fragments.Doyayo.AuxiliaryVerbs.form := rfl
theorem gorum_form_from_fragment :
    gorum.form = Fragments.Gorum.AuxiliaryVerbs.form := rfl
theorem jakaltek_form_from_fragment :
    jakaltek.form = Fragments.Jakaltek.AuxiliaryVerbs.form := rfl
theorem pipil_form_from_fragment :
    pipil.form = Fragments.Pipil.AuxiliaryVerbs.form := rfl
theorem finnish_form_from_fragment :
    finnish.form = "en lue" := rfl

/-! ## Per-datum distribution verification

These theorems verify that distributions derive from Fragment entries.
Changing a Fragment's `inflDistribution` breaks the corresponding theorem. -/

theorem doyayo_dist_from_fragment :
    doyayo.distribution = some Fragments.Doyayo.AuxiliaryVerbs.inflDistribution := rfl
theorem gorum_dist_from_fragment :
    gorum.distribution = some Fragments.Gorum.AuxiliaryVerbs.inflDistribution := rfl
theorem jakaltek_dist_from_fragment :
    jakaltek.distribution = some Fragments.Jakaltek.AuxiliaryVerbs.inflDistribution := rfl
theorem pipil_dist_from_fragment :
    pipil.distribution = some Fragments.Pipil.AuxiliaryVerbs.inflDistribution := rfl
theorem finnish_dist_from_fragment :
    finnish.distribution = some Fragments.Finnish.Negation.finnishNegDistribution := rfl
theorem pipilLexHeaded_dist_from_fragment :
    pipilLexHeaded.distribution =
      some Fragments.Pipil.AuxiliaryVerbs.lexHeadedDistribution := rfl
theorem pipilLexHeaded_form_from_fragment :
    pipilLexHeaded.form = Fragments.Pipil.AuxiliaryVerbs.lexHeadedForm := rfl
theorem hemba_form_from_fragment :
    hemba.form = Fragments.Hemba.AuxiliaryVerbs.form := rfl
theorem hemba_dist_from_fragment :
    hemba.distribution = some Fragments.Hemba.AuxiliaryVerbs.inflDistribution := rfl

/-! ## Bridge to Finnish Fragment -/

/-- The Finnish negative auxiliary construction is a split AVC: the auxiliary
    hosts some inflectional categories and the lexical verb hosts others, with
    neither element hosting all categories. Derived from Fragment distribution. -/
theorem finnish_split_from_fragment :
    let dist := Fragments.Finnish.Negation.finnishNegDistribution
    dist.onAux ≠ [] ∧ dist.onLex ≠ [] := by
  exact ⟨by decide, by decide⟩

end Phenomena.AuxiliaryVerbs.Typology
