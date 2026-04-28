import Linglib.Core.Lexical.UD
import Linglib.Core.Morphology.MorphRule

/-!
# Auxiliary Verb Construction Typology — substrate
@cite{anderson-2006}

Type-level enums + data structure for auxiliary verb construction (AVC)
typology following @cite{anderson-2006}. Anderson's core insight: the
**semantic head is always the lexical verb**, but the **inflectional host**
varies across 5 macro-patterns.

## The Five Patterns

| Pattern        | Infl Host  | Example Language               |
|----------------|------------|--------------------------------|
| Aux-headed     | AUX        | English *will go*              |
| Lex-headed     | LEX        | Pipil *weli ni-nehnemi wehka*  |
| Doubled        | AUX+LEX    | Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru* |
| Split          | AUX or LEX | Doyayo, Jakaltek, Finnish      |
| Split/doubled  | AUX+LEX    | Hemba (some doubled, some split) |

## Schema

- `InflPattern`: the 5-way macro-classification of inflectional distribution
- `AVCElement`: which element(s) of an AVC bear a given property
- `AVCDatum`: a per-language AVC datum (form, pattern, distribution, gloss)

## What lives here vs. `Phenomena/AuxiliaryVerbs/Studies/Anderson2006.lean`

This file holds the substrate types and Fragment-independent invariants
(`semantic_head_always_lex`, `auxHeaded_infl_on_phrasal_head`, etc.).
Per-language `AVCDatum` instances + Fragment-grounding verification
theorems live in the Anderson 2006 study file (paper-anchored data).
-/

namespace Typology.AuxiliaryVerbs

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

/-! ## AVC datum schema -/

/-- A cross-linguistic AVC datum. -/
structure AVCDatum where
  language : String
  form : String
  inflPattern : InflPattern
  distribution : Option Core.Morphology.InflDistribution := none
  gloss : String := ""
  deriving Repr, BEq

/-! ## Invariant theorems

These theorems are about `InflPattern` itself — Fragment-independent
substrate-level facts. Per-language verification theorems live in the
Anderson 2006 study file. -/

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

/-- In aux-headed AVCs, the lexical verb is nonfinite. -/
theorem auxHeaded_lv_nonfinite :
    InflPattern.auxHeaded.lvVerbForm = UD.VerbForm.Inf := rfl

/-- In lex-headed AVCs, the lexical verb is finite. -/
theorem lexHeaded_lv_finite :
    InflPattern.lexHeaded.lvVerbForm = UD.VerbForm.Fin := rfl

end Typology.AuxiliaryVerbs
