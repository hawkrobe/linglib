/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic

/-!
# Auxiliary verb constructions: inflection-locus typology

[anderson-2006]

The auxiliary-verb-construction (AVC) inflection typology of [anderson-2006]:
the **semantic head is always the lexical verb**, but the **inflectional host**
varies across five macro-patterns. Graduated from the dissolved `Typology/`
drawer (the orthogonal be/have-selection typology split off to
`Semantics/ArgumentStructure/AuxiliarySelection.lean`).

## The five patterns

| Pattern        | Infl host  | Example                                   |
|----------------|------------|-------------------------------------------|
| Aux-headed     | AUX        | English *have eaten*, *is eating*         |
| Lex-headed     | LEX        | Pipil *weli ni-nehnemi*                    |
| Doubled        | AUX+LEX    | Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru*           |
| Split          | AUX or LEX | Jakaltek (abs/erg), Finnish neg-aux *ei*  |
| Split/doubled  | AUX+LEX    | Pipil, Doyayo (Ch 5), Hemba               |

## Main definitions

* `InflPattern` — the five-way inflectional-distribution macro-classification.
* `AVCElement` — which element(s) of an AVC bear a given property.
* `InflPattern.semanticHead` / `inflHost` / `inflOnlyOnPhrasalHead` / `lvVerbForm`.

Per-language `AVCDatum` instances + Fragment-grounding verification theorems
live in `Studies/Anderson2006.lean` (paper-anchored data).
-/

namespace AuxiliaryVerbs

/-! ### Core types -/

/-- Anderson's 5-way inflectional pattern typology for AVCs. -/
inductive InflPattern where
  /-- Inflection hosted on auxiliary; lexical verb is nonfinite.
      E.g., English *will go*, French *va manger*. -/
  | auxHeaded
  /-- Inflection hosted on lexical verb; auxiliary is grammaticalized.
      E.g., Pipil *weli ni-nehnemi* (AUX uninflected, LV carries person);
      Doyayo *mi¹ (gi²) kpel¹-ko¹* (Ch 3 ex 15a). -/
  | lexHeaded
  /-- Inflection appears on both auxiliary and lexical verb.
      E.g., Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru* (subject + TAM on both). -/
  | doubled
  /-- Inflection split between AUX and LV (different features on each
      element, with no overlap). E.g., Jakaltek *šk-ach w-ila*
      (absolutive on AUX, ergative on LV); Finnish neg-aux *ei*
      (person/number on AUX, connegative + aspect on LV). -/
  | split
  /-- Some categories on both AUX and LV (doubled), others exclusive
      to one element (split). [anderson-2006] ch. 5 §5.2 dedicates
      ~30 pages to this pattern with 30+ language exemplars across
      §§5.2.1–5.2.3 (Limbu, Manam, Kuot, Doyayo, Mbay, Lamba, Pipil,
      Persian, Swahili, Panyjima, Kemantney, Oshikwanyama, Shambala,
      Vinmavis, Nambiquara, Baure, Luganda, Nasioi, Os, Xhosa, ...).
      Common, not marginal. -/
  | splitDoubled
  deriving DecidableEq, Repr, Inhabited

/-- Which element(s) of an AVC bear a given property. -/
inductive AVCElement where
  | aux   -- auxiliary only
  | lex   -- lexical verb only
  | both  -- both auxiliary and lexical verb
  deriving DecidableEq, Repr

/-! ### Key functions -/

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

/-! ### Invariant theorems

About `InflPattern` itself — Fragment-independent substrate facts. Per-language
verification theorems live in `Studies/Anderson2006.lean`. -/

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

end AuxiliaryVerbs
