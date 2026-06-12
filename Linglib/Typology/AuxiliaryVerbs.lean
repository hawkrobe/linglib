import Linglib.Data.UD.Basic
import Linglib.Morphology.MorphRule

/-!
# Auxiliary Verb Construction Typology — substrate
[anderson-2006]

Type-level enums + data structure for auxiliary verb construction (AVC)
typology following [anderson-2006]. Anderson's core insight: the
**semantic head is always the lexical verb**, but the **inflectional host**
varies across 5 macro-patterns.

## The Five Patterns

| Pattern        | Infl Host  | Example Language                          |
|----------------|------------|-------------------------------------------|
| Aux-headed     | AUX        | English *have eaten*, *is eating*         |
| Lex-headed     | LEX        | Pipil *weli ni-nehnemi*, Doyayo (Ch 3)    |
| Doubled        | AUX+LEX    | Gorum *miŋ ne-gaʔ-ru ne-laʔ-ru*           |
| Split          | AUX or LEX | Jakaltek (abs/erg), Finnish (neg-aux *ei*) |
| Split/doubled  | AUX+LEX    | Pipil *n-yu ni-mitsin-ilwitia*, Doyayo (Ch 5), Hemba |

## Schema

- `InflPattern`: the 5-way macro-classification of inflectional distribution
- `AVCElement`: which element(s) of an AVC bear a given property
- `AVCDatum`: a per-language AVC datum (form, pattern, distribution, gloss)
- Be/have auxiliary selection ([burzio-1986], [sorace-2000]): `PerfectAux`,
  `TransitivityClass`, `SelectionRule`, `selection`

## What lives here vs. `Studies/Anderson2006.lean`

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
  distribution : Option Morphology.InflDistribution := none
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

/-! ## Be/have auxiliary selection
[burzio-1986] [sorace-2000]

Many European languages select between *be* and *have* as the perfect
auxiliary based on the transitivity/unaccusativity of the lexical verb
(the "Auxiliary Selection Hierarchy"): unaccusatives → *be* (Italian
*è arrivato*, French *est arrivé*), unergatives/transitives → *have*
(Italian *ha mangiato*). English has collapsed the split: all verbs take
*have*. Selection operates within aux-headed AVCs — the selecting
auxiliary is the inflectional host. -/

/-- Perfect auxiliary choice. -/
inductive PerfectAux where
  | be   -- Italian *essere*, French *être*, German *sein*
  | have -- Italian *avere*, French *avoir*, German *haben*
  deriving DecidableEq, Repr

/-- Transitivity class relevant to auxiliary selection. -/
inductive TransitivityClass where
  | unaccusative  -- subject = theme (arrive, fall, die)
  | unergative    -- subject = agent, no object (run, laugh)
  | transitive    -- subject = agent, object = theme (eat, build)
  | reflexive     -- reflexive clitic triggers *be* in Romance (Italian/French), *have* in German
  deriving DecidableEq, Repr

/-- Language-level auxiliary selection rule. -/
inductive SelectionRule where
  | split    -- unaccusatives → be, rest → have (Italian, French, German, Dutch)
  | haveOnly -- all verbs → have (English, Spanish)
  | beOnly   -- all verbs → be (rare; some Sardinian dialects)
  | mixed    -- gradient/variable selection (some German dialects)
  deriving DecidableEq, Repr

/-- Auxiliary selection driven by a single binary parameter: does the
    language treat reflexives as BE-selecting (Romance pattern) or
    HAVE-selecting (German pattern)? Unaccusatives always select BE,
    unergatives and transitives always select HAVE; the only point of
    cross-linguistic variation in this small typology is the reflexive
    row ([burzio-1986], [sorace-2000]). -/
def selection (reflexIsBe : Bool) : TransitivityClass → PerfectAux
  | .unaccusative => .be
  | .reflexive    => if reflexIsBe then .be else .have
  | .unergative   => .have
  | .transitive   => .have

/-- Canonical (Romance) auxiliary selection: reflexives → *be*. -/
def canonicalSelection : TransitivityClass → PerfectAux := selection true

/-- German auxiliary selection: reflexives → *haben*, not *sein*
    ([burzio-1986]). -/
def germanSelection : TransitivityClass → PerfectAux := selection false

/-- The auxiliary a selection rule assigns to each transitivity class:
    `split` follows `selection`, `haveOnly`/`beOnly` are constant
    (English *has arrived*), and `mixed` systems make no categorical
    assignment. -/
def SelectionRule.selects (reflexIsBe : Bool) :
    SelectionRule → TransitivityClass → Option PerfectAux
  | .split, c    => some (selection reflexIsBe c)
  | .haveOnly, _ => some .have
  | .beOnly, _   => some .be
  | .mixed, _    => none

/-- Does this transitivity class canonically select *be*?
    Defined off `canonicalSelection` so the equivalence is true by
    construction. -/
def SelectsBe (c : TransitivityClass) : Prop :=
  canonicalSelection c = .be

instance : DecidablePred SelectsBe := fun c => by
  unfold SelectsBe
  infer_instance

end Typology.AuxiliaryVerbs
