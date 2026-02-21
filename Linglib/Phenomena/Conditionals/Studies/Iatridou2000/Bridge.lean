import Linglib.Phenomena.Conditionals.Studies.Iatridou2000.Data
import Linglib.Theories.Semantics.Conditionals.Iatridou
import Linglib.Theories.Semantics.Tense.Deal

/-!
# Iatridou (2000) — Bridge @cite{iatridou-2000}

Connects the cross-linguistic morphological data from Iatridou (2000) to the
ExclF formalization in `Semantics.Conditionals.Iatridou`.

## Bridge Structure

1. **Past layer count = ExclF count**: per-datum verification that the number
   of past morpheme layers matches the ExclF count for each CF type.
2. **Subjunctive generalization**: per-language verification that the
   presence of past subjunctive morphology correlates with CF subjunctive
   requirement.
3. **Classification bridges**: verification that ExclF configuration +
   predicate type correctly classifies example sentences.
4. **Deal bridge**: ExclDimension maps correctly to Deal's PastMorphologyUse.
-/

namespace Phenomena.Conditionals.Studies.Iatridou2000.Bridge

open Semantics.Conditionals.Iatridou
open Semantics.Tense.Deal

-- ════════════════════════════════════════════════════════════════
-- § Past Layer Count = ExclF Count
-- ════════════════════════════════════════════════════════════════

/-- English FLV: 1 past layer = 1 ExclF (FLV). -/
theorem english_flv_layers :
    english_flv.pastLayers = CounterfactualType.flv.exclFCount := rfl

/-- English PresCF: 1 past layer = 1 ExclF (PresCF). -/
theorem english_presCF_layers :
    english_presCF.pastLayers = CounterfactualType.presCF.exclFCount := rfl

/-- English PastCF: 2 past layers = 2 ExclFs (PastCF). -/
theorem english_pastCF_layers :
    english_pastCF.pastLayers = CounterfactualType.pastCF.exclFCount := rfl

/-- Greek FLV: 1 past layer = 1 ExclF (FLV). -/
theorem greek_flv_layers :
    greek_flv.pastLayers = CounterfactualType.flv.exclFCount := rfl

/-- Greek PresCF: 1 past layer = 1 ExclF (PresCF). -/
theorem greek_presCF_layers :
    greek_presCF.pastLayers = CounterfactualType.presCF.exclFCount := rfl

/-- Greek PastCF: 2 past layers = 2 ExclFs (PastCF). -/
theorem greek_pastCF_layers :
    greek_pastCF.pastLayers = CounterfactualType.pastCF.exclFCount := rfl

/-- French FLV: 1 past layer = 1 ExclF (FLV). -/
theorem french_flv_layers :
    french_flv.pastLayers = CounterfactualType.flv.exclFCount := rfl

/-- French PresCF: 1 past layer = 1 ExclF (PresCF). -/
theorem french_presCF_layers :
    french_presCF.pastLayers = CounterfactualType.presCF.exclFCount := rfl

/-- French PastCF: 2 past layers = 2 ExclFs (PastCF). -/
theorem french_pastCF_layers :
    french_pastCF.pastLayers = CounterfactualType.pastCF.exclFCount := rfl

-- ════════════════════════════════════════════════════════════════
-- § Subjunctive Generalization
-- ════════════════════════════════════════════════════════════════

/-- English: no past subjunctive, no CF subjunctive required. -/
theorem english_subj_gen :
    iatridouSubjGeneralization english_subj.hasPastSubjunctive
      english_subj.cfRequiresSubjunctive := rfl

/-- Greek: has past subjunctive, CF requires subjunctive. -/
theorem greek_subj_gen :
    iatridouSubjGeneralization greek_subj.hasPastSubjunctive
      greek_subj.cfRequiresSubjunctive := rfl

/-- French: has past subjunctive, CF requires subjunctive. -/
theorem french_subj_gen :
    iatridouSubjGeneralization french_subj.hasPastSubjunctive
      french_subj.cfRequiresSubjunctive := rfl

-- ════════════════════════════════════════════════════════════════
-- § Classification Bridges
-- ════════════════════════════════════════════════════════════════

/-- "If he knew French" (ILP + 1 modal ExclF) → PresCF. -/
theorem knew_french_is_presCF :
    classifyCounterfactual true false .ilp = some .presCF := rfl

/-- "If he were to leave" (telic + 1 modal ExclF) → FLV. -/
theorem leave_tomorrow_is_flv :
    classifyCounterfactual true false .telic = some .flv := rfl

/-- "If he had left" (telic + 2 ExclFs) → PastCF. -/
theorem had_left_is_pastCF :
    classifyCounterfactual true true .telic = some .pastCF := rfl

/-- "If he were sick" (stative + 1 modal ExclF) → PresCF. -/
theorem were_sick_is_presCF :
    classifyCounterfactual true false .stative = some .presCF := rfl

/-- "If he had known" (ILP + 2 ExclFs) → PastCF. -/
theorem had_known_is_pastCF :
    classifyCounterfactual true true .ilp = some .pastCF := rfl

-- ════════════════════════════════════════════════════════════════
-- § Deal Bridge
-- ════════════════════════════════════════════════════════════════

/-- Modal ExclF = Deal's counterfactual use. -/
theorem exclF_modal_is_deal_cf :
    ExclDimension.toDealUse .modal = .counterfactual := rfl

/-- Temporal ExclF = Deal's temporal use. -/
theorem exclF_temporal_is_deal_temporal :
    ExclDimension.toDealUse .temporal = .temporal := rfl

/-- PastCF is exempt from ULC via Deal's refined ULC.

The counterfactual tense in PastCF is not subject to the upper limit
constraint, because modal ExclF does not encode temporal precedence. -/
theorem pastCF_exempt_from_ulc {T : Type*} [LE T] (R E : T) :
    refinedULC .counterfactual R E :=
  trivial

end Phenomena.Conditionals.Studies.Iatridou2000.Bridge
