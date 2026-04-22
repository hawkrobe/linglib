import Linglib.Theories.Semantics.Modality.Exclusion
import Linglib.Core.Lexical.VerbClass

/-!
# @cite{iatridou-2000} — Morphological Data @cite{iatridou-2000}

Theory-neutral cross-linguistic data on counterfactual morphology from
@cite{iatridou-2000} "The Grammatical Ingredients of Counterfactuality",
*Linguistic Inquiry* 31(2): 231–270.

## Key Empirical Generalizations

1. **Past morphology is uniform**: FLV, PresCF, and PastCF all use past
   morphology, but differ in the *number* of past layers.
2. **Imperfective is not universal**: languages that lack imperfective
   (e.g., English) omit it in CFs; languages with imperfective (e.g., Greek)
   use it in all CF types.
3. **Subjunctive mirrors past subjunctive availability**: a CF can contain
   subjunctive only if the language has a distinct past subjunctive form
   (generalization 42).

## Data Sources

- Tables 1–2 of @cite{iatridou-2000}
- Example sentences from §2

## See also

- `Phenomena/Modality/Studies/CarianiSantorio2018.lean` — selectional
  account where past morphology shifts the modal parameter rather than
  introducing a separate counterfactual operator. C&S §5.3.2 identifies
  *would* with morphological past *will*, dovetailing with Iatridou's
  past-morphology-as-modal-shift generalization.
-/

namespace Iatridou2000

open Semantics.Modality.Exclusion
open Core.Verbs (VendlerClass)

-- ════════════════════════════════════════════════════════════════
-- § @cite{iatridou-2000}'s counterfactual typology
-- ════════════════════════════════════════════════════════════════

/-- @cite{iatridou-2000}'s predicate classification for counterfactual
gating.

The distinction between FLV and PresCF (both with 1 modal ExclF)
depends on the predicate type:
- ILPs and statives yield PresCF ("If he knew French,...")
- Telic predicates yield FLV ("If he were to leave tomorrow,...") -/
inductive IatridouPredType where
  /-- Individual-Level Predicate: "be tall", "know French" -/
  | ilp
  /-- Stage-Level stative: "be sick", "be available" -/
  | stative
  /-- Telic predicate: "arrive", "build a house" -/
  | telic
  deriving DecidableEq, Repr

/-- Map Vendler classes to @cite{iatridou-2000}'s predicate
classification.

States and activities map to stative; achievements and accomplishments
map to telic. -/
def VendlerClass.toIatridou : VendlerClass → IatridouPredType
  | .state | .activity | .semelfactive => .stative
  | .achievement | .accomplishment => .telic

/-- @cite{iatridou-2000}'s three counterfactual conditional types,
distinguished by the number of ExclFs and predicate type. -/
inductive CounterfactualType where
  /-- Future Less Vivid: 1 ExclF modal + telic predicate -/
  | flv
  /-- Present Counterfactual: 1 ExclF modal + ILP/stative -/
  | presCF
  /-- Past Counterfactual: 2 ExclFs (modal + temporal) -/
  | pastCF
  deriving DecidableEq, Repr

/-- The number of ExclFs required for each counterfactual type. -/
def CounterfactualType.exclFCount : CounterfactualType → Nat
  | .flv | .presCF => 1
  | .pastCF => 2

/-- Classify a counterfactual from its ExclF configuration and
predicate type. Returns `none` if there is no modal ExclF
(a non-counterfactual sentence). -/
def classifyCounterfactual (modalExcl temporalExcl : Bool)
    (predType : IatridouPredType) : Option CounterfactualType :=
  match modalExcl, temporalExcl with
  | true, true => some .pastCF
  | true, false => match predType with
    | .telic => some .flv
    | .ilp | .stative => some .presCF
  | false, _ => none

/-- Telic predicate + 1 modal ExclF = FLV. -/
theorem telic_one_exclF_is_flv :
    classifyCounterfactual true false .telic = some .flv := rfl

/-- ILP + 1 modal ExclF = PresCF. -/
theorem ilp_one_exclF_is_presCF :
    classifyCounterfactual true false .ilp = some .presCF := rfl

/-- Stative + 1 modal ExclF = PresCF. -/
theorem stative_one_exclF_is_presCF :
    classifyCounterfactual true false .stative = some .presCF := rfl

/-- Two ExclFs = PastCF regardless of predicate type. -/
theorem two_exclFs_is_pastCF (pred : IatridouPredType) :
    classifyCounterfactual true true pred = some .pastCF := by
  cases pred <;> rfl

/-- No modal ExclF = not a counterfactual. -/
theorem no_modal_not_cf (temporalExcl : Bool) (pred : IatridouPredType) :
    classifyCounterfactual false temporalExcl pred = none := by
  cases temporalExcl <;> rfl

/-- @cite{iatridou-2000}'s subjunctive generalization (42): "A CF can
contain a subjunctive morpheme only if that subjunctive morpheme has a
past tense form".

Strictly, the paper states this as a one-directional conditional
(requires → has). We encode the biconditional because all languages in
our data satisfy both directions: English and Greek lack past
subjunctive and don't require subjunctive in CFs; Italian has past
subjunctive and requires it. -/
def iatridouSubjGeneralization (hasPastSubj requiresSubj : Bool) : Prop :=
  requiresSubj = hasPastSubj

/-- All three counterfactual types collapse to the framework-agnostic
`Core.Mood.SubjunctiveType.counterfactual` tag. -/
def CounterfactualType.toSubjunctiveType (_ : CounterfactualType) :
    Core.Mood.SubjunctiveType :=
  .counterfactual

/-- Every @cite{iatridou-2000} counterfactual type maps to
`.counterfactual`. -/
theorem all_counterfactuals_are_counterfactual (t : CounterfactualType) :
    t.toSubjunctiveType = .counterfactual := by cases t <;> rfl

/-- PastCF tower has depth 2 — corresponding to the two past morpheme
layers observed cross-linguistically.

(Tower-level corollary; uses the `subjShift`/`temporalShift`
infrastructure from `Semantics.Modality.Exclusion`.) -/
theorem pastCF_tower_depth {W E P T : Type*} (c : Core.Context.KContext W E P T)
    (w' : W) (t' t'' : T) :
    (((Core.Context.ContextTower.root c).push
        (Semantics.Mood.subjShift w' t')).push
      (Core.Context.temporalShift t'')).depth = 2 := by
  simp [Core.Context.ContextTower.push, Core.Context.ContextTower.depth,
    Core.Context.ContextTower.root]

-- ════════════════════════════════════════════════════════════════
-- § Datum Structures
-- ════════════════════════════════════════════════════════════════

/-- A morphological datum for counterfactual conditionals.

Each datum records the verb morphology in the antecedent and consequent
of a specific counterfactual type in a specific language. -/
structure CFMorphologyDatum where
  /-- Language name -/
  language : String
  /-- Counterfactual type: "FLV", "PresCF", or "PastCF" -/
  cfType : String
  /-- Verb morphology in the antecedent -/
  antecedentForm : String
  /-- Verb morphology in the consequent -/
  consequentForm : String
  /-- Whether past morphology is present -/
  hasPastMorph : Bool
  /-- Whether imperfective morphology is present -/
  hasImpfMorph : Bool
  /-- Whether subjunctive morphology is present -/
  hasSubjMorph : Bool
  /-- Number of past morpheme layers -/
  pastLayers : Nat
  /-- Gloss of the example -/
  gloss : String
  deriving Repr

/-- A datum for whether a language requires subjunctive in counterfactuals.

Iatridou's generalization: a language requires subjunctive in CFs iff it
has a morphologically distinct past subjunctive. -/
structure SubjRequirementDatum where
  /-- Language name -/
  language : String
  /-- Whether the language has a distinct past subjunctive form -/
  hasPastSubjunctive : Bool
  /-- Whether counterfactuals require subjunctive morphology -/
  cfRequiresSubjunctive : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § English Data
-- ════════════════════════════════════════════════════════════════

/-- English FLV: "If he were to take the exam tomorrow,..." -/
def english_flv : CFMorphologyDatum where
  language := "English"
  cfType := "FLV"
  antecedentForm := "were to V"
  consequentForm := "would V"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 1
  gloss := "If he were to take the exam tomorrow, he would pass."

/-- English PresCF: "If he knew the answer,..." -/
def english_presCF : CFMorphologyDatum where
  language := "English"
  cfType := "PresCF"
  antecedentForm := "V-ed"
  consequentForm := "would V"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 1
  gloss := "If he knew the answer, he would tell us."

/-- English PastCF: "If he had taken the exam,..." -/
def english_pastCF : CFMorphologyDatum where
  language := "English"
  cfType := "PastCF"
  antecedentForm := "had V-ed"
  consequentForm := "would have V-ed"
  hasPastMorph := true
  hasImpfMorph := false
  hasSubjMorph := false
  pastLayers := 2
  gloss := "If he had taken the exam yesterday, he would have passed."

-- ════════════════════════════════════════════════════════════════
-- § Greek Data
-- ════════════════════════════════════════════════════════════════

/-- Greek FLV: "An + past + impf, tha + past + impf"

Based on @cite{iatridou-2000}, example (6). Greek FLV and PresCF have
identical morphological form; the FLV/PresCF distinction is made by
predicate type and temporal adverbials, not by morphology. -/
def greek_flv : CFMorphologyDatum where
  language := "Greek"
  cfType := "FLV"
  antecedentForm := "an + past + impf"
  consequentForm := "tha + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "An eperne to siropi tu avrio, tha yinotan kala."

/-- Greek PresCF: "An + past + impf, tha + past + impf"

Based on @cite{iatridou-2000}, example (6). Morphologically identical
to FLV in Greek; the counterfactual reading arises from the stative
predicate. -/
def greek_presCF : CFMorphologyDatum where
  language := "Greek"
  cfType := "PresCF"
  antecedentForm := "an + past + impf"
  consequentForm := "tha + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "An eperne to siropi tu, tha yinotan kala."

/-- Greek PastCF: "An + past + past + impf, tha + past + past + impf"

Based on @cite{iatridou-2000}, example (6c). The additional past
layer (the pluperfect ixe + participle) distinguishes PastCF from
PresCF/FLV. -/
def greek_pastCF : CFMorphologyDatum where
  language := "Greek"
  cfType := "PastCF"
  antecedentForm := "an + past + past + impf"
  consequentForm := "tha + past + past + impf"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 2
  gloss := "An ixe pari to siropi tu xthes, tha ixe yini kala."

-- ════════════════════════════════════════════════════════════════
-- § French Data
-- ════════════════════════════════════════════════════════════════

/-- French FLV: "imparfait, conditionnel" -/
def french_flv : CFMorphologyDatum where
  language := "French"
  cfType := "FLV"
  antecedentForm := "imparfait"
  consequentForm := "conditionnel"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "S'il passait l'examen demain, il réussirait."

/-- French PresCF: "imparfait, conditionnel" -/
def french_presCF : CFMorphologyDatum where
  language := "French"
  cfType := "PresCF"
  antecedentForm := "imparfait"
  consequentForm := "conditionnel"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 1
  gloss := "S'il savait la réponse, il nous le dirait."

/-- French PastCF: "plus-que-parfait, conditionnel passé" -/
def french_pastCF : CFMorphologyDatum where
  language := "French"
  cfType := "PastCF"
  antecedentForm := "plus-que-parfait"
  consequentForm := "conditionnel passé"
  hasPastMorph := true
  hasImpfMorph := true
  hasSubjMorph := false
  pastLayers := 2
  gloss := "S'il avait passé l'examen hier, il aurait réussi."

-- ════════════════════════════════════════════════════════════════
-- § Subjunctive Requirement Data
-- ════════════════════════════════════════════════════════════════

/-- English: no distinct past subjunctive, no subjunctive required. -/
def english_subj : SubjRequirementDatum where
  language := "English"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- Greek: no past subjunctive, no subjunctive required in CFs.

Greek CFs use past + imperfective morphology (indicative), not subjunctive.
Greek has a subjunctive-like particle (na), but this is not used in
counterfactual conditionals. -/
def greek_subj : SubjRequirementDatum where
  language := "Greek"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- French: no productive past subjunctive, no subjunctive required in CFs.

French CFs use the indicative imparfait ("si j'avais..."), not the
subjonctif. French has a literary past subjunctive (subjonctif imparfait),
but it is not used productively in counterfactuals. -/
def french_subj : SubjRequirementDatum where
  language := "French"
  hasPastSubjunctive := false
  cfRequiresSubjunctive := false

/-- Italian: has distinct past subjunctive, subjunctive required in CFs.

Italian CFs require the congiuntivo (subjunctive), which has a robust
past form (congiuntivo trapassato). This is one of the positive cases
for Iatridou's generalization (42): "A CF can contain a subjunctive
morpheme only if that subjunctive morpheme has a past tense form." -/
def italian_subj : SubjRequirementDatum where
  language := "Italian"
  hasPastSubjunctive := true
  cfRequiresSubjunctive := true

-- ════════════════════════════════════════════════════════════════
-- § Basic Data Theorems
-- ════════════════════════════════════════════════════════════════

/-- All CF types use past morphology. -/
theorem all_cfs_have_past :
    english_flv.hasPastMorph = true ∧
    english_presCF.hasPastMorph = true ∧
    english_pastCF.hasPastMorph = true ∧
    greek_flv.hasPastMorph = true ∧
    greek_presCF.hasPastMorph = true ∧
    greek_pastCF.hasPastMorph = true ∧
    french_flv.hasPastMorph = true ∧
    french_presCF.hasPastMorph = true ∧
    french_pastCF.hasPastMorph = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- PastCF has more past layers than PresCF/FLV. -/
theorem pastCF_has_more_layers :
    english_pastCF.pastLayers > english_presCF.pastLayers ∧
    greek_pastCF.pastLayers > greek_presCF.pastLayers ∧
    french_pastCF.pastLayers > french_presCF.pastLayers := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § Bridge: ExclF, Classification, Deal
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense.CounterfactualTense

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

/-- English: no past subjunctive, no CF subjunctive required. -/
theorem english_subj_gen :
    iatridouSubjGeneralization english_subj.hasPastSubjunctive
      english_subj.cfRequiresSubjunctive := rfl

/-- Greek: no past subjunctive, no CF subjunctive required. -/
theorem greek_subj_gen :
    iatridouSubjGeneralization greek_subj.hasPastSubjunctive
      greek_subj.cfRequiresSubjunctive := rfl

/-- French: no productive past subjunctive, no CF subjunctive required. -/
theorem french_subj_gen :
    iatridouSubjGeneralization french_subj.hasPastSubjunctive
      french_subj.cfRequiresSubjunctive := rfl

/-- Italian: has past subjunctive, CF requires subjunctive. -/
theorem italian_subj_gen :
    iatridouSubjGeneralization italian_subj.hasPastSubjunctive
      italian_subj.cfRequiresSubjunctive := rfl

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

/-- PastCF is exempt from ULC via Deal's refined ULC. -/
theorem pastCF_exempt_from_ulc {T : Type*} [LE T] (R E : T) :
    refinedULC .counterfactual R E :=
  trivial

-- ════════════════════════════════════════════════════════════════
-- § ContextTower Bridge
-- ════════════════════════════════════════════════════════════════

open Core.Context
open Semantics.Mood (subjShift)

abbrev CFCtx := KContext Bool Unit Unit ℤ

/-- The actual context: world = true (actual), time = 0 (now). -/
def actualCtx : CFCtx :=
  { world := true, agent := (), addressee := (), time := 0, position := () }

/-- Root tower: the actual speech-act context, depth 0. -/
def actualTower : ContextTower CFCtx := ContextTower.root actualCtx

/-- FLV/PresCF: one subjunctive shift to a counterfactual world.
    The counterfactual world (false) differs from the actual world (true). -/
def presCFTower : ContextTower CFCtx :=
  actualTower.push (subjShift false 0)

/-- The tower has depth 1 — matching 1 past morpheme layer. -/
theorem presCF_depth : presCFTower.depth = 1 := rfl

/-- Modal ExclF holds: counterfactual world ≠ actual world. -/
theorem presCF_modal_exclF :
    ExclF .modal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF does NOT hold: time is unchanged (0 = 0). -/
theorem presCF_no_temporal_exclF :
    ¬ ExclF .temporal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Tower depth (1) matches English FLV past layers (1). -/
theorem flv_tower_depth_matches_data :
    presCFTower.depth = english_flv.pastLayers := rfl

/-- Tower depth (1) matches English PresCF past layers (1). -/
theorem presCF_tower_depth_matches_data :
    presCFTower.depth = english_presCF.pastLayers := rfl

/-- PastCF: two shifts — one modal (subjunctive, world shift) and one
    temporal (additional past layer, time shift to -5). -/
def pastCFTower : ContextTower CFCtx :=
  presCFTower.push (temporalShift (-5))

/-- Tower depth is 2 — matching 2 past morpheme layers. -/
theorem pastCF_depth : pastCFTower.depth = 2 := rfl

/-- Modal ExclF holds: counterfactual world ≠ actual world. -/
theorem pastCF_modal_exclF :
    ExclF .modal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF holds: shifted time (-5) ≠ speech time (0). -/
theorem pastCF_temporal_exclF :
    ExclF .temporal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift temporalShift; decide

/-- Tower depth (2) matches English PastCF past layers (2). -/
theorem pastCF_tower_depth_matches_data :
    pastCFTower.depth = english_pastCF.pastLayers := rfl

/-- Tower depth (2) matches Greek PastCF past layers (2). -/
theorem pastCF_tower_depth_matches_greek :
    pastCFTower.depth = greek_pastCF.pastLayers := rfl

/-- Even in a PastCF tower (depth 2), the origin context is preserved. -/
theorem pastCF_origin_preserved :
    pastCFTower.origin = actualCtx := rfl

end Iatridou2000
