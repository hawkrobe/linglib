import Linglib.Semantics.Modality.Exclusion
import Mathlib.Data.Finset.Basic

/-!
# Iatridou (2000): The Grammatical Ingredients of Counterfactuality [iatridou-2000]

Theory-neutral cross-linguistic data and the ExclF analysis from [iatridou-2000]
"The Grammatical Ingredients of Counterfactuality", *Linguistic Inquiry* 31(2):
231–270.

Iatridou's central claim: the morphology we call "past tense" provides a skeletal
*exclusion feature* (ExclF), `T(x) excludes C(x)` — the topic `x` excludes the
speaker's `x`. Over times it yields temporal past; over worlds it yields
counterfactuality. A counterfactual is built from ExclF, an aspectual component
(imperfective in some languages), and mood.

## Key empirical generalizations

1. **Past morphology is uniform**: FLV, PresCF, and PastCF all use past
   morphology, differing in the *number* of ExclF layers (1, 1, 2).
2. **Imperfective is not universal**: languages with imperfective (Greek, French)
   use it in CFs; languages without it (English) omit it.
3. **Subjunctive mirrors past-subjunctive availability** (§6.1): a CF uses
   subjunctive only in languages with a past-subjunctive paradigm — German and
   Italian do; French and Indo-Aryan have only a nonpast subjunctive and don't.

## See also

- `Studies/CarianiSantorio2018.lean` — selectional account where past morphology
  shifts the modal parameter rather than introducing a separate CF operator.
-/

namespace Iatridou2000

open Semantics.Modality.Exclusion
open Semantics.Context
open Semantics.Mood (subjShift)

/-! ### Iatridou's counterfactual typology -/

/-- [iatridou-2000]'s three counterfactual conditional types, distinguished by the
    number of ExclFs and (in the one-ExclF cases) the predicate's Aktionsart. -/
inductive CounterfactualType where
  /-- Future Less Vivid: one ExclF (over worlds) + telic/activity predicate. -/
  | flv
  /-- Present Counterfactual: one ExclF (over worlds) + individual-level stative. -/
  | presCF
  /-- Past Counterfactual: two ExclFs — one over worlds, one over times. -/
  | pastCF
  deriving DecidableEq, Repr

/-- ExclF count per type. PresCF/FLV have one (over worlds); PastCF has two — the
    pluperfect's two past layers, one fake (modal) and one real (temporal)
    ([iatridou-2000] §4, p. 252). -/
def CounterfactualType.exclFCount : CounterfactualType → Nat
  | .flv | .presCF => 1
  | .pastCF => 2

/-- Predicate Aktionsart relevant to the FLV/PresCF split ([iatridou-2000],
    Tables 1–2). The individual-level vs stage-level distinction among statives
    is *not* recoverable from Vendler class (both are "states"), so it is encoded
    directly rather than derived from a `VendlerClass`. -/
inductive IatridouPredType where
  /-- Telic: arrive, build a house (evaluated in the future → FLV). -/
  | telic
  /-- Activity: run, push the cart — patterns with telics ([iatridou-2000], fn 24). -/
  | activity
  /-- Individual-level stative: be tall, know French (holds also now → PresCF). -/
  | ilp
  /-- Stage-level stative: be sick, be drunk (future *or* now → FLV *or* PresCF). -/
  | slp
  deriving DecidableEq, Repr

/-- Classify a counterfactual from its ExclF configuration and predicate type,
    returning the *set* of licensed CF readings (`∅` if there is no modal ExclF).

    Faithful to [iatridou-2000] Table 1: with one (modal) ExclF, a telic or
    activity predicate yields FLV, an individual-level stative yields PresCF, and
    a stage-level stative yields *both* (FLV with a future adverbial, PresCF
    otherwise — ex (64)). Two ExclFs yield PastCF regardless of predicate. -/
def classifyCounterfactual : Bool → Bool → IatridouPredType → Finset CounterfactualType
  | false, _,     _         => ∅
  | true,  true,  _         => {.pastCF}
  | true,  false, .telic    => {.flv}
  | true,  false, .activity => {.flv}
  | true,  false, .ilp      => {.presCF}
  | true,  false, .slp      => {.flv, .presCF}

/-- Telic + one modal ExclF → FLV. -/
theorem telic_one_exclF : classifyCounterfactual true false .telic = {.flv} := rfl

/-- Activity + one modal ExclF → FLV ([iatridou-2000], fn 24). -/
theorem activity_one_exclF : classifyCounterfactual true false .activity = {.flv} := rfl

/-- Individual-level stative + one modal ExclF → PresCF only. -/
theorem ilp_one_exclF : classifyCounterfactual true false .ilp = {.presCF} := rfl

/-- Stage-level stative + one modal ExclF → *both* FLV and PresCF
    ([iatridou-2000], Table 1, ex (64)): "If he were drunk at next week's
    meeting" (FLV) vs "If he were drunk, he would be louder" (PresCF). -/
theorem slp_one_exclF : classifyCounterfactual true false .slp = {.flv, .presCF} := rfl

/-- Two ExclFs → PastCF, regardless of predicate type. -/
theorem two_exclFs_pastCF (pred : IatridouPredType) :
    classifyCounterfactual true true pred = {.pastCF} := by cases pred <;> rfl

/-- No modal ExclF → not a counterfactual. -/
theorem no_modal_not_cf (temporalExcl : Bool) (pred : IatridouPredType) :
    classifyCounterfactual false temporalExcl pred = ∅ := by cases temporalExcl <;> rfl

/-- [iatridou-2000]'s subjunctive prediction (§6.1, p. 264): a CF uses subjunctive
    only in languages that have a past-subjunctive paradigm.

    The paper states it one-directionally (uses → has); we encode the
    biconditional, which all languages in the data satisfy: English, Greek, and
    French lack a productive past subjunctive and use none in CFs; Italian has
    one and requires it. -/
def iatridouSubjGeneralization (hasPastSubj requiresSubj : Bool) : Prop :=
  requiresSubj = hasPastSubj

/-- All three CF types collapse to the framework-agnostic
    `Semantics.Mood.SubjunctiveType.counterfactual` tag. -/
def CounterfactualType.toSubjunctiveType (_ : CounterfactualType) :
    Semantics.Mood.SubjunctiveType := .counterfactual

theorem all_counterfactuals_are_counterfactual (t : CounterfactualType) :
    t.toSubjunctiveType = .counterfactual := by cases t <;> rfl

/-- A PastCF tower has depth 2 — the two past morpheme layers (one fake/modal,
    one real/temporal). -/
theorem pastCF_tower_depth {W E P T : Type*} (c : KContext W E P T)
    (w' : W) (t' t'' : T) :
    (((ContextTower.root c).push (subjShift w' t')).push
      (temporalShift t'')).depth = 2 := by
  simp [ContextTower.push, ContextTower.depth, ContextTower.root]

/-! ### Datum structures -/

/-- A morphological datum for a counterfactual conditional: the verb morphology
    in the antecedent and consequent of one CF type in one language. -/
structure CFMorphologyDatum where
  language : String
  cfType : CounterfactualType
  /-- Verb morphology in the antecedent (descriptive). -/
  antecedentForm : String
  /-- Verb morphology in the consequent (descriptive). -/
  consequentForm : String
  hasPastMorph : Bool
  hasImpfMorph : Bool
  hasSubjMorph : Bool
  pastLayers : Nat
  gloss : String
  deriving Repr

/-- Whether a language requires subjunctive in CFs, and whether it has a distinct
    past subjunctive. -/
structure SubjRequirementDatum where
  language : String
  hasPastSubjunctive : Bool
  cfRequiresSubjunctive : Bool
  deriving Repr

/-! ### English data -/

/-- English FLV: "If he were to take the exam tomorrow, …" -/
def english_flv : CFMorphologyDatum where
  language := "English"; cfType := .flv
  antecedentForm := "were to V"; consequentForm := "would V"
  hasPastMorph := true; hasImpfMorph := false; hasSubjMorph := false; pastLayers := 1
  gloss := "If he were to take the exam tomorrow, he would pass."

/-- English PresCF: "If he knew the answer, …" -/
def english_presCF : CFMorphologyDatum where
  language := "English"; cfType := .presCF
  antecedentForm := "V-ed"; consequentForm := "would V"
  hasPastMorph := true; hasImpfMorph := false; hasSubjMorph := false; pastLayers := 1
  gloss := "If he knew the answer, he would tell us."

/-- English PastCF: "If he had taken the exam, …" -/
def english_pastCF : CFMorphologyDatum where
  language := "English"; cfType := .pastCF
  antecedentForm := "had V-ed"; consequentForm := "would have V-ed"
  hasPastMorph := true; hasImpfMorph := false; hasSubjMorph := false; pastLayers := 2
  gloss := "If he had taken the exam yesterday, he would have passed."

/-! ### Greek data -/

/-- Greek FLV ([iatridou-2000], ex (8)): "an + past + impf, tha + past + impf".
    Greek FLV and PresCF have identical morphology; the distinction is by
    predicate type and temporal adverbials, not by morphology (§4, p. 250). -/
def greek_flv : CFMorphologyDatum where
  language := "Greek"; cfType := .flv
  antecedentForm := "an + past + impf"; consequentForm := "tha + past + impf"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 1
  gloss := "An eperne afto to siropi, tha yinotan kala."

/-- Greek PresCF: morphologically identical to the Greek FLV (ex (8)); the CF
    reading arises from the individual-level/stative predicate (Tables 1–2). -/
def greek_presCF : CFMorphologyDatum where
  language := "Greek"; cfType := .presCF
  antecedentForm := "an + past + impf"; consequentForm := "tha + past + impf"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 1
  gloss := "An iksere ti apandisi, tha mas tin elege."

/-- Greek PastCF ([iatridou-2000], ex (5)): the pluperfect (ixe + participle) adds
    a second past layer, distinguishing PastCF from PresCF/FLV. -/
def greek_pastCF : CFMorphologyDatum where
  language := "Greek"; cfType := .pastCF
  antecedentForm := "an + past + past + impf"; consequentForm := "tha + past + past + impf"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 2
  gloss := "An ixe pari to siropi, tha ixe yini kala."

/-! ### French data -/

/-- French FLV: imparfait, conditionnel. -/
def french_flv : CFMorphologyDatum where
  language := "French"; cfType := .flv
  antecedentForm := "imparfait"; consequentForm := "conditionnel"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 1
  gloss := "S'il passait l'examen demain, il réussirait."

/-- French PresCF: imparfait, conditionnel. -/
def french_presCF : CFMorphologyDatum where
  language := "French"; cfType := .presCF
  antecedentForm := "imparfait"; consequentForm := "conditionnel"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 1
  gloss := "S'il savait la réponse, il nous le dirait."

/-- French PastCF ([iatridou-2000], ex (99)): plus-que-parfait, conditionnel passé.
    French uses past *indicative*, not the (lost productive) past subjunctive. -/
def french_pastCF : CFMorphologyDatum where
  language := "French"; cfType := .pastCF
  antecedentForm := "plus-que-parfait"; consequentForm := "conditionnel passé"
  hasPastMorph := true; hasImpfMorph := true; hasSubjMorph := false; pastLayers := 2
  gloss := "S'il avait passé l'examen hier, il aurait réussi."

/-- All morphological data. -/
def allData : List CFMorphologyDatum :=
  [english_flv, english_presCF, english_pastCF,
   greek_flv, greek_presCF, greek_pastCF,
   french_flv, french_presCF, french_pastCF]

/-! ### Subjunctive-requirement data ([iatridou-2000], §6.1) -/

/-- English: no productive past subjunctive (vestigial *were* aside), none required. -/
def english_subj : SubjRequirementDatum where
  language := "English"; hasPastSubjunctive := false; cfRequiresSubjunctive := false

/-- Greek: na-clauses are not CF subjunctive ([iatridou-2000], fn 37); none required. -/
def greek_subj : SubjRequirementDatum where
  language := "Greek"; hasPastSubjunctive := false; cfRequiresSubjunctive := false

/-- French: no productive past subjunctive (only the dubitative); CFs use the past
    indicative ([iatridou-2000], §6.1, ex (99)). -/
def french_subj : SubjRequirementDatum where
  language := "French"; hasPastSubjunctive := false; cfRequiresSubjunctive := false

/-- Italian: has a past subjunctive (congiuntivo trapassato) and requires it in
    CFs — a positive case for [iatridou-2000]'s §6.1 prediction. -/
def italian_subj : SubjRequirementDatum where
  language := "Italian"; hasPastSubjunctive := true; cfRequiresSubjunctive := true

/-- All subjunctive-requirement data. -/
def allSubjData : List SubjRequirementDatum :=
  [english_subj, greek_subj, french_subj, italian_subj]

/-! ### Data theorems -/

/-- Every CF type uses past morphology (generalization 1). -/
theorem all_cfs_have_past : ∀ d ∈ allData, d.hasPastMorph = true := by decide

/-- Each datum's past-layer count matches the ExclF count of its CF type — so
    PastCFs (2 layers) carry strictly more than FLVs/PresCFs (1 layer). -/
theorem pastLayers_eq_exclFCount :
    ∀ d ∈ allData, d.pastLayers = d.cfType.exclFCount := by decide

/-- Each language satisfies [iatridou-2000]'s subjunctive generalization (§6.1). -/
theorem subj_generalization :
    ∀ d ∈ allSubjData,
      iatridouSubjGeneralization d.hasPastSubjunctive d.cfRequiresSubjunctive := by
  unfold iatridouSubjGeneralization; decide

/-! ### ContextTower bridge -/

abbrev CFCtx := KContext Bool Unit Unit ℤ

/-- The actual context: world = true (actual), time = 0 (now). -/
def actualCtx : CFCtx :=
  { world := true, agent := (), addressee := (), time := 0, position := () }

/-- Root tower: the actual speech-act context, depth 0. -/
def actualTower : ContextTower CFCtx := ContextTower.root actualCtx

/-- FLV/PresCF: one subjunctive shift to a counterfactual world (false ≠ true). -/
def presCFTower : ContextTower CFCtx :=
  actualTower.push (subjShift false 0)

/-- The tower has depth 1 — matching one past morpheme layer. -/
theorem presCF_depth : presCFTower.depth = 1 := rfl

/-- Modal ExclF holds: the counterfactual world ≠ the actual world. -/
theorem presCF_modal_exclF : ExclF .modal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF does *not* hold: the time is unchanged (0 = 0). -/
theorem presCF_no_temporal_exclF : ¬ ExclF .temporal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Tower depth (1) matches the English PresCF past-layer count (1). -/
theorem presCF_depth_matches_data : presCFTower.depth = english_presCF.pastLayers := rfl

/-- PastCF: a modal shift (subjunctive, world) plus a temporal shift (an extra
    past layer, time → -5). -/
def pastCFTower : ContextTower CFCtx :=
  presCFTower.push (temporalShift (-5))

/-- The tower has depth 2 — matching two past morpheme layers. -/
theorem pastCF_depth : pastCFTower.depth = 2 := rfl

/-- Modal ExclF holds: the counterfactual world ≠ the actual world. -/
theorem pastCF_modal_exclF : ExclF .modal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF holds: the shifted time (-5) ≠ the speech time (0). -/
theorem pastCF_temporal_exclF : ExclF .temporal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift temporalShift; decide

/-- Tower depth (2) matches the English PastCF past-layer count (2). -/
theorem pastCF_depth_matches_data : pastCFTower.depth = english_pastCF.pastLayers := rfl

/-- Even in a PastCF tower (depth 2), the origin context is preserved. -/
theorem pastCF_origin_preserved : pastCFTower.origin = actualCtx := rfl

end Iatridou2000
