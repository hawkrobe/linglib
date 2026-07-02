import Linglib.Semantics.Modality.Exclusion
import Linglib.Data.Examples.Iatridou2000
import Linglib.Fragments.English.Conditionals
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
open Data.Examples (LinguisticExample)

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

/-- Whether a language requires subjunctive in CFs, and whether it has a distinct
    past subjunctive. -/
structure SubjRequirementDatum where
  language : String
  hasPastSubjunctive : Bool
  cfRequiresSubjunctive : Bool
  deriving Repr

/-! ### Per-language imperfective ([iatridou-2000], generalization 2)

The CF-type *layer counts* (generalization 1) are language-neutral properties of
`CounterfactualType.exclFCount` — see the data theorems below — so there is no
per-(language × CF-type) morphology table. The one morphological ingredient that varies
cross-linguistically is the imperfective: a per-language fact. -/

/-- The languages [iatridou-2000] draws CF morphology from. -/
inductive CFLanguage where
  | english | greek | french
  deriving DecidableEq, Repr

/-- Whether a language uses imperfective morphology in counterfactuals: Greek and French
    do, English does not. Uniform across CF types within a language. Grounded in the
    `impf` tags of `Data/Examples/Iatridou2000.json` by `imperfective_grounded` below. -/
def usesImperfectiveInCF : CFLanguage → Bool
  | .english => false
  | .greek => true
  | .french => true

-- The conditional connective used by the English CF data is `if`, which marks both
-- hypothetical and premise conditionals. The connective is the theory-neutral,
-- Fragment-level lexical fact (cf. Mizuno's use of Japanese `eba` / Mandarin `ruguo`);
-- the CF-type morphology classification below is [iatridou-2000]'s analysis (this study).
#guard English.Conditionals.if_.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

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

/-- Generalization 1 ([iatridou-2000]): every CF type carries past morphology — it has at
    least one ExclF (past) layer. A property of the `CounterfactualType` taxonomy, not a
    per-row stipulation. -/
theorem cf_has_past_layer (t : CounterfactualType) : 1 ≤ t.exclFCount := by
  cases t <;> decide

/-- The pluperfect's extra layer ([iatridou-2000] §3): PastCF carries strictly more ExclF
    layers than the one-layer FLV and PresCF. -/
theorem flv_presCF_fewer_layers :
    CounterfactualType.flv.exclFCount < CounterfactualType.pastCF.exclFCount ∧
    CounterfactualType.presCF.exclFCount < CounterfactualType.pastCF.exclFCount := by decide

/-- Generalization 2 ([iatridou-2000]): the imperfective is not a universal ingredient of
    counterfactuality — some languages use it, others do not. -/
theorem imperfective_not_universal :
    (∃ l, usesImperfectiveInCF l = true) ∧ (∃ l, usesImperfectiveInCF l = false) :=
  ⟨⟨.greek, rfl⟩, ⟨.english, rfl⟩⟩

/-- Each language satisfies [iatridou-2000]'s subjunctive generalization (§6.1). -/
theorem subj_generalization :
    ∀ d ∈ allSubjData,
      iatridouSubjGeneralization d.hasPastSubjunctive d.cfRequiresSubjunctive := by
  unfold iatridouSubjGeneralization; decide

/-! ### Grounding in the glossed stimuli

The generalizations are grounded in the verified glossed sentences of
`Data/Examples/Iatridou2000.json` (generated `Iatridou2000.Examples`): all three CF types
are attested, and the per-language imperfective fact matches the examples' `impf` tags. -/

/-- Value of a `paperFeatures` key, if present. -/
def featureOf (e : LinguisticExample) (k : String) : Option String :=
  (e.paperFeatures.find? (·.1 == k)).map (·.2)

/-- The `impf` tag read as a Bool. -/
def impfTag (e : LinguisticExample) : Option Bool :=
  match featureOf e "impf" with
  | some "yes" => some true
  | some "no"  => some false
  | _          => none

/-- All three CF types are attested in the English stimuli. -/
theorem cf_types_attested :
    featureOf Examples.en_flv "cf_type" = some "flv" ∧
    featureOf Examples.en_presCF "cf_type" = some "presCF" ∧
    featureOf Examples.en_pastCF "cf_type" = some "pastCF" := by decide

/-- `usesImperfectiveInCF` matches the example `impf` tags — English (no), Greek (yes),
    French (yes). Flipping a JSON tag or the generalization breaks this. -/
theorem imperfective_grounded :
    impfTag Examples.en_flv = some (usesImperfectiveInCF .english) ∧
    impfTag Examples.gr_flv = some (usesImperfectiveInCF .greek) ∧
    impfTag Examples.fr_flv = some (usesImperfectiveInCF .french) := by decide

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
theorem presCF_modal_exclF : ExclF .modal presCFTower :=
  subjShift_produces_modal_exclF actualCtx false 0 Bool.false_ne_true

/-- Temporal ExclF does *not* hold: the time is unchanged (0 = 0). -/
theorem presCF_no_temporal_exclF : ¬ ExclF .temporal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Tower depth (1) matches the PresCF ExclF-layer count (1). -/
theorem presCF_depth_matches_data :
    presCFTower.depth = CounterfactualType.presCF.exclFCount := rfl

/-- PastCF: a modal shift (subjunctive, world) plus a temporal shift (an extra
    past layer, time → -5). -/
def pastCFTower : ContextTower CFCtx :=
  presCFTower.push (temporalShift (-5))

/-- The tower has depth 2 — matching two past morpheme layers. -/
theorem pastCF_depth : pastCFTower.depth = 2 := rfl

/-- Modal ExclF holds: the counterfactual world ≠ the actual world. The
    modal+temporal pair is the substrate's PastCF configuration
    (`two_shifts_two_exclFs`). -/
theorem pastCF_modal_exclF : ExclF .modal pastCFTower :=
  (two_shifts_two_exclFs actualCtx false 0 (-5) Bool.false_ne_true (by decide)).1

/-- Temporal ExclF holds: the shifted time (-5) ≠ the speech time (0). -/
theorem pastCF_temporal_exclF : ExclF .temporal pastCFTower :=
  (two_shifts_two_exclFs actualCtx false 0 (-5) Bool.false_ne_true (by decide)).2

/-- Tower depth (2) matches the PastCF ExclF-layer count (2). -/
theorem pastCF_depth_matches_data :
    pastCFTower.depth = CounterfactualType.pastCF.exclFCount := rfl

/-- Even in a PastCF tower (depth 2), the origin context is preserved. -/
theorem pastCF_origin_preserved : pastCFTower.origin = actualCtx := rfl

/-- The present/past-CF ExclF diagnostics are witnessed by Iatridou's (2a)/(2b): (2a) is
    a PresCF (one modal ExclF, tower depth 1), (2b) a PastCF (two ExclFs, depth 2). Ties
    the glossed (2)-stimuli to the ContextTower model. -/
theorem cf_diagnostics_examples :
    featureOf Examples.ex2a "cf_type" = some "presCF" ∧
    featureOf Examples.ex2b "cf_type" = some "pastCF" ∧
    presCFTower.depth = 1 ∧ pastCFTower.depth = 2 :=
  ⟨by decide, by decide, rfl, rfl⟩

end Iatridou2000
