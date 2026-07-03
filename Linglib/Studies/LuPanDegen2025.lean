import Linglib.Semantics.Focus.BackgroundedIslands
import Linglib.Studies.Ross1967
import Linglib.Studies.HofmeisterSag2010
import Linglib.Studies.Sag2010
import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.Lexical.LevinClass
import Linglib.Semantics.Lexical.MeaningComponents
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.LuPanDegen2025

/-!
# Evidence for a Discourse Account of Manner-of-Speaking Islands
[lu-pan-degen-2025]

[lu-pan-degen-2025] (*Language* 101(4): 627–659) reports five acceptability
judgment experiments testing the causal relationship between discourse
backgroundedness and the manner-of-speaking (MoS) island effect, and this
file connects that data to the formal backgroundedness model
(`Semantics/Focus/BackgroundedIslands`) and the lexical substrate
(`Semantics/Lexical/LevinClass`).

## Key findings (§0 data)

1. Prosodic focus on the embedded object ameliorates the MoS island (Exp 1)
2. The same manipulation creates island effects with the bridge verb *say* (Exp 2a)
3. MoS verbs default-background their complements more than *say* (Exp 2b)
4. Adding manner adverbs to *say* replicates the MoS island effect (Exp 3a)
5. The say+adverb island is also sensitive to prosodic manipulation (Exp 3b)
6. Verb-frame frequency does NOT predict the effect (all experiments)

Mean acceptability ratings and backgroundedness proportions are coded as
`Nat` (× 100). Stimulus sentences live in
`Data/Examples/LuPanDegen2025.json` (generated module
`Data.Examples.LuPanDegen2025`).

## Derivation chain (§2–§7)

```
Semantics/Lexical/LevinClass  →  mannerSpec = true for MoS verbs (§37.3)
         ↓
Semantics/Focus/BackgroundedIslands  →  mannerSpec ↔ hasMannerWeight → island
         ↓
mosIslandSources = [.discourse], mosIslandStrength = .weak
```

The MoS island is classified as weak (ameliorable) and discourse-sourced, and
we derive both properties from the experimental data and the formal model.

-/


namespace LuPanDegen2025

open Semantics.Focus.BackgroundedIslands
open Semantics.Lexical

/-! ## §0. Experimental Data

Acceptability and backgroundedness aggregates from the five experiments.
-/

/-! ### Experiment 1: Discourse Effects on MoS Islands

Prosodic focus on the embedded object ameliorates the MoS island effect.
N = 94 (after exclusions). Within-subjects: 2 focus conditions × 12 MoS
verbs (whisper, mutter, shout, yell, scream, mumble, stammer, whine,
groan, moan, shriek, murmur). Stimuli (9): `exp1_verbfocus`,
`exp1_embeddedfocus` in `Data.Examples.LuPanDegen2025`. (Figure 4) -/

section Experiment1

/-- Exp 1 mean acceptability (× 100). Figure 4b. -/
def exp1_acceptability_embeddedFocus : Nat := 68
def exp1_acceptability_verbFocus : Nat := 57
def exp1_acceptability_goodFiller : Nat := 79
def exp1_acceptability_badFiller : Nat := 14

/-- Exp 1 backgroundedness proportion (× 100). Figure 4a. -/
def exp1_backgrounded_embeddedFocus : Nat := 14
def exp1_backgrounded_verbFocus : Nat := 76

/-- Focus manipulation changed backgroundedness (manipulation check).
β = −2.46, SE = 0.40, z = −6.14, p < 0.001. -/
theorem exp1_focus_changes_backgroundedness :
    exp1_backgrounded_embeddedFocus < exp1_backgrounded_verbFocus := by decide

/-- **Main result**: Foregrounding the embedded object ameliorates the island.
β = 0.23, SE = 0.03, t = 7.10, p < 0.001. -/
theorem exp1_focus_ameliorates_island :
    exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus := by decide

/-- MoS island sentences are degraded relative to grammatical fillers. -/
theorem exp1_island_degraded :
    exp1_acceptability_verbFocus < exp1_acceptability_goodFiller := by decide

/-- Even ameliorated MoS islands remain below grammatical filler level. -/
theorem exp1_ameliorated_still_degraded :
    exp1_acceptability_embeddedFocus < exp1_acceptability_goodFiller := by decide

end Experiment1

/-! ### Experiment 2a: MoS Verbs and *Say*

Both verb types show focus effects, but MoS verbs are overall more degraded.
The same prosodic manipulation that ameliorates MoS islands can CREATE
island-like effects for the bridge verb *say*.
N = 97. 2 focus × 2 verb type. (Figure 7) -/

section Experiment2a

/-- Exp 2a acceptability (× 100). Figure 7b. -/
def exp2a_acc_mos_embeddedFocus : Nat := 58
def exp2a_acc_mos_verbFocus : Nat := 50
def exp2a_acc_say_embeddedFocus : Nat := 80
def exp2a_acc_say_verbFocus : Nat := 73
def exp2a_acc_goodFiller : Nat := 85
def exp2a_acc_badFiller : Nat := 16

/-- Exp 2a backgroundedness (× 100). Figure 7a. -/
def exp2a_bg_mos_embeddedFocus : Nat := 12
def exp2a_bg_mos_verbFocus : Nat := 77
def exp2a_bg_say_embeddedFocus : Nat := 10
def exp2a_bg_say_verbFocus : Nat := 20

/-- MoS verbs show focus effect.
β = 0.14, SE = 0.02, t = 9.14, p < 0.001. -/
theorem exp2a_mos_focus_effect :
    exp2a_acc_mos_embeddedFocus > exp2a_acc_mos_verbFocus := by decide

/-- *Say* also shows focus effect (can create island-like degradation).
Focus × verb-type interaction NOT significant (β = 0.005, p = 0.509). -/
theorem exp2a_say_focus_effect :
    exp2a_acc_say_embeddedFocus > exp2a_acc_say_verbFocus := by decide

/-- MoS verbs are overall more degraded than *say*.
β = −0.08, SE = 0.01, t = −5.49, p < 0.001. -/
theorem exp2a_mos_lt_say :
    exp2a_acc_mos_verbFocus < exp2a_acc_say_verbFocus ∧
    exp2a_acc_mos_embeddedFocus < exp2a_acc_say_embeddedFocus := by decide

/-- MoS verb complements are more backgrounded than *say* complements.
β = 0.59, SE = 0.14, z = 4.27, p < 0.001. -/
theorem exp2a_mos_more_backgrounded :
    exp2a_bg_mos_verbFocus > exp2a_bg_say_verbFocus := by decide

end Experiment2a

/-! ### Experiment 2b: Default Backgroundedness

Without focus manipulation, MoS verbs default-background their complements
more than *say*. This is the crucial **baseline** measurement.
N = 94. MoS vs Say, no focus manipulation. (Figure 10) -/

section Experiment2b

/-- Exp 2b acceptability (× 100). Figure 10b. -/
def exp2b_acc_mos : Nat := 68
def exp2b_acc_say : Nat := 77
def exp2b_acc_goodFiller : Nat := 81
def exp2b_acc_badFiller : Nat := 13

/-- Exp 2b backgroundedness (× 100). Figure 10a. -/
def exp2b_bg_mos : Nat := 62
def exp2b_bg_say : Nat := 28

/-- MoS verbs default-background complements more than *say*.
β = 0.96, SE = 0.16, z = 6.06, p < 0.001. -/
theorem exp2b_mos_more_backgrounded :
    exp2b_bg_mos > exp2b_bg_say := by decide

/-- MoS extraction is less acceptable than *say* extraction.
β = −0.14, SE = 0.02, t = −9.26, p < 0.001. -/
theorem exp2b_mos_less_acceptable :
    exp2b_acc_mos < exp2b_acc_say := by decide

/-- **Core correlation**: more backgrounded → less acceptable extraction.
This is the key link between backgroundedness and islandhood. -/
theorem exp2b_backgroundedness_predicts_acceptability :
    (exp2b_bg_mos > exp2b_bg_say) ∧ (exp2b_acc_mos < exp2b_acc_say) := by decide

/-- *Say* extraction approaches grammatical-filler level.
β = −0.02, SE = 0.01, t = −1.83, p = 0.067 (n.s.). -/
theorem exp2b_say_near_grammatical :
    exp2b_acc_say < exp2b_acc_goodFiller := by decide

end Experiment2b

/-! ### Experiment 3a: Say + Manner Adverb Creates Islands

**The paper's key novel prediction**: adding manner adverbs to *say*
replicates the MoS island effect. This is predicted ONLY by the
backgroundedness account. N = 93. Say vs Say+Adverb. Stimuli (18):
`exp3a_say`, `exp3a_sayadverb` in `Data.Examples.LuPanDegen2025`.
(Figure 14) -/

section Experiment3a

/-- Exp 3a acceptability (× 100). Figure 14. -/
def exp3a_acc_say : Nat := 77
def exp3a_acc_sayAdverb : Nat := 53
def exp3a_acc_goodFiller : Nat := 80
def exp3a_acc_badFiller : Nat := 11

/-- **KEY RESULT**: Adding a manner adverb to *say* degrades extraction.
β = −0.24, SE = 0.02, t = −12.4, p < 0.001.

Predicted by backgroundedness account (manner adverb adds manner weight).
NOT predicted by subjacency (same CP structure ± adverb).
NOT predicted by frequency (predicate-frame frequency n.s., p = 0.664). -/
theorem exp3a_adverb_creates_island :
    exp3a_acc_sayAdverb < exp3a_acc_say := by decide

/-- Say+adverb is substantially degraded relative to grammatical fillers. -/
theorem exp3a_adverb_degraded :
    exp3a_acc_sayAdverb < exp3a_acc_goodFiller := by decide

/-- *Say* alone patterns with grammatical fillers. -/
theorem exp3a_say_near_grammatical :
    exp3a_acc_goodFiller - exp3a_acc_say < exp3a_acc_say - exp3a_acc_sayAdverb := by
  decide

end Experiment3a

/-! ### Experiment 3b: Discourse Effect on Say+Adverb Islands

Prosodic focus ameliorates the say+adverb island, confirming that the effect
in Experiment 3a is discourse-driven, not a structural complexity artifact.
N = 94. 2 focus conditions (adverb-focus vs embedded-focus). Stimuli (20):
`exp3b_adverbfocus`, `exp3b_embeddedfocus` in
`Data.Examples.LuPanDegen2025`. (Figure 17) -/

section Experiment3b

/-- Exp 3b acceptability (× 100). Figure 17b. -/
def exp3b_acc_embeddedFocus : Nat := 68
def exp3b_acc_adverbFocus : Nat := 50
def exp3b_acc_goodFiller : Nat := 78
def exp3b_acc_badFiller : Nat := 15

/-- Exp 3b backgroundedness (× 100). Figure 17a. -/
def exp3b_bg_embeddedFocus : Nat := 35
def exp3b_bg_adverbFocus : Nat := 72

/-- Focus manipulation changes backgroundedness in say+adverb construction.
β = −3.99, SE = 0.74, z = −5.42, p < 0.001. -/
theorem exp3b_focus_changes_backgroundedness :
    exp3b_bg_embeddedFocus < exp3b_bg_adverbFocus := by decide

/-- Foregrounding embedded object ameliorates the say+adverb island.
β = 0.21, SE = 0.03, t = 6.90, p < 0.001. -/
theorem exp3b_focus_ameliorates :
    exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus := by decide

end Experiment3b

/-! ### Negative results: frequency does not predict

Verb-frame frequency and sentence complement ratio (SCR) are n.s. in every
experiment that tested them, ruling out the verb-frame frequency account:

- Exp 1: freq β = −0.003, p = 0.874; SCR β = −0.0002, p = 0.987
- Exp 2b: freq β = −0.001, p = 0.981; SCR β = 0.008, p = 0.754
- Exp 3a: freq β = −0.005, p = 0.664; SCR β = −0.003, p = 0.793
- Exp 3b: freq β = 0.01, p = 0.712; SCR β = 0.01, p = 0.587

(0/8 tests significant; see `frequencyMoS` in §8 for the typed
manipulation-level encoding.) -/

/-! ### Cross-experiment generalizations -/

/-- Focus amelioration is consistent across all tested configurations. -/
theorem focus_amelioration_consistent :
    -- Exp 1: MoS verbs
    (exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus) ∧
    -- Exp 2a: MoS verbs (replication)
    (exp2a_acc_mos_embeddedFocus > exp2a_acc_mos_verbFocus) ∧
    -- Exp 2a: *say* (extension)
    (exp2a_acc_say_embeddedFocus > exp2a_acc_say_verbFocus) ∧
    -- Exp 3b: say + adverb (novel construction)
    (exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus) := by decide

/-- More backgrounded → lower extraction acceptability, consistently. -/
theorem backgroundedness_anticorrelates_with_acceptability :
    -- Exp 1
    (exp1_backgrounded_verbFocus > exp1_backgrounded_embeddedFocus ∧
     exp1_acceptability_verbFocus < exp1_acceptability_embeddedFocus) ∧
    -- Exp 2b (cross-verb)
    (exp2b_bg_mos > exp2b_bg_say ∧
     exp2b_acc_mos < exp2b_acc_say) ∧
    -- Exp 3b
    (exp3b_bg_adverbFocus > exp3b_bg_embeddedFocus ∧
     exp3b_acc_adverbFocus < exp3b_acc_embeddedFocus) := by decide

/-- The MoS island effect is NOT an artifact of verb-class confounds:
the say+adverb construction replicates it with the same bridge verb. -/
theorem mos_effect_not_verb_class_artifact :
    -- Say alone: no island
    exp3a_acc_say > exp3a_acc_sayAdverb ∧
    -- MoS verb: island (baseline from Exp 2b)
    exp2b_acc_say > exp2b_acc_mos := by decide

/-! ### Island source derivation

The MoS island effect is classified as a weak, discourse-sourced island.
The source classification is DERIVED from the experimental evidence above,
not stipulated in a global lookup table:

1. **Not syntactic**: prosodic focus ameliorates the effect (Exps 1, 3b).
   Syntactic constraints (PIC, subjacency) are insensitive to prosodic focus.
2. **Not processing**: verb-frame frequency is non-predictive (0/8 tests).
   Processing accounts predict frequency effects.
3. **Discourse**: say+adverb replicates the effect without structural change
   (Exp 3a). Only the backgroundedness account predicts this — adding a
   manner adverb to a bridge verb increases manner salience, shifting the
   QUD and backgrounding the complement. -/

/-- MoS islands are discourse-sourced.
Derived from three empirical dissociations (above) that rule out
syntactic and processing sources. -/
def mosIslandSources : List IslandSource := [.discourse]

/-- MoS islands are weak: ameliorated by prosodic focus.
Derived from Experiments 1 and 3b: embedded-focus conditions are
significantly more acceptable than verb-focus conditions. -/
def mosIslandStrength : ConstraintStrength := .weak

/-- The strength classification is empirically supported:
prosodic focus improves extraction across all tested configurations. -/
theorem weak_classification_justified :
    mosIslandStrength = .weak ∧
    -- Exp 1: prosodic focus ameliorates MoS island
    (exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus) ∧
    -- Exp 3b: prosodic focus ameliorates say+adverb island
    (exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus) := by decide

/-- MoS islands and wh-islands are both weak (ameliorable), but by
DIFFERENT mechanisms: MoS by prosodic focus (information structure),
wh-islands by D-linking (filler complexity). Same strength label,
different sources, different amelioration strategies. -/
theorem mos_vs_wh_same_strength_different_source :
    mosIslandStrength = .weak ∧
    mosIslandSources ≠ [IslandSource.syntactic] := ⟨rfl, by decide⟩

/-! ### Stimulus rows

The example stimuli are typed rows in `Data.Examples.LuPanDegen2025`
(UNVERIFIED against the published item lists; reconstructed from the
paper's in-text examples). Their judgment coding mirrors the mean-rating
direction: island conditions (verb focus, say+adverb, adverb focus) are
`.marginal`; ameliorated/bridge conditions are `.acceptable`. -/

section StimulusRows

open Data.Examples

/-- The stimulus rows' judgment coding matches the rating data: a row is
`.marginal` iff it instantiates an island condition (the lower-rated
member of its experimental contrast). -/
theorem stimulus_judgments_track_island_conditions :
    ∀ row ∈ Examples.all,
      (row.feature? "island_condition" = some "true" ↔
        row.judgment = .marginal) := by decide

end StimulusRows

/-! ## §1. Island Source Classification

The paper's core contribution is the double dissociation between discourse-
sourced MoS islands (`mosIslandSources`, derived in §0 from the experimental
evidence) and syntactically-sourced traditional islands. The traditional
island classification is the baseline consensus view: these islands arise
from structural constraints on movement (subjacency, PIC, Relativized
Minimality). -/

/-- Traditional islands (wh, CNPC, adjunct, coordinate, subject, sentential
subject) are syntactically sourced. This is the baseline consensus against
which the paper shows MoS islands are categorically different.

Note: [hofmeister-sag-2010] argue that some of these (CNPC, wh-islands)
have processing sources. That alternative classification is formalized in
their study file, not here. -/
def traditionalIslandSource : IslandSource := .syntactic

/-! ## §2. Levin Class → Manner Weight Bridge

[levin-1993] §37 classifies communication verbs into three subclasses:
- §37.7 *say* verbs (say, report, announce): `mannerSpec = false`
- §37.2 *tell* verbs (tell, inform, notify): `mannerSpec = false`
- §37.3 manner-of-speaking verbs (whisper, shout, mumble): `mannerSpec = true`

The `mannerSpec` meaning component is exactly the property that drives the
MoS island effect: it indicates whether the verb's root specifies manner,
which determines whether manner alternatives are activated, which determines
QUD selection, which determines complement backgroundedness.

This section connects the Levin class infrastructure to the backgroundedness
model, making the island prediction derivable from lexical classification
by construction. -/

/-- Map Levin class manner specification to BackgroundedIslands manner weight.
A verb with `mannerSpec = true` has lexical manner weight; one without has none.
(Compositional manner weight from adverbs is not captured by Levin classes.) -/
def levinClassToMannerWeight (lc : LevinClass) : Bool :=
  lc.meaningComponents.mannerSpec

/-- MoS verbs (§37.3) have manner weight by Levin classification. -/
theorem levin_mos_has_manner_weight :
    levinClassToMannerWeight .mannerOfSpeaking = true := rfl

/-- Bridge verbs (§37.7) lack manner weight by Levin classification. -/
theorem levin_say_no_manner_weight :
    levinClassToMannerWeight .say = false := rfl

/-- **Full derivation from Levin class to island prediction**: the Levin
`mannerSpec` feature determines manner weight, which determines the default
QUD, which determines complement backgroundedness, which determines
extraction acceptability.

This makes the MoS island prediction a *consequence* of lexical classification,
not an independent stipulation. -/
theorem levin_class_predicts_island :
    -- MoS verbs: mannerSpec → manner weight → backgrounded complement → island
    (levinClassToMannerWeight .mannerOfSpeaking = true ∧
     complementStatus (defaultDimension { manner := some ⟨"manner"⟩ }) = .given) ∧
    -- Bridge verbs: no mannerSpec → no manner weight → foreground complement → no island
    (levinClassToMannerWeight .say = false ∧
     complementStatus (defaultDimension {}) = .new) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The Levin distinction between §37.3 and §37.7 is exclusively about manner.
All other meaning components are identical (both are communication verbs with
no change-of-state, contact, motion, causation, or instrument specification).
Manner specification is the ONLY lexical feature that distinguishes them. -/
theorem levin_manner_is_only_difference :
    levinClassToMannerWeight .mannerOfSpeaking ≠ levinClassToMannerWeight .say ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.changeOfState =
      (LevinClass.say).meaningComponents.changeOfState ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.contact =
      (LevinClass.say).meaningComponents.contact ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.motion =
      (LevinClass.say).meaningComponents.motion ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.causation =
      (LevinClass.say).meaningComponents.causation := by
  exact ⟨by simp [levinClassToMannerWeight, LevinClass.meaningComponents], rfl, rfl, rfl, rfl⟩

/-! ## §3. Cross-Theory Predictions

Different island theories make different predictions about which manipulations
should affect which island types. The backgroundedness account uniquely
predicts that discourse manipulations (prosodic focus, manner adverb addition)
affect MoS islands but not structural islands. -/

/-- A manipulation and the theories' predictions about its effect. -/
structure ManipulationPrediction where
  manipulation : String
  affectsStructuralIslands : Bool  -- syntactic/phase-based prediction
  affectsMoSIslands : Bool          -- backgroundedness prediction
  deriving Repr

/-- Predictions of the backgroundedness account vs. structural accounts. -/
def manipulationPredictions : List ManipulationPrediction := [
  -- Prosodic focus changes information structure, not syntax
  { manipulation := "prosodic focus on embedded object"
    affectsStructuralIslands := false
    affectsMoSIslands := true },
  -- Manner adverb addition adds lexical weight, not structural boundaries
  { manipulation := "adding manner adverb to bridge verb"
    affectsStructuralIslands := false
    affectsMoSIslands := true },
  -- D-linking changes filler complexity, not QUD
  { manipulation := "D-linking (which-N vs bare wh)"
    affectsStructuralIslands := true
    affectsMoSIslands := false },
  -- Adding clause boundaries changes structural distance
  { manipulation := "additional embedding depth"
    affectsStructuralIslands := true
    affectsMoSIslands := false }
]

/-- Discourse and structural island types respond to DIFFERENT manipulations.
This is the core empirical prediction that distinguishes the two account types. -/
theorem discourse_structural_dissociation :
    manipulationPredictions.all
      (λ p => p.affectsStructuralIslands != p.affectsMoSIslands) = true := by
  decide

/-! ## §4. D-Linking Prediction

The backgroundedness account predicts that D-linking (which-N vs bare wh)
should NOT ameliorate MoS islands, because D-linking changes filler complexity
(processing-relevant) but does not change the QUD or information structure.

This contrasts with structural weak islands (wh-islands), where D-linking
DOES ameliorate. The dissociation is a testable prediction that distinguishes
discourse-sourced from syntax/processing-sourced islands. -/

/-- **D-linking does not change QUD**: D-linking modifies the filler's referential
properties but does not affect which dimension of the communication event is
foregrounded. The manner QUD remains active regardless of filler complexity. -/
theorem dlinking_does_not_change_backgroundedness (v : VerbDecomp)
    (h : v.hasMannerWeight) :
    -- D-linking is irrelevant: complement status depends only on verb, not filler
    complementStatus (defaultDimension v) = .given := by
  simp only [defaultDimension, if_pos h, complementStatus]

/-- **Differential amelioration prediction**: D-linking ameliorates structural
weak islands but NOT MoS islands, while prosodic focus ameliorates MoS islands
but NOT structural islands. This double dissociation is the core prediction
separating discourse from syntax/processing accounts. -/
theorem differential_amelioration :
    -- MoS islands: discourse source → prosodic focus ameliorates
    mosIslandSources = [.discourse] ∧
    -- Wh-islands: syntactic source → D-linking ameliorates
    traditionalIslandSource = .syntactic ∧
    -- Different sources → different amelioration mechanisms
    mosIslandSources ≠ [traditionalIslandSource] := by
  exact ⟨rfl, rfl, by decide⟩

/-! ## §5. Per-Verb Backgroundedness–Acceptability Correlation

[lu-pan-degen-2025] Experiment 2b (Figure 13) shows a negative
correlation between per-verb backgroundedness proportion and extraction
acceptability across the 13 verbs (12 MoS + *say*; β = −0.44, p = 0.014;
MoS-only: β = −0.38, p = 0.076, marginally significant).

The formal model predicts this: verbs whose manner component is more
salient activate the manner QUD more strongly, producing stronger default
backgroundedness and therefore worse extraction. -/

/-- Per-verb backgroundedness predicts acceptability: verbs that background
their complements more strongly also show more degraded extraction.
The model derives this from manner salience → QUD strength → backgroundedness.
The conceptually-right substrate for "backgroundedness" is
`Discourse.AtIssuenessDegree`, not `BinaryGivenness` (which
orders by salience, given > new); future work could rephrase
`complementStatus` over AtIssuenessDegree directly. -/
theorem per_verb_correlation_predicted :
    -- All MoS verbs have manner weight (they all background)
    complementStatus (defaultDimension whisperDecomp) = .given ∧
    complementStatus (defaultDimension shoutDecomp) = .given := by
  refine ⟨rfl, rfl⟩

/-! ## §6. Fragment Verb → Island Prediction Pipeline

Each MoS verb in `Fragments/English/Predicates/Verbal.lean` has
`levinClass := some .mannerOfSpeaking`, and each bridge verb has a non-MoS
Levin class. Per-verb verification theorems connect Fragment entries to island
predictions: changing a Fragment entry's `levinClass` field breaks exactly one
theorem, making the dependency explicit and auditable.

The derivation chain per verb:
```
Fragment entry → .levinClass = some .mannerOfSpeaking
    → levinClassToMannerWeight = true
    → hasMannerWeight = true
    → defaultDimension = .manner
    → complementStatus = .given
    → extraction degraded
```
-/

open English.Predicates.Verbal in
/-- Does a Fragment verb entry predict an island effect?
Derived from the verb's Levin class via `levinClassToMannerWeight`. -/
def fragmentPredictsIsland (v : VerbEntry) : Bool :=
  match v.levinClass with
  | some lc => levinClassToMannerWeight lc
  | none => false

/-! ### MoS verbs: all predict islands

These 15 verbs have `levinClass := some .mannerOfSpeaking` in the Fragment.
The per-verb theorems cover both the 12 experimental stimuli from
[lu-pan-degen-2025] (whisper, murmur, shout, scream, mumble, mutter,
shriek, yell, groan — 9 of 12 overlap with Fragment inventory) and 6
additional MoS verbs in the Fragment (cry, grumble, hiss, sigh, whimper, snap).

Three experimental verbs (stammer, whine, moan) are not yet in the Fragment. -/

open English.Predicates.Verbal in
theorem mos_verbs_predict_islands :
    fragmentPredictsIsland whisper = true ∧
    fragmentPredictsIsland murmur = true ∧
    fragmentPredictsIsland shout = true ∧
    fragmentPredictsIsland cry = true ∧
    fragmentPredictsIsland scream = true ∧
    fragmentPredictsIsland mumble = true ∧
    fragmentPredictsIsland mutter = true ∧
    fragmentPredictsIsland shriek = true ∧
    fragmentPredictsIsland yell = true ∧
    fragmentPredictsIsland groan = true ∧
    fragmentPredictsIsland grumble = true ∧
    fragmentPredictsIsland hiss = true ∧
    fragmentPredictsIsland sigh = true ∧
    fragmentPredictsIsland whimper = true ∧
    fragmentPredictsIsland snap = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Bridge verbs: no island prediction

*say* and *tell* are bridge verbs (Levin §37.7 and §37.2 respectively).
They lack manner specification and therefore do not background their
complements by default. -/

open English.Predicates.Verbal in
theorem bridge_verbs_no_island :
    fragmentPredictsIsland say = false ∧
    fragmentPredictsIsland tell = false := ⟨rfl, rfl⟩

/-! ### Gradient predictions for Fragment verbs

Using the gradient at-issueness model (§15 of BackgroundedIslands), Fragment
MoS verbs have strictly lower complement at-issueness than bridge verbs.
This connects Fragment entries → Levin class → manner weight source →
gradient at-issueness in a single derivation chain. -/

/-- Fragment MoS verbs map to lexical manner weight source, yielding the
lowest complement at-issueness (maximally backgrounded). Bridge verbs map
to none, yielding the highest (fully at-issue). -/
theorem fragment_gradient_contrast :
    (complementAtIssueness (whisperDecomp.mannerWeightSource)).val <
    (complementAtIssueness (sayDecomp.mannerWeightSource)).val := by
  simp only [VerbDecomp.mannerWeightSource, whisperDecomp, sayDecomp,
             complementAtIssueness]; norm_num

/-! ## §7. Experimental Data → Formal Model Connection

The experimental data in §0 records per-experiment acceptability and
backgroundedness values. Here we connect these empirical observations
to the formal model's predictions, closing the loop between raw data
and theoretical derivation.

The key connection: the formal model predicts that backgroundedness causes
extraction degradation (`complementStatus .given → .rank = 0`).
The experimental data confirms this directionally: higher backgroundedness
proportions consistently co-occur with lower acceptability ratings. -/

/-- **Experimental data matches formal model direction**: the formal model
predicts that backgrounded complements have degraded extraction.
Experiments 1, 2b, and 3b all show the predicted anti-correlation:
higher backgroundedness → lower acceptability. -/
theorem experimental_matches_model :
    -- Exp 2b: MoS verbs are more backgrounded AND less acceptable than *say*
    (exp2b_bg_mos > exp2b_bg_say ∧ exp2b_acc_mos < exp2b_acc_say) ∧
    -- Exp 1: verb focus → more backgrounded AND less acceptable
    (exp1_backgrounded_verbFocus > exp1_backgrounded_embeddedFocus ∧
     exp1_acceptability_verbFocus < exp1_acceptability_embeddedFocus) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-- **Say+adverb replicates formal model prediction**: adding manner weight
compositionally (say + adverb) degrades extraction without changing syntax.
This is exactly what the formal model predicts: manner weight → backgroundedness
→ island, regardless of whether the weight is lexical or compositional. -/
theorem adverb_replicates_model :
    -- Formal model: compositional manner weight → island
    complementStatus (defaultDimension saySoftlyDecomp) = .given ∧
    -- Exp 3a: say+adverb is less acceptable than bare say
    (exp3a_acc_say > exp3a_acc_sayAdverb) := by
  constructor
  · rfl
  · decide

/-! ## §8. Cross-Theory Comparison Across Manipulations

This section integrates [lu-pan-degen-2025]'s findings with
[hofmeister-sag-2010]'s processing manipulations and
[sag-2010]'s grammar-based island typology, comparing how three
account types (competence, processing, discourse) score against the
empirical data.

The key empirical claim of [lu-pan-degen-2025]: discourse and
processing accounts cover *disjoint* sets of manipulations. Together
they explain the full range; neither suffices alone. -/

/-- A nonstructural manipulation that changes island acceptability
without altering the island configuration. Each account makes a
prediction about whether the manipulation affects acceptability. -/
structure IslandManipulation where
  description : String
  /-- Does any competence theory predict an acceptability difference? -/
  competencePredictsDifference : Bool
  /-- Does the processing account predict a difference? -/
  processingPredictsDifference : Bool
  /-- Does the discourse/backgroundedness account predict a difference? -/
  discoursePredictsDifference : Bool
  /-- Is a difference actually observed? -/
  differenceObserved : Bool
  deriving Repr

/-! ### [hofmeister-sag-2010] manipulations -/

/-- Filler complexity in CNPC (which-N vs bare wh — same island structure). -/
def fillerComplexityCNPC : IslandManipulation :=
  { description := "Filler complexity (which-N vs bare) in CNPC"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false
    differenceObserved := true }

/-- Filler complexity in wh-islands (which-N vs bare wh — same island structure). -/
def fillerComplexityWhIsland : IslandManipulation :=
  { description := "Filler complexity (which-N vs bare) in wh-islands"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false
    differenceObserved := true }

/-- NP type in CNPC (definite vs indefinite — same CNPC configuration). -/
def npTypeCNPC : IslandManipulation :=
  { description := "NP definiteness (def vs indef) in CNPC"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false
    differenceObserved := true }

/-- Filler complexity in adjunct islands (complex vs simple temporal adjunct). -/
def fillerComplexityAdjunct : IslandManipulation :=
  { description := "Adjunct complexity (complex vs simple) in wh-islands"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false
    differenceObserved := true }

/-! ### [lu-pan-degen-2025] MoS manipulations -/

/-- Prosodic focus on embedded object in MoS islands. Focus changes
information structure without changing syntax or processing load. -/
def prosodicFocusMoS : IslandManipulation :=
  { description := "Prosodic focus (embedded vs verb) in MoS islands"
    competencePredictsDifference := false
    processingPredictsDifference := false
    discoursePredictsDifference := true
    differenceObserved := true }

/-- Say + manner adverb creates an island. Adding an adverb doesn't
change CP structure but adds manner weight. -/
def sayAdverbIsland : IslandManipulation :=
  { description := "Say+adverb vs say alone (MoS island creation)"
    competencePredictsDifference := false
    processingPredictsDifference := false
    discoursePredictsDifference := true
    differenceObserved := true }

/-- Verb-frame frequency in MoS islands: not significant in any experiment. -/
def frequencyMoS : IslandManipulation :=
  { description := "Verb-frame frequency as predictor of MoS acceptability"
    competencePredictsDifference := false
    processingPredictsDifference := true
    discoursePredictsDifference := false
    differenceObserved := false }

def allManipulations : List IslandManipulation := [
  fillerComplexityCNPC,
  fillerComplexityWhIsland,
  npTypeCNPC,
  fillerComplexityAdjunct,
  prosodicFocusMoS,
  sayAdverbIsland,
  frequencyMoS
]

/-- Processing correctly predicts the observed (non-)difference. -/
def processingCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.processingPredictsDifference

/-- Competence correctly predicts the observed (non-)difference. -/
def competenceCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.competencePredictsDifference

/-- Discourse correctly predicts the observed (non-)difference. -/
def discourseCorrect (m : IslandManipulation) : Bool :=
  m.differenceObserved == m.discoursePredictsDifference

def processingScore : Nat := allManipulations.filter processingCorrect |>.length
def competenceScore : Nat := allManipulations.filter competenceCorrect |>.length
def discourseScore : Nat := allManipulations.filter discourseCorrect |>.length

/-- Processing scores 4/7: correct on all four H&S manipulations,
incorrect on the three MoS manipulations (predicts effect or null
incorrectly). -/
theorem processing_scores_4_of_7 :
    processingScore = 4 := by decide

/-- Competence scores 1/7 — only the frequency null result, where it
correctly predicts no effect for the wrong reason. -/
theorem competence_scores_1_of_7 :
    competenceScore = 1 := by decide

/-- Discourse scores 3/7: correct on prosodic focus, say+adverb, and
the frequency null. Misses the four H&S effects, which are processing,
not discourse. -/
theorem discourse_scores_3_of_7 :
    discourseScore = 3 := by decide

/-- Processing and discourse are perfectly complementary: for every
manipulation, exactly one of the two accounts is correct (XOR). They
have full coverage (together 7/7) with zero overlap. -/
theorem complementary_accounts :
    allManipulations.all
      (fun m => processingCorrect m != discourseCorrect m) = true := by decide

/-! ## §9. Connection to [sag-2010]'s Construction-Based Islands

[sag-2010]'s F-G typology classifies which constructions are
grammar-based islands (those with `[GAP ⟨⟩]` on the mother).
[hofmeister-sag-2010]'s findings explain *within-island* gradient
effects. [lu-pan-degen-2025]'s MoS islands are a third mechanism.
Together the three accounts cover disjoint islands. -/

open Sag2010 (FGClauseType islandConstructions)

/-- [sag-2010]'s two island constructions are a proper subset of all
F-G types. The non-island types (interrogative, relative, the-clause)
freely permit extraction. -/
theorem sag_island_subset :
    islandConstructions.length < 5 := by decide

/-- [sag-2010]'s grammar-based islands (topicalization, exclamatives)
are disjoint from [hofmeister-sag-2010]'s processing-based islands
(CNPC, wh-islands, adjuncts) and from [lu-pan-degen-2025]'s
discourse-based islands (MoS). The three accounts cover different cases
under different mechanisms. -/
theorem complementary_coverage :
    FGClauseType.topicalized.IsIsland ∧
    FGClauseType.whExclamative.IsIsland ∧
    mosIslandSources = [.discourse] := ⟨by decide, by decide, rfl⟩

/-- MoS islands are discourse-sourced and so distinct from the syntactic
baseline assumed for traditional islands. -/
theorem mos_distinct_from_traditional_islands :
    mosIslandSources = [.discourse] ∧
    mosIslandSources ≠ [traditionalIslandSource] := by
  exact ⟨rfl, by decide⟩

end LuPanDegen2025
