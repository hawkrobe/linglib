import Linglib.Phenomena.Islands.Data

/-!
# Manner-of-Speaking Island Effects: Experimental Data

Empirical data from Lu, Pan & Degen (2025), "Evidence for a discourse account
of manner-of-speaking islands," *Language* 101(4): 627–659.

Five acceptability judgment experiments testing the causal relationship between
discourse backgroundedness and the manner-of-speaking (MoS) island effect.

## Key Findings

1. Prosodic focus on the embedded object ameliorates the MoS island (Exp 1)
2. The same manipulation creates island effects with the bridge verb *say* (Exp 2a)
3. MoS verbs default-background their complements more than *say* (Exp 2b)
4. Adding manner adverbs to *say* replicates the MoS island effect (Exp 3a)
5. The say+adverb island is also sensitive to prosodic manipulation (Exp 3b)
6. Verb-frame frequency does NOT predict the effect (all experiments)

All acceptability ratings coded as Nat (mean × 100, 0 = completely unacceptable,
100 = completely acceptable). Backgroundedness proportions coded as Nat (× 100).

## References

- Lu, J., Pan, D., & Degen, J. (2025). Evidence for a discourse account of
  manner-of-speaking islands. *Language* 101(4): 627–659.
  DOI: https://doi.org/10.1353/lan.2025.a978271
-/

namespace Phenomena.Islands.MannerOfSpeaking

/-! ## Verb Inventory -/

/-- Manner-of-speaking verbs used in the experiments (12 verbs).
These verbs lexically encode the manner of verbal communication. -/
inductive MoSVerb where
  | whisper | mutter | shout | yell | scream | mumble
  | stammer | whine | groan | moan | shriek | murmur
  deriving DecidableEq, Repr, BEq

/-- Focus conditions manipulated via prosodic capitalization/bolding. -/
inductive FocusCondition where
  /-- Matrix verb capitalized: foregrounds verb, backgrounds complement -/
  | verbFocus
  /-- Embedded object capitalized: foregrounds embedded object -/
  | embeddedFocus
  /-- Manner adverb capitalized (Exp 3b only) -/
  | adverbFocus
  deriving DecidableEq, Repr, BEq

/-- Verb types compared across experiments. -/
inductive VerbType where
  | mos         -- Manner-of-speaking verb (whisper, shout, etc.)
  | say         -- Bridge verb *say*
  | sayAdverb   -- *say* + manner adverb (say softly, say loudly, etc.)
  deriving DecidableEq, Repr, BEq

/-! ## Experiment 1: Discourse Effects on MoS Islands

Prosodic focus on the embedded object ameliorates the MoS island effect.
N = 94 (after exclusions). Within-subjects: 2 focus conditions × MoS verbs.

Example stimuli (9):
- Verb-focus:     "John didn't **WHISPER** that Mary met with the lawyer."
                  "Then who did John whisper that Mary met with?"
- Embedded-focus: "John didn't whisper that Mary met with the **LAWYER**."
                  "Then who did John whisper that Mary met with?"

(Figure 4)
-/

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
    exp1_backgrounded_embeddedFocus < exp1_backgrounded_verbFocus := by native_decide

/-- **Main result**: Foregrounding the embedded object ameliorates the island.
β = 0.23, SE = 0.03, t = 7.10, p < 0.001. -/
theorem exp1_focus_ameliorates_island :
    exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus := by native_decide

/-- MoS island sentences are degraded relative to grammatical fillers. -/
theorem exp1_island_degraded :
    exp1_acceptability_verbFocus < exp1_acceptability_goodFiller := by native_decide

/-- Even ameliorated MoS islands remain below grammatical filler level. -/
theorem exp1_ameliorated_still_degraded :
    exp1_acceptability_embeddedFocus < exp1_acceptability_goodFiller := by native_decide

end Experiment1

/-! ## Experiment 2a: MoS Verbs and *Say*

Both verb types show focus effects, but MoS verbs are overall more degraded.
The same prosodic manipulation that ameliorates MoS islands can CREATE
island-like effects for the bridge verb *say*.
N = 97. 2 focus × 2 verb type.

(Figure 7)
-/

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
    exp2a_acc_mos_embeddedFocus > exp2a_acc_mos_verbFocus := by native_decide

/-- *Say* also shows focus effect (can create island-like degradation).
Focus × verb-type interaction NOT significant (β = 0.005, p = 0.509). -/
theorem exp2a_say_focus_effect :
    exp2a_acc_say_embeddedFocus > exp2a_acc_say_verbFocus := by native_decide

/-- MoS verbs are overall more degraded than *say*.
β = −0.08, SE = 0.01, t = −5.49, p < 0.001. -/
theorem exp2a_mos_lt_say :
    exp2a_acc_mos_verbFocus < exp2a_acc_say_verbFocus ∧
    exp2a_acc_mos_embeddedFocus < exp2a_acc_say_embeddedFocus := by
  constructor <;> native_decide

/-- MoS verb complements are more backgrounded than *say* complements.
β = 0.59, SE = 0.14, z = 4.27, p < 0.001. -/
theorem exp2a_mos_more_backgrounded :
    exp2a_bg_mos_verbFocus > exp2a_bg_say_verbFocus := by native_decide

end Experiment2a

/-! ## Experiment 2b: Default Backgroundedness

Without focus manipulation, MoS verbs default-background their complements
more than *say*. This is the crucial **baseline** measurement.
N = 94. MoS vs Say, no focus manipulation.

(Figure 10)
-/

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
    exp2b_bg_mos > exp2b_bg_say := by native_decide

/-- MoS extraction is less acceptable than *say* extraction.
β = −0.14, SE = 0.02, t = −9.26, p < 0.001. -/
theorem exp2b_mos_less_acceptable :
    exp2b_acc_mos < exp2b_acc_say := by native_decide

/-- **Core correlation**: more backgrounded → less acceptable extraction.
This is the key link between backgroundedness and islandhood. -/
theorem exp2b_backgroundedness_predicts_acceptability :
    (exp2b_bg_mos > exp2b_bg_say) ∧ (exp2b_acc_mos < exp2b_acc_say) := by
  constructor <;> native_decide

/-- *Say* extraction approaches grammatical-filler level.
β = −0.02, SE = 0.01, t = −1.83, p = 0.067 (n.s.). -/
theorem exp2b_say_near_grammatical :
    exp2b_acc_say < exp2b_acc_goodFiller := by native_decide

end Experiment2b

/-! ## Experiment 3a: Say + Manner Adverb Creates Islands

**The paper's key novel prediction**: adding manner adverbs to *say* replicates
the MoS island effect. This is predicted ONLY by the backgroundedness account.
N = 93. Say vs Say+Adverb.

Example stimuli (18):
- *Say*:        "John didn't say that Mary met with the lawyer."
                "Then who did John say that Mary met with?"
- *Say+Adverb*: "John didn't say softly that Mary met with the lawyer."
                "Then who did John say softly that Mary met with?"

(Figure 14)
-/

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
    exp3a_acc_sayAdverb < exp3a_acc_say := by native_decide

/-- Say+adverb is substantially degraded relative to grammatical fillers. -/
theorem exp3a_adverb_degraded :
    exp3a_acc_sayAdverb < exp3a_acc_goodFiller := by native_decide

/-- *Say* alone patterns with grammatical fillers. -/
theorem exp3a_say_near_grammatical :
    exp3a_acc_goodFiller - exp3a_acc_say < exp3a_acc_say - exp3a_acc_sayAdverb := by
  native_decide

end Experiment3a

/-! ## Experiment 3b: Discourse Effect on Say+Adverb Islands

Prosodic focus ameliorates the say+adverb island, confirming that the effect
in Experiment 3a is discourse-driven, not a structural complexity artifact.
N = 94. 2 focus conditions (adverb-focus vs embedded-focus).

Example stimuli (20):
- Adverb-focus:    "John didn't say **SOFTLY** that Mary met with the lawyer."
                   "Then who did John say softly that Mary met with?"
- Embedded-focus:  "John didn't say softly that Mary met with the **LAWYER**."
                   "Then who did John say softly that Mary met with?"

(Figure 17)
-/

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
    exp3b_bg_embeddedFocus < exp3b_bg_adverbFocus := by native_decide

/-- Foregrounding embedded object ameliorates the say+adverb island.
β = 0.21, SE = 0.03, t = 6.90, p < 0.001. -/
theorem exp3b_focus_ameliorates :
    exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus := by native_decide

end Experiment3b

/-! ## Negative Results: Frequency Does Not Predict

Verb-frame frequency and sentence complement ratio (SCR) do not significantly
predict the MoS island effect in ANY experiment. This rules out the
verb-frame frequency account (Liu et al. 2019, 2022; Kothari 2008). -/

section FrequencyNullEffects

/-- A regression coefficient that did not reach significance. -/
structure NullEffect where
  /-- Standardized coefficient × 1000 -/
  β : Int
  /-- p > 0.05 (not significant) -/
  p_gt_05 : Bool
  deriving Repr

/-- Exp 1: verb-frame frequency n.s. (β = −0.003, p = 0.874). -/
def exp1_freq : NullEffect := { β := -3, p_gt_05 := true }

/-- Exp 1: SCR n.s. (β = −0.0002, p = 0.987). -/
def exp1_scr : NullEffect := { β := 0, p_gt_05 := true }

/-- Exp 2b: verb-frame frequency n.s. (β = −0.001, p = 0.981). -/
def exp2b_freq : NullEffect := { β := -1, p_gt_05 := true }

/-- Exp 2b: SCR n.s. (β = 0.008, p = 0.754). -/
def exp2b_scr : NullEffect := { β := 8, p_gt_05 := true }

/-- Exp 3a: predicate-frame frequency n.s. (β = −0.005, p = 0.664). -/
def exp3a_freq : NullEffect := { β := -5, p_gt_05 := true }

/-- Exp 3a: SCR n.s. (β = −0.003, p = 0.793). -/
def exp3a_scr : NullEffect := { β := -3, p_gt_05 := true }

/-- Exp 3b: predicate-frame frequency n.s. (β = 0.01, p = 0.712). -/
def exp3b_freq : NullEffect := { β := 10, p_gt_05 := true }

/-- Exp 3b: SCR n.s. (β = 0.01, p = 0.587). -/
def exp3b_scr : NullEffect := { β := 10, p_gt_05 := true }

/-- Frequency is never significant across all experiments. -/
theorem frequency_never_significant :
    exp1_freq.p_gt_05 ∧ exp1_scr.p_gt_05 ∧
    exp2b_freq.p_gt_05 ∧ exp2b_scr.p_gt_05 ∧
    exp3a_freq.p_gt_05 ∧ exp3a_scr.p_gt_05 ∧
    exp3b_freq.p_gt_05 ∧ exp3b_scr.p_gt_05 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FrequencyNullEffects

/-! ## Cross-Experiment Generalizations -/

/-- Focus amelioration is consistent across all tested configurations. -/
theorem focus_amelioration_consistent :
    -- Exp 1: MoS verbs
    (exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus) ∧
    -- Exp 2a: MoS verbs (replication)
    (exp2a_acc_mos_embeddedFocus > exp2a_acc_mos_verbFocus) ∧
    -- Exp 2a: *say* (extension)
    (exp2a_acc_say_embeddedFocus > exp2a_acc_say_verbFocus) ∧
    -- Exp 3b: say + adverb (novel construction)
    (exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

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
     exp3b_acc_adverbFocus < exp3b_acc_embeddedFocus) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> native_decide

/-- The MoS island effect is NOT an artifact of verb-class confounds:
the say+adverb construction replicates it with the same bridge verb. -/
theorem mos_effect_not_verb_class_artifact :
    -- Say alone: no island
    exp3a_acc_say > exp3a_acc_sayAdverb ∧
    -- MoS verb: island (baseline from Exp 2b)
    exp2b_acc_say > exp2b_acc_mos := by
  constructor <;> native_decide

/-! ## Bridge to Islands/Data.lean

The MoS island effect is classified as a weak, discourse-sourced island.
These theorems connect our experimental data to the shared island infrastructure. -/

section IslandBridge

/-- MoS islands are classified as weak — ameliorable by prosodic focus.
This is empirically justified by Experiments 1 and 3b. -/
theorem mos_island_is_weak :
    constraintStrength .mannerOfSpeaking = .weak := rfl

/-- MoS islands are discourse-sourced, not syntactic.
Justified by: (1) prosodic focus ameliorates the effect (Exps 1, 3b),
(2) say+adverb replicates it without structural change (Exp 3a),
(3) frequency is not predictive (all experiments). -/
theorem mos_island_is_discourse :
    constraintSource .mannerOfSpeaking = .discourse := rfl

/-- The ameliorability of MoS islands (weak classification) is empirically supported:
prosodic focus improves extraction across all tested configurations. -/
theorem weak_classification_justified :
    constraintStrength .mannerOfSpeaking = .weak ∧
    -- Exp 1: prosodic focus ameliorates MoS island
    (exp1_acceptability_embeddedFocus > exp1_acceptability_verbFocus) ∧
    -- Exp 3b: prosodic focus ameliorates say+adverb island
    (exp3b_acc_embeddedFocus > exp3b_acc_adverbFocus) := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

/-- MoS islands differ from traditional weak islands (e.g., wh-islands):
traditional weak islands are ameliorated by D-linking (filler complexity),
while MoS islands are ameliorated by prosodic focus (information structure).
Both are classified as `.weak`, but the amelioration mechanisms differ. -/
theorem mos_and_wh_both_weak :
    constraintStrength .mannerOfSpeaking = .weak ∧
    constraintStrength .embeddedQuestion = .weak := ⟨rfl, rfl⟩

/-- MoS islands differ from traditional weak islands in source:
wh-islands are syntactically sourced; MoS islands are discourse-sourced. -/
theorem mos_vs_wh_different_source :
    constraintSource .mannerOfSpeaking ≠ constraintSource .embeddedQuestion := by
  simp [constraintSource]

end IslandBridge

end Phenomena.Islands.MannerOfSpeaking
