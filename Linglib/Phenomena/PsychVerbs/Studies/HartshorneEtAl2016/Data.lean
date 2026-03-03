import Linglib.Phenomena.PsychVerbs.Data

/-!
# @cite{hartshorne-etal-2016} — Empirical Data

@cite{hartshorne-etal-2016}

Psych verbs, the linking problem, and the acquisition of language.
Cognition 157: 268–288.

## Core empirical claim

The experiencer-subject / experiencer-object split maps onto a semantic
distinction between **habitual attitudes** and **caused emotional episodes**:

| Verb class | Semantic type | Example |
|-----------|---------------|---------|
| Fear-type (Class I, exp-subj) | Habitual attitude | "Mary fears spiders" |
| Frighten-type (Class II, exp-obj) | Caused emotional episode | "Spiders frighten Mary" |

This is diagnosed by three empirical properties:
1. **Duration**: attitudes are longer-lasting than episodes
2. **Causation**: episodes encode causal responsibility of stimulus; attitudes do not
3. **Cross-linguistic**: the mapping holds in English, Mandarin, Korean, Japanese

## Semantic structures (Fig. 11)

- Attitudes: BE(experiencer, emotional_state ABOUT target)
- Episodes: CAUSE(stimulus, BECOME(experiencer, emotional_state))

## Linking mechanism (Section 5.4.1)

**Prominence preservation**: the highest argument in the semantic structure
maps to subject. For attitudes, experiencer is the argument of BE (the main
predicate), so it is highest → subject. For episodes, stimulus is the argument
of CAUSE (the outermost predicate), so it is highest → subject.

## Studies

| Study | Language | Population | Finding |
|-------|----------|-----------|---------|
| 1 | English | Adults | Fear-type rated longer duration |
| 2–4 | English, Mandarin, Korean, Japanese | Adults | Frighten-type rated higher causation |
| 5 | English | Adults (novel verbs) | Generalization to nonce verbs |
| 6–7 | Japanese | Adults (novel verbs) | Generalization + morphological cue |
| 8 | Russian | Adults (novel verbs) | Generalization cross-linguistically |
| 9 | English | Children (4–5 y.o.) | Early emergence of the distinction |
-/

namespace Phenomena.PsychVerbs.Studies.HartshorneEtAl2016

open Phenomena.PsychVerbs.Data (PsychVerbClass ClassIIReading SubjectRole)

-- ════════════════════════════════════════════════════
-- § 1. Semantic Type Distinction
-- ════════════════════════════════════════════════════

/-- The two semantic types for psych verbs (@cite{hartshorne-etal-2016}, Fig. 11).

    This is the paper's central theoretical claim: psych verb classes
    correspond to distinct semantic types, not merely different linking
    patterns. -/
inductive SemanticType where
  /-- BE(experiencer, emotional_state ABOUT target).
      Enduring psychological state directed at a target. -/
  | habitualAttitude
  /-- CAUSE(stimulus, BECOME(experiencer, emotional_state)).
      Specific instance where a stimulus causes an emotion. -/
  | causedEpisode
  deriving DecidableEq, BEq, Repr

/-- Map B&R class to Hartshorne et al.'s semantic type. -/
def PsychVerbClass.toSemanticType : PsychVerbClass → Option SemanticType
  | .classI => some .habitualAttitude
  | .classII => some .causedEpisode
  | .classIII => none

/-- Map Class II reading to semantic type.
    Eventive Class II = caused episode (clear mapping).
    Stative Class II does not cleanly map to either Hartshorne category:
    stative frighten-type verbs ("concern", "bore") still encode stimulus
    causation (unlike attitudes) but have longer duration than eventive
    Class II (p. 273: avg 3.7 vs 2.9 vs fear-type 5.2). -/
def ClassIIReading.toSemanticType : ClassIIReading → Option SemanticType
  | .eventive => some .causedEpisode
  | .stative => none

-- ════════════════════════════════════════════════════
-- § 2. Empirical Properties
-- ════════════════════════════════════════════════════

/-- Properties that distinguish the two semantic types empirically. -/
structure SemanticTypeProfile where
  /-- Does the verb encode longer duration?
      Attitudes = true (enduring), episodes = false (transient). -/
  longerDuration : Bool
  /-- Does the verb encode causal responsibility of the stimulus?
      Episodes = true (CAUSE), attitudes = false (no CAUSE). -/
  stimulusCausal : Bool
  /-- Does the verb involve a transition (BECOME)?
      Episodes = true (BECOME), attitudes = false (BE). -/
  involvesBecome : Bool
  deriving DecidableEq, BEq, Repr

/-- Profile for habitual attitudes (fear-type).
    Long duration, no causal responsibility, no transition. -/
def attitudeProfile : SemanticTypeProfile :=
  { longerDuration := true
    stimulusCausal := false
    involvesBecome := false }

/-- Profile for caused emotional episodes (frighten-type).
    Short duration, causal responsibility, involves transition. -/
def episodeProfile : SemanticTypeProfile :=
  { longerDuration := false
    stimulusCausal := true
    involvesBecome := true }

/-- The two profiles differ on every dimension. -/
theorem profiles_differ_on_all :
    attitudeProfile.longerDuration ≠ episodeProfile.longerDuration ∧
    attitudeProfile.stimulusCausal ≠ episodeProfile.stimulusCausal ∧
    attitudeProfile.involvesBecome ≠ episodeProfile.involvesBecome := by
  exact ⟨by decide, by decide, by decide⟩

/-- Map semantic type to its expected profile. -/
def SemanticType.expectedProfile : SemanticType → SemanticTypeProfile
  | .habitualAttitude => attitudeProfile
  | .causedEpisode => episodeProfile

-- ════════════════════════════════════════════════════
-- § 3. Prominence-Based Linking (Section 5.4.1)
-- ════════════════════════════════════════════════════

/-- The structurally prominent role in each semantic type (Section 5.4.1).

    In the attitude structure BE(experiencer, state ABOUT target),
    experiencer is the highest argument (argument of the main predicate BE).

    In the episode structure CAUSE(stimulus, BECOME(experiencer, state)),
    stimulus is the highest argument (argument of the outermost predicate
    CAUSE).

    This determines linking via prominence preservation: the highest
    argument maps to subject position. -/
def SemanticType.prominentRole : SemanticType → SubjectRole
  | .habitualAttitude => .experiencer
  | .causedEpisode => .stimulus

/-- Prominence preservation (@cite{hartshorne-etal-2016}, Section 5.4.1):
    the most prominent argument in the semantic decomposition becomes the
    subject. This is the paper's central theoretical claim about HOW
    semantic type determines argument structure.

    The predicted subject role from prominence matches the observed
    Belletti & Rizzi class pattern: Class I → experiencer-subject,
    Class II → stimulus-subject. -/
theorem prominence_determines_linking (c : PsychVerbClass) (t : SemanticType)
    (h : PsychVerbClass.toSemanticType c = some t) :
    PsychVerbClass.expectedSubjectRole c = some (SemanticType.prominentRole t) := by
  cases c <;> simp [PsychVerbClass.toSemanticType] at h <;> subst h <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Cross-Linguistic Data
-- ════════════════════════════════════════════════════

/-- Languages tested in @cite{hartshorne-etal-2016}. -/
inductive Language where
  | english | mandarin | korean | japanese | russian
  deriving DecidableEq, BEq, Repr

/-- Cross-linguistic replication datum: the attitude/episode distinction
    holds in each language tested. -/
structure CrossLinguisticDatum where
  language : Language
  /-- Do fear-type verbs rate higher on duration than frighten-type? -/
  fearLongerDuration : Bool
  /-- Do frighten-type verbs rate higher on causation than fear-type? -/
  frightenMoreCausal : Bool
  deriving BEq, Repr

/-- Cross-linguistic data: all four languages show the same pattern.
    Experiments 1–4, summarized in Fig. 7–8. -/
def crossLinguisticData : List CrossLinguisticDatum := [
  ⟨.english,  true, true⟩,  -- Experiment 1
  ⟨.mandarin, true, true⟩,  -- Experiment 2
  ⟨.korean,   true, true⟩,  -- Experiment 3
  ⟨.japanese, true, true⟩   -- Experiment 4
]

/-- The attitude/episode distinction is universal across tested languages. -/
theorem crosslinguistic_universal :
    crossLinguisticData.all (fun d => d.fearLongerDuration && d.frightenMoreCausal)
      = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Generalization & Acquisition
-- ════════════════════════════════════════════════════

/-- A generalization experiment: does the semantic type distinction
    guide argument structure assignment for novel (nonce) verbs? -/
structure GeneralizationDatum where
  language : Language
  isChildPopulation : Bool
  /-- Attitude semantics → experiencer-subject preference? -/
  attitudePredictExpSubj : Bool
  /-- Episode semantics → experiencer-object preference? -/
  episodePredictExpObj : Bool
  deriving BEq, Repr

/-- Generalization data from Experiments 5–9.
    Adults and children use the semantic type distinction to determine
    argument structure for novel verbs across languages. -/
def generalizationData : List GeneralizationDatum := [
  ⟨.english,  false, true, true⟩,  -- Experiment 5: English adults
  ⟨.japanese, false, true, true⟩,  -- Experiments 6–7: Japanese adults
  ⟨.russian,  false, true, true⟩,  -- Experiment 8: Russian adults
  ⟨.english,  true,  true, true⟩   -- Experiment 9: English children (4–5 y.o.)
]

/-- All generalization experiments show the predicted pattern. -/
theorem generalization_universal :
    generalizationData.all (fun d => d.attitudePredictExpSubj && d.episodePredictExpObj)
      = true := by native_decide

/-- The distinction emerges early in development (4–5 y.o.). -/
theorem children_generalize :
    (generalizationData.filter (·.isChildPopulation)).all
      (fun d => d.attitudePredictExpSubj && d.episodePredictExpObj) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Verb-Level Data
-- ════════════════════════════════════════════════════

/-- A psych verb datum from Hartshorne et al.'s norming studies. -/
structure VerbDatum where
  verb : String
  semanticType : SemanticType
  brClass : PsychVerbClass
  deriving BEq, Repr

/-- Representative verb data from @cite{hartshorne-etal-2016}.
    Fear-type verbs are habitual attitudes, frighten-type are caused episodes. -/
def verbData : List VerbDatum := [
  -- Fear-type (exp-subject, habitual attitude)
  ⟨"fear", .habitualAttitude, .classI⟩,
  ⟨"like", .habitualAttitude, .classI⟩,
  ⟨"love", .habitualAttitude, .classI⟩,
  ⟨"hate", .habitualAttitude, .classI⟩,
  ⟨"enjoy", .habitualAttitude, .classI⟩,
  ⟨"dread", .habitualAttitude, .classI⟩,
  ⟨"admire", .habitualAttitude, .classI⟩,
  ⟨"respect", .habitualAttitude, .classI⟩,
  -- Frighten-type (exp-object, caused episode)
  ⟨"frighten", .causedEpisode, .classII⟩,
  ⟨"amuse", .causedEpisode, .classII⟩,
  ⟨"bore", .causedEpisode, .classII⟩,
  ⟨"scare", .causedEpisode, .classII⟩,
  ⟨"surprise", .causedEpisode, .classII⟩,
  ⟨"shock", .causedEpisode, .classII⟩,
  ⟨"irritate", .causedEpisode, .classII⟩,
  ⟨"annoy", .causedEpisode, .classII⟩
]

/-- All fear-type verbs in the data are habitual attitudes. -/
theorem fear_type_are_attitudes :
    (verbData.filter (·.brClass == .classI)).all
      (·.semanticType == .habitualAttitude) = true := by native_decide

/-- All frighten-type verbs in the data are caused episodes. -/
theorem frighten_type_are_episodes :
    (verbData.filter (·.brClass == .classII)).all
      (·.semanticType == .causedEpisode) = true := by native_decide

/-- The class–type mapping is perfect: no verb has a mismatched type. -/
theorem class_type_alignment :
    verbData.all (fun d =>
      match d.brClass with
      | .classI => d.semanticType == .habitualAttitude
      | .classII => d.semanticType == .causedEpisode
      | .classIII => true  -- not tested
    ) = true := by native_decide

end Phenomena.PsychVerbs.Studies.HartshorneEtAl2016
