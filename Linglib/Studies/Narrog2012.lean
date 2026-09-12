import Linglib.Semantics.Modality.Narrog

/-!
# Narrog (2012): Modality, Subjectivity, and Semantic Change

This file formalizes the category hierarchy and the category-climbing hypothesis of
[narrog-2012]. Scope data from Japanese order the grammatical categories of the verbal
clause from voice and benefactives at the bottom through aspect, dynamic and deontic
modality, negation and epistemic modality, and tense to mood and illocutionary
modification at the top (`GramCategory`, `GramCategory.scopeLevel`), an empirical
hierarchy finer than the stipulated universal one of [cinque-1999]; epistemic modality
outscopes deontic and dynamic modality, and mood outscopes modality proper
(`epistemic_outscopes_deontic`, `mood_outscopes_modality`). Scope level determines speaker
orientation (`scope_implies_orientation`), and the categories that serve as diachronic
sources of modality lie strictly below those that serve as its targets
(`GramCategory.changeRole`, `source_below_target`), the structural precondition of the
hypothesis that semantic change involving grammatical categories climbs from narrower to
wider scope. Langacker's stages in the development of the English modals ascend the
orientation levels in the same direction (`langackerStages`, `langacker_stages_monotone`).

## Implementation notes

The scope levels follow the combined hierarchy of the book's third chapter, categories on
a shared level being unordered; the source and target classification extends the book's
table of non-modal categories by placing the modal categories at the bidirectional level.
The directionality of the attested changes themselves is proved in `Studies/Narrog2010`.

## References

* [narrog-2012]
* [narrog-2009a]
* [cinque-1999]
-/

namespace Narrog2012

open Modality.Narrog

/-- Grammatical categories relevant to the verbal clause, drawn from
    [narrog-2012] Tables 3.5–3.9 and [narrog-2009a].

    The categories are ordered by empirical scope from Japanese data:
    lower scope (event-oriented) to wider scope (speech-act-oriented).
    Categories at the same scope level are grouped into a shared
    `scopeLevel`. -/
inductive GramCategory where
  | voice              -- passive, causative (lowest scope)
  | benefactive        -- benefactive applicatives
  | phasalAspect       -- begin, continue, finish
  | dynamicModality    -- ability, volition (boulomaic)
  | perfImperfAspect   -- perfective/imperfective
  | deontic1           -- necessity: must, have to
  | evidentiality1     -- predictive appearance
  | negation           -- internal negation
  | epistemic1         -- necessity/expectation
  | evidentiality2     -- inferential evidentiality
  | tense              -- past, present, future
  | deontic2           -- valuative obligation, recommendation
  | epistemic2         -- possibility
  | evidentiality3     -- reportive
  | epistemic3         -- speculative, epistemic mood
  | volitiveMood       -- imperative, hortative
  | illocutionaryMod   -- sentence-final particles, tag questions (widest scope)
  deriving DecidableEq, Repr

/-- Empirical scope level from Japanese data ([narrog-2009a],
    [narrog-2012] Tables 3.5–3.7, 3.9). Lower number = narrower scope.

    Multiple categories can share a level; the ordering between
    categories at the same level is not empirically established.

    Level assignments follow the groupings established in the text (p. 97):
    "Evidentiality 3 and Epistemic modality 2... are located on the same
    level as Tense"; "Epistemic modality 1 and Evidentiality 2... are
    located at the same level as (Internal) negation." Non-modal anchors
    (Tense, Negation, Perf/Imperf, Phasal aspect) and the modal categories
    listed alongside them share the same level. -/
def GramCategory.scopeLevel : GramCategory → Nat
  | .voice | .benefactive                                     => 0
  | .phasalAspect | .dynamicModality                          => 1
  | .perfImperfAspect | .deontic1 | .evidentiality1           => 2
  | .negation | .epistemic1 | .evidentiality2                 => 3
  | .tense | .deontic2 | .epistemic2 | .evidentiality3        => 4
  | .epistemic3 | .volitiveMood                               => 5
  | .illocutionaryMod                                         => 6

instance : LE GramCategory where le a b := a.scopeLevel ≤ b.scopeLevel
instance : LT GramCategory where lt a b := a.scopeLevel < b.scopeLevel

instance (a b : GramCategory) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.scopeLevel ≤ b.scopeLevel))

instance (a b : GramCategory) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.scopeLevel < b.scopeLevel))

/-- Epistemic modality outscopes deontic modality. -/
theorem epistemic_outscopes_deontic : GramCategory.deontic1 < GramCategory.epistemic1 := by
  decide

/-- Dynamic modality (ability) has narrower scope than deontic. -/
theorem dynamic_below_deontic : GramCategory.dynamicModality < GramCategory.deontic1 := by
  decide

/-- Mood outscopes all levels of modality proper. -/
theorem mood_outscopes_modality :
    GramCategory.epistemic3 ≤ GramCategory.volitiveMood ∧
    GramCategory.deontic2 < GramCategory.volitiveMood := by
  exact ⟨by decide, by decide⟩

/-- Illocutionary modification is the widest-scope category. -/
theorem im_is_widest (c : GramCategory) : c ≤ GramCategory.illocutionaryMod := by
  cases c <;> decide

/-- Map a category to its speaker-orientation level in Narrog's 2D map.

    Categories below the aspect boundary are event-oriented; categories
    at the modal level are speaker-oriented; mood and IM are mood-level.

    At scope level 2, event-oriented (perfective aspect) and speaker-oriented
    (deontic 1, evidentiality 1) categories coexist, reflecting Narrog's
    observation (p. 97, point 4) that volitive modalities rank low due to
    descriptive use. The mapping is therefore approximate at the
    event/speaker boundary; see `scope_implies_orientation` for the
    precise (strict `<`) relationship. -/
def GramCategory.toOrientation : GramCategory → SpeakerOrientationLevel
  | .voice | .benefactive | .phasalAspect | .dynamicModality
  | .perfImperfAspect => .eventOriented
  | .deontic1 | .deontic2 | .epistemic1 | .epistemic2
  | .evidentiality1 | .evidentiality2 | .evidentiality3
  | .negation | .tense => .speakerOriented
  | .epistemic3 | .volitiveMood | .illocutionaryMod => .mood

/-- Strict scope increase implies non-decreasing orientation.

    If category `a` is strictly narrower in scope than `b`, then `a`'s
    orientation is no higher than `b`'s. This is the formal link between
    Narrog's Hypothesis I (category climbing: narrow → wide scope) and
    Hypothesis II (event-oriented → speech-act-oriented).

    The theorem requires strict `<` rather than `≤` because at the
    boundary between event-oriented and speaker-oriented categories
    (scope level 2), perfective/imperfective aspect (event-oriented) and
    deontic modality 1 (speaker-oriented) share the same scope level.
    Narrog (p. 97, point 4) notes this: volitive categories rank low in
    the scope hierarchy due to their descriptive use, even though their
    performative use is high. -/
theorem scope_implies_orientation (a b : GramCategory) (h : a < b) :
    a.toOrientation ≤ b.toOrientation := by
  revert h; cases a <;> cases b <;> decide

/-- Role of a grammatical category relative to modality in diachronic change.

    Based on [narrog-2012] Table 3.10 (p. 113), which lists *non-modal*
    source, target, and bidirectional categories. Table 3.10 also includes
    categories not in our scope hierarchy: possession and directionals
    (sources), referent honorification (both), and politeness/addressee
    honorification (targets). Our `changeRole` function extends Table 3.10
    to the full `GramCategory` type by classifying modal categories (deontic,
    epistemic, evidentiality) as `.both`. -/
inductive ChangeRole where
  | source  -- lower scope: voice, benefactives (+ possession, directionals in Table 3.10)
  | target  -- higher scope: mood, IM (+ politeness/honorification in Table 3.10)
  | both    -- same level: aspect, tense, negation (+ referent honorification in Table 3.10)
  deriving DecidableEq, Repr

/-- Classification of categories by their diachronic role relative to
    modality. Extends [narrog-2012] Table 3.10 to cover all
    `GramCategory` constructors (see `ChangeRole` docstring). -/
def GramCategory.changeRole : GramCategory → ChangeRole
  | .voice | .benefactive          => .source
  | .phasalAspect | .perfImperfAspect | .tense | .negation => .both
  | .dynamicModality | .deontic1 | .deontic2
  | .epistemic1 | .epistemic2 | .epistemic3
  | .evidentiality1 | .evidentiality2 | .evidentiality3 => .both
  | .volitiveMood | .illocutionaryMod => .target

/-- Every source category has strictly narrower scope than every target
    category. This is the structural precondition for category-climbing:
    semantic change from source to target always increases scope. -/
theorem source_below_target (c d : GramCategory)
    (hc : c.changeRole = .source) (hd : d.changeRole = .target) :
    c < d := by
  revert hc hd; cases c <;> cases d <;> decide

/-- All source categories are event-oriented; all target categories are
    at the mood level. The diachronic role aligns with the synchronic
    orientation: categories that *give rise to* modality sit at the event
    level, while categories that modality *develops into* sit at the
    speech-act level. -/
theorem source_is_event_oriented (c : GramCategory) (h : c.changeRole = .source) :
    c.toOrientation = .eventOriented := by
  revert h; cases c <;> decide

theorem target_is_mood (c : GramCategory) (h : c.changeRole = .target) :
    c.toOrientation = .mood := by
  revert h; cases c <;> decide

/-- A stage in the diachronic development of English modals.
    [narrog-2012] Table 3.3, following Langacker (1990; 1998; 1999). -/
structure ModalDevelopmentStage where
  stageLabel : String
  semanticChange : String
  historicalCorrelate : String
  orientation : SpeakerOrientationLevel
  deriving Repr

/-- Langacker's stages for English modal verbs ([narrog-2012] Table 3.3).

    Stage I>II: Physical → social force (main verb → modal verb).
    Stage I>II: Potency source/target diffuse (main verb → modal verb).
    Stage II: Maximal diffusion = deontic → epistemic meaning.
    Stage II,III: Potency → speaker's knowledge (present-oriented epistemic).
    Stage II>III: Directed potency lost → grounding predications. -/
def langackerStages : List ModalDevelopmentStage :=
  [ ⟨"I>II", "domain of force shifts from physical to social",
    "main verb to modal verb", .eventOriented⟩
  , ⟨"I>II", "diffusion of source and target of potency",
    "main verb to modal verb", .eventOriented⟩
  , ⟨"II", "maximal diffusion of source and target of potency",
    "deontic to epistemic meaning", .speakerOriented⟩
  , ⟨"II,III", "potency pertains to evolution of speaker's knowledge of reality",
    "present-oriented epistemic meanings", .speakerOriented⟩
  , ⟨"II>III", "directed potency loses profiled status",
    "modals become grounding predications", .mood⟩
  ]

/-- The stages are monotonically non-decreasing in orientation —
    consistent with Narrog's directionality hypothesis. -/
theorem langacker_stages_monotone :
    langackerStages.Pairwise (λ a b => a.orientation ≤ b.orientation) := by
  simp [langackerStages]
  decide

end Narrog2012
