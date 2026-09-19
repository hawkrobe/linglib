import Linglib.Semantics.Modality.SpeechActOrientation

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
orientation (`scope_implies_orientation`), and the non-modal categories that are only
diachronic sources of modality lie strictly below those that are only its targets
(`GramCategory.IsSource`, `GramCategory.IsTarget`, `source_below_target`), the structural
precondition of the hypothesis that semantic change involving grammatical categories climbs
from narrower to wider scope.

## Implementation notes

The scope levels follow the combined hierarchy of the book's third chapter, categories on
a shared level being unordered. Possession, directionals, and the two kinds of
honorification, which the book's table of source and target categories also lists, are not
in the scope hierarchy and are left out. The most frequent attested changes of modal meaning
are tabulated in `Studies/Narrog2010`.

## TODO

The book derives a category's role as source or target from its scope level relative to the
modal categories. `IsSource` and `IsTarget` transcribe the table; deriving them turns on
whether the speculative category on the level of volitive mood counts as modality or as mood.

## References

* [narrog-2012]
* [narrog-2009a]
* [cinque-1999]
-/

namespace Narrog2012

open Modality

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

/-- Categories are compared by scope level, categories on one level lying below each other. -/
instance : Preorder GramCategory := Preorder.lift GramCategory.scopeLevel

instance : DecidableLE GramCategory :=
  fun a b ↦ inferInstanceAs (Decidable (a.scopeLevel ≤ b.scopeLevel))

instance : DecidableLT GramCategory :=
  fun a b ↦ inferInstanceAs (Decidable (a.scopeLevel < b.scopeLevel))

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
    at the modal level are speaker-oriented; mood and illocutionary modification are
    speech act-oriented.

    At scope level 2, event-oriented (perfective aspect) and speaker-oriented
    (deontic 1, evidentiality 1) categories coexist, reflecting Narrog's
    observation (p. 97, point 4) that volitive modalities rank low due to
    descriptive use. The mapping is therefore approximate at the
    event/speaker boundary; see `scope_implies_orientation` for the
    precise (strict `<`) relationship. -/
def GramCategory.toOrientation : GramCategory → SpeechActOrientation
  | .voice | .benefactive | .phasalAspect | .dynamicModality
  | .perfImperfAspect => .eventOriented
  | .deontic1 | .deontic2 | .epistemic1 | .epistemic2
  | .evidentiality1 | .evidentiality2 | .evidentiality3
  | .negation | .tense => .speakerOriented
  | .epistemic3 | .volitiveMood | .illocutionaryMod => .speechActOriented

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

namespace GramCategory

/-- The non-modal categories from which modal markers may derive, in the book's table of
potential source and target categories for modality: voice and benefactives, and aspect,
tense, and negation, which the table lists as both source and target. -/
def IsSource (c : GramCategory) : Prop :=
  c ∈ [voice, benefactive, phasalAspect, perfImperfAspect, tense, negation]

/-- The non-modal categories into which modal markers may develop: mood and illocutionary
modification, and aspect, tense, and negation. -/
def IsTarget (c : GramCategory) : Prop :=
  c ∈ [phasalAspect, perfImperfAspect, tense, negation, volitiveMood, illocutionaryMod]

instance : DecidablePred IsSource := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))
instance : DecidablePred IsTarget := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

end GramCategory

/-- Every category that is only a source has strictly narrower scope than every category that
is only a target, the structural precondition for category climbing. -/
theorem source_below_target (c d : GramCategory) (hc : c.IsSource) (hc' : ¬ c.IsTarget)
    (hd : d.IsTarget) (hd' : ¬ d.IsSource) : c < d := by
  revert hc hc' hd hd'; cases c <;> cases d <;> decide

/-- The categories that are only sources are event-oriented. -/
theorem source_is_event_oriented (c : GramCategory) (hc : c.IsSource) (hc' : ¬ c.IsTarget) :
    c.toOrientation = .eventOriented := by
  revert hc hc'; cases c <;> decide

/-- The categories that are only targets are speech act-oriented. -/
theorem target_is_speech_act_oriented (c : GramCategory) (hc : c.IsTarget)
    (hc' : ¬ c.IsSource) : c.toOrientation = .speechActOriented := by
  revert hc hc'; cases c <;> decide

end Narrog2012
