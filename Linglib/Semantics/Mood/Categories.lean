/-!
# Grammatical Mood Categories

Morphological mood categories (indicative vs subjunctive, with
subtypes) and the lexical classification of mood-selecting predicates.

This is the verb-morphological distinction, independent of:
- `Illocutionary` (declarative/interrogative/imperative — speech act force)
- `SAPMood` (configurational mood from Speas & Tenny's 2×2 matrix)

The two dimensions are orthogonal: a clause can be
[interrogative, indicative] ("Does he sleep?") or
[interrogative, subjunctive] (Spanish "¿Que duerma?").

The semantic content of these categories lives downstream:
situation-level operators in `Semantics/Mood/Situation.lean`
([mendes-2025]: SUBJ introduces a situation dref, IND retrieves),
event-level operators in `Semantics/Mood/Eventuality.lean`
([grano-2024]: `Grammatical.eventDenotation` — indicative closes the
event argument, subjunctive leaves it open), and the dynamic lifts in
`Semantics/Mood/Dynamic.lean` (`Grammatical.dynOp` — indicative
eliminative, subjunctive generative).

This file lives in `Semantics/Mood/` alongside `Illocutionary.lean`
(force) and `ClauseType.lean` (force × mood); together they form the
unified mood-category namespace `Semantics.Mood`. Discourse-act
material (Searle classes, direction of fit, preparatory conditions,
discourse roles) lives in `Discourse/SpeechAct.lean`.
-/

namespace Semantics.Mood

/--
Grammatical mood categories.

Following the typological literature:
- **Indicative**: The default, "realis" mood
- **Subjunctive**: Non-default, "irrealis" mood (covers many subtypes)
-/
inductive Grammatical where
  | indicative
  | subjunctive
  deriving DecidableEq, Repr, Inhabited

/--
Subjunctive subtypes (for finer-grained analysis).

Different languages grammaticalize different subjunctive functions:
- Counterfactual: contrary-to-fact conditionals
- Dubitative: epistemic uncertainty
- Optative: wishes and desires
- Potential: epistemic/circumstantial possibility
-/
inductive SubjunctiveType where
  | counterfactual  -- contrary to fact
  | dubitative      -- epistemic uncertainty
  | optative        -- wishes
  | potential        -- possibility
  | subordinateFuture  -- Mendes' SF (present morphology, future reference)
  deriving DecidableEq, Repr

/--
Mood selection by embedding predicates.

Certain predicates select for specific moods in their complement:
- "know", "see" → typically indicative
- "want", "wish" → robustly subjunctive cross-linguistically
- "hope" → cross-linguistically variable ([grano-2024], Table 1)
- "say", "think" → mood-neutral (pragmatically flexible)

The projection onto the semantic operators is
`Selector.toVerbalOp` (`Semantics/Mood/Verbal.lean`).
-/
inductive Selector where
  | indicativeSelecting          -- "know", "see", "believe"
  | subjunctiveSelecting         -- "want", "wish", "demand", "intend"
  | crossLinguisticallyVariable  -- "hope", "expect": SBJV in some languages,
                                 -- IND in others ([grano-2024], Table 1)
  | moodNeutral                  -- "say", "think" (pragmatically flexible)
  deriving DecidableEq, Repr

end Semantics.Mood
