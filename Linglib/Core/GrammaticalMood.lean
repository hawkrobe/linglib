/-!
# Grammatical Mood

Morphological mood categories: indicative vs subjunctive (and subtypes).

This is the verb-morphological distinction, independent of:
- `IllocutionaryMood` (declarative/interrogative/imperative — speech act force)
- `SAPMood` (configurational mood from Speas & Tenny's 2×2 matrix)

The two dimensions are orthogonal: a clause can be
[interrogative, indicative] ("Does he sleep?") or
[interrogative, subjunctive] (Spanish "¿Que duerma?").

See `Theories/Semantics/Mood/Basic.lean` for the semantic operators (SUBJ, IND)
that interpret these categories.
-/

namespace Core

/--
Grammatical mood categories.

Following the typological literature:
- **Indicative**: The default, "realis" mood
- **Subjunctive**: Non-default, "irrealis" mood (covers many subtypes)
-/
inductive GramMood where
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
The semantic effects of grammatical mood, connecting two independent dimensions:

- **Situation-level** (@cite{mendes-2025}): SUBJ introduces a new situation dref;
  IND retrieves an existing one
- **Eventuality-level** (@cite{grano-2024}): SBJV leaves the complement's eventuality
  argument open for abstraction; IND existentially closes it

These dimensions are complementary: situation introduction enables temporal
anchoring (SF in Portuguese/Spanish), while eventuality openness enables
abstraction over the event argument (required by causatives, intention reports,
aspectual predicates, and memory/perception reports).
-/
structure MoodEffect where
  /-- SUBJ introduces a new situation dref (@cite{mendes-2025}) -/
  introducesSituation : Bool
  /-- SBJV leaves the eventuality argument open for abstraction (@cite{grano-2024}) -/
  eventualityOpen : Bool
  deriving DecidableEq, Repr

/-- Map grammatical mood to its semantic effects.

    Indicative mood does neither: it retrieves an existing situation and
    existentially closes the eventuality argument.

    Subjunctive mood does both: it introduces a new situation dref and
    leaves the eventuality argument open for abstraction. -/
def GramMood.effect : GramMood → MoodEffect
  | .indicative  => { introducesSituation := false, eventualityOpen := false }
  | .subjunctive => { introducesSituation := true,  eventualityOpen := true }

/-- Indicative mood closes the eventuality argument. -/
theorem ind_closes_eventuality : GramMood.indicative.effect.eventualityOpen = false := rfl

/-- Subjunctive mood leaves the eventuality argument open. -/
theorem subj_opens_eventuality : GramMood.subjunctive.effect.eventualityOpen = true := rfl

/-- Indicative and subjunctive differ on both dimensions. -/
theorem mood_effects_differ :
    GramMood.indicative.effect ≠ GramMood.subjunctive.effect := by decide

end Core
