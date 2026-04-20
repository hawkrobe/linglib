import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Representationality and Epistemic Licensing
@cite{anand-hacquard-2013} @cite{bolinger-1968} @cite{stalnaker-1984}

Attitude verbs split into two fundamental semantic classes
(@cite{bolinger-1968}):

- **Representational** attitudes convey a mental picture — a consistent
  set of propositions defining a non-trivial set of possible worlds
  (an *information state*). Doxastics (`believe`, `think`),
  argumentatives (`say`, `argue`), and semifactives (`know`, `realize`).

- **Non-representational** attitudes combine with their complement via a
  logic of preference, comparing the complement to contextual alternatives
  on a preference scale (@cite{villalta-2008}). Desideratives (`want`,
  `wish`) and directives (`demand`, `order`).

- **Hybrid** attitudes have both components: a representational (doxastic)
  component providing an information state, and a preference component
  ordering alternatives. Emotive doxastics (`hope`, `fear`) and
  dubitatives (`doubt`).

The central empirical generalization (@cite{anand-hacquard-2013}):

**Epistemic Licensing Generalization**: Epistemic modals are licensed only
in the scope of attitudes that provide an information state — i.e.,
attitudes with a representational component.

| Attitude class      | Representational | Pref | might | must |
|---------------------|-----------------|------|-------|------|
| Doxastics           | ✓               | ✗    | ✓     | ✓    |
| Argumentatives      | ✓               | ✗    | ✓     | ✓    |
| Semifactives        | ✓               | ✗    | ✓     | ✓    |
| Desideratives       | ✗               | ✓    | ✗     | ✗    |
| Directives          | ✗               | ✓    | ✗     | ✗    |
| Emotive doxastics   | ✓               | ✓    | ✓     | ✗    |
| Dubitatives         | ✓               | ✓    | ✓     | ✗    |

The might/must asymmetry under hybrids follows from the uncertainty
condition: emotive doxastics require that the attitude holder is uncertain
about the complement. This is compatible with epistemic *possibility*
(∃w'∈DOX: φ(w')) but contradicts epistemic *necessity* (∀w'∈DOX: φ(w')),
which would entail certainty.

## Mood Correlation

Epistemic licensing correlates with mood selection in Romance, but they
track different things:
- Epistemics track **representationality** (information state provision)
- Subjunctive mood tracks **preferences** (comparative semantics)

The overlap is large because most preference-based attitudes are
non-representational. But hybrids (emotive doxastics) have both,
explaining why they license possibility epistemics AND select subjunctive.
-/

namespace Semantics.Attitudes.Representationality

-- ════════════════════════════════════════════════════════════════
-- § 1. Representationality Classification
-- ════════════════════════════════════════════════════════════════

/-- Classification of attitude semantics by representationality.

An attitude is representational iff its semantics provides a non-trivial
information state (a set of worlds) that embedded epistemics can be
anaphoric to (@cite{anand-hacquard-2013}, §3). -/
inductive Representationality where
  /-- Provides information state S = DOX(x,w). Doxastics, argumentatives,
      semifactives. Epistemics quantify over DOX directly. -/
  | representational
  /-- No information state: S = ∅. Desideratives, directives.
      Comparative semantics over alternatives (@cite{villalta-2008}).
      Embedded epistemics yield tautology (might) or contradiction (must). -/
  | nonRepresentational
  /-- Both components: representational (provides DOX for epistemic
      anaphora) + preference (orders alternatives). Emotive doxastics
      (hope, fear), dubitatives (doubt). -/
  | hybrid
  deriving DecidableEq, Repr

/-- An attitude with a representational component provides an information
    state that epistemics can quantify over. -/
def HasInformationState : Representationality → Prop
  | .representational => True
  | .nonRepresentational => False
  | .hybrid => True

instance : DecidablePred HasInformationState := fun r => by
  cases r <;> unfold HasInformationState <;> infer_instance

/-- An attitude with a preference component uses comparative semantics. -/
def HasPreferenceComponent : Representationality → Prop
  | .representational => False
  | .nonRepresentational => True
  | .hybrid => True

instance : DecidablePred HasPreferenceComponent := fun r => by
  cases r <;> unfold HasPreferenceComponent <;> infer_instance

-- ════════════════════════════════════════════════════════════════
-- § 2. Epistemic Licensing
-- ════════════════════════════════════════════════════════════════

/-- Epistemic modal force. -/
inductive EpistemicForce where
  | possibility  -- might, may, can (∃)
  | necessity    -- must, have to (∀)
  deriving DecidableEq, Repr

/-- Whether an attitude class licenses an embedded epistemic of given
    force. This is the central prediction of @cite{anand-hacquard-2013}.

    - Representational: licenses both might and must (S = DOX, non-trivial)
    - Non-representational: licenses neither (S = ∅, trivial modal base)
    - Hybrid: licenses might but not must (S = DOX, but uncertainty
      condition contradicts universal quantification) -/
def LicensesEpistemic : Representationality → EpistemicForce → Prop
  | .representational,    _             => True
  | .nonRepresentational, _             => False
  | .hybrid,              .possibility  => True
  | .hybrid,              .necessity    => False

instance : ∀ r f, Decidable (LicensesEpistemic r f) := fun r f => by
  cases r <;> cases f <;> unfold LicensesEpistemic <;> infer_instance

-- ════════════════════════════════════════════════════════════════
-- § 3. Verification Theorems
-- ════════════════════════════════════════════════════════════════

/-- Representational attitudes license all epistemics. -/
theorem representational_licenses_all (f : EpistemicForce) :
    LicensesEpistemic .representational f := by
  cases f <;> trivial

/-- Non-representational attitudes block all epistemics. -/
theorem nonRepresentational_blocks_all (f : EpistemicForce) :
    ¬ LicensesEpistemic .nonRepresentational f := by
  cases f <;> exact id

/-- Hybrids license possibility but not necessity. -/
theorem hybrid_possibility_only :
    LicensesEpistemic .hybrid .possibility ∧
    ¬ LicensesEpistemic .hybrid .necessity :=
  ⟨trivial, id⟩

/-- Epistemic licensing requires an information state. -/
theorem licensing_requires_information_state (r : Representationality)
    (f : EpistemicForce) (h : LicensesEpistemic r f) :
    HasInformationState r := by
  cases r <;> cases f <;> trivial

-- ════════════════════════════════════════════════════════════════
-- § 4. Mood Selection Correlation
-- ════════════════════════════════════════════════════════════════

open Semantics.Mood

/-- Map mood selector to expected representationality.

This captures the strong (but imperfect) correlation between mood
selection and representationality across Romance. The correlation
is imperfect because subjunctive tracks preferences, not
representationality directly (@cite{anand-hacquard-2013}, §6). -/
def fromMoodSelector : MoodSelector → Representationality
  | .indicativeSelecting         => .representational
  | .subjunctiveSelecting        => .nonRepresentational
  | .crossLinguisticallyVariable => .hybrid
  | .moodNeutral                 => .representational

/-- Indicative-selecting attitudes are representational:
    they provide an information state and license epistemics. -/
theorem indicative_representational :
    fromMoodSelector .indicativeSelecting = .representational := rfl

/-- Subjunctive-selecting attitudes are non-representational:
    they use comparative semantics and block epistemics. -/
theorem subjunctive_nonRepresentational :
    fromMoodSelector .subjunctiveSelecting = .nonRepresentational := rfl

/-- Cross-linguistically variable attitudes are hybrid:
    they have both representational and preference components. -/
theorem variable_hybrid :
    fromMoodSelector .crossLinguisticallyVariable = .hybrid := rfl

-- ════════════════════════════════════════════════════════════════
-- § 5. Attitude Verb Classification
-- ════════════════════════════════════════════════════════════════

/-- Classification of specific attitude verbs. Each verb maps to a
    representationality class, which determines its epistemic licensing
    behavior. -/
inductive AttitudeClass where
  | doxastic          -- believe, think, suppose
  | argumentative     -- say, argue, conclude
  | semifactive       -- know, realize, discover
  | desiderative      -- want, wish
  | directive         -- demand, order, require
  | emotiveDoxastic   -- hope, fear
  | dubitative        -- doubt
  deriving DecidableEq, Repr

/-- Each attitude class maps to a representationality value. -/
def AttitudeClass.representationality : AttitudeClass → Representationality
  | .doxastic        => .representational
  | .argumentative   => .representational
  | .semifactive     => .representational
  | .desiderative    => .nonRepresentational
  | .directive       => .nonRepresentational
  | .emotiveDoxastic => .hybrid
  | .dubitative      => .hybrid

/-- Derived epistemic licensing for attitude classes. -/
def AttitudeClass.LicensesEpistemic (c : AttitudeClass)
    (f : EpistemicForce) : Prop :=
  Representationality.LicensesEpistemic c.representationality f

instance : ∀ c f, Decidable (AttitudeClass.LicensesEpistemic c f) := fun c f => by
  unfold AttitudeClass.LicensesEpistemic; infer_instance

-- ════════════════════════════════════════════════════════════════
-- § 6. The Table 3 Data as Verification Theorems
-- ════════════════════════════════════════════════════════════════

/-! Per-cell verification of @cite{anand-hacquard-2013} Table 3. -/

theorem doxastic_might : AttitudeClass.LicensesEpistemic .doxastic .possibility := trivial
theorem doxastic_must  : AttitudeClass.LicensesEpistemic .doxastic .necessity := trivial

theorem argumentative_might : AttitudeClass.LicensesEpistemic .argumentative .possibility := trivial
theorem argumentative_must  : AttitudeClass.LicensesEpistemic .argumentative .necessity := trivial

theorem semifactive_might : AttitudeClass.LicensesEpistemic .semifactive .possibility := trivial
theorem semifactive_must  : AttitudeClass.LicensesEpistemic .semifactive .necessity := trivial

theorem desiderative_might : ¬ AttitudeClass.LicensesEpistemic .desiderative .possibility := id
theorem desiderative_must  : ¬ AttitudeClass.LicensesEpistemic .desiderative .necessity := id

theorem directive_might : ¬ AttitudeClass.LicensesEpistemic .directive .possibility := id
theorem directive_must  : ¬ AttitudeClass.LicensesEpistemic .directive .necessity := id

theorem emotiveDoxastic_might : AttitudeClass.LicensesEpistemic .emotiveDoxastic .possibility := trivial
theorem emotiveDoxastic_must  : ¬ AttitudeClass.LicensesEpistemic .emotiveDoxastic .necessity := id

theorem dubitative_might : AttitudeClass.LicensesEpistemic .dubitative .possibility := trivial
theorem dubitative_must  : ¬ AttitudeClass.LicensesEpistemic .dubitative .necessity := id

end Semantics.Attitudes.Representationality
