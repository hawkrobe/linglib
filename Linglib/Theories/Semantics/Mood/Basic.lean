/-
# Mood Semantics

Semantic operators for grammatical mood (IND, SUBJ), operating at two
independent levels:

## Two Dimensions of Mood

**Situation-level** (@cite{mendes-2025}): Mood operators function like
determiners for situations:
- **SUBJ**: Introduces a new situation dref (like indefinite "a")
- **IND**: Retrieves/uses an existing situation (like definite "the")

**Eventuality-level** (@cite{grano-2024}): Mood morphemes existentially close
or leave open the complement clause's eventuality argument:
- **IND**: ∃e.P(e) — existentially closes, yielding a proposition
- **SBJV₁**: P — leaves open, enabling eventuality abstraction
- **SBJV₂**: P + CAUSE* — leaves open with causal self-reference (intentions)

These dimensions are complementary: situation introduction enables temporal
anchoring, while eventuality openness enables abstraction (required by
causatives, intention reports, aspectual predicates, memory/perception reports).

## Subordinate Future

The "Subordinate Future" (SF) in Portuguese/Spanish:
- Uses present morphology for future reference in subordinate contexts
- Is actually **subjunctive** - introduces a situation dref
- This dref is retrieved by the main clause for temporal anchoring

## CDRT Connection

In CDRT, these operators compose dynamically:
- SUBJ introduces a situation variable and updates the context
- IND retrieves a situation from the context

-/

import Linglib.Theories.Semantics.Tense.BranchingTime
import Linglib.Core.Context.Shifts
import Linglib.Core.Mood.Basic

namespace Semantics.Mood

open Core.Time
open Semantics.Tense.BranchingTime

-- Re-export Core.Mood types into this namespace for backward compatibility
export Core.Mood (GramMood SubjunctiveType MoodEffect)


/--
Type of situation predicates: (situation, situation) → Prop

The two situations are:
- s: The "local" or "described" situation
- s': The "anchor" or "reference" situation
-/
abbrev SitPred (W Time : Type*) := Situation W Time → Situation W Time → Prop

/--
SUBJ operator (@cite{mendes-2025}, Definition on p.29).

⟦SUBJ^{s₁}_{s₀}⟧ = λP. [s₁ | s₁ ∈ hist(s₀)]; P(s₁)(s₀)

The subjunctive:
1. Introduces a new situation dref s₁
2. Constrains s₁ to be in the historical alternatives of s₀
3. Passes s₁ and s₀ to the embedded predicate P

Analogous to an indefinite for situations.
-/
def SUBJ {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) : Prop :=
  ∃ s₁ : Situation W Time,
    s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀

/--
IND operator (@cite{mendes-2025}, Definition on p.29).

⟦IND_{s₁,s₂}⟧ = λP. [| s₂ ≤ w_{s₁}]; P(s₂)(s₁)

The indicative:
1. Retrieves existing situations s₁ and s₂
2. Requires s₂'s world to be "part of" s₁'s world (same world)
3. Passes s₂ and s₁ to P

Analogous to a definite for situations.
-/
def IND {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : Situation W Time) : Prop :=
  s₂.world = s₁.world ∧ P s₂ s₁

-- ════════════════════════════════════════════════════════════════
-- § Eventuality-Level Mood Operators (@cite{grano-2024})
-- ════════════════════════════════════════════════════════════════

/-!
### Mood as Eventuality Closure

@cite{grano-2024} proposes that mood morphemes operate on the eventuality
argument of the complement clause:

- **IND**: existentially closes the eventuality argument (87),
  yielding a proposition
- **SBJV₁**: leaves the eventuality argument open (88a),
  yielding an event predicate (identity function)
- **SBJV₂**: leaves the eventuality argument open AND requires
  causal self-reference (134), for intention reports

This is independent of — and complementary to — the situation-level
SUBJ/IND operators defined above.
-/

/-- IND existentially closes the eventuality argument (@cite{grano-2024}, (87)).

    ⟦INDIC⟧ = λP_(⟨vt⟩).∃e.P(e)

    The eventuality variable is bound; the complement denotes a proposition. -/
def INDev {Ev : Type*} (P : Ev → Prop) : Prop := ∃ e, P e

/-- SBJV₁ leaves the eventuality argument open (@cite{grano-2024}, (88a);
    §7 Subjunctive₃ (135)).

    ⟦SBJV₁⟧ = λP_(⟨vt⟩).P

    The complement retains type ⟨vt⟩ — an event predicate, not a proposition.
    In the core proposal (§5, (88a)), this is the general non-closing mood
    operator. In the §7 unified theory, it becomes specifically Subjunctive₃
    (135) — the identity variant for perception predicates ('see'), causative
    predicates ('make'), and aspectual predicates ('begin'). These predicates
    require or are compatible with eventuality abstraction but do not involve
    causal self-reference or ordering semantics. Distinct from the 'want'
    variant (§7, Subjunctive₁ (133)), which uses Portner & Rubinstein's `ln`
    (local necessity), and the 'intend' variant (Subjunctive₂ (134) =
    `SBJVev₂`), which incorporates CAUSE*. -/
def SBJVev₁ {Ev : Type*} (P : Ev → Prop) : Ev → Prop := P

/-- SBJV₂ leaves the eventuality argument open AND requires causal
    self-reference (@cite{grano-2024}, (134); unified theory §7).

    ⟦Subjunctive₂⟧ = λPλe[sn({λw.∃e'.CAUSE*(e,e',w) & P(w)(e')}, content(e), e)]

    This is the variant operative with 'intend' in the §7 unified theory,
    which integrates CAUSE* from the core proposal (§4, (79)) with Portner
    & Rubinstein's (@cite{portner-rubinstein-2020}) modal quantification
    framework. The attitude state e must causally bring about the described
    event e' "in the right way" (@cite{searle-1983}; @cite{harman-1976}). -/
def SBJVev₂ {Ev W : Type*}
    (causeStar : Ev → Ev → W → Prop)  -- CAUSE*(state, event, world)
    (content : Ev → W → Prop)          -- content of the attitude state
    (P : W → Ev → Prop)               -- world-indexed event predicate
    (e : Ev) : Prop :=
  ∀ w, content e w → ∃ e', causeStar e e' w ∧ P w e'

/-- IND closure yields a proposition (no free eventuality variable). -/
theorem INDev_is_propositional {Ev : Type*} (P : Ev → Prop) :
    (INDev P) = (∃ e, P e) := rfl

/-- SBJV₁ is the identity on event predicates. -/
theorem SBJVev₁_is_identity {Ev : Type*} (P : Ev → Prop) :
    SBJVev₁ P = P := rfl


/--
Mood selection by embedding predicates.

Certain predicates select for specific moods in their complement:
- "know", "see" → typically indicative
- "want", "wish" → robustly subjunctive cross-linguistically
- "hope" → cross-linguistically variable (@cite{grano-2024}, Table 1)
- "say", "think" → mood-neutral (pragmatically flexible)
-/
inductive MoodSelector where
  | indicativeSelecting          -- "know", "see", "believe"
  | subjunctiveSelecting         -- "want", "wish", "demand", "intend"
  | crossLinguisticallyVariable  -- "hope", "expect": SBJV in some languages,
                                 -- IND in others (@cite{grano-2024}, Table 1)
  | moodNeutral                  -- "say", "think" (pragmatically flexible)
  deriving DecidableEq, Repr

/--
Does the selector prefer subjunctive?
-/
def prefersSubjunctive : MoodSelector → Bool
  | .indicativeSelecting => false
  | .subjunctiveSelecting => true
  | .crossLinguisticallyVariable => false  -- default: variable, not robust SBJV
  | .moodNeutral => false  -- default to indicative

/--
Conditional with SF antecedent (@cite{mendes-2025}, main application).

"If Maria be.SF home, she will answer"

Structure:
1. SUBJ introduces s₁ ∈ hist(s₀) (the "if" situation)
2. Antecedent is evaluated at s₁
3. Consequent is temporally anchored to s₁

This explains why SF enables future reference: the subjunctive
introduces a future situation that the main clause can refer back to.
-/
def conditionalSF {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (antecedent : Situation W Time → Prop)  -- "Maria is home"
    (consequent : Situation W Time → Situation W Time → Prop)  -- "she answers"
    (s₀ : Situation W Time) : Prop :=
  SUBJ history (λ s₁ s₀' => antecedent s₁ → consequent s₁ s₀') s₀

/--
Standard indicative conditional (for comparison).

"If Maria is home, she answers"

Here the antecedent is evaluated at the same situation as the main clause.
No new situation is introduced.
-/
def conditionalIND {W Time : Type*}
    (antecedent : Situation W Time → Prop)
    (consequent : Situation W Time → Prop)
    (s : Situation W Time) : Prop :=
  antecedent s → consequent s


/--
SUBJ is existential: it introduces a situation.
-/
theorem subj_is_existential {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) :
    SUBJ history P s₀ → ∃ s₁, P s₁ s₀ := by
  intro ⟨s₁, _, hP⟩
  exact ⟨s₁, hP⟩

/--
SUBJ constrains to historical base: the introduced situation
is in the historical alternatives.
-/
theorem subj_in_hist {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) :
    SUBJ history P s₀ → ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀ := by
  intro h
  exact h

/--
IND requires same world: the two situations must share a world.
-/
theorem ind_same_world {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : Situation W Time) :
    IND P s₁ s₂ → s₂.world = s₁.world := by
  intro ⟨h, _⟩
  exact h

/--
SUBJ with reflexive history: if the history is reflexive,
the current situation is always an option.
-/
theorem subj_current_option {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (h_refl : history.reflexive)
    (P : SitPred W Time)
    (s₀ : Situation W Time)
    (h_P : P s₀ s₀) :
    SUBJ history P s₀ := by
  use s₀
  refine ⟨?_, h_P⟩
  -- s₀ ∈ historicalBase history s₀
  simp only [historicalBase, Set.mem_setOf_eq]
  exact ⟨h_refl s₀, le_refl s₀.time⟩


/--
Non-veridicality:

A propositional operator F is non-veridical iff:
  F(p) does NOT entail p

The subjunctive is associated with non-veridical contexts because
SUBJ introduces a situation that may differ from the actual one.
-/
def nonVeridical {W Time : Type*}
    (F : (Situation W Time → Prop) → Situation W Time → Prop) : Prop :=
  ∃ (P : Situation W Time → Prop) (s : Situation W Time),
    F P s ∧ ¬P s

/--
SUBJ is non-veridical: the introduced situation may differ from actual.

This follows from the existential nature of SUBJ: it quantifies over
situations in the historical base, which includes non-actual futures.
-/
theorem subj_nonveridical {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    -- Need: history has an option distinct from the evaluation point
    (h_branching : ∃ s₀ s₁ : Situation W Time,
      s₁ ∈ historicalBase history s₀ ∧ s₀ ≠ s₁) :
    nonVeridical (λ P s₀ => SUBJ history (λ s₁ _ => P s₁) s₀) := by
  obtain ⟨s₀, s₁, h₁, hne⟩ := h_branching
  use (λ s => s = s₁), s₀
  refine ⟨⟨s₁, h₁, rfl⟩, ?_⟩
  -- ¬(s₀ = s₁)
  exact hne

-- ════════════════════════════════════════════════════════════════
-- § Bridge: SUBJ and Attitude Temporal Anchoring
-- ════════════════════════════════════════════════════════════════

/-!
### SUBJ as Temporal Anchor
@cite{giannakidou-1998} @cite{mendes-2025} @cite{muskens-1996}

Both SUBJ's situation introduction and attitude embedding create new temporal
reference points for embedded clauses:

- **SUBJ**: introduces s₁ ∈ hist(s₀) with τ(s₁) ≥ τ(s₀). The embedded clause
  evaluates at τ(s₁), not τ(s₀). This is why the Subordinate Future (SF) enables
  future reference.

- **Attitude verbs**: set embedded P = matrix E. The embedded clause's tense is
  relative to the matrix event time, not speech time.

The structural parallel: both mechanisms shift the temporal evaluation point
of the embedded clause from the default (speech time or matrix time) to a
newly introduced temporal anchor.

See `Semantics.Attitudes.SituationDependent` for the attitude side
and `Semantics.Tense.SequenceOfTense` for the formal connection.
-/

section AttitudeTemporalAnchor

/-- SUBJ introduces a temporal anchor: the introduced situation's time
    is at or after the base situation's time.

    This parallels attitude embedding, where the embedded clause's
    perspective time shifts to the matrix event time. Both mechanisms
    create a new temporal reference point for embedded evaluation. -/
theorem subj_temporal_anchor {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time)
    (h : SUBJ history P s₀) :
    ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ s₁.time ≥ s₀.time ∧ P s₁ s₀ := by
  obtain ⟨s₁, h_hist, h_P⟩ := h
  refine ⟨s₁, h_hist, ?_, h_P⟩
  have hmem := h_hist
  simp only [historicalBase, Set.mem_setOf_eq] at hmem
  exact hmem.2

end AttitudeTemporalAnchor

-- ════════════════════════════════════════════════════════════════
-- § Tower Integration: SUBJ as Context Shift
-- ════════════════════════════════════════════════════════════════

/-!
### SUBJ as Tower Push

SUBJ introduces a new situation from the historical base. In the tower
framework, this corresponds to pushing a mood-labeled context shift that
changes the world and time coordinates to those of the introduced situation.

The tower-based `subjShift` is *not* a replacement for the existential
`SUBJ` operator — rather, it is the shift that the tower records when
a subjunctive clause is entered. The existential quantification over
situations is a separate semantic step. Both descriptions are independently
useful: the tower version tracks depth and enables interaction with other
depth-sensitive operations (presupposition, tense indexing); the existential
version directly models the semantics.
-/

section TowerMood

variable {W : Type*} {Time : Type*}

/-- SUBJ as a context shift: a mood-labeled shift that changes the
    world and time to those of the introduced situation.

    This is the shift that the tower records when a subjunctive clause
    is entered. The `newWorld` and `newTime` are the coordinates of the
    existentially introduced situation s₁. -/
def subjShift {E P : Type*} (newWorld : W) (newTime : Time) :
    Core.Context.ContextShift (Core.Context.KContext W E P Time) where
  apply := λ c => { c with world := newWorld, time := newTime }
  label := .mood

/-- Pushing a `subjShift` changes the world to the introduced situation's world. -/
theorem subjShift_changes_world {E P : Type*}
    (w : W) (t : Time) (c : Core.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).world = w := rfl

/-- Pushing a `subjShift` changes the time to the introduced situation's time. -/
theorem subjShift_changes_time {E P : Type*}
    (w : W) (t : Time) (c : Core.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).time = t := rfl

/-- Pushing a `subjShift` preserves the agent. -/
theorem subjShift_preserves_agent {E P : Type*}
    (w : W) (t : Time) (c : Core.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).agent = c.agent := rfl

/-- The tower-based subjunctive: SUBJ holds iff there exists a situation
    in the historical base such that pushing `subjShift` for that situation
    and evaluating the predicate yields truth.

    This is the bridge between the existential `SUBJ` and the tower `push`. -/
theorem subj_as_tower_push [LE Time]
    (history : WorldHistory W Time)
    (Q : SitPred W Time)
    (s₀ : Situation W Time) :
    SUBJ history Q s₀ ↔
    ∃ s₁ ∈ historicalBase history s₀,
      Q s₁ s₀ := by
  simp only [SUBJ]

end TowerMood

end Semantics.Mood
