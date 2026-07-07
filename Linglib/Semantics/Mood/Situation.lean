import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Context.Shifts

/-!
# Situation-Level Mood Operators
[mendes-2025]

[mendes-2025]'s mood operators work like determiners for situations:
`SUBJ` introduces a new situation dref constrained to the historical
alternatives of the anchor (like indefinite *a*), `IND` retrieves an
existing situation and tests same-worldhood (like definite *the*).
This is the situation-level dimension of grammatical mood — see
`Semantics/Mood/Eventuality.lean` for the complementary event-level
dimension ([grano-2024]) and `Semantics/Mood/Dynamic.lean` for the
dynamic lifts (`dynSUBJ` generative, `dynIND` eliminative).

The Subordinate Future (SF) of Portuguese/Spanish — present morphology
with future reference in subordinate contexts — is [mendes-2025]'s
main application: SF is subjunctive, introducing a future situation
dref that the main clause retrieves for temporal anchoring
(`conditionalSF`).

## Main declarations

* `SitPred`, `sameWorld` — situation predicates and the modal kernel.
* `SUBJ`, `IND` — the situation-level mood operators.
* `conditionalSF` — the SF conditional.
* `nonVeridical`, `subj_nonveridical` — subjunctive non-veridicality.
* `subjShift`, `subj_as_tower_push` — SUBJ as a tower context shift.
-/

namespace Semantics.Mood

open Intensional (WorldTimeIndex)

open HistoricalAlternatives


/--
Type of situation predicates: (situation, situation) → Prop

The two situations are:
- s: The "local" or "described" situation
- s': The "anchor" or "reference" situation
-/
abbrev SitPred (W Time : Type*) := WorldTimeIndex W Time → WorldTimeIndex W Time → Prop

/--
The `sameWorld` kernel: two situations share their world coordinate.

This is the modal counterpart of the temporal kernels
(`Tense.precedes`/`coincides`/`follows`). The static `IND`
operator and its dynamic lift `Semantics.Mood.dynIND` both call this
kernel; they share *the same modal constraint*, lifted from a static
situation predicate to a context filter via
`Semantics.Dynamic.Core.dynRelationOn`.

`abbrev` (= `@[reducible] def`) so `decide`/`rw` see through it.
-/
abbrev sameWorld {W Time : Type*}
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  s₁.world = s₂.world

/--
SUBJ operator ([mendes-2025], Definition on p.29).

⟦SUBJ^{s₁}_{s₀}⟧ = λP. [s₁ | s₁ ∈ hist(s₀)]; P(s₁)(s₀)

The subjunctive:
1. Introduces a new situation dref s₁
2. Constrains s₁ to be in the historical alternatives of s₀
3. Passes s₁ and s₀ to the embedded predicate P

Analogous to an indefinite for situations.
-/
def SUBJ {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (P : SitPred W Time)
    (s₀ : WorldTimeIndex W Time) : Prop :=
  ∃ s₁ : WorldTimeIndex W Time,
    s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀

/--
IND operator ([mendes-2025], Definition on p.29).

⟦IND_{s₁,s₂}⟧ = λP. [| s₂ ≤ w_{s₁}]; P(s₂)(s₁)

The indicative:
1. Retrieves existing situations s₁ and s₂
2. Requires s₂'s world to be "part of" s₁'s world (same world)
3. Passes s₂ and s₁ to P

Analogous to a definite for situations.
-/
def IND {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  sameWorld s₂ s₁ ∧ P s₂ s₁

/--
Conditional with SF antecedent ([mendes-2025], main application).

"If Maria be.SF home, she will answer"

Structure:
1. SUBJ introduces s₁ ∈ hist(s₀) (the "if" situation)
2. Antecedent is evaluated at s₁
3. Consequent is temporally anchored to s₁

This explains why SF enables future reference: the subjunctive
introduces a future situation that the main clause can refer back to.
-/
def conditionalSF {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (antecedent : WorldTimeIndex W Time → Prop)  -- "Maria is home"
    (consequent : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)  -- "she answers"
    (s₀ : WorldTimeIndex W Time) : Prop :=
  SUBJ history (λ s₁ s₀' => antecedent s₁ → consequent s₁ s₀') s₀

/--
Standard indicative conditional (for comparison).

"If Maria is home, she answers"

Here the antecedent is evaluated at the same situation as the main clause.
No new situation is introduced.
-/
def conditionalIND {W Time : Type*}
    (antecedent : WorldTimeIndex W Time → Prop)
    (consequent : WorldTimeIndex W Time → Prop)
    (s : WorldTimeIndex W Time) : Prop :=
  antecedent s → consequent s


/--
SUBJ is existential: it introduces a situation.
-/
theorem subj_is_existential {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (P : SitPred W Time)
    (s₀ : WorldTimeIndex W Time) :
    SUBJ history P s₀ → ∃ s₁, P s₁ s₀ := by
  intro ⟨s₁, _, hP⟩
  exact ⟨s₁, hP⟩

/--
SUBJ constrains to historical base: the introduced situation
is in the historical alternatives.
-/
theorem subj_in_hist {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (P : SitPred W Time)
    (s₀ : WorldTimeIndex W Time) :
    SUBJ history P s₀ → ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀ := by
  intro h
  exact h

/--
IND requires same world: the two situations must share a world.
-/
theorem ind_same_world {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : WorldTimeIndex W Time) :
    IND P s₁ s₂ → s₂.world = s₁.world := by
  intro ⟨h, _⟩
  exact h

/--
SUBJ with reflexive history: if the history is reflexive,
the current situation is always an option.
-/
theorem subj_current_option {W Time : Type*} [Preorder Time]
    (history : HistoricalAlternatives W Time)
    (h_refl : history.reflexive)
    (P : SitPred W Time)
    (s₀ : WorldTimeIndex W Time)
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
    (F : (WorldTimeIndex W Time → Prop) → WorldTimeIndex W Time → Prop) : Prop :=
  ∃ (P : WorldTimeIndex W Time → Prop) (s : WorldTimeIndex W Time),
    F P s ∧ ¬P s

/--
SUBJ is non-veridical: the introduced situation may differ from actual.

This follows from the existential nature of SUBJ: it quantifies over
situations in the historical base, which includes non-actual futures.
-/
theorem subj_nonveridical {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    -- Need: history has an option distinct from the evaluation point
    (h_branching : ∃ s₀ s₁ : WorldTimeIndex W Time,
      s₁ ∈ historicalBase history s₀ ∧ s₀ ≠ s₁) :
    nonVeridical (λ P s₀ => SUBJ history (λ s₁ _ => P s₁) s₀) := by
  obtain ⟨s₀, s₁, h₁, hne⟩ := h_branching
  use (λ s => s = s₁), s₀
  refine ⟨⟨s₁, h₁, rfl⟩, ?_⟩
  -- ¬(s₀ = s₁)
  exact hne

/-! ### SUBJ as temporal anchor
[giannakidou-1998] [mendes-2025] [muskens-1996]

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
and `Tense.SOT.Decomposition` for the formal connection.
-/

section AttitudeTemporalAnchor

/-- SUBJ introduces a temporal anchor: the introduced situation's time
    is at or after the base situation's time.

    This parallels attitude embedding, where the embedded clause's
    perspective time shifts to the matrix event time. Both mechanisms
    create a new temporal reference point for embedded evaluation. -/
theorem subj_temporal_anchor {W Time : Type*} [LE Time]
    (history : HistoricalAlternatives W Time)
    (P : SitPred W Time)
    (s₀ : WorldTimeIndex W Time)
    (h : SUBJ history P s₀) :
    ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ s₁.time ≥ s₀.time ∧ P s₁ s₀ := by
  obtain ⟨s₁, h_hist, h_P⟩ := h
  refine ⟨s₁, h_hist, ?_, h_P⟩
  have hmem := h_hist
  simp only [historicalBase, Set.mem_setOf_eq] at hmem
  exact hmem.2

end AttitudeTemporalAnchor

/-! ### SUBJ as tower push

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
    Semantics.Context.ContextShift (Semantics.Context.KContext W E P Time) where
  apply := λ c => { c with world := newWorld, time := newTime }
  label := .mood

/-- Pushing a `subjShift` changes the world to the introduced situation's world. -/
theorem subjShift_changes_world {E P : Type*}
    (w : W) (t : Time) (c : Semantics.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).world = w := rfl

/-- Pushing a `subjShift` changes the time to the introduced situation's time. -/
theorem subjShift_changes_time {E P : Type*}
    (w : W) (t : Time) (c : Semantics.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).time = t := rfl

/-- Pushing a `subjShift` preserves the agent. -/
theorem subjShift_preserves_agent {E P : Type*}
    (w : W) (t : Time) (c : Semantics.Context.KContext W E P Time) :
    ((subjShift (E := E) (P := P) w t).apply c).agent = c.agent := rfl

/-- The tower-based subjunctive: SUBJ holds iff there exists a situation
    in the historical base such that pushing `subjShift` for that situation
    and evaluating the predicate yields truth.

    This is the bridge between the existential `SUBJ` and the tower `push`. -/
theorem subj_as_tower_push [LE Time]
    (history : HistoricalAlternatives W Time)
    (Q : SitPred W Time)
    (s₀ : WorldTimeIndex W Time) :
    SUBJ history Q s₀ ↔
    ∃ s₁ ∈ historicalBase history s₀,
      Q s₁ s₀ := by
  simp only [SUBJ]

end TowerMood

end Semantics.Mood
