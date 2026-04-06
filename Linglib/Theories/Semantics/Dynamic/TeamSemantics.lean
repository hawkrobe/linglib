import Mathlib.Data.Set.Basic

/-!
# Team Semantics Infrastructure
@cite{aloni-2022} @cite{ciardelli-groenendijk-roelofsen-2018}

Team semantics evaluates formulas relative to sets of evaluation points
(teams) rather than single points. This module provides the core infrastructure.

## Background

Team semantics originated in logic and has been
applied to linguistics for:
- Inquisitive Semantics: questions as issues (sets of info states)
- Free Choice: Aloni's BSML derives FC via non-emptiness constraints
- Modified Numerals: first-order team semantics
- Exceptional Scope: indefinites with team-based evaluation

## Key Concepts

- `Team W`: A set of worlds (characteristic function `W -> Bool`)
- Team operations: empty, full, singleton, subset, union, intersection, etc.

## Architecture

This module provides general infrastructure. Specific applications:
- `Systems/BSML/`: Bilateral State-based Modal Logic
- `Questions/Inquisitive.lean`: Inquisitive semantics for questions

-/

namespace Semantics.Dynamic.TeamSemantics

/--
A team is a set of worlds, represented as a characteristic function.

In team semantics, formulas are evaluated relative to teams rather than
single worlds. A team represents an information state: the set of worlds
compatible with current information.

This is equivalent to `InfoState` in Inquisitive Semantics.
-/
abbrev Team (W : Type*) := W -> Bool

/-- The empty team (inconsistent information state) -/
def Team.empty {W : Type*} : Team W := λ _ => false

/-- The full team (no information / total ignorance) -/
def Team.full {W : Type*} : Team W := λ _ => true

/-- Singleton team containing just one world -/
def Team.singleton {W : Type*} [DecidableEq W] (w : W) : Team W := λ w' => w == w'

/-- Check if a team is empty (no worlds) -/
def Team.isEmpty {W : Type*} (t : Team W) (worlds : List W) : Bool :=
  !worlds.any t

/-- Check if a team is non-empty -/
def Team.isNonEmpty {W : Type*} (t : Team W) (worlds : List W) : Bool :=
  worlds.any t

/-- Team membership: world w is in team t -/
def Team.mem {W : Type*} (t : Team W) (w : W) : Bool := t w

/-- Team subset: t ⊆ t' -/
def Team.subset {W : Type*} (t t' : Team W) (worlds : List W) : Bool :=
  worlds.all λ w => !t w || t' w

/-- Team intersection: t ∩ t' -/
def Team.inter {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w && t' w

/-- Team union: t ∪ t' -/
def Team.union {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w || t' w

/-- Team complement: W \ t -/
def Team.compl {W : Type*} (t : Team W) : Team W :=
  λ w => !t w

/-- Team difference: t \ t' -/
def Team.diff {W : Type*} (t t' : Team W) : Team W :=
  λ w => t w && !t' w

/-- Filter team by predicate -/
def Team.filter {W : Type*} (t : Team W) (p : W -> Bool) : Team W :=
  λ w => t w && p w

/-- All worlds in team satisfy predicate -/
def Team.all {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !t w || p w

/-- Some world in team satisfies predicate -/
def Team.any {W : Type*} (t : Team W) (p : W -> Bool) (worlds : List W) : Bool :=
  worlds.any λ w => t w && p w

/-- Convert team to list of worlds -/
def Team.toList {W : Type*} (t : Team W) (worlds : List W) : List W :=
  worlds.filter t

/-- Team from list of worlds -/
def Team.ofList {W : Type*} [DecidableEq W] (ws : List W) : Team W :=
  λ w => ws.contains w

/-- Team equality (extensional, given finite world list) -/
def Team.beq {W : Type*} (t t' : Team W) (worlds : List W) : Bool :=
  worlds.all λ w => t w == t' w

-- ============================================================================
-- §2: Assignment Teams and Dependence (@cite{hodges-1997}, @cite{vaananen-2007})
-- ============================================================================

/-- An assignment team: a set of variable assignments.
    Variables are `V`, entities are `E`. Each assignment maps
    variables to entities; a team is a list of such assignments.

    This is the setting for dependence logic (@cite{vaananen-2007}) and
    the semantics of indefinites in @cite{degano-aloni-2025}. -/
abbrev AssignmentTeam (V E : Type) := List (V → E)

/-- **Variation**: variable `x` varies with respect to parameter `y` in team `t`.

    `var(y, x)` holds iff there exist two assignments in `t` that agree on `y`
    but disagree on `x`. When `y` is a world variable `v`, this captures
    variation within a single epistemic world; when `y = ∅` (modeled by
    passing a vacuous variable), variation is across all worlds.

    @cite{degano-aloni-2025}: variation gives indefinite vs. non-specific
    readings; constancy gives definite vs. specific readings. -/
def variation {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V) : Bool :=
  t.any λ a₁ => t.any λ a₂ => a₁ y == a₂ y && a₁ x != a₂ x

/-- **Constancy** (dependence): variable `x` depends on parameter `y` in team `t`.

    `dep(y, x)` holds iff all assignments in `t` that agree on `y` also
    agree on `x`. This is functional dependence: `x` is a function of `y`.

    When `y` is a world variable `v`, this means `x` has a constant value
    within each epistemic world (= specific). When `y = ∅`, `x` has a
    constant value across all worlds (= specific known).

    @cite{degano-aloni-2025}, @cite{vaananen-2007} Definition 3.1. -/
def constancy {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V) : Bool :=
  t.all λ a₁ => t.all λ a₂ => a₁ y != a₂ y || a₁ x == a₂ x

/-- A finite witness: variation and constancy are jointly unsatisfiable.
    Demonstrated on a concrete 2-assignment team. -/
theorem constancy_excludes_variation_witness :
    let t : AssignmentTeam (Fin 2) (Fin 2) :=
      [λ v => if v = 0 then 0 else 0,   -- assignment 1: y↦0, x↦0
       λ v => if v = 0 then 0 else 1]    -- assignment 2: y↦0, x↦1
    -- var(y, x) holds: a₁ and a₂ agree on y (var 0) but disagree on x (var 1)
    variation t 0 1 = true ∧
    -- dep(y, x) fails: a₁ and a₂ agree on y but disagree on x
    constancy t 0 1 = false := by native_decide

/-- Constancy and variation are contradictory: for any team and
    variables, they cannot both be true. This follows because
    constancy requires all y-agreeing assignments to x-agree,
    while variation requires at least two y-agreeing assignments
    to x-disagree. -/
theorem constancy_excludes_variation {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (y x : V)
    (hdep : constancy t y x = true)
    (hvar : variation t y x = true) : False := by
  unfold constancy at hdep
  unfold variation at hvar
  simp only [List.all_eq_true, List.any_eq_true,
             Bool.and_eq_true, Bool.or_eq_true,
             bne_iff_ne, ne_eq, beq_iff_eq] at hdep hvar
  obtain ⟨a₁, ha₁, a₂, ha₂, hyeq, hxne⟩ := hvar
  have := hdep a₁ ha₁ a₂ ha₂
  rcases this with hyneq | hxeq
  · exact hyneq hyeq
  · exact hxne hxeq

/-- If two assignments agree on `v` but disagree on `x`, and they both
    also agree on `y` (vacuously — e.g., `y` is a constant), then
    `var(y, x)` holds. This is the core of the "weakening" direction
    in Degano & Aloni's diachronic predictions:
    `var(v, x) → var(∅, x)` when ∅ is modeled as a trivially-agreed
    parameter. Grounds non-specific → epistemic change
    (@cite{bubnov-2026} §6). -/
theorem variation_monotone {V E : Type} [DecidableEq V] [DecidableEq E]
    (t : AssignmentTeam V E) (v y x : V)
    (hvar : variation t v x = true)
    (h_agree : ∀ (a₁ a₂ : V → E), a₁ v = a₂ v → a₁ y = a₂ y) :
    variation t y x = true := by
  unfold variation at hvar ⊢
  simp only [List.any_eq_true, Bool.and_eq_true,
             bne_iff_ne, ne_eq, beq_iff_eq] at hvar ⊢
  obtain ⟨a₁, ha₁, a₂, ha₂, hveq, hxne⟩ := hvar
  exact ⟨a₁, ha₁, a₂, ha₂, h_agree a₁ a₂ hveq, hxne⟩

end Semantics.Dynamic.TeamSemantics
