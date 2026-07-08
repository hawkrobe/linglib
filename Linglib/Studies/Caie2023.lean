import Linglib.Discourse.CommonGround
import Mathlib.Data.Set.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Disjunctive Context Updating
[caie-2023]

Michael Caie. Context Dynamics. Semantics and Pragmatics 16, Article 3: 1–37.

## The Problem

Standard accounts of conversational updating ([stalnaker-1978]) assume
that, at each world w in the context set, there is a unique compositional
context c_w interpreting an assertion of φ. The context set is updated by
diagonalization: eliminate w iff ⟦φ⟧^{c_w} is false at w.

[caie-2023] argues this uniqueness assumption fails for context-sensitive
expressions like configurational predicates ("pair of socks"), where multiple
compositional contexts may be available at a single world. Standard Updating
combined with Minimal Symmetry and Preservation incorrectly predicts the
falsity of Safe Information in natural discourses.

## The Solution

**Disjunctive Multi-Context Updating**: at each world w, there is a non-empty
set I^φ_w of compositional contexts. A world w survives iff *some* context in
I^φ_w makes φ true at w. When I^φ_w is a singleton, this reduces to Standard
Updating.

**Contextual Pruning**: interpretation sets narrow across discourse. If β
immediately follows α, the contexts available for β at w are exactly those
that made α true at w.

## Architecture

Disjunctive Updating is an instance of ∃-projection over a **fragment set**
(§ 0): meaning depends on a parameter — here the compositional context C —
and the fragment set `F c w := I w c` says which contexts are available at
each world. `disjunctiveUpdate` = `existentialUpdate` and `prune` =
`fiberwiseFilter` (both with argument order swapped).

The § 0 substrate is deliberately framework-general (thresholds,
precisifications, comparison classes, assignments are all parameters in the
same sense), so the general results — De Morgan duality, monotone collapse,
sequential update = single conjunctive update — apply directly.

## Relationship to Existing Infrastructure

- `ContextSet.update c p` in `CommonGround.lean` is the special case where
  every world gets the same interpretation (no context sensitivity).
  See `disjunctiveUpdate_constant`.

- The `SpecSpace` in `Supervaluation/Basic.lean` is the ∀-dual:
  super-truth = true under ALL specs; Caie's survival = true under SOME.

- `CCP` in `Dynamic/Connectives/CCP.lean` operates on ⟨assignment, world⟩
  pairs; `ContextFragment` here uses ⟨compositional-context, world⟩ — a
  structural analogue with different conceptual content.
-/

namespace Caie2023

open CommonGround (ContextSet)

-- ════════════════════════════════════════════════════════════════
-- § 0. Parameterized Update (general substrate)
-- ════════════════════════════════════════════════════════════════

/-!
Framework-agnostic infrastructure for **parameter uncertainty**: meaning
depends on a parameter (threshold, compositional context, comparison class,
variable assignment) and truth at a world involves quantifying over
available parameters.

A fragment set F ⊆ P × W is a fiber bundle over worlds W; the fiber at w,
F_w = {p : F(p, w)}, collects the parameters available at that world. An
assertion φ with parameterized semantics ⟦φ⟧ : P → W → Prop acts as a
**fiberwise filter**: F' = {(p, w) ∈ F : ⟦φ⟧(p, w)}. Theories differ in how
they project from the bundle back to worlds, via the ∃ ⊣ Δ ⊣ ∀ adjunction:

- **∃-projection** ([caie-2023], [barker-2002]): w survives iff
  ∃ p ∈ F_w, ⟦φ⟧(p, w)
- **∀-projection** (supervaluation, [fine-1975]): w survives iff
  ∀ p ∈ F_w, ⟦φ⟧(p, w)
- **Σ-projection** (RSA, [lassiter-goodman-2017]): score(w) =
  Σ_p weight(p) · ⟦φ⟧(p, w) — a soft interpolation, not formalized here

Comparison classes ([klein-1980]) are ∃-projected parameters in the same
sense. When the semantics is antitone in the parameter (degree semantics:
`d > θ`), the projections collapse to extremal checks, and the gap between
min and max is the **borderline region** where ∃ and ∀ disagree.
-/

section ParameterizedUpdate

variable {P W : Type*}

/-- A fragment set: a relation between parameters and worlds.
    F(p, w) holds iff parameter p is available at world w.
    The fiber at w is F_w = {p : F p w}.

    Generalizes `InterpAssignment C W` from [caie-2023]
    (argument order swapped). -/
abbrev FragmentSet (P W : Type*) := P → W → Prop

/-- Fiberwise filter: restrict a fragment set to parameter–world pairs
    where the semantics holds.

    Generalizes Contextual Pruning ([caie-2023]): after asserting α,
    only parameters that made α true remain available. -/
def fiberwiseFilter (F : FragmentSet P W) (sem : P → W → Prop) :
    FragmentSet P W :=
  λ p w => F p w ∧ sem p w

/-- Existential projection: w survives iff some parameter in F_w makes
    the semantics true.

    This is [caie-2023]'s disjunctive updating and [barker-2002]'s
    dynamics of vagueness. -/
def existentialProjection (F : FragmentSet P W) (sem : P → W → Prop) :
    Set W :=
  λ w => ∃ p, F p w ∧ sem p w

/-- Universal projection: w survives iff all parameters in F_w make the
    semantics true.

    This is super-truth ([fine-1975]): truth under all admissible
    precisifications. -/
def universalProjection (F : FragmentSet P W) (sem : P → W → Prop) :
    Set W :=
  λ w => ∀ p, F p w → sem p w

/-- Existential update: restrict to the context set, then ∃-project.

    `existentialUpdate cs F sem w ↔ w ∈ cs ∧ ∃ p ∈ F_w, sem(p, w)`. -/
def existentialUpdate (cs : Set W) (F : FragmentSet P W)
    (sem : P → W → Prop) : Set W :=
  λ w => cs w ∧ existentialProjection F sem w

/-- Universal update: restrict to the context set, then ∀-project.

    `universalUpdate cs F sem w ↔ w ∈ cs ∧ ∀ p ∈ F_w, sem(p, w)`. -/
def universalUpdate (cs : Set W) (F : FragmentSet P W)
    (sem : P → W → Prop) : Set W :=
  λ w => cs w ∧ universalProjection F sem w

/-- **De Morgan duality** (∃-side): ∃-projection of sem ↔
    negation of ∀-projection of the negation. -/
theorem deMorgan_existential_universal (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    existentialProjection F sem w ↔
    ¬ universalProjection F (λ p w => ¬ sem p w) w := by
  constructor
  · intro ⟨p, hF, hs⟩ hall; exact hall p hF hs
  · intro h; by_contra hne
    exact h fun p hF hs => hne ⟨p, hF, hs⟩

/-- **De Morgan duality** (∀-side): ∀-projection of sem ↔
    negation of ∃-projection of the negation. -/
theorem deMorgan_universal_existential (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    universalProjection F sem w ↔
    ¬ existentialProjection F (λ p w => ¬ sem p w) w := by
  constructor
  · intro hall ⟨p, hF, hs⟩; exact hs (hall p hF)
  · intro h p hF; by_contra hs; exact h ⟨p, hF, hs⟩

/-- Monotone collapse (∃): when sem is `Antitone` in p and F_w has
    a least element, ∃-projection reduces to checking the minimum.

    The `Antitone` condition on `fun p => sem p w` means `p₁ ≤ p₂ →
    sem p₂ w → sem p₁ w` — truth propagates downward in the parameter
    ordering. This is the standard situation in degree semantics:
    `⟦tall⟧(θ, w) = degree(w) > θ` is antitone in θ. -/
theorem monotoneCollapse_exists [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p₀ : P)
    (h_least : IsLeast {p | F p w} p₀)
    (h_anti : Antitone (λ p => sem p w)) :
    existentialProjection F sem w ↔ sem p₀ w := by
  constructor
  · intro ⟨p, hF, hs⟩; exact h_anti (h_least.2 hF) hs
  · intro hs; exact ⟨p₀, h_least.1, hs⟩

/-- Monotone collapse (∀): when sem is `Antitone` in p and F_w has
    a greatest element, ∀-projection reduces to checking the maximum.

    For degree semantics: the ∀-projection `∀ θ ∈ Θ, degree(w) > θ`
    collapses to `degree(w) > max(Θ)`. -/
theorem monotoneCollapse_forall [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p₀ : P)
    (h_greatest : IsGreatest {p | F p w} p₀)
    (h_anti : Antitone (λ p => sem p w)) :
    universalProjection F sem w ↔ sem p₀ w := by
  constructor
  · intro hall; exact hall p₀ h_greatest.1
  · intro hs p hF; exact h_anti (h_greatest.2 hF) hs

/-- Corollary: when sem is antitone and F_w has both a least and
    greatest element, the ∃ and ∀ projections agree iff w is outside
    the **borderline region** — either sem holds at the hardest
    parameter (clearly in) or fails at the easiest (clearly out).

    The borderline region where projections disagree is precisely
    `sem p_min w ∧ ¬ sem p_max w`. -/
theorem projections_agree_iff_clear [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p_min p_max : P)
    (h_least : IsLeast {p | F p w} p_min)
    (h_greatest : IsGreatest {p | F p w} p_max)
    (h_anti : Antitone (λ p => sem p w)) :
    (existentialProjection F sem w ↔ universalProjection F sem w) ↔
    (sem p_max w ∨ ¬ sem p_min w) := by
  rw [monotoneCollapse_exists F sem w p_min h_least h_anti,
      monotoneCollapse_forall F sem w p_max h_greatest h_anti]
  constructor
  · intro ⟨mp, _⟩
    by_cases h : sem p_min w
    · exact Or.inl (mp h)
    · exact Or.inr h
  · intro h
    cases h with
    | inl hmax => exact ⟨λ _ => hmax, λ hs => h_anti (h_least.2 h_greatest.1) hs⟩
    | inr hmin => exact ⟨λ hs => absurd hs hmin,
        λ hs => h_anti (h_least.2 h_greatest.1) hs⟩

/-- Sequential ∃-update with pruning: asserting α then β (where β's
    parameters are pruned by α) equals a single ∃-update checking
    both α and β.

    This is the general form of Contextual Pruning ([caie-2023]):
    the two-step process (update context set by α, prune parameters
    by α, then update by β) is equivalent to a single update requiring
    both α and β under the same parameter. -/
theorem sequential_existentialUpdate (cs : Set W) (F : FragmentSet P W)
    (sem₁ sem₂ : P → W → Prop) :
    existentialUpdate
      (existentialUpdate cs F sem₁)
      (fiberwiseFilter F sem₁)
      sem₂ =
    existentialUpdate cs F (λ p w => sem₁ p w ∧ sem₂ p w) := by
  funext w
  simp only [existentialUpdate, existentialProjection, fiberwiseFilter]
  exact propext ⟨
    λ ⟨⟨hcs, _⟩, p, ⟨hF, hs₁⟩, hs₂⟩ => ⟨hcs, p, hF, hs₁, hs₂⟩,
    λ ⟨hcs, p, hF, hs₁, hs₂⟩ => ⟨⟨hcs, p, hF, hs₁⟩, p, ⟨hF, hs₁⟩, hs₂⟩⟩

/-- Sequential ∀-update with pruning: asserting α then β (where β's
    parameters are pruned by α) equals a single ∀-update checking
    both α and β.

    The ∀ case works because: if all parameters satisfy α (first step),
    then "pruned parameters" = "all parameters", so requiring β for
    pruned parameters = requiring β for all parameters. -/
theorem sequential_universalUpdate (cs : Set W) (F : FragmentSet P W)
    (sem₁ sem₂ : P → W → Prop) :
    universalUpdate
      (universalUpdate cs F sem₁)
      (fiberwiseFilter F sem₁)
      sem₂ =
    universalUpdate cs F (λ p w => sem₁ p w ∧ sem₂ p w) := by
  funext w
  simp only [universalUpdate, universalProjection, fiberwiseFilter]
  exact propext ⟨
    λ ⟨⟨hcs, h₁⟩, h₂⟩ =>
      ⟨hcs, λ p hF => ⟨h₁ p hF, h₂ p ⟨hF, h₁ p hF⟩⟩⟩,
    λ ⟨hcs, hall⟩ =>
      ⟨⟨hcs, λ p hF => (hall p hF).1⟩,
       λ p ⟨hF, _⟩ => (hall p hF).2⟩⟩

/-- ∃-projection is `Monotone` in the fragment set: expanding available
    parameters can only add surviving worlds. The `FragmentSet P W`
    type `P → W → Prop` carries the pointwise `→` ordering, and
    `∃-projection` preserves it. -/
theorem existentialProjection_mono (F₁ F₂ : FragmentSet P W)
    (sem : P → W → Prop) (h : ∀ p w, F₁ p w → F₂ p w) (w : W) :
    existentialProjection F₁ sem w → existentialProjection F₂ sem w :=
  λ ⟨p, hF, hs⟩ => ⟨p, h p w hF, hs⟩

/-- ∀-projection is `Antitone` in the fragment set: expanding available
    parameters can only remove surviving worlds (more to check). -/
theorem universalProjection_anti (F₁ F₂ : FragmentSet P W)
    (sem : P → W → Prop) (h : ∀ p w, F₁ p w → F₂ p w) (w : W) :
    universalProjection F₂ sem w → universalProjection F₁ sem w :=
  λ hall p hF₁ => hall p (h p w hF₁)

/-- ∃-update only removes worlds from the context set. -/
theorem existentialUpdate_restricts (cs : Set W) (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    existentialUpdate cs F sem w → cs w :=
  And.left

/-- ∀-update only removes worlds from the context set. -/
theorem universalUpdate_restricts (cs : Set W) (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    universalUpdate cs F sem w → cs w :=
  And.left

/-- Fiberwise filter only removes parameters. -/
theorem fiberwiseFilter_sub (F : FragmentSet P W) (sem : P → W → Prop)
    (p : P) (w : W) :
    fiberwiseFilter F sem p w → F p w :=
  And.left

/-- ∀-update implies ∃-update when the fiber is non-empty.
    Super-truth implies disjunctive survival. -/
theorem universalUpdate_implies_existentialUpdate (cs : Set W)
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W)
    (h_ne : ∃ p, F p w) :
    universalUpdate cs F sem w → existentialUpdate cs F sem w :=
  λ ⟨hcs, hall⟩ => let ⟨p, hF⟩ := h_ne; ⟨hcs, p, hF, hall p hF⟩

/-- When F_w is a singleton {p₀}, both projections agree with
    a direct check of sem(p₀, w). No parameter uncertainty. -/
theorem singleton_projections_agree (p₀ : P) (sem : P → W → Prop) (w : W) :
    existentialProjection (λ p _ => p = p₀) sem w ↔
    universalProjection (λ p _ => p = p₀) sem w := by
  constructor
  · intro ⟨_, hp, hs⟩ p hp'; subst hp; subst hp'; exact hs
  · intro hall; exact ⟨p₀, rfl, hall p₀ rfl⟩

/-- Singleton ∃-update reduces to propositional filtering. -/
theorem existentialUpdate_singleton (cs : Set W) (p₀ : P)
    (sem : P → W → Prop) :
    existentialUpdate cs (λ p _ => p = p₀) sem =
    λ w => cs w ∧ sem p₀ w := by
  funext w
  simp only [existentialUpdate, existentialProjection]
  exact propext ⟨
    λ ⟨hcs, _, hp, hs⟩ => by subst hp; exact ⟨hcs, hs⟩,
    λ ⟨hcs, hs⟩ => ⟨hcs, p₀, rfl, hs⟩⟩

end ParameterizedUpdate


-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

variable {C W : Type*}

/-- A context fragment: an ordered pair ⟨compositional context, world⟩.

Context fragments are the state representation for Disjunctive Updating.
The compositional context determines how context-sensitive expressions
(indexicals, gradable adjectives, configurational predicates) are
interpreted; the world determines matters of fact.

Structurally analogous to `Possibility W E` in `Dynamic/Core/Update.lean`
(⟨world, assignment⟩ pairs in dynamic semantics), but the non-world
parameter is a compositional context rather than a variable assignment. -/
structure ContextFragment (C W : Type*) where
  ctx : C
  world : W

/-- An interpretation assignment maps worlds to predicates on compositional
    contexts. `I w c` holds iff c is available to interpret an assertion at w.

    [caie-2023]: "for each world w in the relevant context set, a
    non-empty set of compositional contexts that interpret that assertion
    of φ at w: I^φ_w."

    This is a `FragmentSet C W` with swapped argument order:
    `I w c` ↔ `F c w` where `F : FragmentSet C W`. -/
abbrev InterpAssignment (C W : Type*) := W → C → Prop

/-- Convert an `InterpAssignment` to a `FragmentSet` by swapping argument
    order. This is the bridge between Caie's convention (index by world
    first) and the § 0 convention (index by parameter
    first). -/
abbrev InterpAssignment.toFragmentSet (I : InterpAssignment C W) :
    FragmentSet C W :=
  λ c w => I w c


-- ════════════════════════════════════════════════════════════════
-- § 2. Standard Updating
-- ════════════════════════════════════════════════════════════════

/-- Standard Updating with explicit diagonalization
    ([stalnaker-1978], formulated following [caie-2023] §1).

    At each world w, a unique compositional context c_w determines the
    proposition expressed. The diagonal proposition is
    {w ∈ C : w ∈ ⟦φ⟧^{c_w}}.

    Note: `Assertion.Stalnaker.assert` in `Stalnaker.lean` implements the
    degenerate case where the proposition is fixed across worlds (no
    diagonalization needed). This definition makes the compositional
    context parameter explicit. -/
def standardUpdate (cs : Set W) (c_w : W → C) (sem : C → W → Prop) : Set W :=
  λ w => cs w ∧ sem (c_w w) w


-- ════════════════════════════════════════════════════════════════
-- § 3. Disjunctive Multi-Context Updating
-- ════════════════════════════════════════════════════════════════

/-- Disjunctive Multi-Context Updating ([caie-2023] §3).

    A world w survives iff there exists some compositional context c in the
    interpretation set I_w such that ⟦φ⟧^c is true at w. When I_w is a
    singleton {c_w}, this reduces to `standardUpdate`.

    Defined as `existentialUpdate` (§ 0) with the
    interpretation assignment as the fragment set (argument order swapped).

    [caie-2023]: "The result of updating the context given the assertion
    is C^φ = {w ∈ C_φ : w ∈ ⟦φ⟧^c, for some c ∈ I^φ_w}." -/
abbrev disjunctiveUpdate (cs : Set W) (I : InterpAssignment C W)
    (sem : C → W → Prop) : Set W :=
  existentialUpdate cs I.toFragmentSet sem


-- ════════════════════════════════════════════════════════════════
-- § 4. Contextual Pruning
-- ════════════════════════════════════════════════════════════════

/-- Contextual Pruning ([caie-2023] §3): restrict interpretation sets
    to truth-making contexts.

    If β immediately follows α in a discourse at world w, the compositional
    contexts available for β at w are exactly those that made α true at w.

    Defined as `fiberwiseFilter` (§ 0, argument order
    swapped).

    [caie-2023]: "if {c : c ∈ I^α_w and w ∈ ⟦α⟧^c} ≠ ∅, then
    I^β_w = {c : c ∈ I^α_w and w ∈ ⟦α⟧^c}."

    Note: the paper's definition includes a non-emptiness precondition —
    pruning applies only when at least one context survives. This definition
    unconditionally restricts; in all applications here, the pruned set is
    non-empty by construction (both discourses have truth-making contexts
    at every world). -/
abbrev prune (I : InterpAssignment C W) (sem : C → W → Prop) :
    InterpAssignment C W :=
  λ w c => fiberwiseFilter I.toFragmentSet sem c w


-- ════════════════════════════════════════════════════════════════
-- § 5. Fragmentation
-- ════════════════════════════════════════════════════════════════

/-- The fragmentation of a context set: all ⟨c, w⟩ pairs where w is in
    the context set and c is an available interpretation at w.

    [caie-2023]: "Call a context fragment an ordered pair of a
    compositional context and a world, and call the fragmentation of C_φ
    the set of context fragments ⟨c, w⟩ such that w ∈ C_φ and c interprets
    φ in w." -/
def fragmentation (cs : Set W) (I : InterpAssignment C W) :
    ContextFragment C W → Prop :=
  λ f => cs f.world ∧ I f.world f.ctx

/-- Project fragments to their world components. -/
def fragmentWorlds (frags : ContextFragment C W → Prop) : Set W :=
  λ w => ∃ c, frags ⟨c, w⟩

/-- Disjunctive updating is equivalent to updating the fragmentation and
    projecting to worlds. -/
theorem disjunctiveUpdate_eq_fragmentWorlds (cs : Set W)
    (I : InterpAssignment C W) (sem : C → W → Prop) :
    disjunctiveUpdate cs I sem =
    fragmentWorlds (λ f => fragmentation cs I f ∧ sem f.ctx f.world) := by
  funext w
  simp only [disjunctiveUpdate, existentialUpdate, existentialProjection,
             fragmentWorlds, fragmentation, InterpAssignment.toFragmentSet]
  exact propext ⟨
    λ ⟨hw, c, hI, hs⟩ => ⟨c, ⟨hw, hI⟩, hs⟩,
    λ ⟨c, ⟨hw, hI⟩, hs⟩ => ⟨hw, c, hI, hs⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § 6. Structural Properties
-- ════════════════════════════════════════════════════════════════

/-- Standard Updating is the singleton case of Disjunctive Updating.
    When the interpretation set at each world is {c_w}, the existential
    in Disjunctive Updating collapses to a single check. -/
theorem standard_eq_disjunctive_singleton (cs : Set W)
    (c_w : W → C) (sem : C → W → Prop) :
    standardUpdate cs c_w sem =
    disjunctiveUpdate cs (λ w c => c = c_w w) sem := by
  funext w
  simp only [standardUpdate, disjunctiveUpdate, existentialUpdate,
             existentialProjection, InterpAssignment.toFragmentSet]
  exact propext ⟨
    λ ⟨hw, hs⟩ => ⟨hw, _, rfl, hs⟩,
    λ ⟨hw, _, hc, hs⟩ => by subst hc; exact ⟨hw, hs⟩⟩

/-- Expanding interpretation sets can only add worlds to the result. -/
theorem disjunctiveUpdate_mono_interp (cs : Set W)
    (I₁ I₂ : InterpAssignment C W) (sem : C → W → Prop)
    (h : ∀ w c, I₁ w c → I₂ w c) (w : W) :
    disjunctiveUpdate cs I₁ sem w → disjunctiveUpdate cs I₂ sem w :=
  λ ⟨hw, c, hc, hs⟩ => ⟨hw, c, h w c hc, hs⟩


-- ════════════════════════════════════════════════════════════════
-- § 7. Connection to ContextSet.update
-- ════════════════════════════════════════════════════════════════

/-- When there is a single fixed interpretation for all worlds, disjunctive
    updating reduces to propositional filtering — the mechanism formalized
    as `ContextSet.update` in `CommonGround.lean`.

    This witnesses the fact that `ContextSet.update` is the degenerate case
    of Disjunctive Updating where context sensitivity plays no role: the
    same proposition is expressed at every world. -/
theorem disjunctiveUpdate_constant (cs : Set W) (c₀ : C)
    (sem : C → W → Prop) :
    disjunctiveUpdate cs (λ _ c => c = c₀) sem = λ w => cs w ∧ sem c₀ w := by
  funext w
  simp only [disjunctiveUpdate, existentialUpdate, existentialProjection,
             InterpAssignment.toFragmentSet]
  exact propext ⟨
    λ ⟨hw, _, hc, hs⟩ => by subst hc; exact ⟨hw, hs⟩,
    λ ⟨hw, hs⟩ => ⟨hw, _, rfl, hs⟩⟩

/-- Disjunctive updating with a fixed context reduces to `ContextSet.update`.

    This explicitly connects the general framework to the infrastructure in
    `CommonGround.lean`: context-insensitive assertions (same proposition at
    every world) update via ordinary propositional filtering. -/
theorem disjunctiveUpdate_eq_contextSet_update (cs : Set W) (c₀ : C)
    (sem : C → W → Prop) :
    disjunctiveUpdate cs (λ _ c => c = c₀) sem =
    ContextSet.update cs (sem c₀) := by
  exact disjunctiveUpdate_constant cs c₀ sem


-- ════════════════════════════════════════════════════════════════
-- § 8. Generalized Preservation
-- ════════════════════════════════════════════════════════════════

/-- Generalized Preservation ([caie-2023] §3): if there is a unique
    compositional context interpreting α at w, and it makes α true, then
    it persists as the unique context for subsequent assertions.

    [caie-2023]: "for each w ∈ C_α if there is a unique compositional
    context c that interprets an assertion of α in w, then if w ∈ C^α, then
    c uniquely interprets the subsequent assertion of β in w."

    This follows directly from Contextual Pruning: when the input is a
    singleton and the element makes α true, pruning preserves it. -/
theorem generalized_preservation
    (I : InterpAssignment C W) (sem : C → W → Prop)
    (w : W) (c₀ : C)
    (h_unique : ∀ c, I w c ↔ c = c₀) (h_true : sem c₀ w) :
    ∀ c, prune I sem w c ↔ c = c₀ := by
  intro c
  constructor
  · intro ⟨hI, _⟩; exact (h_unique c).mp hI
  · rintro rfl; exact ⟨(h_unique _).mpr rfl, h_true⟩


-- ════════════════════════════════════════════════════════════════
-- § 9. Discourse Sequencing
-- ════════════════════════════════════════════════════════════════

/-- A discourse step: update the context set and prune interpretation sets.
    Returns the new context set and the narrowed interpretation assignment. -/
def discourseStep (cs : Set W) (I : InterpAssignment C W)
    (sem : C → W → Prop) : Set W × InterpAssignment C W :=
  (disjunctiveUpdate cs I sem, prune I sem)

/-- Sequential discourse steps are monotonically restrictive in both
    the context set and interpretation sets. -/
theorem discourseStep_restricts (cs : Set W) (I : InterpAssignment C W)
    (sem : C → W → Prop) :
    let ⟨cs', I'⟩ := discourseStep cs I sem
    (∀ w, cs' w → cs w) ∧ (∀ w c, I' w c → I w c) :=
  ⟨λ w => existentialUpdate_restricts cs I.toFragmentSet sem w,
   λ w c => fiberwiseFilter_sub I.toFragmentSet sem c w⟩

/-- Contextual Pruning reduces to the general sequential ∃-update theorem:
    asserting α then β (with pruned parameters) = single ∃-update checking
    both α and β under the same parameter.

    This is [caie-2023]'s central mechanism, obtained for free from
    `sequential_existentialUpdate` (§ 0). -/
theorem contextual_pruning_sequential (cs : Set W)
    (I : InterpAssignment C W) (sem₁ sem₂ : C → W → Prop) :
    disjunctiveUpdate
      (disjunctiveUpdate cs I sem₁)
      (prune I sem₁)
      sem₂ =
    disjunctiveUpdate cs I (λ c w => sem₁ c w ∧ sem₂ c w) :=
  sequential_existentialUpdate cs I.toFragmentSet sem₁ sem₂


-- ════════════════════════════════════════════════════════════════
-- § 10. Sarah's Socks — Worked Example
-- ════════════════════════════════════════════════════════════════

/-! ## Sarah's Socks ([caie-2023] §2.1)

Tim has strong preferences about socks. Two discourses communicate
that Tim likes matching socks and dislikes mixed ones:

**Tim Likes Matching**: (1) Sarah has two pairs of socks.
(2) Tim likes both of them. (3) Both of them are matching.

**Tim Dislikes Mixed**: (1) Sarah has two pairs of socks.
(4) Tim dislikes both of them. (5) Both of them are mixed.

### Model

- **Worlds** (`TimPref`): Tim likes matching pairs, or likes mixed pairs.
- **Contexts** (`DressInt`): dressing intension is matching or mixed.
- **Initial interpretation set**: both intensions at every world.
- **4 context fragments**: {matching, mixed} × {likesMatching, likesMixed}.

### Verification Table (from [caie-2023])

For Tim Likes Matching:

|                                 | C⁽¹⁾ | C⁽¹⁾⁽²⁾ | C⁽¹⁾⁽²⁾⁽³⁾ |
|---------------------------------|-------|----------|-------------|
| ⟨matchInt, wMatch⟩             |  ✓   |    ✓     |     ✓       |
| ⟨mixedInt, wMatch⟩             |  ✓   |    ✗     |     ✗       |
| ⟨matchInt, wMixed⟩             |  ✓   |    ✗     |     ✗       |
| ⟨mixedInt, wMixed⟩             |  ✓   |    ✓     |     ✗       |

Only ⟨matchInt, wMatch⟩ survives: Tim likes matching socks. -/

/-- Tim's preference: the world parameter. -/
inductive TimPref | likesMatching | likesMixed
  deriving DecidableEq, Repr

/-- Dressing intension: the compositional context parameter.
    Determines which non-overlapping pairings of Sarah's socks are in
    the domain of quantification. -/
inductive DressInt | matching | mixed
  deriving DecidableEq, Repr

namespace SarahsSocks

-- ──── Sentence semantics ────

/-- "Tim likes both of them": true when the intension picks the kind
    of pairs Tim likes. -/
def likes : DressInt → TimPref → Prop
  | .matching, .likesMatching => True
  | .mixed,    .likesMixed    => True
  | _,         _              => False

instance : ∀ (c : DressInt) (w : TimPref), Decidable (likes c w)
  | .matching, .likesMatching => isTrue trivial
  | .matching, .likesMixed    => isFalse (fun h => h)
  | .mixed,    .likesMatching => isFalse (fun h => h)
  | .mixed,    .likesMixed    => isTrue trivial

/-- "Tim dislikes both of them": complement of `likes`. -/
def dislikes (c : DressInt) (w : TimPref) : Prop := ¬ likes c w

instance (c : DressInt) (w : TimPref) : Decidable (dislikes c w) :=
  inferInstanceAs (Decidable (¬ _))

/-- "Both of them are matching": true under matching intension. -/
def isMatching : DressInt → TimPref → Prop
  | .matching, _ => True
  | .mixed,    _ => False

instance : ∀ (c : DressInt) (w : TimPref), Decidable (isMatching c w)
  | .matching, _ => isTrue trivial
  | .mixed,    _ => isFalse (fun h => h)

/-- "Both of them are mixed": true under mixed intension. -/
def isMixed : DressInt → TimPref → Prop
  | .mixed,    _ => True
  | .matching, _ => False

instance : ∀ (c : DressInt) (w : TimPref), Decidable (isMixed c w)
  | .mixed,    _ => isTrue trivial
  | .matching, _ => isFalse (fun h => h)

-- ──── Discourse composition ────

-- Both discourses share sentence (1), which is uninformative.
-- The initial interpretation set is full: both intensions at every world.
-- Pruning by (1) leaves the interpretation set unchanged.
-- So we start from the full interpretation set and compose (2)+(3) or (4)+(5).

/-- Tim Likes Matching result: w survives iff there exists a context c
    such that `likes c w` (surviving (2)) AND `isMatching c w` (surviving (3)).
    The conjunction arises from Contextual Pruning: only contexts that made
    (2) true are available to interpret (3). -/
def timLikesMatchingResult (w : TimPref) : Prop :=
  -- ∃ c ∈ {matching, mixed}, likes c w ∧ isMatching c w
  (likes .matching w ∧ isMatching .matching w) ∨
  (likes .mixed w ∧ isMatching .mixed w)

instance (w : TimPref) : Decidable (timLikesMatchingResult w) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Tim Dislikes Mixed result: w survives iff ∃ c, dislikes c w ∧ isMixed c w. -/
def timDislikesMixedResult (w : TimPref) : Prop :=
  (dislikes .matching w ∧ isMixed .matching w) ∨
  (dislikes .mixed w ∧ isMixed .mixed w)

instance (w : TimPref) : Decidable (timDislikesMixedResult w) :=
  inferInstanceAs (Decidable (_ ∨ _))

-- ──── Verification ────

/-- Tim Likes Matching keeps the matching-preference world. -/
theorem tlm_keeps_matching : timLikesMatchingResult .likesMatching := by decide

/-- Tim Likes Matching eliminates the mixed-preference world. -/
theorem tlm_eliminates_mixed : ¬ timLikesMatchingResult .likesMixed := by decide

/-- Tim Dislikes Mixed keeps the matching-preference world. -/
theorem tdm_keeps_matching : timDislikesMixedResult .likesMatching := by decide

/-- Tim Dislikes Mixed eliminates the mixed-preference world. -/
theorem tdm_eliminates_mixed : ¬ timDislikesMixedResult .likesMixed := by decide

/-- Both discourses yield the same result. -/
theorem discourses_agree (w : TimPref) :
    timLikesMatchingResult w ↔ timDislikesMixedResult w := by
  cases w
  · exact ⟨fun _ => tdm_keeps_matching, fun _ => tlm_keeps_matching⟩
  · exact ⟨fun h => (tlm_eliminates_mixed h).elim,
           fun h => (tdm_eliminates_mixed h).elim⟩

-- ──── Safe Information ────

/-- The set of fact-worlds: those where Tim likes matching and dislikes mixed. -/
def facts (w : TimPref) : Prop :=
  match w with | .likesMatching => True | .likesMixed => False

instance : ∀ (w : TimPref), Decidable (facts w)
  | .likesMatching => isTrue trivial
  | .likesMixed    => isFalse (fun h => h)

/-- Safe Information condition (i): the update result is a subset of
    the fact-worlds. Under Disjunctive Updating, asserting Tim Likes
    Matching eliminates all non-fact worlds. -/
theorem safe_info_i_tlm (w : TimPref) :
    timLikesMatchingResult w → facts w := by
  cases w
  · intro _; trivial
  · intro h; exact (tlm_eliminates_mixed h).elim

/-- Safe Information condition (ii): every fact-world where the discourse
    occurs is retained. -/
theorem safe_info_ii_tlm (w : TimPref) :
    facts w → timLikesMatchingResult w := by
  cases w
  · intro _; exact tlm_keeps_matching
  · intro h; exact h.elim

/-- Safe Information condition (i) for Tim Dislikes Mixed. -/
theorem safe_info_i_tdm (w : TimPref) :
    timDislikesMixedResult w → facts w := by
  cases w
  · intro _; trivial
  · intro h; exact (tdm_eliminates_mixed h).elim

/-- Safe Information condition (ii) for Tim Dislikes Mixed. -/
theorem safe_info_ii_tdm (w : TimPref) :
    facts w → timDislikesMixedResult w := by
  cases w
  · intro _; exact tdm_keeps_matching
  · intro h; exact h.elim

-- ──── Negative results: why Standard Updating fails ────

/-- [caie-2023] §2.2, first Claim: Standard Updating + Preservation +
    Minimal Symmetry → ¬Safe Information.

    Under Minimal Symmetry, the same dressing intension c interprets
    sentence (1) in both discourses (at fact-worlds w₁ and w₂ that
    agree on all pre-assertion facts). Under Preservation, c persists
    to interpret later sentences. Safe Information (ii) then requires:
    - `likes c w` (for TLM to retain a fact-world)
    - `dislikes c w` (for TDM to retain a fact-world)
    But `dislikes = ¬likes`, so no intension c satisfies both.

    This is the paper's central argument against Standard Updating. -/
theorem standard_update_incompatible (c : DressInt) (w : TimPref) :
    ¬(likes c w ∧ dislikes c w) := by
  rintro ⟨hl, hd⟩; exact hd hl

/-- [caie-2023] §2.2, second Claim: Standard Updating + Uniform Charity
    → ¬Safe Information (condition i).

    Under Uniform Charity (prefer truth-making interpretations), each
    sentence individually has a truth-making context at every world.
    Under Standard Updating (unique context per sentence, shifts allowed),
    each sentence is interpreted by its truth-making context. No world is
    eliminated, so the update result includes non-fact worlds.

    Witness: at `.likesMixed`, sentence (2) is true under mixed intension
    (Tim likes mixed pairs in that world) and sentence (3) is true under
    matching intension. Yet `.likesMixed` is not a fact-world. -/
theorem uniform_charity_retains_nonfact :
    (∃ c : DressInt, likes c .likesMixed) ∧
    (∃ c : DressInt, isMatching c .likesMixed) ∧
    ¬ facts .likesMixed :=
  ⟨⟨.mixed, trivial⟩, ⟨.matching, trivial⟩, fun h => h⟩

-- ──── Connection to general framework ────

/-- The hand-computed Tim Likes Matching result agrees with the Prop-valued
    `disjunctiveUpdate` applied via `discourseStep`.

    This connects the hand-computed verification above to the
    general theory. -/
theorem tlm_agrees_with_framework (w : TimPref) :
    timLikesMatchingResult w ↔
    (disjunctiveUpdate
      (disjunctiveUpdate (λ _ => True) (λ _ _ => True)
        (λ c w => likes c w))
      (prune (λ _ _ => True) (λ c w => likes c w))
      (λ c w => isMatching c w)) w := by
  cases w with
  | likesMatching =>
    constructor
    · intro _
      exact ⟨⟨trivial, .matching, trivial, trivial⟩,
             .matching, ⟨trivial, trivial⟩, trivial⟩
    · intro _; exact tlm_keeps_matching
  | likesMixed =>
    constructor
    · intro h; exact (tlm_eliminates_mixed h).elim
    · intro ⟨_, c, ⟨_, hlikes⟩, hmatch⟩
      cases c with
      | matching => exact hlikes.elim
      | mixed => exact hmatch.elim

/-- The hand-computed Tim Dislikes Mixed result agrees with the Prop-valued
    framework. Mirror of `tlm_agrees_with_framework`. -/
theorem tdm_agrees_with_framework (w : TimPref) :
    timDislikesMixedResult w ↔
    (disjunctiveUpdate
      (disjunctiveUpdate (λ _ => True) (λ _ _ => True)
        (λ c w => dislikes c w))
      (prune (λ _ _ => True) (λ c w => dislikes c w))
      (λ c w => isMixed c w)) w := by
  cases w with
  | likesMatching =>
    constructor
    · intro _
      refine ⟨⟨trivial, .mixed, trivial, ?_⟩,
              .mixed, ⟨trivial, ?_⟩, trivial⟩
      · intro h; exact h.elim
      · intro h; exact h.elim
    · intro _; exact tdm_keeps_matching
  | likesMixed =>
    constructor
    · intro h; exact (tdm_eliminates_mixed h).elim
    · intro ⟨_, c, ⟨_, hdis⟩, hmix⟩
      cases c with
      | matching => exact hmix.elim
      | mixed => exact (hdis trivial).elim

-- ──── Complement and agreement properties ────

/-- Dislikes is the complement of likes. -/
theorem dislikes_eq_not_likes (c : DressInt) (w : TimPref) :
    dislikes c w ↔ ¬ likes c w := Iff.rfl

/-- isMatching and isMixed are complements. -/
theorem matching_mixed_compl (c : DressInt) (w : TimPref) :
    isMatching c w ↔ ¬ isMixed c w := by
  cases c
  · exact ⟨fun _ h => h.elim, fun _ => trivial⟩
  · exact ⟨fun h => h.elim, fun h => (h trivial).elim⟩

end SarahsSocks

end Caie2023
