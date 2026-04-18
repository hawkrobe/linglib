import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Semantics.ParameterizedUpdate

/-!
# Disjunctive Context Updating
@cite{caie-2023}

Michael Caie. Context Dynamics. Semantics and Pragmatics 16, Article 3: 1–37.

## The Problem

Standard accounts of conversational updating (@cite{stalnaker-1978}) assume
that, at each world w in the context set, there is a unique compositional
context c_w interpreting an assertion of φ. The context set is updated by
diagonalization: eliminate w iff ⟦φ⟧^{c_w} is false at w.

@cite{caie-2023} argues this uniqueness assumption fails for context-sensitive
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

Disjunctive Updating is an instance of ∃-projection from
`Core.Semantics.ParameterizedUpdate`: the parameter is the compositional
context C, and the fragment set `F c w := I w c` says which contexts are
available at each world. `disjunctiveUpdate` = `existentialUpdate` and
`prune` = `fiberwiseFilter` (both with argument order swapped).

This means general results — De Morgan duality, monotone collapse,
sequential update = single conjunctive update — apply directly.

## Relationship to Existing Infrastructure

- `ContextSet.update c p` in `CommonGround.lean` is the special case where
  every world gets the same interpretation (no context sensitivity).
  See `disjunctiveUpdate_constant`.

- The `SpecSpace` in `Supervaluation/Basic.lean` is the ∀-dual:
  super-truth = true under ALL specs; Caie's survival = true under SOME.

- `CCP` in `Dynamic/Core/CCP.lean` operates on ⟨assignment, world⟩ pairs;
  `ContextFragment` here uses ⟨compositional-context, world⟩ — a structural
  analogue with different conceptual content.
-/

namespace Pragmatics.Assertion.DisjunctiveUpdate

open Core.CommonGround (ContextSet)
open Core.Proposition (Prop')
open Core.Semantics.ParameterizedUpdate


-- ════════════════════════════════════════════════════════════════
-- § 1. Core Types
-- ════════════════════════════════════════════════════════════════

variable {C W : Type*}

/-- A context fragment: an ordered pair ⟨compositional context, world⟩.

Context fragments are the state representation for Disjunctive Updating.
The compositional context determines how context-sensitive expressions
(indexicals, gradable adjectives, configurational predicates) are
interpreted; the world determines matters of fact.

Structurally analogous to `Possibility W E` in `Dynamic/Core/CCP.lean`
(⟨world, assignment⟩ pairs in dynamic semantics), but the non-world
parameter is a compositional context rather than a variable assignment. -/
structure ContextFragment (C W : Type*) where
  ctx : C
  world : W

/-- An interpretation assignment maps worlds to predicates on compositional
    contexts. `I w c` holds iff c is available to interpret an assertion at w.

    @cite{caie-2023}: "for each world w in the relevant context set, a
    non-empty set of compositional contexts that interpret that assertion
    of φ at w: I^φ_w."

    This is a `FragmentSet C W` with swapped argument order:
    `I w c` ↔ `F c w` where `F : FragmentSet C W`. -/
abbrev InterpAssignment (C W : Type*) := W → C → Prop

/-- Convert an `InterpAssignment` to a `FragmentSet` by swapping argument
    order. This is the bridge between Caie's convention (index by world
    first) and the `ParameterizedUpdate` convention (index by parameter
    first). -/
abbrev InterpAssignment.toFragmentSet (I : InterpAssignment C W) :
    FragmentSet C W :=
  λ c w => I w c


-- ════════════════════════════════════════════════════════════════
-- § 2. Standard Updating
-- ════════════════════════════════════════════════════════════════

/-- Standard Updating with explicit diagonalization
    (@cite{stalnaker-1978}, formulated following @cite{caie-2023} §1).

    At each world w, a unique compositional context c_w determines the
    proposition expressed. The diagonal proposition is
    {w ∈ C : w ∈ ⟦φ⟧^{c_w}}.

    Note: `Assertion.Stalnaker.assert` in `Stalnaker.lean` implements the
    degenerate case where the proposition is fixed across worlds (no
    diagonalization needed). This definition makes the compositional
    context parameter explicit. -/
def standardUpdate (cs : Prop' W) (c_w : W → C) (sem : C → W → Prop) : Prop' W :=
  λ w => cs w ∧ sem (c_w w) w


-- ════════════════════════════════════════════════════════════════
-- § 3. Disjunctive Multi-Context Updating
-- ════════════════════════════════════════════════════════════════

/-- Disjunctive Multi-Context Updating (@cite{caie-2023} §3).

    A world w survives iff there exists some compositional context c in the
    interpretation set I_w such that ⟦φ⟧^c is true at w. When I_w is a
    singleton {c_w}, this reduces to `standardUpdate`.

    Defined as `existentialUpdate` from `ParameterizedUpdate` with the
    interpretation assignment as the fragment set (argument order swapped).

    @cite{caie-2023}: "The result of updating the context given the assertion
    is C^φ = {w ∈ C_φ : w ∈ ⟦φ⟧^c, for some c ∈ I^φ_w}." -/
abbrev disjunctiveUpdate (cs : Prop' W) (I : InterpAssignment C W)
    (sem : C → W → Prop) : Prop' W :=
  existentialUpdate cs I.toFragmentSet sem


-- ════════════════════════════════════════════════════════════════
-- § 4. Contextual Pruning
-- ════════════════════════════════════════════════════════════════

/-- Contextual Pruning (@cite{caie-2023} §3): restrict interpretation sets
    to truth-making contexts.

    If β immediately follows α in a discourse at world w, the compositional
    contexts available for β at w are exactly those that made α true at w.

    Defined as `fiberwiseFilter` from `ParameterizedUpdate` (argument order
    swapped).

    @cite{caie-2023}: "if {c : c ∈ I^α_w and w ∈ ⟦α⟧^c} ≠ ∅, then
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

    @cite{caie-2023}: "Call a context fragment an ordered pair of a
    compositional context and a world, and call the fragmentation of C_φ
    the set of context fragments ⟨c, w⟩ such that w ∈ C_φ and c interprets
    φ in w." -/
def fragmentation (cs : Prop' W) (I : InterpAssignment C W) :
    ContextFragment C W → Prop :=
  λ f => cs f.world ∧ I f.world f.ctx

/-- Project fragments to their world components. -/
def fragmentWorlds (frags : ContextFragment C W → Prop) : Prop' W :=
  λ w => ∃ c, frags ⟨c, w⟩

/-- Disjunctive updating is equivalent to updating the fragmentation and
    projecting to worlds. -/
theorem disjunctiveUpdate_eq_fragmentWorlds (cs : Prop' W)
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
theorem standard_eq_disjunctive_singleton (cs : Prop' W)
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
theorem disjunctiveUpdate_mono_interp (cs : Prop' W)
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
theorem disjunctiveUpdate_constant (cs : Prop' W) (c₀ : C)
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
theorem disjunctiveUpdate_eq_contextSet_update (cs : Prop' W) (c₀ : C)
    (sem : C → W → Prop) :
    disjunctiveUpdate cs (λ _ c => c = c₀) sem =
    ContextSet.update cs (sem c₀) := by
  exact disjunctiveUpdate_constant cs c₀ sem


-- ════════════════════════════════════════════════════════════════
-- § 8. Generalized Preservation
-- ════════════════════════════════════════════════════════════════

/-- Generalized Preservation (@cite{caie-2023} §3): if there is a unique
    compositional context interpreting α at w, and it makes α true, then
    it persists as the unique context for subsequent assertions.

    @cite{caie-2023}: "for each w ∈ C_α if there is a unique compositional
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
def discourseStep (cs : Prop' W) (I : InterpAssignment C W)
    (sem : C → W → Prop) : Prop' W × InterpAssignment C W :=
  (disjunctiveUpdate cs I sem, prune I sem)

/-- Sequential discourse steps are monotonically restrictive in both
    the context set and interpretation sets. -/
theorem discourseStep_restricts (cs : Prop' W) (I : InterpAssignment C W)
    (sem : C → W → Prop) :
    let ⟨cs', I'⟩ := discourseStep cs I sem
    (∀ w, cs' w → cs w) ∧ (∀ w c, I' w c → I w c) :=
  ⟨λ w => existentialUpdate_restricts cs I.toFragmentSet sem w,
   λ w c => fiberwiseFilter_sub I.toFragmentSet sem c w⟩

/-- Contextual Pruning reduces to the general sequential ∃-update theorem:
    asserting α then β (with pruned parameters) = single ∃-update checking
    both α and β under the same parameter.

    This is @cite{caie-2023}'s central mechanism, obtained for free from
    `sequential_existentialUpdate` in `ParameterizedUpdate.lean`. -/
theorem contextual_pruning_sequential (cs : Prop' W)
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

/-! ## Sarah's Socks (@cite{caie-2023} §2.1)

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

### Verification Table (from @cite{caie-2023})

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
def likes : DressInt → TimPref → Bool
  | .matching, .likesMatching => true
  | .mixed,    .likesMixed    => true
  | _,         _              => false

/-- "Tim dislikes both of them": complement of `likes`. -/
def dislikes (c : DressInt) (w : TimPref) : Bool := !likes c w

/-- "Both of them are matching": true under matching intension. -/
def isMatching : DressInt → TimPref → Bool
  | .matching, _ => true
  | .mixed,    _ => false

/-- "Both of them are mixed": true under mixed intension. -/
def isMixed : DressInt → TimPref → Bool
  | .mixed,    _ => true
  | .matching, _ => false

-- ──── Discourse composition ────

-- Both discourses share sentence (1), which is uninformative.
-- The initial interpretation set is full: both intensions at every world.
-- Pruning by (1) leaves the interpretation set unchanged.
-- So we start from the full interpretation set and compose (2)+(3) or (4)+(5).

/-- Tim Likes Matching result: w survives iff there exists a context c
    such that `likes c w` (surviving (2)) AND `isMatching c w` (surviving (3)).
    The conjunction arises from Contextual Pruning: only contexts that made
    (2) true are available to interpret (3). -/
def timLikesMatchingResult (w : TimPref) : Bool :=
  -- ∃ c ∈ {matching, mixed}, likes c w ∧ isMatching c w
  (likes .matching w && isMatching .matching w) ||
  (likes .mixed w && isMatching .mixed w)

/-- Tim Dislikes Mixed result: w survives iff ∃ c, dislikes c w ∧ isMixed c w. -/
def timDislikesMixedResult (w : TimPref) : Bool :=
  (dislikes .matching w && isMixed .matching w) ||
  (dislikes .mixed w && isMixed .mixed w)

-- ──── Verification ────

/-- Tim Likes Matching keeps the matching-preference world. -/
theorem tlm_keeps_matching : timLikesMatchingResult .likesMatching = true := rfl

/-- Tim Likes Matching eliminates the mixed-preference world. -/
theorem tlm_eliminates_mixed : timLikesMatchingResult .likesMixed = false := rfl

/-- Tim Dislikes Mixed keeps the matching-preference world. -/
theorem tdm_keeps_matching : timDislikesMixedResult .likesMatching = true := rfl

/-- Tim Dislikes Mixed eliminates the mixed-preference world. -/
theorem tdm_eliminates_mixed : timDislikesMixedResult .likesMixed = false := rfl

/-- Both discourses yield the same result. -/
theorem discourses_agree :
    timLikesMatchingResult = timDislikesMixedResult := by
  funext w; cases w <;> rfl

-- ──── Safe Information ────

/-- The set of fact-worlds: those where Tim likes matching and dislikes mixed. -/
def facts (w : TimPref) : Bool :=
  match w with | .likesMatching => true | .likesMixed => false

/-- Safe Information condition (i): the update result is a subset of
    the fact-worlds. Under Disjunctive Updating, asserting Tim Likes
    Matching eliminates all non-fact worlds. -/
theorem safe_info_i_tlm (w : TimPref) :
    timLikesMatchingResult w = true → facts w = true := by
  cases w <;> simp [timLikesMatchingResult, facts, likes, isMatching]

/-- Safe Information condition (ii): every fact-world where the discourse
    occurs is retained. -/
theorem safe_info_ii_tlm (w : TimPref) :
    facts w = true → timLikesMatchingResult w = true := by
  cases w <;> simp [timLikesMatchingResult, facts, likes, isMatching]

/-- Safe Information condition (i) for Tim Dislikes Mixed. -/
theorem safe_info_i_tdm (w : TimPref) :
    timDislikesMixedResult w = true → facts w = true := by
  cases w <;> simp [timDislikesMixedResult, facts, dislikes, likes, isMixed]

/-- Safe Information condition (ii) for Tim Dislikes Mixed. -/
theorem safe_info_ii_tdm (w : TimPref) :
    facts w = true → timDislikesMixedResult w = true := by
  cases w <;> simp [timDislikesMixedResult, facts, dislikes, likes, isMixed]

-- ──── Negative results: why Standard Updating fails ────

/-- @cite{caie-2023} §2.2, first Claim: Standard Updating + Preservation +
    Minimal Symmetry → ¬Safe Information.

    Under Minimal Symmetry, the same dressing intension c interprets
    sentence (1) in both discourses (at fact-worlds w₁ and w₂ that
    agree on all pre-assertion facts). Under Preservation, c persists
    to interpret later sentences. Safe Information (ii) then requires:
    - `likes c w = true` (for TLM to retain a fact-world)
    - `dislikes c w = true` (for TDM to retain a fact-world)
    But `dislikes = ¬likes`, so no intension c satisfies both.

    This is the paper's central argument against Standard Updating. -/
theorem standard_update_incompatible (c : DressInt) (w : TimPref) :
    ¬(likes c w = true ∧ dislikes c w = true) := by
  cases c <;> cases w <;> decide

/-- @cite{caie-2023} §2.2, second Claim: Standard Updating + Uniform Charity
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
    (∃ c : DressInt, likes c .likesMixed = true) ∧
    (∃ c : DressInt, isMatching c .likesMixed = true) ∧
    facts .likesMixed = false :=
  ⟨⟨.mixed, rfl⟩, ⟨.matching, rfl⟩, rfl⟩

-- ──── Connection to general framework ────

/-- The Bool-valued Tim Likes Matching result agrees with the Prop-valued
    `disjunctiveUpdate` applied via `discourseStep`.

    This connects the hand-computed verification above to the
    general theory. -/
theorem tlm_agrees_with_framework (w : TimPref) :
    timLikesMatchingResult w = true ↔
    (disjunctiveUpdate
      (disjunctiveUpdate (λ _ => True) (λ _ _ => True)
        (λ c w => likes c w = true))
      (prune (λ _ _ => True) (λ c w => likes c w = true))
      (λ c w => isMatching c w = true)) w := by
  cases w with
  | likesMatching =>
    constructor
    · intro _
      exact ⟨⟨trivial, .matching, trivial, rfl⟩,
             .matching, ⟨trivial, rfl⟩, rfl⟩
    · intro _; rfl
  | likesMixed =>
    constructor
    · intro h; simp [timLikesMatchingResult, likes, isMatching] at h
    · intro ⟨_, c, ⟨_, hlikes⟩, hmatch⟩
      cases c with
      | matching => exact absurd hlikes (by decide)
      | mixed => exact absurd hmatch (by decide)

/-- The Bool-valued Tim Dislikes Mixed result agrees with the Prop-valued
    framework. Mirror of `tlm_agrees_with_framework`. -/
theorem tdm_agrees_with_framework (w : TimPref) :
    timDislikesMixedResult w = true ↔
    (disjunctiveUpdate
      (disjunctiveUpdate (λ _ => True) (λ _ _ => True)
        (λ c w => dislikes c w = true))
      (prune (λ _ _ => True) (λ c w => dislikes c w = true))
      (λ c w => isMixed c w = true)) w := by
  cases w with
  | likesMatching =>
    constructor
    · intro _
      exact ⟨⟨trivial, .mixed, trivial, rfl⟩,
             .mixed, ⟨trivial, rfl⟩, rfl⟩
    · intro _; rfl
  | likesMixed =>
    constructor
    · intro h; simp [timDislikesMixedResult, dislikes, likes, isMixed] at h
    · intro ⟨_, c, ⟨_, hdis⟩, hmix⟩
      cases c with
      | matching => exact absurd hmix (by decide)
      | mixed => exact absurd hdis (by decide)

-- ──── Complement and agreement properties ────

/-- Dislikes is the complement of likes. -/
theorem dislikes_eq_not_likes (c : DressInt) (w : TimPref) :
    dislikes c w = !likes c w := rfl

/-- isMatching and isMixed are complements. -/
theorem matching_mixed_compl (c : DressInt) (w : TimPref) :
    isMatching c w = !isMixed c w := by
  cases c <;> rfl

end SarahsSocks

end Pragmatics.Assertion.DisjunctiveUpdate
