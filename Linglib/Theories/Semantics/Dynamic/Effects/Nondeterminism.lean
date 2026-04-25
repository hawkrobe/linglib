import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Connectives.CCP

/-!
# Nondeterminism Effect: Plural / Choice Alternatives
@cite{charlow-2019} @cite{charlow-2021} @cite{muskens-1996}

The nondeterminism effect models indefinites as introducing sets of alternatives
rather than single values. This underlies:
- Indefinites as choice functions
- Plural / cumulative readings
- Set-valued update (pointwise lifting)

The key type is `Set α` (or `List α` for computational purposes) — meanings
are sets of possible values rather than single values.

This file consolidates two former modules:
- `NDMeaning` (Set monad on meanings) — was `Dynamic/Nondeterminism/Basic.lean`
- `liftPW` / `lowerPW` (Charlow's ↑ / ↓ pointwise/collectivized bridge) —
  was `Dynamic/Nondeterminism/PointwiseUpdate.lean`

The companion paper-level study (Charlow 2019's `StateCCP`, distributivity,
destructive-update theorems) lives in `Dynamic/Nondeterminism/Charlow2019.lean`
pending Phase 4e of the discourse restructure (where it migrates to
`Phenomena/Anaphora/Studies/Charlow2019.lean`).
-/

-- ════════════════════════════════════════════════════════════════
-- § 1. Set-Monad Meanings (NDMeaning)
-- ════════════════════════════════════════════════════════════════

namespace Semantics.Dynamic.Nondeterminism

open Semantics.Dynamic.Core

/--
A nondeterministic meaning: produces a set of possible outputs.

This is the semantic type for indefinites — "a man" denotes the set
of all men, and the nondeterminism effect handles choice.
-/
def NDMeaning (α : Type*) (β : Type*) := α → Set β

/--
Bind for the nondeterminism monad (Set).

Sequencing nondeterministic computations: for each possible value from
the first computation, run the second and collect all results.
-/
def NDMeaning.bind {α β γ : Type*} (m : NDMeaning α β) (f : β → Set γ) : NDMeaning α γ :=
  λ a => { c | ∃ b ∈ m a, c ∈ f b }

/--
Pure / return for nondeterminism: a single deterministic value.
-/
def NDMeaning.pure {α β : Type*} (b : β) : NDMeaning α β :=
  λ _ => {b}

/--
Alternative / choice: union of two nondeterministic meanings.
-/
def NDMeaning.alt {α β : Type*} (m₁ m₂ : NDMeaning α β) : NDMeaning α β :=
  λ a => m₁ a ∪ m₂ a

/--
Maximization: select maximal elements from a nondeterministic meaning
with respect to some ordering. Used for cumulative readings.
-/
def NDMeaning.maximize {α β : Type*} (m : NDMeaning α β) (better : β → β → Prop) : NDMeaning α β :=
  λ a => { b ∈ m a | ∀ b' ∈ m a, ¬better b b' }

end Semantics.Dynamic.Nondeterminism

-- ════════════════════════════════════════════════════════════════
-- § 2. Pointwise ↔ Update-Theoretic Bridge (Charlow's ↑ / ↓)
-- ════════════════════════════════════════════════════════════════

/-!
Connects the pointwise `DRS S := S → S → Prop` type (Dynamic Ty2, @cite{muskens-1996})
to the update-theoretic `StateCCP W E := State W E → State W E` type.

The key operations are @cite{charlow-2021}'s ↑ (lift) and ↓ (lower):
- `liftPW`: promotes a pointwise DRS to a context-level update
- `lowerPW`: extracts a pointwise relation from a context update

The central result: `liftPW D` is always distributive,
meaning pointwise meanings can never produce irreducibly context-level effects.
Cumulative readings require non-distributive M_v, which lives only in `StateCCP`.
-/

namespace Semantics.Dynamic.Core.PointwiseUpdate

open Semantics.Dynamic.Core

variable {W E : Type*}

/-- Charlow's ↑ (equation 76): lift a pointwise DRS to an update on states.
    `liftPW D s = {⟨w, h⟩ | ∃ ⟨w, g⟩ ∈ s, D g h}`
    Each world-assignment pair in the output comes from applying D to some
    input assignment in s, preserving the world. -/
def liftPW (D : DRS (Assignment E)) : StateCCP W E :=
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ D q.2 p.2}

/-- Charlow's ↓ (equation 77): extract a pointwise DRS from a state update.
    Evaluates K on a singleton context at an arbitrary world. -/
def lowerPW (K : StateCCP W E) (w₀ : W) : DRS (Assignment E) :=
  λ g h => (w₀, h) ∈ K {(w₀, g)}

/-- Round-trip identity: lowering a lifted DRS recovers the original.

    `↓(↑D) = D` because the singleton context `{(w₀, g)}` passes through ↑
    with only `(w₀, g)` as witness, leaving exactly the pairs `h` with `D g h`. -/
theorem lowerPW_liftPW (D : DRS (Assignment E)) (w₀ : W) :
    lowerPW (liftPW D) w₀ = D := by
  ext g h
  constructor
  · intro hm
    show D g h
    simp only [lowerPW, liftPW, Set.mem_setOf_eq] at hm
    obtain ⟨q, hq, h1, h2⟩ := hm
    cases hq; exact h2
  · intro hD
    show (w₀, h) ∈ liftPW D {(w₀, g)}
    simp only [liftPW, Set.mem_setOf_eq]
    exact ⟨(w₀, g), rfl, rfl, hD⟩

/-- ↑ is injective: distinct DRSs yield distinct state updates.

    Follows from the round-trip: `D = ↓(↑D)`, so `↑D₁ = ↑D₂` implies
    `D₁ = ↓(↑D₁) = ↓(↑D₂) = D₂`. Requires `W` to be nonempty for the
    lowering witness world. -/
theorem liftPW_injective [Nonempty W] (D₁ D₂ : DRS (Assignment E))
    (h : liftPW (W := W) D₁ = liftPW D₂) :
    D₁ = D₂ := by
  have w₀ : W := Classical.arbitrary W
  calc D₁ = lowerPW (liftPW D₁) w₀ := (lowerPW_liftPW D₁ w₀).symm
    _ = lowerPW (liftPW D₂) w₀ := by rw [h]
    _ = D₂ := lowerPW_liftPW D₂ w₀

/-- Lifted pointwise DRSs are always distributive (@cite{charlow-2021}, §6, key lemma).

    `↑D` processes each element of the input state independently — the output
    at `p` depends only on whether some `q ∈ s` satisfies `D q.2 p.2` with
    matching world `p.1 = q.1`. This is exactly the singleton decomposition
    `(↑D)(s) = ⋃_{i∈s} (↑D)({i})`, which is the definition of distributivity. -/
theorem liftPW_preserves_distributive (D : DRS (Assignment E)) :
    IsDistributive (liftPW (W := W) D) := by
  intro s; ext p
  constructor
  · intro hp
    simp only [liftPW, Set.mem_setOf_eq] at hp
    obtain ⟨q, hq, h1, h2⟩ := hp
    exact ⟨q, hq, by simp only [liftPW, Set.mem_setOf_eq]; exact ⟨q, rfl, h1, h2⟩⟩
  · rintro ⟨i, hi, hp⟩
    simp only [liftPW, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨q, hq, h1, h2⟩ := hp
    cases hq; exact ⟨i, hi, h1, h2⟩

/-- ↑↓ ≠ id: there exist irreducibly update-theoretic meanings K such that
    liftPW (lowerPW K w₀) ≠ K.

    The simplest witness is `K _ = {(w₀, g₀)}` (constant function ignoring
    input). Then `K ∅ = {(w₀, g₀)}`, but `liftPW (lowerPW K w₀) ∅ = ∅`
    because ↑ has no input pairs to draw.

    Requires `Nonempty W` and `Nonempty E` to construct the witness. -/
theorem liftPW_lowerPW_not_id [Nonempty W] [Nonempty E] :
    ∃ (K : StateCCP W E) (w₀ : W), liftPW (lowerPW K w₀) ≠ K := by
  let w₀ : W := Classical.arbitrary W
  let g₀ : Assignment E := λ _ => Classical.arbitrary E
  let K : StateCCP W E := λ _ => {(w₀, g₀)}
  use K, w₀
  intro heq
  -- liftPW (lowerPW K w₀) ∅ = ∅ (no input pairs to draw from)
  have h₁ : liftPW (lowerPW K w₀) ∅ = (∅ : State W E) := by
    ext p; simp only [liftPW, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨q, hq, _, _⟩; exact hq
  -- But K ∅ = {(w₀, g₀)} ≠ ∅
  have h₂ : K ∅ = ({(w₀, g₀)} : State W E) := rfl
  rw [heq] at h₁
  rw [h₂] at h₁
  -- h₁ : {(w₀, g₀)} = ∅, but singletons are nonempty
  have : (w₀, g₀) ∈ ({(w₀, g₀)} : State W E) := rfl
  rw [h₁] at this
  exact this

end Semantics.Dynamic.Core.PointwiseUpdate
