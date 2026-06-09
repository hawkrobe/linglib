import Mathlib.Order.Monotone.Basic
import Linglib.Core.Logic.Intensional.Frame

/-!
# Situations: Partial Indices

[kratzer-1989] [barwise-perry-1983]

A situation is a *partial* point of evaluation. Where possible-worlds
semantics evaluates propositions at total worlds, situation semantics
evaluates them at situations equipped with a parthood preorder `s ≤ s'`
("s is a part of s'"). Worlds are recovered as the *maximal* situations.

This module provides the Core-level abstraction. The premise primitives
in `Premise.lean` are already polymorphic over an abstract `Index`; this
file simply refines that index to one carrying a partial order, and gives
the parthood structure a name.

## Why this is just an order, and lives in Core

Kratzer's situation semantics has many moving parts (lumping, accidental
generalizations, persistence-respecting modal bases, ...) but the
*foundation* is tiny: a partial order on indices. Persistence is then
literally `Monotone : (S → Prop) → Prop` from mathlib. Possible-worlds
semantics is the special case where `≤` is the discrete order
(`s ≤ s' ↔ s = s'`), so every index is maximal.

Putting the abstraction in `Core/Logic/Intensional/` lets all higher
modules opt in by adding `[PartialOrder Index]`, without forcing a
choice of "worlds vs. situations" in the index type.

## Key definitions

- `SituationFrame` — entity/index types whose `Index` carries a partial order
- `Persistent p` — a proposition is true at `s'` whenever it is true
  at any `s ≤ s'` (= mathlib's `Monotone`)
- `IsWorld s` — `s` is maximal under `≤`
- `discreteSituationFrame E W` — a situation frame on `E`/`W` with the
  discrete order, where every index is a world (PWS reduct)

## What lives elsewhere

The relation **lumping** between propositions and the distinction
between accidental and non-accidental generalizations belong in
`Core/Logic/Intensional/Lumping.lean`; those are theory-laden and
depend on a chosen modal base. This file keeps only the order-theoretic
core.
-/

namespace Core.Logic.Intensional

/-! ## Situation frames -/

/-- A **situation frame** carries an entity domain and an index set whose
    indices are equipped with a partial order (parthood). Worlds are the
    maximal elements; truly possible-worlds-style frames arise from the
    discrete order. -/
structure SituationFrame where
  /-- The domain of individuals. -/
  Entity : Type
  /-- The index set (situations). -/
  Index : Type
  /-- The parthood preorder on indices. -/
  [order : PartialOrder Index]

attribute [instance] SituationFrame.order

/-- Denotation domains for a situation frame, computed from its entity and
    index types. -/
abbrev SituationFrame.Denot (F : SituationFrame) : Ty → Type :=
  _root_.Core.Logic.Intensional.Denot F.Entity F.Index

/-- `s ≤ s'` — `s` is a part of `s'` (situation parthood). -/
infixl:50 " ≼ " => fun (s s' : _) => s ≤ s'

/-! ## Persistence -/

/-- A proposition is **persistent** iff it is monotone in parthood:
    truth at `s` carries up to any `s' ≽ s`.

    This is precisely mathlib's `Monotone`; the abbreviation exists so
    that linguistic prose (`Persistent p`) and order-theoretic prose
    (`Monotone p`) are the same theorem. -/
abbrev Persistent {S : Type*} [Preorder S] (p : S → Prop) : Prop := Monotone p

/-- Conjunction of persistent propositions is persistent. -/
theorem Persistent.and {S : Type*} [Preorder S] {p q : S → Prop}
    (hp : Persistent p) (hq : Persistent q) : Persistent (fun s => p s ∧ q s) :=
  fun _ _ h ⟨hps, hqs⟩ => ⟨hp h hps, hq h hqs⟩

/-- Disjunction of persistent propositions is persistent. -/
theorem Persistent.or {S : Type*} [Preorder S] {p q : S → Prop}
    (hp : Persistent p) (hq : Persistent q) : Persistent (fun s => p s ∨ q s) :=
  fun _ _ h hs => hs.imp (hp h) (hq h)

/-- The `True` proposition is persistent. -/
theorem Persistent.const_true {S : Type*} [Preorder S] :
    Persistent (fun _ : S => True) := fun _ _ _ _ => trivial

/-! ## Worlds as maximal situations -/

/-- A situation is a **world** (in Kratzer's sense) iff it is maximal
    under parthood: nothing properly extends it. -/
def IsWorld {S : Type*} [Preorder S] (s : S) : Prop :=
  ∀ s', s ≤ s' → s' ≤ s

/-- The collection of worlds in a situation frame: the maximal indices. -/
def SituationFrame.Worlds (F : SituationFrame) : Set F.Index :=
  { s | IsWorld s }

/-! ## Possible-worlds semantics as the discrete special case

The discrete partial order on a type makes `s ≤ s'` equivalent to
`s = s'`. In that order every element is maximal, so every situation
is a world — and `Persistent p` reduces to "no constraint at all."
This is the formal sense in which possible-worlds semantics is the
degenerate case of situation semantics. -/

/-- The discrete partial order on any type: `s ≤ s' ↔ s = s'`.
    Marked `@[reducible]` so that the `≤` from this instance reduces
    definitionally to `Eq` for downstream proofs. -/
@[reducible] def discreteOrder (X : Type*) : PartialOrder X where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

/-- Build a situation frame from entity and index types using the discrete
    order on the index set. This is the formal witness that PWS is a special
    case of situation semantics. -/
def discreteSituationFrame (E W : Type) : SituationFrame where
  Entity := E
  Index := W
  order := discreteOrder W

section DiscreteCorollaries
variable (W : Type)

/-- Bring the discrete partial order on `W` into scope as an instance
    so the corollaries below can quantify over it without explicit `@`. -/
local instance : PartialOrder W := discreteOrder W

/-- Under the discrete order, every element of a discrete situation frame
    is maximal — i.e., a world. -/
theorem discrete_isWorld_all (s : W) : IsWorld s :=
  fun _ h => h.symm.le

/-- Under the discrete order on a frame, every proposition `p : W → Prop`
    is automatically persistent: there's nothing to commute past. -/
theorem discrete_persistent_all (p : W → Prop) : Persistent p :=
  fun _ _ h hp => h ▸ hp

end DiscreteCorollaries

end Core.Logic.Intensional
