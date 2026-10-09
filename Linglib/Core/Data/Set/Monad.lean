/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Functor

/-!
# The set monad under the state and reader transformers

Membership in the computations of `StateT σ Set` and `ReaderT σ Set`, with `Set.monad` as the
monad: a computation run at an input is a set of results, and `pure`, `<$>`, `>>=` and `<*>`
act on it as singleton, image, indexed union and pointwise application. The statements are
about the local instance `Set.monad`, so they apply wherever a file enables it.

## Main results

* `Set.mem_stateT_bind`, `Set.mem_stateT_map`, `Set.mem_stateT_pure`, `Set.mem_stateT_seq`:
  results of `StateT σ Set` computations.
* `Set.mem_readerT_bind`, `Set.mem_readerT_map`, `Set.mem_readerT_pure`: results of
  `ReaderT σ Set` computations.
-/

@[expose] public section

attribute [local instance] Set.monad

universe u

namespace Set

/-! ### `StateT σ Set` -/

section StateT

variable {σ α β : Type u}

@[simp] theorem mem_stateT_bind (m : StateT σ Set α) (f : α → StateT σ Set β) (s : σ)
    (r : β × σ) : r ∈ (m >>= f) s ↔ ∃ q ∈ m s, r ∈ f q.1 q.2 := by
  show r ∈ StateT.bind m f s ↔ _
  simp [StateT.bind, Set.bind_def]

@[simp] theorem mem_stateT_map (f : α → β) (m : StateT σ Set α) (s : σ) (r : β × σ) :
    r ∈ (f <$> m) s ↔ ∃ q ∈ m s, r = (f q.1, q.2) := by
  simp only [← bind_pure_comp, mem_stateT_bind]; rfl

@[simp] theorem mem_stateT_pure (a : α) (s : σ) (r : α × σ) :
    r ∈ (pure a : StateT σ Set α) s ↔ r = (a, s) := Iff.rfl

@[simp] theorem mem_stateT_seq (m : StateT σ Set (α → β)) (n : StateT σ Set α) (s : σ)
    (r : β × σ) : r ∈ (m <*> n) s ↔ ∃ q ∈ m s, ∃ q' ∈ n q.2, r = (q.1 q'.1, q'.2) := by
  simp only [seq_eq_bind_map, mem_stateT_bind, mem_stateT_map]

end StateT

/-! ### `ReaderT σ Set` -/

section ReaderT

variable {σ α β : Type u}

@[simp] theorem mem_readerT_bind (m : ReaderT σ Set α) (f : α → ReaderT σ Set β) (s : σ)
    (r : β) : r ∈ (m >>= f) s ↔ ∃ x ∈ m s, r ∈ f x s := by
  show r ∈ ReaderT.bind m f s ↔ _
  simp [ReaderT.bind, Set.bind_def]

@[simp] theorem mem_readerT_map (f : α → β) (m : ReaderT σ Set α) (s : σ) (r : β) :
    r ∈ (f <$> m) s ↔ ∃ x ∈ m s, r = f x := by
  simp only [← bind_pure_comp, mem_readerT_bind]; rfl

@[simp] theorem mem_readerT_pure (a : α) (s : σ) (r : α) :
    r ∈ (pure a : ReaderT σ Set α) s ↔ r = a := Iff.rfl

end ReaderT

end Set
