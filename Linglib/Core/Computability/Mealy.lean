/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs
import Linglib.Core.Data.List.Fold

/-!
# Mealy machines

A Mealy machine [mealy-1955] is a deterministic transducer which reads its input left to
right and emits exactly one output symbol per input symbol, so the function it computes
is length-preserving by construction. Output coordinate `i` of the run is the step
output at the state reached after the length-`i` input prefix (`Mealy.getElem?_run`),
so the output is prefix-determined at every coordinate.

Note that this definition allows for machines with infinite states; a `Fintype`
instance must be supplied for true finite-state machines.

## Main definitions

* `Mealy σ α β`: transducer with states `σ`, input alphabet `α`, output alphabet `β`
* `Mealy.run`, `Mealy.runRight`: the left-to-right and right-to-left passes
* `Mealy.ofFlag`: the one-bit machine tracking whether an earlier symbol satisfies `p`
* `Mealy.reindex`: lifts an equivalence on states to an equivalence on machines

## Main theorems

* `Mealy.getElem?_run`: output coordinate `i` is the step output at the state reached
  after the length-`i` input prefix
* `Mealy.getElem?_ofFlag_run`, `Mealy.getElem?_ofFlag_runRight`: each coordinate of a
  flag machine sees the flag over its strict prefix (its strict suffix, for the
  right-to-left pass)

[UPSTREAM] candidate: `Mathlib.Computability.Mealy`.
-/

namespace Subregular

variable {σ α β : Type*}

/-- A Mealy machine is a set of states (`σ`), a starting state (`initial`) and a
transition function from a state and an input symbol to the successor state and one
output symbol (`step`); it is synchronous, emitting exactly one output symbol per
input symbol. -/
structure Mealy (σ α β : Type*) where
  /-- Starting state. -/
  initial : σ
  /-- Transition function from a state and an input symbol to the successor state and
  the emitted output symbol. -/
  step : σ → α → σ × β

namespace Mealy

variable (T : Mealy σ α β)

/-- `T.stateAfter s x` is the state reached from `s` after consuming the input `x`. -/
def stateAfter (s : σ) : List α → σ :=
  List.foldl (fun s x => (T.step s x).1) s

/-- `T.runFrom s x` runs `T` on the input `x` starting from the state `s`, emitting one
output symbol per input symbol. -/
def runFrom : σ → List α → List β
  | _, [] => []
  | s, x :: xs => (T.step s x).2 :: runFrom (T.step s x).1 xs

/-- `T.run x` runs `T` on the input `x` starting from the state `T.initial`. -/
def run : List α → List β := T.runFrom T.initial

/-- `T.runRight x` runs `T` right-to-left: reverse the input, run, reverse the
output. -/
def runRight (xs : List α) : List β := (T.run xs.reverse).reverse

@[simp] theorem runFrom_nil (s : σ) : T.runFrom s [] = [] := rfl
@[simp] theorem runFrom_cons (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = (T.step s x).2 :: T.runFrom (T.step s x).1 xs := rfl
@[simp] theorem stateAfter_nil (s : σ) : T.stateAfter s [] = s := rfl
@[simp] theorem stateAfter_cons (s : σ) (x : α) (xs : List α) :
    T.stateAfter s (x :: xs) = T.stateAfter (T.step s x).1 xs := rfl

theorem stateAfter_append (s : σ) (xs ys : List α) :
    T.stateAfter s (xs ++ ys) = T.stateAfter (T.stateAfter s xs) ys :=
  List.foldl_append

theorem runFrom_append (s : σ) (xs ys : List α) :
    T.runFrom s (xs ++ ys) = T.runFrom s xs ++ T.runFrom (T.stateAfter s xs) ys := by
  induction xs generalizing s <;> simp [*]

/-- The run is length-preserving (one output symbol per input symbol). -/
@[simp] theorem length_runFrom (s : σ) (xs : List α) :
    (T.runFrom s xs).length = xs.length := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem length_run (xs : List α) :
    (T.run xs).length = xs.length := T.length_runFrom T.initial xs

@[simp] theorem length_runRight (xs : List α) :
    (T.runRight xs).length = xs.length := by simp [runRight]

@[simp] theorem runRight_reverse (xs : List α) :
    T.runRight xs.reverse = (T.run xs).reverse := by simp [runRight]

@[simp] theorem runRight_nil : T.runRight [] = [] := rfl

/-- The right-to-left pass emits the head output at the state reached over the entire
reversed tail: the right scan reads the future. -/
@[simp] theorem runRight_cons (x : α) (xs : List α) :
    T.runRight (x :: xs)
      = (T.step (T.stateAfter T.initial xs.reverse) x).2 :: T.runRight xs := by
  simp [runRight, run, runFrom_append]

/-- Output coordinate `i` of the run is the step output at the state reached after the
first `i` input symbols. -/
theorem getElem?_runFrom (s : σ) (xs : List α) (i : ℕ) :
    (T.runFrom s xs)[i]? = xs[i]?.map fun x => (T.step (T.stateAfter s (xs.take i)) x).2 := by
  induction xs generalizing s i <;> cases i <;> simp [*]

/-- Output coordinate `i` of `T.run` is the step output at the state reached after the
first `i` input symbols. -/
theorem getElem?_run (xs : List α) (i : ℕ) :
    (T.run xs)[i]? = xs[i]?.map fun x => (T.step (T.stateAfter T.initial (xs.take i)) x).2 :=
  T.getElem?_runFrom T.initial xs i

/-! ### Flag machines

The recurring one-sided-trigger shape: the state is the one-bit "some earlier symbol
satisfies `p`" flag, so `stateAfter` computes `List.any` and each output cell sees the
flag over its strict prefix. Under the right-to-left pass `runRight`, the cell sees the
flag over its strict suffix (`getElem?_ofFlag_runRight`). -/

variable (p : α → Bool) (out : Bool → α → β)

/-- The Mealy machine whose state is the monotone flag "a symbol satisfying `p` has
occurred". -/
def ofFlag : Mealy Bool α β where
  initial := false
  step b a := (b || p a, out b a)

@[simp] theorem ofFlag_initial : (ofFlag p out).initial = false := rfl

@[simp] theorem ofFlag_step (b : Bool) (a : α) :
    (ofFlag p out).step b a = (b || p a, out b a) := rfl

@[simp] theorem ofFlag_stateAfter (b : Bool) (xs : List α) :
    (ofFlag p out).stateAfter b xs = (b || xs.any p) := by
  simp [stateAfter, List.foldl_or]

/-- Each coordinate of a flag machine sees the flag over its strict prefix. -/
theorem getElem?_ofFlag_run (xs : List α) (i : ℕ) :
    ((ofFlag p out).run xs)[i]? = xs[i]?.map fun a => out ((xs.take i).any p) a := by
  simp [getElem?_run]

/-- Each coordinate of a flag machine run right-to-left sees the flag over its strict
suffix. -/
theorem getElem?_ofFlag_runRight (xs : List α) (i : ℕ) :
    ((ofFlag p out).runRight xs)[i]? = xs[i]?.map fun a => out ((xs.drop (i + 1)).any p) a := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [*]

/-! ### Reindexing states -/

variable {τ : Type*}

/-- Lifts an equivalence on states to an equivalence on Mealy machines. -/
@[simps apply_initial apply_step]
def reindex (g : σ ≃ τ) : Mealy σ α β ≃ Mealy τ α β where
  toFun T := {
    initial := g T.initial
    step := fun t x => (g (T.step (g.symm t) x).1, (T.step (g.symm t) x).2)
  }
  invFun T := {
    initial := g.symm T.initial
    step := fun s x => (g.symm (T.step (g s) x).1, (T.step (g s) x).2)
  }
  left_inv T := by simp
  right_inv T := by simp

@[simp] theorem reindex_refl : reindex (Equiv.refl σ) T = T := rfl

@[simp] theorem symm_reindex (g : σ ≃ τ) :
    (reindex (α := α) (β := β) g).symm = reindex g.symm := rfl

@[simp] theorem stateAfter_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).stateAfter t xs = g (T.stateAfter (g.symm t) xs) := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem runFrom_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  induction xs generalizing t <;> simp [*]

/-- The reindexed machine computes the same string function. -/
@[simp] theorem run_reindex (g : σ ≃ τ) : (reindex g T).run = T.run := by
  funext xs; simp [run]

end Mealy

end Subregular
