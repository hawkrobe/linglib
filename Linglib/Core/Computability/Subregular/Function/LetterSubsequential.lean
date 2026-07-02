/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# Synchronous (letter) left-subsequential functions

A `Mealy` machine is a deterministic left-to-right transducer emitting exactly one
output symbol per input symbol — the synchronous case, length-preserving by
construction. Its output coordinate `i` is a function of the input prefix `[0..i]`, so
the class is cleanly characterised by the `OutputDependsOn` footprint
(`SideDeterminacy.lean`): `IsLetterLeftSubsequential f → ∀ i, LeftDetermined f i`, hence
right-myopic.

This is the characterisation the *block* `IsLeftSubsequential` (`Subsequential.lean`)
lacks: a length-preserving block transducer can delay output (emit `[]` then `[x,y]`),
so output coordinate `0` depends on input position `1` — not prefix-determined. The
synchronous restriction is what makes the dependency-footprint view line up with the
machine view.

## Main definitions

* `Mealy` — synchronous one-symbol-per-step transducer; `run` is length-preserving.
* `IsLetterLeftSubsequential` — computed by a finite-state `Mealy`.

## Main results

* `Mealy.runFrom_getElem?` — output `i` is `(step (state-after-prefix) (input i)).2`.
* `IsLetterLeftSubsequential.leftDetermined` / `.isRightMyopic` — synchronous
  left-subsequential maps are prefix-determined, hence right-myopic.

## Todo

* The Myhill–Nerode *converse*: `(∀ i, LeftDetermined f i) ∧ finite prefix-congruence ⟹
  IsLetterLeftSubsequential f` (build the transducer from the prefix-congruence quotient).
-/

namespace Subregular

variable {σ α β : Type*}

/-- A synchronous letter-to-letter left-to-right transducer: exactly one output symbol
per input symbol (length-preserving by construction). -/
structure Mealy (σ α β : Type*) where
  initial : σ
  step : σ → α → σ × β

namespace Mealy

/-- State reached after consuming a prefix. -/
def stateAfter (T : Mealy σ α β) : σ → List α → σ
  | s, [] => s
  | s, x :: xs => T.stateAfter (T.step s x).1 xs

/-- Run from a state: one output symbol per input symbol. -/
def runFrom (T : Mealy σ α β) : σ → List α → List β
  | _, [] => []
  | s, x :: xs => (T.step s x).2 :: T.runFrom (T.step s x).1 xs

/-- Run from the initial state. -/
def run (T : Mealy σ α β) : List α → List β := T.runFrom T.initial

@[simp] theorem runFrom_nil (T : Mealy σ α β) (s : σ) : T.runFrom s [] = [] := rfl
@[simp] theorem runFrom_cons (T : Mealy σ α β) (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = (T.step s x).2 :: T.runFrom (T.step s x).1 xs := rfl
@[simp] theorem stateAfter_nil (T : Mealy σ α β) (s : σ) : T.stateAfter s [] = s := rfl
@[simp] theorem stateAfter_cons (T : Mealy σ α β) (s : σ) (x : α) (xs : List α) :
    T.stateAfter s (x :: xs) = T.stateAfter (T.step s x).1 xs := rfl

/-- The run is length-preserving (one output symbol per input symbol). -/
theorem runFrom_length (T : Mealy σ α β) (s : σ) (xs : List α) :
    (T.runFrom s xs).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem run_length (T : Mealy σ α β) (xs : List α) :
    (T.run xs).length = xs.length := T.runFrom_length T.initial xs

/-- **The coordinate characterization**: output `i` is the step output at
`(state after the prefix [0..i-1], input i)`. -/
theorem runFrom_getElem? (T : Mealy σ α β) (s : σ) (xs : List α) (i : ℕ) :
    (T.runFrom s xs)[i]?
      = (xs[i]?).map (fun x => (T.step (T.stateAfter s (xs.take i)) x).2) := by
  induction xs generalizing s i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ j => simp [ih, List.take_succ_cons]

/-! ### Flag machines

The recurring one-sided-trigger shape (the `Mealy` counterpart of `Bimachine.ofFlags`):
the state is the one-bit "some earlier symbol satisfies `p`" flag, so `stateAfter`
computes `List.any` and each output cell sees the flag over its strict prefix. Scanned
right-to-left (reverse, run, reverse), the cell sees the flag over its strict suffix
(`ofFlag_run_reverse_getElem?`). -/

/-- The Mealy machine whose state is the monotone flag "a symbol satisfying `p` has
occurred". -/
def ofFlag (p : α → Bool) (out : Bool → α → β) : Mealy Bool α β where
  initial := false
  step b a := (b || p a, out b a)

@[simp] theorem ofFlag_stateAfter (p : α → Bool) (out : Bool → α → β) (b : Bool)
    (xs : List α) : (ofFlag p out).stateAfter b xs = (b || xs.any p) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [stateAfter_cons, show ((ofFlag p out).step b x).1 = (b || p x) from rfl, ih]
    simp [Bool.or_assoc]

theorem ofFlag_run_getElem? (p : α → Bool) (out : Bool → α → β) (xs : List α) (i : ℕ) :
    ((ofFlag p out).run xs)[i]? = xs[i]?.map fun a => out ((xs.take i).any p) a := by
  rw [show (ofFlag p out).run xs = (ofFlag p out).runFrom (ofFlag p out).initial xs from rfl,
    runFrom_getElem?]
  cases xs[i]? with
  | none => rfl
  | some a =>
    rw [ofFlag_stateAfter, show (ofFlag p out).initial = false from rfl, Bool.false_or]
    rfl

/-- Coordinates of a flag machine scanned right-to-left: cell `i` sees the flag over its
strict suffix. -/
theorem ofFlag_run_reverse_getElem? (p : α → Bool) (out : Bool → α → β) (xs : List α)
    (i : ℕ) :
    (((ofFlag p out).run xs.reverse).reverse)[i]?
      = xs[i]?.map fun a => out ((xs.drop (i + 1)).any p) a := by
  by_cases hi : i < xs.length
  · rw [List.getElem?_reverse (by rw [(ofFlag p out).run_length]; simpa using hi),
      (ofFlag p out).run_length, List.length_reverse, ofFlag_run_getElem?,
      List.getElem?_reverse (by omega),
      show xs.length - 1 - (xs.length - 1 - i) = i from by omega,
      List.take_reverse, show xs.length - (xs.length - 1 - i) = i + 1 from by omega,
      List.any_reverse]
  · rw [List.getElem?_eq_none
        (by rw [List.length_reverse, (ofFlag p out).run_length, List.length_reverse]; omega),
      List.getElem?_eq_none (le_of_not_gt hi), Option.map_none]

/-- Transfer a `Mealy` along a state-space equivalence `σ ≃ τ`, preserving `run`.
Mirrors `SFST.transferEquiv`; the use case is bringing a `Type*` finite state down to
`Fin (Fintype.card σ) : Type 0` so a universe-polymorphic machine can witness the
`Type 0`-state existential of `IsLetterLeftSubsequential`. -/
def transferEquiv {τ : Type*} (T : Mealy σ α β) (e : σ ≃ τ) : Mealy τ α β where
  initial := e T.initial
  step t x := (e (T.step (e.symm t) x).1, (T.step (e.symm t) x).2)

theorem transferEquiv_runFrom {τ : Type*} (T : Mealy σ α β) (e : σ ≃ τ)
    (s : σ) (xs : List α) :
    (T.transferEquiv e).runFrom (e s) xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    show (T.step (e.symm (e s)) x).2
            :: (T.transferEquiv e).runFrom (e (T.step (e.symm (e s)) x).1) xs
         = (T.step s x).2 :: T.runFrom (T.step s x).1 xs
    rw [e.symm_apply_apply, ih]

/-- The transferred machine computes the same string function. -/
@[simp] theorem transferEquiv_run {τ : Type*} (T : Mealy σ α β) (e : σ ≃ τ) :
    (T.transferEquiv e).run = T.run := by
  funext xs; exact T.transferEquiv_runFrom e T.initial xs

end Mealy

/-- The synchronous left-subsequential class: computed by a finite-state `Mealy`. -/
def IsLetterLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : Mealy σ α β), T.run = f

/-- **Constructor lemma**: every finite-state `Mealy` witnesses
`IsLetterLeftSubsequential` for its `run`. The state `σ` is accepted at arbitrary
`Type*` and brought down to `Fin (Fintype.card σ) : Type 0` via `transferEquiv` and
`Fintype.equivFin`, so bounded-window ISL/OSL states at the alphabet's universe can
witness the predicate (mirrors `SFST.isLeftSubsequential`). -/
theorem Mealy.isLetterLeftSubsequential {σ : Type*} [Fintype σ] {α β : Type*}
    (T : Mealy σ α β) : IsLetterLeftSubsequential T.run :=
  ⟨Fin (Fintype.card σ), inferInstance, T.transferEquiv (Fintype.equivFin σ),
   T.transferEquiv_run _⟩

/-- **Forward footprint bridge.** A letter-left-subsequential map is left-determined at
every coordinate — output `i` depends only on the prefix `{k | k ≤ i}`. (The *block*
`IsLeftSubsequential` lacks this, by delayed output.) -/
theorem IsLetterLeftSubsequential.leftDetermined {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  intro u v hlen hag
  have hi : u[i]? = v[i]? := hag i (by simp)
  have htake : u.take i = v.take i :=
    take_eq_of_agree fun k hk => hag k (by simp only [Set.mem_setOf_eq]; omega)
  show (T.runFrom T.initial u)[i]? = (T.runFrom T.initial v)[i]?
  rw [Mealy.runFrom_getElem? T T.initial u i,
      Mealy.runFrom_getElem? T T.initial v i, hi, htake]

/-- A synchronous left-subsequential map is **right-myopic** — it has no look-ahead. -/
theorem IsLetterLeftSubsequential.isRightMyopic {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) : IsMyopicTowards f .right :=
  IsMyopicTowards.right_of_leftDetermined hf.leftDetermined

/-! ### Myhill–Nerode converse

`f` is letter-left-subsequential as soon as it admits a *finite-state, left-congruent
summary that determines its output* — the constructive direction of Myhill–Nerode. The
finite `state` plays the role of the prefix-congruence's quotient; `δ`/`out` are the
induced transition and output. (The natural Nerode congruence, when of finite index, is
one such summary — that instantiation is the Todo above.) -/

/-- **Myhill–Nerode converse (constructive).** A length-preserving `f` with a finite
`state : List α → σ` that is left-congruent (`hδ`) and determines `f`'s output at each
position (`hout`) is letter-left-subsequential. -/
theorem isLetterLeftSubsequential_of_stateSummary
    {f : List α → List β} {σ : Type} [Fintype σ]
    (state : List α → σ) (δ : σ → α → σ) (out : σ → α → β)
    (hδ : ∀ u x, state (u ++ [x]) = δ (state u) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (state u) x))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsLetterLeftSubsequential f := by
  refine ⟨σ, inferInstance, { initial := state [], step := fun s x => (δ s x, out s x) }, ?_⟩
  set T : Mealy σ α β := { initial := state [], step := fun s x => (δ s x, out s x) }
  have hstate : ∀ (p₀ ps : List α), T.stateAfter (state p₀) ps = state (p₀ ++ ps) := by
    intro p₀ ps
    induction ps generalizing p₀ with
    | nil => simp
    | cons x xs ih =>
      rw [Mealy.stateAfter_cons]
      show T.stateAfter (δ (state p₀) x) xs = state (p₀ ++ x :: xs)
      rw [← hδ p₀ x, ih (p₀ ++ [x])]
      simp
  funext xs
  apply List.ext_getElem?
  intro i
  show (T.runFrom T.initial xs)[i]? = (f xs)[i]?
  rw [Mealy.runFrom_getElem? T T.initial xs i]
  show (xs[i]?).map (fun x => out (T.stateAfter (state []) (xs.take i)) x) = (f xs)[i]?
  rw [hstate [] (xs.take i), List.nil_append]
  rcases lt_or_ge i xs.length with hi | hi
  · have hdecomp : xs.take i ++ xs[i] :: xs.drop (i + 1) = xs := by
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    have htlen : (xs.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
    have key := hout (xs.take i) (xs[i]) (xs.drop (i + 1))
    rw [htlen, hdecomp] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none (by rw [hlen]; exact hi)]
    simp

/-- Non-vacuity: the identity is letter-left-subsequential via a one-state summary. -/
example : IsLetterLeftSubsequential (id : List α → List α) :=
  isLetterLeftSubsequential_of_stateSummary
    (fun _ => ()) (fun _ _ => ()) (fun _ x => x)
    (fun _ _ => rfl) (fun u x w => by simp) (fun _ => rfl)

end Subregular
