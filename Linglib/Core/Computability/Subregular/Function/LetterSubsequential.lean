/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# Synchronous (letter) left-subsequential functions

A `LetterSFST` is a deterministic left-to-right transducer emitting exactly one output
symbol per input symbol — the Mealy / synchronous case, length-preserving by
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

* `LetterSFST` — synchronous one-symbol-per-step transducer; `run` is length-preserving.
* `IsLetterLeftSubsequential` — computed by a finite-state `LetterSFST`.

## Main results

* `LetterSFST.runFrom_getElem?` — output `i` is `(step (state-after-prefix) (input i)).2`.
* `IsLetterLeftSubsequential.leftDetermined` / `.isRightMyopic` — synchronous
  left-subsequential maps are prefix-determined, hence right-myopic.

## Todo

* The Myhill–Nerode *converse*: `(∀ i, LeftDetermined f i) ∧ finite prefix-congruence ⟹
  IsLetterLeftSubsequential f` (build the transducer from the prefix-congruence quotient).
-/

namespace Core.Computability.Subregular.Function

variable {σ α β : Type*}

/-- A synchronous letter-to-letter left-to-right transducer: exactly one output symbol
per input symbol (length-preserving by construction). -/
structure LetterSFST (σ α β : Type*) where
  initial : σ
  step : σ → α → σ × β

namespace LetterSFST

/-- State reached after consuming a prefix. -/
def stateAfter (T : LetterSFST σ α β) : σ → List α → σ
  | s, [] => s
  | s, x :: xs => T.stateAfter (T.step s x).1 xs

/-- Run from a state: one output symbol per input symbol. -/
def runFrom (T : LetterSFST σ α β) : σ → List α → List β
  | _, [] => []
  | s, x :: xs => (T.step s x).2 :: T.runFrom (T.step s x).1 xs

/-- Run from the initial state. -/
def run (T : LetterSFST σ α β) : List α → List β := T.runFrom T.initial

@[simp] theorem runFrom_nil (T : LetterSFST σ α β) (s : σ) : T.runFrom s [] = [] := rfl
@[simp] theorem runFrom_cons (T : LetterSFST σ α β) (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = (T.step s x).2 :: T.runFrom (T.step s x).1 xs := rfl
@[simp] theorem stateAfter_nil (T : LetterSFST σ α β) (s : σ) : T.stateAfter s [] = s := rfl
@[simp] theorem stateAfter_cons (T : LetterSFST σ α β) (s : σ) (x : α) (xs : List α) :
    T.stateAfter s (x :: xs) = T.stateAfter (T.step s x).1 xs := rfl

/-- The run is length-preserving (one output symbol per input symbol). -/
theorem runFrom_length (T : LetterSFST σ α β) (s : σ) (xs : List α) :
    (T.runFrom s xs).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem run_length (T : LetterSFST σ α β) (xs : List α) :
    (T.run xs).length = xs.length := T.runFrom_length T.initial xs

/-- **The coordinate characterization**: output `i` is the step output at
`(state after the prefix [0..i-1], input i)`. -/
theorem runFrom_getElem? (T : LetterSFST σ α β) (s : σ) (xs : List α) (i : ℕ) :
    (T.runFrom s xs)[i]?
      = (xs[i]?).map (fun x => (T.step (T.stateAfter s (xs.take i)) x).2) := by
  induction xs generalizing s i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ j => simp [ih, List.take_succ_cons]

end LetterSFST

/-- The synchronous left-subsequential class: computed by a finite-state `LetterSFST`. -/
def IsLetterLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : LetterSFST σ α β), T.run = f

/-- **Forward footprint bridge.** A letter-left-subsequential map is left-determined at
every coordinate — output `i` depends only on the prefix `{k | k ≤ i}`. (The *block*
`IsLeftSubsequential` lacks this, by delayed output.) -/
theorem IsLetterLeftSubsequential.leftDetermined {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  intro u v hlen hag
  have hi : u[i]? = v[i]? := hag i (by simp)
  have htake : u.take i = v.take i := by
    apply List.ext_getElem?
    intro k
    rcases lt_or_ge k i with hk | hk
    · simpa only [List.getElem?_take_of_lt hk] using hag k (by simp only [Set.mem_setOf_eq]; omega)
    · simp [List.getElem?_take_eq_none hk]
  show (T.runFrom T.initial u)[i]? = (T.runFrom T.initial v)[i]?
  rw [LetterSFST.runFrom_getElem? T T.initial u i,
      LetterSFST.runFrom_getElem? T T.initial v i, hi, htake]

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
  set T : LetterSFST σ α β := { initial := state [], step := fun s x => (δ s x, out s x) }
  have hstate : ∀ (p₀ ps : List α), T.stateAfter (state p₀) ps = state (p₀ ++ ps) := by
    intro p₀ ps
    induction ps generalizing p₀ with
    | nil => simp
    | cons x xs ih =>
      rw [LetterSFST.stateAfter_cons]
      show T.stateAfter (δ (state p₀) x) xs = state (p₀ ++ x :: xs)
      rw [← hδ p₀ x, ih (p₀ ++ [x])]
      simp
  funext xs
  apply List.ext_getElem?
  intro i
  show (T.runFrom T.initial xs)[i]? = (f xs)[i]?
  rw [LetterSFST.runFrom_getElem? T T.initial xs i]
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

end Core.Computability.Subregular.Function
