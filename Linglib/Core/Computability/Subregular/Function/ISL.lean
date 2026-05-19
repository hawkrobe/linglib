/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Linglib.Core.Direction
import Linglib.Core.StringHom
import Linglib.Core.Computability.Subregular.Function.Subsequential

/-!
# Input Strictly Local (ISL) Functions

A function `f : List α → List β` is **k-Input Strictly Local** when each
output block depends only on the last `k - 1` input symbols plus the
current input symbol. ISL is the most restrictive class of the
function-level subregular hierarchy.

## Main definitions

* `ISLRule k α β` — a `k`-ISL rule: a window-based output function
  `List α → α → List β` consuming the `k - 1`-symbol left context plus
  the current input symbol and emitting an output block.
* `ISLRule.apply` — the induced string function `List α → List β`.
* `IsLeftInputStrictlyLocal k f`, `IsRightInputStrictlyLocal k f` —
  witness predicates: there exists an `ISLRule k α β` whose `apply`
  computes `f` (resp. via right-to-left scan).
* `IsInputStrictlyLocal d k f` — direction-parameterised umbrella.

## Main results

* `isRightInputStrictlyLocal_iff_left_reverse` — the right class is the
  reverse-conjugate of the left class.
* `isLeftInputStrictlyLocal_left_subsequential` — every Left-ISL
  function is Left-Subsequential, witnessed by `ISLRule.toSFST`.
* `Core.StringHom.apply_isLeftInputStrictlyLocal_one`,
  `Core.Tier.apply_isLeftInputStrictlyLocal_one` — letterwise
  homomorphisms and tier projections are the `k = 1` specialisation.

## Implementation notes

The witness style `IsX k f := ∃ r : XRule k α β, r.apply = f` mirrors
`IsStrictlyLocal k L := ∃ G, G.lang = L` from `StrictlyLocal.lean`. The
`k` parameter is a type-level annotation only: `windowOutput` is
unconstrained at the type level (compare `SLGrammar k α`); `applyAux`
truncates the threaded window to length `k - 1`.

## References

* @cite{chandlee-2014}
* @cite{chandlee-heinz-2018}
* @cite{chandlee-eyraud-heinz-2015}
* @cite{heinz-lai-2013}
* @cite{jardine-2016}
-/

namespace Core.Computability.Subregular.Function

variable {α β : Type*}

/-- The last `n` elements of a list. Defined as `xs.drop (xs.length - n)`;
when `n ≥ xs.length`, returns `xs` (since `Nat` subtraction truncates).

Equivalent to `String.takeRight` and `Substring.takeRight` in Lean core
but no `List.takeRight` exists yet (batteries flags `-- TODO: takeRight,
dropRight` in `Batteries/Data/String/Lemmas.lean`). Promote upstream
once a `List.takeRight` lands. -/
def lastN (n : ℕ) (xs : List α) : List α := xs.drop (xs.length - n)

@[simp] lemma lastN_nil (n : ℕ) : lastN n ([] : List α) = [] := by
  simp [lastN]

/-- A **k-Input-Strictly-Local rule** over input alphabet `α` and output
alphabet `β`. The single field `windowOutput` consumes the
(k − 1)-symbol left context window plus the current input symbol and
emits an output block (a list of output symbols, which can be empty for
deletion or contain multiple symbols for insertion-on-trigger).

The `k` parameter is purely a type-level annotation — it constrains the
*intended semantics* of `windowOutput`'s first argument (the caller in
`apply` always supplies a window of length at most `k - 1`) but is not
enforced by the type. This mirrors `SLGrammar k α` from
`StrictlyLocal.lean`, where the `permitted` factor set is similarly
unconstrained at the type level. -/
structure ISLRule (k : ℕ) (α β : Type*) where
  /-- Map from (left-context window, current input symbol) to output
  block. The window argument has length at most `k - 1` when called by
  `ISLRule.apply`. -/
  windowOutput : List α → α → List β

namespace ISLRule

variable {k : ℕ}

/-- Apply the rule, threading a window of accumulated input symbols.
Tail-recursive on the remaining input. The window grows from `[]` and
is truncated to keep at most `k − 1` symbols at each step. -/
def applyAux (r : ISLRule k α β) :
    (window : List α) → (rest : List α) → List β
  | _, [] => []
  | window, x :: xs =>
    r.windowOutput window x ++ applyAux r (lastN (k - 1) (window ++ [x])) xs

/-- Apply a k-ISL rule to an input string. Scans left-to-right; at each
position emits `r.windowOutput window x` where `window` is the (last
`k − 1`) preceding input symbols and `x` is the current symbol. -/
def apply (r : ISLRule k α β) (input : List α) : List β :=
  applyAux r [] input

@[simp] lemma applyAux_nil (r : ISLRule k α β) (window : List α) :
    r.applyAux window [] = [] := rfl

@[simp] lemma applyAux_cons (r : ISLRule k α β) (window : List α)
    (x : α) (xs : List α) :
    r.applyAux window (x :: xs)
      = r.windowOutput window x ++ r.applyAux (lastN (k - 1) (window ++ [x])) xs :=
  rfl

@[simp] lemma apply_nil (r : ISLRule k α β) : r.apply [] = [] := rfl

@[simp] lemma apply_singleton (r : ISLRule k α β) (x : α) :
    r.apply [x] = r.windowOutput [] x := by
  show r.windowOutput [] x ++ r.applyAux _ [] = r.windowOutput [] x
  exact List.append_nil _

end ISLRule

/-- `f : List α → List β` is **k-Left-Input-Strictly-Local** iff some
`k`-ISL rule computes it via left-to-right scan. -/
def IsLeftInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : ISLRule k α β, r.apply = f

/-- `f : List α → List β` is **k-Right-Input-Strictly-Local** iff some
`k`-ISL rule computes it via right-to-left scan. Mirror image of the
left class via `f ↦ List.reverse ∘ f ∘ List.reverse`; see
`isRightInputStrictlyLocal_iff_left_reverse`. -/
def IsRightInputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : ISLRule k α β, (fun input => (r.apply input.reverse).reverse) = f

/-- Direction-parameterised ISL predicate. Mirrors the OSL/Subseq
umbrella style; concrete claims should typically use one of
`IsLeftInputStrictlyLocal` / `IsRightInputStrictlyLocal` directly for
clarity. -/
def IsInputStrictlyLocal (d : Direction) (k : ℕ)
    (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftInputStrictlyLocal k f
  | .right => IsRightInputStrictlyLocal k f

@[simp] lemma isInputStrictlyLocal_left (k : ℕ) (f : List α → List β) :
    IsInputStrictlyLocal .left k f ↔ IsLeftInputStrictlyLocal k f := Iff.rfl

@[simp] lemma isInputStrictlyLocal_right (k : ℕ) (f : List α → List β) :
    IsInputStrictlyLocal .right k f ↔ IsRightInputStrictlyLocal k f := Iff.rfl

/-- Every ISL rule witnesses `IsLeftInputStrictlyLocal` for the function
it computes. -/
lemma ISLRule.isLeftInputStrictlyLocal_apply {k : ℕ} (r : ISLRule k α β) :
    IsLeftInputStrictlyLocal k r.apply :=
  ⟨r, rfl⟩

/-- **Reverse-conjugation lemma**: a function is k-Right-ISL iff its
reverse-conjugate is k-Left-ISL. The two classes are isomorphic via the
involution `f ↦ List.reverse ∘ f ∘ List.reverse`. -/
theorem isRightInputStrictlyLocal_iff_left_reverse {k : ℕ}
    (f : List α → List β) :
    IsRightInputStrictlyLocal k f
      ↔ IsLeftInputStrictlyLocal k (fun xs => (f xs.reverse).reverse) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    funext xs
    have h := congrFun hr xs.reverse
    rw [List.reverse_reverse] at h
    show r.apply xs = (f xs.reverse).reverse
    rw [← h, List.reverse_reverse]
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    funext xs
    show (r.apply xs.reverse).reverse = f xs
    have h := congrFun hr xs.reverse
    rw [List.reverse_reverse] at h
    rw [h, List.reverse_reverse]

/-- The empty-output function is ISL for any `k`. Witness: the rule that
emits `[]` regardless of window or current symbol. -/
lemma isLeftInputStrictlyLocal_const_nil (k : ℕ) :
    IsLeftInputStrictlyLocal (α := α) (β := β) k (fun _ => []) := by
  refine ⟨⟨fun _ _ => []⟩, ?_⟩
  funext input
  show (⟨fun _ _ => []⟩ : ISLRule k α β).apply input = []
  suffices h : ∀ window : List α,
      (⟨fun _ _ => []⟩ : ISLRule k α β).applyAux window input = [] from h []
  intro window
  induction input generalizing window with
  | nil => rfl
  | cons x xs ih =>
    show ([] : List β) ++ _ = []
    rw [List.nil_append, ih]

/-! ### StringHom / Tier as the `k = 1` specialisation

`StringHom α β := α → List β` is the `k = 1` specialisation: the window
argument is always empty and only the current input symbol matters.
`Tier α β := α → Option β` is the further erasing specialisation. -/

/-- Embed a string homomorphism as a 1-ISL rule (no left context). The
windowOutput ignores its window argument and behaves letterwise. -/
def ISLRule.ofStringHom (h : Core.StringHom α β) : ISLRule 1 α β where
  windowOutput := fun _ x => h x

private lemma ISLRule.applyAux_ofStringHom (h : Core.StringHom α β)
    (window : List α) (xs : List α) :
    (ISLRule.ofStringHom h).applyAux window xs = Core.StringHom.apply h xs := by
  induction xs generalizing window with
  | nil => rfl
  | cons x ys ih =>
    show h x ++ _ = h x ++ _
    congr 1
    exact ih _

/-- The 1-ISL rule constructed from `h` computes `h` on lists. Definitional
up to `applyAux` unfolding; the inductive proof handles the window-threading. -/
@[simp] theorem ISLRule.ofStringHom_apply (h : Core.StringHom α β) :
    (ISLRule.ofStringHom h).apply = Core.StringHom.apply h := by
  funext xs
  show (ISLRule.ofStringHom h).applyAux [] xs = _
  exact ISLRule.applyAux_ofStringHom h [] xs

/-- **Every string homomorphism is 1-Left-ISL.** The substrate-level claim
that `StringHom α β` and `ISLRule 1 α β` denote the same function class. -/
theorem Core.StringHom.apply_isLeftInputStrictlyLocal_one (h : Core.StringHom α β) :
    IsLeftInputStrictlyLocal 1 (Core.StringHom.apply h) :=
  ⟨ISLRule.ofStringHom h, ISLRule.ofStringHom_apply h⟩

/-- **Every tier projection is 1-Left-ISL.** Tier projections are
letterwise erasing (`Tier α β := α → Option β`), hence a special case
of `ISLRule.ofStringHom` via `fun x => (T x).toList`. -/
theorem Core.Tier.apply_isLeftInputStrictlyLocal_one (T : Core.Tier α β) :
    IsLeftInputStrictlyLocal 1 (Core.Tier.apply T) := by
  -- Tier.apply T = filterMap T = flatMap (Option.toList ∘ T) = StringHom.apply (Option.toList ∘ T)
  refine ⟨ISLRule.ofStringHom (fun x => (T x).toList), ?_⟩
  rw [ISLRule.ofStringHom_apply]
  funext xs
  show List.flatMap (fun x => (T x).toList) xs = List.filterMap T xs
  induction xs with
  | nil => rfl
  | cons x ys ih =>
    cases h : T x with
    | none =>
      simp only [List.flatMap_cons, List.filterMap_cons, h, Option.toList_none,
        List.nil_append, ih]
    | some v =>
      simp only [List.flatMap_cons, List.filterMap_cons, h, Option.toList_some,
        List.cons_append, List.nil_append, ih]

/-! ### ISL ⊆ Subsequential

`ISLRule.toSFST` projects an ISL rule into an SFST; the inclusion rides
on the run-equality. Co-located on the source side because the
dependency direction (SFST in `Subsequential.lean`; ISL projects into
it) forces both construction and cast into this file. -/

section ISLToSubseq

variable {α β : Type}

/-- Construction: every ISL rule induces an SFST whose state is the
input window (length ≤ k − 1) and whose `finalOutput` is empty. -/
def ISLRule.toSFST {k : ℕ} (r : ISLRule k α β) : SFST (List α) α β where
  initial := []
  step window x := (lastN (k - 1) (window ++ [x]), r.windowOutput window x)
  finalOutput _ := []

/-- The SFST induced by an ISL rule computes the same string function. -/
theorem ISLRule.toSFST_run_eq_apply {k : ℕ} (r : ISLRule k α β) :
    r.toSFST.run = r.apply := by
  funext input
  show SFST.runFrom r.toSFST [] input = ISLRule.applyAux r [] input
  suffices h : ∀ window : List α,
      SFST.runFrom r.toSFST window input = ISLRule.applyAux r window input from h []
  intro window
  induction input generalizing window with
  | nil => rfl
  | cons x xs ih =>
    change r.windowOutput window x
              ++ SFST.runFrom r.toSFST (lastN (k - 1) (window ++ [x])) xs
         = r.windowOutput window x
              ++ ISLRule.applyAux r (lastN (k - 1) (window ++ [x])) xs
    rw [ih]

/-- **Left-ISL ⊆ Left-Subsequential.** -/
theorem isLeftInputStrictlyLocal_left_subsequential {k : ℕ}
    {f : List α → List β} (h : IsLeftInputStrictlyLocal k f) :
    IsLeftSubsequential f := by
  obtain ⟨r, hr⟩ := h
  exact ⟨List α, r.toSFST, hr ▸ r.toSFST_run_eq_apply⟩

/-- Direction-parameterised: ISL_d ⊆ Subseq_d for both directions. -/
theorem isInputStrictlyLocal_isSubsequential {d : Direction} {k : ℕ}
    {f : List α → List β} (h : IsInputStrictlyLocal d k f) :
    IsSubsequential d f := by
  cases d with
  | left => exact isLeftInputStrictlyLocal_left_subsequential h
  | right =>
    rw [isSubsequential_right]
    rw [isInputStrictlyLocal_right] at h
    rw [isRightInputStrictlyLocal_iff_left_reverse] at h
    rw [isRightSubsequential_iff_left_reverse]
    exact isLeftInputStrictlyLocal_left_subsequential h

end ISLToSubseq

end Core.Computability.Subregular.Function
