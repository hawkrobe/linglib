/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Linglib.Core.Data.List.DropRight
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
* `flatMap_isLeftInputStrictlyLocal_one`,
  `filterMap_isLeftInputStrictlyLocal_one` — letterwise homomorphisms and
  erasing (tier) projections are the `k = 1` specialisation.

## Implementation notes

The witness style `IsX k f := ∃ r : XRule k α β, r.apply = f` mirrors
`Language.IsStrictlyLocal L k := ∃ G, G.language k = L` from
`StrictlyLocal.lean`. The `k` parameter is a type-level annotation only:
`windowOutput` is unconstrained at the type level; `applyAux` truncates the
threaded window to length `k - 1`.
-/

namespace Subregular

variable {α β : Type*}

/-- The "list of length at most `n`" subtype is finite when `α` is. The
witness is a surjection from `Σ m : Fin (n + 1), List.Vector α m` (which
has a `Fintype` instance via `Mathlib.Data.Fintype.{Sigma,Vector}`). Used
to give ISL/OSL projections into SFST a manifestly-finite state space
(matching [mohri-1997]'s finite-state assumption). Uses `classical`
to discharge the `DecidableEq` side condition without imposing it on
consumers (matches mathlib pattern for finite types over `Fintype α`). -/
noncomputable instance fintypeListLengthLE {α : Type*} [Fintype α] (n : ℕ) :
    Fintype {l : List α // l.length ≤ n} := by
  classical
  exact Fintype.ofSurjective
    (fun (s : Σ m : Fin (n + 1), List.Vector α m) =>
      (⟨s.snd.toList, by
        rw [List.Vector.toList_length]
        exact Nat.lt_succ_iff.mp s.fst.isLt⟩ :
        {l : List α // l.length ≤ n}))
    (fun l => ⟨⟨⟨l.val.length, Nat.lt_succ_iff.mpr l.property⟩,
                  ⟨l.val, rfl⟩⟩, rfl⟩)

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
    r.windowOutput window x ++ applyAux r ((window ++ [x]).rtake (k - 1)) xs

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
      = r.windowOutput window x ++ r.applyAux ((window ++ [x]).rtake (k - 1)) xs :=
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

/-! ### Letterwise homomorphisms / Tier as the `k = 1` specialisation

A letterwise string homomorphism `h : α → List β` (string action `List.flatMap h`,
the free-monoid lift) is the `k = 1` specialisation: the window argument is always
empty and only the current input symbol matters. An erasing letterwise map
`g : α → Option β` (string action `List.filterMap g`) is the further erasing
specialisation. -/

/-- Embed a letterwise string homomorphism `h : α → List β` as a 1-ISL rule (no left
context). The windowOutput ignores its window argument and behaves letterwise. -/
def ISLRule.ofStringHom (h : α → List β) : ISLRule 1 α β where
  windowOutput := fun _ x => h x

private lemma ISLRule.applyAux_ofStringHom (h : α → List β)
    (window : List α) (xs : List α) :
    (ISLRule.ofStringHom h).applyAux window xs = List.flatMap h xs := by
  induction xs generalizing window with
  | nil => rfl
  | cons x ys ih =>
    show h x ++ _ = h x ++ _
    congr 1
    exact ih _

/-- The 1-ISL rule constructed from `h` computes `List.flatMap h` on lists.
Definitional up to `applyAux` unfolding; the inductive proof handles the window-threading. -/
@[simp] theorem ISLRule.ofStringHom_apply (h : α → List β) :
    (ISLRule.ofStringHom h).apply = List.flatMap h := by
  funext xs
  show (ISLRule.ofStringHom h).applyAux [] xs = _
  exact ISLRule.applyAux_ofStringHom h [] xs

/-- **Every letterwise string homomorphism is 1-Left-ISL.** The substrate-level
claim that the letterwise-homomorphism function class (`List.flatMap h` for
`h : α → List β`) and `ISLRule 1 α β` denote the same function class. -/
theorem flatMap_isLeftInputStrictlyLocal_one (h : α → List β) :
    IsLeftInputStrictlyLocal 1 (List.flatMap h) :=
  ⟨ISLRule.ofStringHom h, ISLRule.ofStringHom_apply h⟩

/-- **Every erasing letterwise projection is 1-Left-ISL.** `List.filterMap g`
(for `g : α → Option β`) is letterwise erasing, hence a special case of
`ISLRule.ofStringHom` via `fun x => (g x).toList`. -/
theorem filterMap_isLeftInputStrictlyLocal_one (g : α → Option β) :
    IsLeftInputStrictlyLocal 1 (List.filterMap g) := by
  -- filterMap g = List.flatMap (fun x => (g x).toList)
  refine ⟨ISLRule.ofStringHom (fun x => (g x).toList), ?_⟩
  rw [ISLRule.ofStringHom_apply]
  funext xs
  show List.flatMap (fun x => (g x).toList) xs = List.filterMap g xs
  induction xs with
  | nil => rfl
  | cons x ys ih =>
    cases h : g x with
    | none =>
      simp only [List.flatMap_cons, List.filterMap_cons, h, Option.toList_none,
        List.nil_append, ih]
    | some v =>
      simp only [List.flatMap_cons, List.filterMap_cons, h, Option.toList_some,
        List.cons_append, List.nil_append, ih]

/-! ### ISL ⊆ Subsequential

`ISLRule.toFinSFST` projects an ISL rule into a finite-state SFST whose
state space is the bounded input window `{l : List α // l.length ≤ k - 1}`.
The `[Fintype α]` constraint matches the source literature [mohri-1997]:
every subsequential model has a finite alphabet and finite state by
definition. The inclusion theorem
rides on the run-equality. Co-located on the source side because the
dependency direction (SFST in `Subsequential.lean`; ISL projects into
it) forces both construction and cast into this file. -/

/-- Construction: every ISL rule induces a **finite-state** SFST whose
state is the bounded input window `{l : List α // l.length ≤ k - 1}`,
and whose `finalOutput` is empty. The state is manifestly finite via
`fintypeListLengthLE`, witnessing ISL ⊆ Subsequential under the source
literature's finite-state assumption. -/
def ISLRule.toFinSFST {k : ℕ} [Fintype α] (r : ISLRule k α β) :
    SFST {l : List α // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x :=
    (⟨(w.val ++ [x]).rtake (k - 1), List.length_rtake_le _ _⟩,
     r.windowOutput w.val x)
  finalOutput _ := []

/-- The finite-state SFST induced by an ISL rule computes the same
string function. -/
theorem ISLRule.toFinSFST_run_eq_apply {k : ℕ} [Fintype α] (r : ISLRule k α β) :
    r.toFinSFST.run = r.apply := by
  funext input
  show SFST.runFrom r.toFinSFST ⟨[], Nat.zero_le _⟩ input
    = ISLRule.applyAux r [] input
  suffices h : ∀ (w : {l : List α // l.length ≤ k - 1}),
      SFST.runFrom r.toFinSFST w input = ISLRule.applyAux r w.val input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    change r.windowOutput w.val x
              ++ SFST.runFrom r.toFinSFST
                  ⟨(w.val ++ [x]).rtake (k - 1), List.length_rtake_le _ _⟩ xs
         = r.windowOutput w.val x
              ++ ISLRule.applyAux r ((w.val ++ [x]).rtake (k - 1)) xs
    exact congrArg _ (ih _)

/-- **Left-ISL ⊆ Left-Subsequential** (over a finite input alphabet).
The `[Fintype α]` matches [mohri-1997]'s finite-alphabet assumption
and lets the bounded input window serve as a finite state space. -/
theorem isLeftInputStrictlyLocal_left_subsequential {k : ℕ} [Fintype α]
    {f : List α → List β} (h : IsLeftInputStrictlyLocal k f) :
    IsLeftSubsequential f := by
  obtain ⟨r, hr⟩ := h
  have heq : r.toFinSFST.run = f := r.toFinSFST_run_eq_apply.trans hr
  exact heq ▸ r.toFinSFST.isLeftSubsequential

/-- **Right-ISL ⊆ Right-Subsequential**, derived from the Left- side via
the reverse-conjugation lemmas. The Right-ISL ↔ Left-ISL and
Right-Subseq ↔ Left-Subseq isomorphisms commute. -/
theorem isRightInputStrictlyLocal_right_subsequential {k : ℕ} [Fintype α]
    {f : List α → List β} (h : IsRightInputStrictlyLocal k f) :
    IsRightSubsequential f := by
  rw [isRightInputStrictlyLocal_iff_left_reverse] at h
  rw [isRightSubsequential_iff_left_reverse]
  exact isLeftInputStrictlyLocal_left_subsequential h

/-- Direction-parameterised: ISL_d ⊆ Subseq_d for both directions (over
a finite input alphabet). Delegates to the Left- / Right- specialised
theorems. -/
theorem isInputStrictlyLocal_isSubsequential {d : Direction} {k : ℕ}
    [Fintype α] {f : List α → List β} (h : IsInputStrictlyLocal d k f) :
    IsSubsequential d f := by
  cases d with
  | left => exact isLeftInputStrictlyLocal_left_subsequential h
  | right => exact isRightInputStrictlyLocal_right_subsequential h

end Subregular
