/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.Subsequential

/-!
# Output Strictly Local (OSL) Functions

A function `f : List α → List β` is **k-Output Strictly Local** when each
output block depends only on the last `k - 1` *output* symbols plus the
current input symbol. OSL captures iterative spreading processes —
progressive nasal harmony, vowel harmony, tone spreading — where the
decision at position *i* feeds forward to the decision at position
*i + 1*. The function-level subregular hierarchy at this layer is
ISL ⊊ OSL ⊊ Subsequential; bidirectional iterative harmony (Maasai,
Turkana ATR) is Weakly Deterministic (composition of two
opposite-direction subsequentials) rather than OSL in either direction.

## Main definitions

* `OSLRule k α β` — a `k`-OSL rule: a window-based output function
  `List β → α → List β` consuming the (k - 1)-symbol output context
  plus the current input symbol and emitting an output block.
* `OSLRule.apply` — the induced string function, threading the output
  window left-to-right.
* `IsLeftOutputStrictlyLocal k f`, `IsRightOutputStrictlyLocal k f` —
  witness predicates for each scan direction.
* `IsOutputStrictlyLocal d k f` — direction-parameterised umbrella.

## Main results

* `isRightOutputStrictlyLocal_iff_left_reverse` — Right-OSL is the
  reverse-conjugate of Left-OSL.
* `isLeftOutputStrictlyLocal_left_subsequential` — Left-OSL ⊆
  Left-Subsequential, via `OSLRule.toSFST`.

## Implementation notes

The witness style `IsX k f := ∃ r : OSLRule k α β, r.apply = f` mirrors
`IsLeftInputStrictlyLocal` in `ISL.lean`. Unlike ISL, whose window is
over input symbols and threads independently of what was emitted, the
OSL window is over **already-emitted output** — each step truncates
`outputWindow ++ windowOutput outputWindow x` to the last `k - 1`
symbols before recursing. The `k` parameter is a type-level annotation;
window-length truncation in `applyAux` is what enforces it semantically.

`OSLRule.toSFST` deliberately repeats `r.windowOutput outputWindow x`
in the two tuple components of `step` rather than `let`-binding it, so
that `(step ow x).2` reduces definitionally for `toSFST_run_eq_apply`.

## References

* [chandlee-eyraud-heinz-2015]
* [aksenova-rawski-graf-heinz-2020]
* [heinz-lai-2013]
* [meinhardt-mai-bakovic-mccollum-2024]
-/

namespace Subregular.Function

variable {α β : Type*}

/-- A **k-Output-Strictly-Local rule** over input alphabet `α` and
output alphabet `β`. The single field `windowOutput` consumes the
(k − 1)-symbol output context window plus the current input symbol and
emits an output block.

In contrast to `ISLRule` (whose window is over input symbols), the
window here is over **already-emitted output symbols**. This lets the
rule see what it has just produced and react accordingly — the
mechanism behind iterative spreading.

The `k` parameter is a type-level annotation; semantic enforcement
happens in `apply`'s window threading. -/
structure OSLRule (k : ℕ) (α β : Type*) where
  /-- Map from (output context window, current input symbol) to output
  block. The window argument has length at most `k - 1` when called by
  `OSLRule.apply`. -/
  windowOutput : List β → α → List β

namespace OSLRule

variable {k : ℕ}

/-- Apply the rule, threading a window of accumulated output symbols.
At each input position, emit `r.windowOutput outputWindow x`, then
extend the output window with the just-emitted block (truncated to keep
at most `k − 1` symbols). -/
def applyAux (r : OSLRule k α β) :
    (outputWindow : List β) → (rest : List α) → List β
  | _, [] => []
  | outputWindow, x :: xs =>
    r.windowOutput outputWindow x
      ++ applyAux r (lastN (k - 1) (outputWindow ++ r.windowOutput outputWindow x)) xs

/-- Apply a k-OSL rule to an input string, scanning left-to-right. -/
def apply (r : OSLRule k α β) (input : List α) : List β :=
  applyAux r [] input

@[simp] lemma applyAux_nil (r : OSLRule k α β) (outputWindow : List β) :
    r.applyAux outputWindow [] = [] := rfl

@[simp] lemma applyAux_cons (r : OSLRule k α β) (outputWindow : List β)
    (x : α) (xs : List α) :
    r.applyAux outputWindow (x :: xs)
      = r.windowOutput outputWindow x
          ++ r.applyAux (lastN (k - 1) (outputWindow ++ r.windowOutput outputWindow x)) xs :=
  rfl

@[simp] lemma apply_nil (r : OSLRule k α β) : r.apply [] = [] := rfl

@[simp] lemma apply_singleton (r : OSLRule k α β) (x : α) :
    r.apply [x] = r.windowOutput [] x := by
  show r.windowOutput [] x ++ r.applyAux _ [] = r.windowOutput [] x
  exact List.append_nil _

end OSLRule

/-- A function `f : List α → List β` is **k-Left-Output-Strictly-Local**
iff some `k`-OSL rule computes it via left-to-right scan. -/
def IsLeftOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : OSLRule k α β, r.apply = f

/-- A function `f : List α → List β` is **k-Right-Output-Strictly-Local**
iff some `k`-OSL rule computes it via right-to-left scan. -/
def IsRightOutputStrictlyLocal (k : ℕ) (f : List α → List β) : Prop :=
  ∃ r : OSLRule k α β, (fun input => (r.apply input.reverse).reverse) = f

/-- Direction-parameterised OSL predicate. -/
def IsOutputStrictlyLocal (d : Direction) (k : ℕ) (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftOutputStrictlyLocal k f
  | .right => IsRightOutputStrictlyLocal k f

@[simp] lemma isOutputStrictlyLocal_left (k : ℕ) (f : List α → List β) :
    IsOutputStrictlyLocal .left k f ↔ IsLeftOutputStrictlyLocal k f := Iff.rfl

@[simp] lemma isOutputStrictlyLocal_right (k : ℕ) (f : List α → List β) :
    IsOutputStrictlyLocal .right k f ↔ IsRightOutputStrictlyLocal k f := Iff.rfl

/-- Every OSL rule witnesses `IsLeftOutputStrictlyLocal` for the function
it computes. -/
lemma OSLRule.isLeftOutputStrictlyLocal_apply {k : ℕ} (r : OSLRule k α β) :
    IsLeftOutputStrictlyLocal k r.apply :=
  ⟨r, rfl⟩

/-- **Reverse-conjugation lemma**: a function is k-Right-OSL iff its
reverse-conjugate is k-Left-OSL. The two classes are isomorphic via the
involution `f ↦ List.reverse ∘ f ∘ List.reverse`. -/
theorem isRightOutputStrictlyLocal_iff_left_reverse {k : ℕ}
    (f : List α → List β) :
    IsRightOutputStrictlyLocal k f
      ↔ IsLeftOutputStrictlyLocal k (fun xs => (f xs.reverse).reverse) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    funext xs
    have h := congrFun hr xs.reverse
    -- h : (r.apply xs.reverse.reverse).reverse = f xs.reverse
    -- = (r.apply xs).reverse = f xs.reverse
    rw [List.reverse_reverse] at h
    show r.apply xs = (f xs.reverse).reverse
    rw [← h, List.reverse_reverse]
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    funext xs
    show (r.apply xs.reverse).reverse = f xs
    have h := congrFun hr xs.reverse
    -- h : r.apply xs.reverse = (f xs.reverse.reverse).reverse = (f xs).reverse
    rw [List.reverse_reverse] at h
    rw [h, List.reverse_reverse]

/-! ### OSL ⊆ Subsequential

`OSLRule.toFinSFST` projects an OSL rule into an SFST whose state is
the bounded output window (length ≤ k − 1). The inclusion rides on the
run-equality plus the `Fintype` instance for the bounded-window subtype
(reusing `fintypeListLengthLE` from `ISL.lean`). Co-located on the
source side because the dependency direction (SFST in
`Subsequential.lean`; OSL projects into it) forces both construction
and cast into this file.

The output alphabet `[Fintype β]` constraint matches [mohri-1997]'s
finite-alphabet assumption — the state space (a bounded output window)
is finite precisely when the output alphabet is. -/

/-- Construction: every Left-OSL rule induces an SFST whose state is the
output window — a list of output symbols of length at most `k − 1` —
and whose `finalOutput` is empty.

The `windowOutput` call is repeated in the two tuple components rather
than `let`-bound so that `(step ow x).2` reduces definitionally to
`r.windowOutput ow x` for the proof of `toFinSFST_run_eq_apply`. -/
def OSLRule.toFinSFST {k : ℕ} (r : OSLRule k α β) :
    SFST {l : List β // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x :=
    (⟨lastN (k - 1) (w.val ++ r.windowOutput w.val x), lastN_length_le _ _⟩,
     r.windowOutput w.val x)
  finalOutput _ := []

/-- The SFST induced by an OSL rule computes the same string function. -/
theorem OSLRule.toFinSFST_run_eq_apply {k : ℕ} (r : OSLRule k α β) :
    r.toFinSFST.run = r.apply := by
  funext input
  show SFST.runFrom r.toFinSFST ⟨[], Nat.zero_le _⟩ input
         = OSLRule.applyAux r [] input
  suffices h : ∀ w : {l : List β // l.length ≤ k - 1},
      SFST.runFrom r.toFinSFST w input = OSLRule.applyAux r w.val input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    change r.windowOutput w.val x
              ++ SFST.runFrom r.toFinSFST
                  ⟨lastN (k - 1) (w.val ++ r.windowOutput w.val x),
                   lastN_length_le _ _⟩ xs
         = r.windowOutput w.val x
              ++ OSLRule.applyAux r
                  (lastN (k - 1) (w.val ++ r.windowOutput w.val x)) xs
    exact congrArg _ (ih _)

/-- **Left-OSL ⊆ Left-Subsequential** (over a finite output alphabet).
The `[Fintype β]` matches [mohri-1997]'s finite-alphabet assumption
and lets the bounded output window serve as a finite state space. -/
theorem isLeftOutputStrictlyLocal_left_subsequential {k : ℕ} [Fintype β]
    {f : List α → List β} (h : IsLeftOutputStrictlyLocal k f) :
    IsLeftSubsequential f := by
  obtain ⟨r, hr⟩ := h
  have heq : r.toFinSFST.run = f := r.toFinSFST_run_eq_apply.trans hr
  exact heq ▸ r.toFinSFST.isLeftSubsequential

/-- **Right-OSL ⊆ Right-Subsequential**, derived from the Left- side via
the reverse-conjugation lemmas. The Right-OSL ↔ Left-OSL and
Right-Subseq ↔ Left-Subseq isomorphisms commute. -/
theorem isRightOutputStrictlyLocal_right_subsequential {k : ℕ} [Fintype β]
    {f : List α → List β} (h : IsRightOutputStrictlyLocal k f) :
    IsRightSubsequential f := by
  rw [isRightOutputStrictlyLocal_iff_left_reverse] at h
  rw [isRightSubsequential_iff_left_reverse]
  exact isLeftOutputStrictlyLocal_left_subsequential h

/-- **Direction-parameterised OSL ⊆ Subsequential umbrella**: in both
scan directions, OSL functions are subsequential. Delegates to the
Left- / Right- specialised theorems. -/
theorem isOutputStrictlyLocal_isSubsequential {d : Direction} {k : ℕ}
    [Fintype β] {f : List α → List β} (h : IsOutputStrictlyLocal d k f) :
    IsSubsequential d f := by
  cases d with
  | left => exact isLeftOutputStrictlyLocal_left_subsequential h
  | right => exact isRightOutputStrictlyLocal_right_subsequential h

end Subregular.Function
