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
output block depends only on the **last k − 1 output symbols** plus the
current input symbol @cite{chandlee-eyraud-heinz-2015}. The OSL class
captures iterative spreading processes — patterns where the spreading
feature value of segment *i* depends on the spreading feature value of
segment *i − 1* (already determined by the OSL function), not on the
underlying input value.

Like Subsequential, OSL has **left** and **right** variants depending on
scan direction. Left-OSL: each output block depends on previous output
(processed left-to-right). Right-OSL: each output block depends on
following output (process right-to-left).

OSL is **properly contained** in Subsequential and **properly contains**
ISL @cite{aksenova-rawski-graf-heinz-2020}. The proper containments are:
* ISL ⊊ OSL: many iterative spreading patterns (e.g. progressive nasal
  harmony) are OSL but not ISL — output decisions feed forward.
* OSL ⊊ Subsequential: subsequential FSTs can carry richer state than
  bounded output windows; iterative-with-blocking patterns may need this.

Bidirectional iterative harmony patterns (Maasai, Turkana ATR harmony)
are above all unidirectional OSL classes — they need the Weakly
Deterministic class @cite{heinz-lai-2013} @cite{meinhardt-mai-bakovic-mccollum-2024}.

## Main definitions

* `OSLRule k α β` — a k-OSL rule: a window-based output function
  `(List β) → α → List β` that consumes the (k − 1)-symbol output
  context plus the current input symbol and emits an output block.
* `OSLRule.apply r` — the induced string function `List α → List β`,
  threading the output window left-to-right.
* `IsLeftOutputStrictlyLocal k f`, `IsRightOutputStrictlyLocal k f`,
  `IsOutputStrictlyLocal d k f` — Direction-parameterised predicates.
-/

namespace Core.Computability.Subregular.Function

variable {α β : Type}

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

end Core.Computability.Subregular.Function
