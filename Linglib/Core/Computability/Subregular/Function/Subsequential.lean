/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Prod
import Linglib.Core.Computability.Subregular.Defs

/-!
# Subsequential Functions and Finite-State Transducers

A function `f : List α → List β` is **subsequential** when it is computed
by a deterministic finite-state transducer with state-based final output
[mohri-1997]. Subsequential functions form a proper subclass of the
regular relations (= rational functions) and a proper superclass of the
Output Strictly Local class [aksenova-rawski-graf-heinz-2020].

The class comes in **left** and **right** variants depending on whether
the FST consumes input left-to-right or right-to-left
[meinhardt-mai-bakovic-mccollum-2024]. The right-subsequential
class equals the image of the left-subsequential class under input/output
reversal: `f ∈ R-Subseq ↔ (List.reverse ∘ f ∘ List.reverse) ∈ L-Subseq`.

## Main definitions

* `Direction` — `.left` or `.right`; orientation of the FST scan.
* `SFST σ α β` — a deterministic finite-state transducer with state
  space `σ`, input alphabet `α`, output alphabet `β`, total transition
  emitting an output block, plus a state-indexed `finalOutput` emitted
  on termination.
* `SFST.run` — left-to-right pass: input → output.
* `SFST.runRight` — right-to-left pass via `List.reverse`-conjugation.
* `IsSubsequential d f` — predicate witness-style: some `SFST` computes
  `f` under direction `d`.

## What this file does NOT cover

* **Finite-state minimisation**, canonical forms, equivalence of SFSTs
  (Choffrut 1979, Mohri 1997 §5).
* **Two-way subsequential** functions (extended class for some
  reduplication patterns, Dolatian-Heinz 2020).
* **p-subsequential** functions (Mohri 1997 footnote 7) — handle
  variation/optionality with multiple outputs per input.
-/

namespace Subregular.Function

/-! ## Direction of FST scan

`Direction` (left or right) controls whether an FST consumes its input
head-first (left scan) or tail-first via `List.reverse` conjugation
(right scan). The two scan modes give rise to distinct function classes
isomorphic under reversal but not equal as subclasses of the regular
functions over un-reversed strings.

Re-exported from `Core/Direction.lean` so the classification predicates
below can use `.left`/`.right` unqualified. -/


/-- A **subsequential finite-state transducer** with state space `σ`,
input alphabet `α`, output alphabet `β`. The scan is total deterministic
— `step` always returns a next state and an output block — and the FST
emits `finalOutput` on terminating in any state.

This is the standard subsequential model of [mohri-1997]: a
deterministic FST with state-final outputs, computing partial functions
extended to total functions on `List α`. We model totality by requiring
`step` to be total; partial subsequential functions can be encoded by
adding a `none`/sink state. -/
structure SFST (σ α β : Type*) where
  /-- The starting state from which scans begin. -/
  initial : σ
  /-- Total deterministic transition: at each state, on each input
  symbol, move to a next state and emit a (possibly empty) output block. -/
  step : σ → α → σ × List β
  /-- Output emitted upon terminating in a given state. -/
  finalOutput : σ → List β

namespace SFST

variable {σ α β : Type*}

/-- Run the FST starting from a given state, accumulating output. The
scan walks left-to-right, emitting each transition's output block, and
finally appends the terminating state's `finalOutput`. -/
def runFrom (T : SFST σ α β) : σ → List α → List β
  | s, [] => T.finalOutput s
  | s, x :: xs =>
    (T.step s x).2 ++ runFrom T (T.step s x).1 xs

/-- Run the FST from its initial state. The standard left-subsequential
function denoted by `T`. -/
def run (T : SFST σ α β) (input : List α) : List β :=
  runFrom T T.initial input

/-- Right-subsequential application: reverse the input, run the FST
left-to-right, then reverse the output. The standard "right-to-left
scan" interpretation. -/
def runRight (T : SFST σ α β) (input : List α) : List β :=
  (T.run input.reverse).reverse

@[simp] lemma runFrom_nil (T : SFST σ α β) (s : σ) :
    T.runFrom s [] = T.finalOutput s := rfl

@[simp] lemma runFrom_cons (T : SFST σ α β) (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = (T.step s x).2 ++ T.runFrom (T.step s x).1 xs := rfl

@[simp] lemma run_nil (T : SFST σ α β) :
    T.run [] = T.finalOutput T.initial := rfl

@[simp] lemma runRight_nil (T : SFST σ α β) :
    T.runRight [] = (T.finalOutput T.initial).reverse := rfl

/-- Walk an SFST over an input list **without** appending the final-state
output. Returns the terminating state and the concatenation of all
transition outputs along the way.

Useful as a building block for product constructions (e.g. composition
closure): the consumer FST may need to see only the transition outputs
of the producer, not the producer's final flush. -/
def runOnList (T : SFST σ α β) : σ → List α → σ × List β
  | s, [] => (s, [])
  | s, x :: xs =>
    let (s', out) := T.step s x
    let (s'', rest) := T.runOnList s' xs
    (s'', out ++ rest)

@[simp] lemma runOnList_nil (T : SFST σ α β) (s : σ) :
    T.runOnList s [] = (s, []) := rfl

@[simp] lemma runOnList_cons (T : SFST σ α β) (s : σ) (x : α) (xs : List α) :
    T.runOnList s (x :: xs) =
      ((T.runOnList (T.step s x).1 xs).1,
       (T.step s x).2 ++ (T.runOnList (T.step s x).1 xs).2) := rfl

/-- The relationship between `runFrom` and `runOnList`: `runFrom` is
`runOnList` followed by appending the final-state output. -/
lemma runFrom_eq_runOnList (T : SFST σ α β) (s : σ) (xs : List α) :
    T.runFrom s xs =
      (T.runOnList s xs).2 ++ T.finalOutput (T.runOnList s xs).1 := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [runFrom_cons, runOnList_cons]
    rw [ih]
    rw [List.append_assoc]

/-- `runOnList` distributes over input concatenation: walking on `xs ++ ys`
equals walking on `xs` then on `ys` from the resulting state, with
outputs concatenated. -/
lemma runOnList_append (T : SFST σ α β) (s : σ) (xs ys : List α) :
    T.runOnList s (xs ++ ys) =
      ((T.runOnList (T.runOnList s xs).1 ys).1,
       (T.runOnList s xs).2 ++ (T.runOnList (T.runOnList s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, runOnList_cons, ih]
    rw [List.append_assoc]

/-- `runFrom` distributes over input concatenation: walking on `xs ++ ys`
equals walking the prefix via `runOnList` (no final emission yet), then
running `runFrom` from the resulting state on `ys` (which DOES include
the final emission). -/
lemma runFrom_append (T : SFST σ α β) (s : σ) (xs ys : List α) :
    T.runFrom s (xs ++ ys) =
      (T.runOnList s xs).2 ++ T.runFrom (T.runOnList s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, runFrom_cons, runOnList_cons, ih]
    rw [List.append_assoc]

end SFST

/-! ### State-space transfer

Transferring an SFST along a state-space equivalence preserves its
`run` function. The headline use case is bringing a universe-polymorphic
state down to `Fin n` (universe `Type 0`) via `Fintype.equivFin`, which
lets the universe-polymorphic constructions in `ISL.lean` / `OSL.lean`
witness the `Type 0`-state existential of `IsLeftSubsequential` /
`IsRightSubsequential`. -/

namespace SFST

variable {σ τ α β : Type*}

/-- Transfer an SFST along a state-space equivalence `σ ≃ τ`. Replaces
each state-valued field with the corresponding `τ`-valued one via the
equivalence. -/
def transferEquiv (T : SFST σ α β) (e : σ ≃ τ) : SFST τ α β where
  initial := e T.initial
  step t x :=
    let (s', out) := T.step (e.symm t) x
    (e s', out)
  finalOutput t := T.finalOutput (e.symm t)

lemma transferEquiv_runFrom (T : SFST σ α β) (e : σ ≃ τ)
    (s : σ) (xs : List α) :
    (T.transferEquiv e).runFrom (e s) xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil =>
    show T.finalOutput (e.symm (e s)) = T.finalOutput s
    rw [e.symm_apply_apply]
  | cons x xs ih =>
    show (T.step (e.symm (e s)) x).2
            ++ (T.transferEquiv e).runFrom (e (T.step (e.symm (e s)) x).1) xs
         = (T.step s x).2 ++ T.runFrom (T.step s x).1 xs
    rw [e.symm_apply_apply, ih]

/-- The transferred SFST computes the same string function as the original. -/
@[simp] theorem transferEquiv_run (T : SFST σ α β) (e : σ ≃ τ) :
    (T.transferEquiv e).run = T.run := by
  funext xs
  show (T.transferEquiv e).runFrom (e T.initial) xs = T.runFrom T.initial xs
  exact T.transferEquiv_runFrom e _ _

end SFST

/-! ### Composition

Subsequential functions are closed under composition (Mohri 1997 §3,
back to Schützenberger and Choffrut). This is the load-bearing fact
that makes the Heinz-Lai 2013 Weakly Deterministic class definition
work (compositions of two subsequentials).

Construction: the **product SFST** with state `σ_f × σ_g` threads both
machines, where the consumer FST `T_g` walks over each output block
emitted by the producer FST `T_f`. -/

namespace SFST

variable {σf σg α β γ : Type*}

/-- Compose two SFSTs: `T_f : SFST σ_f α β` and `T_g : SFST σ_g β γ`
yield an SFST `σ_f × σ_g → α → γ` whose `run` computes `T_g.run ∘ T_f.run`.

State threading: each input symbol triggers one `T_f` step (which may
emit a multi-symbol β block); `T_g` then walks through that block via
`runOnList`, advancing its state. The combined `finalOutput` runs
`T_f.finalOutput` through `T_g` (including `T_g`'s own final flush). -/
def compose (Tg : SFST σg β γ) (Tf : SFST σf α β) : SFST (σf × σg) α γ where
  initial := (Tf.initial, Tg.initial)
  step := fun s x =>
    let (sf', block) := Tf.step s.1 x
    let (sg', out) := Tg.runOnList s.2 block
    ((sf', sg'), out)
  finalOutput := fun s =>
    let (sg', out) := Tg.runOnList s.2 (Tf.finalOutput s.1)
    out ++ Tg.finalOutput sg'

/-- **Compose's `runFrom` agrees with sequential `runFrom`s**. The product
SFST `compose Tg Tf` walks `Tf` over the input from `s.1`, threading
each emitted block through `Tg` from `s.2`. -/
theorem compose_runFrom (Tg : SFST σg β γ) (Tf : SFST σf α β)
    (s : σf × σg) (xs : List α) :
    (Tg.compose Tf).runFrom s xs = Tg.runFrom s.2 (Tf.runFrom s.1 xs) := by
  induction xs generalizing s with
  | nil =>
    -- Both sides reduce to the final-output handling.
    show (Tg.compose Tf).finalOutput s = Tg.runFrom s.2 (Tf.finalOutput s.1)
    show (Tg.runOnList s.2 (Tf.finalOutput s.1)).2
            ++ Tg.finalOutput (Tg.runOnList s.2 (Tf.finalOutput s.1)).1
         = Tg.runFrom s.2 (Tf.finalOutput s.1)
    rw [SFST.runFrom_eq_runOnList]
  | cons x xs ih =>
    show (Tg.compose Tf).runFrom s (x :: xs) = Tg.runFrom s.2 (Tf.runFrom s.1 (x :: xs))
    rw [SFST.runFrom_cons, SFST.runFrom_cons]
    show (Tg.runOnList s.2 (Tf.step s.1 x).2).2
           ++ (Tg.compose Tf).runFrom
                ((Tf.step s.1 x).1, (Tg.runOnList s.2 (Tf.step s.1 x).2).1) xs
         = Tg.runFrom s.2
              ((Tf.step s.1 x).2 ++ Tf.runFrom (Tf.step s.1 x).1 xs)
    rw [SFST.runFrom_append, ih]

end SFST

/-! ### Subsequential classification predicates

The witness-style predicates below follow mathlib's `Language.IsRegular`
shape: the state space `σ` is existentially quantified at `Type` with a
`Fintype σ` instance, while the alphabets `α β` are universe-polymorphic
at `Type*`. The `Fintype` constraint matches the source literature
([mohri-1997] §3; [heinz-lai-2013]; [chandlee-2014]),
where every SFST has finitely many states by definition, and also lets
the universe parameter for state collapse cleanly without `universe`
declarations or `ULift` coercions.

Constructor lemmas (`SFST.isLeftSubsequential`, `SFST.isRightSubsequential`
below) hide the existential-over-types shape so future redesigns
(e.g. to a Myhill–Nerode finite-index characterization with σ ≃ Fin n)
won't touch consumer sites. Downstream ISL/OSL inclusion theorems take
`[Fintype α]` / `[Fintype β]` and use a bounded-window finite state to
witness the predicate (`Function/{ISL,OSL}.lean`). -/

/-- A function `f : List α → List β` is **left-subsequential** iff some
SFST with a finite state space computes it via left-to-right scan. The
`Fintype σ` constraint matches the source literature
([mohri-1997]; [chandlee-2014]). -/
def IsLeftSubsequential {α β : Type*} (f : List α → List β) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ T : SFST σ α β, T.run = f

/-- A function `f : List α → List β` is **right-subsequential** iff some
SFST with a finite state space computes it via right-to-left scan
(`runRight`). -/
def IsRightSubsequential {α β : Type*} (f : List α → List β) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ T : SFST σ α β, T.runRight = f

/-- A function `f : List α → List β` is **subsequential in direction `d`**
iff some finite-state SFST computes it via the corresponding scan
direction. Direction-parameterised umbrella; concrete claims should
typically use one of `IsLeftSubsequential` / `IsRightSubsequential`
directly for clarity. -/
def IsSubsequential {α β : Type*} (d : Direction) (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftSubsequential f
  | .right => IsRightSubsequential f

@[simp] lemma isSubsequential_left {α β : Type*} (f : List α → List β) :
    IsSubsequential .left f ↔ IsLeftSubsequential f := Iff.rfl

@[simp] lemma isSubsequential_right {α β : Type*} (f : List α → List β) :
    IsSubsequential .right f ↔ IsRightSubsequential f := Iff.rfl

/-- **Constructor lemma**: every finite-state SFST witnesses
`IsLeftSubsequential` for its `run` function. Consumers should use
`T.isLeftSubsequential` rather than constructing
`⟨σ, inferInstance, T, rfl⟩` quadruples directly — this hides the
existential-over-types shape of the predicate, so future redesigns
(e.g. to a Myhill–Nerode finite-index characterization with σ ≃ Fin n)
only need to update this lemma's body, not every consumer call site.

The state space `σ` is accepted at arbitrary `Type*`; the witness is
brought down to `Fin (Fintype.card σ)` (which lives in `Type`) via
`SFST.transferEquiv` and `Fintype.equivFin`. This lets bounded-window
ISL/OSL states at the alphabet's universe witness the predicate. -/
theorem SFST.isLeftSubsequential {σ : Type*} [Fintype σ] {α β : Type*}
    (T : SFST σ α β) : IsLeftSubsequential T.run := by
  refine ⟨Fin (Fintype.card σ), inferInstance,
          T.transferEquiv (Fintype.equivFin σ), ?_⟩
  exact T.transferEquiv_run _

/-- **Constructor lemma**: every finite-state SFST witnesses
`IsRightSubsequential` for its `runRight` function. See
`SFST.isLeftSubsequential` for rationale. -/
theorem SFST.isRightSubsequential {σ : Type*} [Fintype σ] {α β : Type*}
    (T : SFST σ α β) : IsRightSubsequential T.runRight := by
  refine ⟨Fin (Fintype.card σ), inferInstance,
          T.transferEquiv (Fintype.equivFin σ), ?_⟩
  funext xs
  show ((T.transferEquiv _).run xs.reverse).reverse = (T.run xs.reverse).reverse
  rw [T.transferEquiv_run]

/-- **Reverse-conjugation lemma**: a function is Right-Subsequential iff
its reverse-conjugate is Left-Subsequential. The two classes are
isomorphic via the involution `f ↦ List.reverse ∘ f ∘ List.reverse`. -/
theorem isRightSubsequential_iff_left_reverse {α β : Type*}
    (f : List α → List β) :
    IsRightSubsequential f
      ↔ IsLeftSubsequential (fun xs => (f xs.reverse).reverse) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, _, T, hT⟩
    refine ⟨σ, inferInstance, T, ?_⟩
    funext xs
    have h := congrFun hT xs.reverse
    -- h : T.runRight xs.reverse = f xs.reverse
    -- T.runRight xs.reverse = (T.run xs.reverse.reverse).reverse = (T.run xs).reverse
    show T.run xs = (f xs.reverse).reverse
    have : (T.run xs).reverse = f xs.reverse := by
      rw [SFST.runRight, List.reverse_reverse] at h
      exact h
    rw [← this, List.reverse_reverse]
  · rintro ⟨σ, _, T, hT⟩
    refine ⟨σ, inferInstance, T, ?_⟩
    funext xs
    show (T.run xs.reverse).reverse = f xs
    have h := congrFun hT xs.reverse
    -- h : T.run xs.reverse = (f xs.reverse.reverse).reverse = (f xs).reverse
    rw [List.reverse_reverse] at h
    rw [h, List.reverse_reverse]

/-- **Subsequential functions are closed under composition** (Mohri 1997
§3, originally Schützenberger and Choffrut). The load-bearing fact that
makes the Heinz-Lai 2013 Weakly Deterministic class definition work as
the composition of two subsequential functions reading from opposite
directions. The product state `σf × σg` inherits `Fintype` automatically
from `Mathlib.Data.Fintype.Prod`. -/
theorem IsLeftSubsequential.comp {α β γ : Type*}
    {g : List β → List γ} (hg : IsLeftSubsequential g)
    {f : List α → List β} (hf : IsLeftSubsequential f) :
    IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σf, _, Tf, hTf⟩ := hf
  obtain ⟨σg, _, Tg, hTg⟩ := hg
  refine ⟨σf × σg, inferInstance, Tg.compose Tf, ?_⟩
  funext xs
  show (Tg.compose Tf).run xs = g (f xs)
  show (Tg.compose Tf).runFrom (Tf.initial, Tg.initial) xs = g (f xs)
  rw [SFST.compose_runFrom]
  show Tg.runFrom Tg.initial (Tf.runFrom Tf.initial xs) = g (f xs)
  show Tg.run (Tf.run xs) = g (f xs)
  rw [hTf, hTg]

/-- **Right-Subsequential closure under composition**, derived from the
Left- counterpart via `isRightSubsequential_iff_left_reverse`. The
reverse-conjugate of a composition equals the composition of
reverse-conjugates, so Left-Subseq closure carries over to Right-Subseq. -/
theorem IsRightSubsequential.comp {α β γ : Type*}
    {g : List β → List γ} (hg : IsRightSubsequential g)
    {f : List α → List β} (hf : IsRightSubsequential f) :
    IsRightSubsequential (g ∘ f) := by
  rw [isRightSubsequential_iff_left_reverse] at hg hf ⊢
  have h := hg.comp hf
  convert h using 1
  funext xs
  show ((g ∘ f) xs.reverse).reverse
      = ((fun ys => (g ys.reverse).reverse) ∘ (fun ys => (f ys.reverse).reverse)) xs
  simp [Function.comp_apply, List.reverse_reverse]

/-- **Direction-parameterised composition closure**: both Left- and
Right-Subsequential functions are closed under composition. Delegates to
`IsLeftSubsequential.comp` / `IsRightSubsequential.comp`. -/
theorem IsSubsequential.comp {α β γ : Type*} {d : Direction}
    {g : List β → List γ} (hg : IsSubsequential d g)
    {f : List α → List β} (hf : IsSubsequential d f) :
    IsSubsequential d (g ∘ f) := by
  cases d with
  | left => exact IsLeftSubsequential.comp hg hf
  | right => exact IsRightSubsequential.comp hg hf

end Subregular.Function
