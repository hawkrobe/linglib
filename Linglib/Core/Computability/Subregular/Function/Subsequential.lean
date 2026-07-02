/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Core.Computability.Subregular.Function.Direction

/-!
# Subsequential Functions and Finite-State Transducers

A function `f : List α → List β` is *subsequential* when it is computed by a
deterministic finite-state transducer with state-based final output
[mohri-1997]. Subsequential functions form a proper subclass of the rational
functions (the functional regular relations).

The class has *left* and *right* variants according to scan direction; the two
are isomorphic under input/output reversal (`f` is right-subsequential iff
`List.reverse ∘ f ∘ List.reverse` is left-subsequential).

## Main definitions

* `SFST α β σ`: a deterministic FST with states `σ`, input alphabet `α`,
  output alphabet `β`, a total output-emitting transition, and a state-indexed
  `finalOutput` emitted on termination.
* `SFST.run`, `SFST.runRight`: the left-to-right and right-to-left passes.
* `IsLeftSubsequential f`, `IsRightSubsequential f`: `f` is computed by some
  finite-state `SFST` scanning in that direction.
* `IsSubsequential d f`: direction-parameterised umbrella over the two.

## Main theorems

* `IsLeftSubsequential.comp`, `IsRightSubsequential.comp`, `IsSubsequential.comp`:
  subsequential functions are closed under composition (Schützenberger–Choffrut,
  [mohri-1997]) — the fact that makes the weakly-deterministic class well-defined.
* `isRightSubsequential_iff_left_reverse`: the left and right classes are
  isomorphic via reverse-conjugation.

## Implementation notes

`SFST` models the *total* subsequential functions: `step` is total, so `run`
is a total function on `List α`. Partial subsequential functions can be encoded
by adding a sink state.

## TODO

* Finite-state minimisation, canonical forms, and SFST equivalence (Choffrut,
  [mohri-1997]).
* Two-way subsequential functions (two-way deterministic transducers).
* p-subsequential functions [mohri-1997] (multiple outputs per input).
-/

namespace Subregular

/-- A *subsequential finite-state transducer*: a deterministic FST with state
space `σ`, input alphabet `α`, output alphabet `β`, and state-final outputs
[mohri-1997]. The transition `step` is total, so the machine computes a total
function `List α → List β`. -/
structure SFST (α β σ : Type*) where
  /-- Starting state. -/
  start : σ
  /-- Total deterministic transition: move to a next state and emit a
  (possibly empty) output block. -/
  step : σ → α → σ × List β
  /-- Output emitted on terminating in a given state. -/
  finalOutput : σ → List β

namespace SFST

variable {σ α β : Type*} (T : SFST α β σ)

/-- `T.runFrom s x` runs `T` from state `s`, concatenating each step's output
block and finally `T.finalOutput` of the terminating state. -/
def runFrom : σ → List α → List β
  | s, [] => T.finalOutput s
  | s, x :: xs => (T.step s x).2 ++ runFrom (T.step s x).1 xs

/-- `T.run x` runs `T` from its start state; the left-subsequential function
`T` denotes. -/
def run : List α → List β := T.runFrom T.start

/-- `T.runRight x` runs `T` right-to-left: reverse the input, run, reverse the
output. -/
def runRight (input : List α) : List β := (T.run input.reverse).reverse

@[simp] lemma runFrom_nil (s : σ) : T.runFrom s [] = T.finalOutput s := rfl

@[simp] lemma runFrom_cons (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = (T.step s x).2 ++ T.runFrom (T.step s x).1 xs := rfl

@[simp] lemma run_nil : T.run [] = T.finalOutput T.start := rfl

@[simp] lemma runRight_nil : T.runRight [] = (T.finalOutput T.start).reverse := rfl

/-- `T.runOnList s x` walks `T` from `s` without the final flush: the terminating
state with the concatenated per-step outputs. Building block for `compose`. -/
def runOnList : σ → List α → σ × List β
  | s, [] => (s, [])
  | s, x :: xs =>
    let (s', out) := T.step s x
    Prod.map id (out ++ ·) (runOnList s' xs)

@[simp] lemma runOnList_nil (s : σ) : T.runOnList s [] = (s, []) := rfl

@[simp] lemma runOnList_cons (s : σ) (x : α) (xs : List α) :
    T.runOnList s (x :: xs) =
      ((T.runOnList (T.step s x).1 xs).1,
       (T.step s x).2 ++ (T.runOnList (T.step s x).1 xs).2) := rfl

/-- The relationship between `runFrom` and `runOnList`: `runFrom` is
`runOnList` followed by appending the final-state output. -/
lemma runFrom_eq_runOnList (s : σ) (xs : List α) :
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
lemma runOnList_append (s : σ) (xs ys : List α) :
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
lemma runFrom_append (s : σ) (xs ys : List α) :
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

variable {σ τ α β : Type*} (T : SFST α β σ)

/-- Transfer an SFST along a state-space equivalence `σ ≃ τ`. Replaces
each state-valued field with the corresponding `τ`-valued one via the
equivalence. -/
def transferEquiv (e : σ ≃ τ) : SFST α β τ where
  start := e T.start
  step t x :=
    let (s', out) := T.step (e.symm t) x
    (e s', out)
  finalOutput t := T.finalOutput (e.symm t)

lemma transferEquiv_runFrom (e : σ ≃ τ)
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
@[simp] theorem transferEquiv_run (e : σ ≃ τ) :
    (T.transferEquiv e).run = T.run := by
  funext xs
  show (T.transferEquiv e).runFrom (e T.start) xs = T.runFrom T.start xs
  exact T.transferEquiv_runFrom e _ _

end SFST

/-! ### Composition

Subsequential functions are closed under composition ([mohri-1997],
back to Schützenberger and Choffrut). This is the load-bearing fact
that makes the weakly-deterministic class (compositions of two
subsequentials) well-defined.

Construction: the *product SFST* with state `σ_f × σ_g` threads both
machines, where the consumer FST `T_g` walks over each output block
emitted by the producer FST `T_f`. -/

namespace SFST

variable {σf σg α β γ : Type*}

/-- Compose two SFSTs: `T_f : SFST α β σ_f` and `T_g : SFST β γ σ_g`
yield an SFST with state `σ_f × σ_g` whose `run` computes `T_g.run ∘ T_f.run`.

State threading: each input symbol triggers one `T_f` step (which may
emit a multi-symbol β block); `T_g` then walks through that block via
`runOnList`, advancing its state. The combined `finalOutput` runs
`T_f.finalOutput` through `T_g` (including `T_g`'s own final flush). -/
def compose (Tg : SFST β γ σg) (Tf : SFST α β σf) : SFST α γ (σf × σg) where
  start := (Tf.start, Tg.start)
  step s x :=
    let (sf', block) := Tf.step s.1 x
    let (sg', out) := Tg.runOnList s.2 block
    ((sf', sg'), out)
  finalOutput s :=
    let (sg', out) := Tg.runOnList s.2 (Tf.finalOutput s.1)
    out ++ Tg.finalOutput sg'

/-- `compose`'s `runFrom` agrees with sequential `runFrom`s: the product
SFST `compose Tg Tf` walks `Tf` over the input from `s.1`, threading
each emitted block through `Tg` from `s.2`. -/
theorem compose_runFrom (Tg : SFST β γ σg) (Tf : SFST α β σf)
    (s : σf × σg) (xs : List α) :
    (Tg.compose Tf).runFrom s xs = Tg.runFrom s.2 (Tf.runFrom s.1 xs) := by
  induction xs generalizing s with
  | nil => simp [SFST.compose, SFST.runFrom_eq_runOnList]
  | cons x xs ih => rw [SFST.runFrom_cons, SFST.runFrom_cons, SFST.runFrom_append, ih]; rfl

end SFST

/-! ### Subsequential classification predicates

The witness-style predicates below follow mathlib's `Language.IsRegular`
shape: the state space `σ` is existentially quantified at `Type` with a
`Fintype σ` instance, while the alphabets `α β` are universe-polymorphic
at `Type*`. The `Fintype` constraint matches the source literature
([mohri-1997]), where every SFST has finitely many states by definition,
and also lets the universe parameter for state collapse cleanly without
`universe` declarations or `ULift` coercions.

Constructor lemmas (`SFST.isLeftSubsequential`, `SFST.isRightSubsequential`
below) hide the existential-over-types shape so future redesigns
(e.g. to a Myhill–Nerode finite-index characterization with σ ≃ Fin n)
won't touch consumer sites. Downstream ISL/OSL inclusion theorems take
`[Fintype α]` / `[Fintype β]` and use a bounded-window finite state to
witness the predicate (`Function/{ISL,OSL}.lean`). -/

variable {α β γ : Type*}

/-- A function `f : List α → List β` is *left-subsequential* iff some
SFST with a finite state space computes it via left-to-right scan. The
`Fintype σ` constraint matches the source literature [mohri-1997]. -/
def IsLeftSubsequential (f : List α → List β) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ T : SFST α β σ, T.run = f

/-- A function `f : List α → List β` is *right-subsequential* iff some
SFST with a finite state space computes it via right-to-left scan
(`runRight`). -/
def IsRightSubsequential (f : List α → List β) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ T : SFST α β σ, T.runRight = f

/-- A function `f : List α → List β` is *subsequential in direction `d`*
iff some finite-state SFST computes it via the corresponding scan
direction. Direction-parameterised umbrella; concrete claims should
typically use one of `IsLeftSubsequential` / `IsRightSubsequential`
directly for clarity. -/
def IsSubsequential (d : Direction) (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftSubsequential f
  | .right => IsRightSubsequential f

@[simp] lemma isSubsequential_left (f : List α → List β) :
    IsSubsequential .left f ↔ IsLeftSubsequential f := Iff.rfl

@[simp] lemma isSubsequential_right (f : List α → List β) :
    IsSubsequential .right f ↔ IsRightSubsequential f := Iff.rfl

/-- Every finite-state SFST witnesses `IsLeftSubsequential` for its `run`.
Consumers use `T.isLeftSubsequential` instead of building the existential
quadruple, so a redesign of `IsLeftSubsequential` touches only this lemma. The
arbitrary-`Type*` state is brought down to `Fin (Fintype.card σ)` via
`SFST.transferEquiv` and `Fintype.equivFin`. -/
theorem SFST.isLeftSubsequential {σ : Type*} [Fintype σ] (T : SFST α β σ) :
    IsLeftSubsequential T.run :=
  ⟨Fin (Fintype.card σ), inferInstance,
    T.transferEquiv (Fintype.equivFin σ), T.transferEquiv_run _⟩

/-- Every finite-state SFST witnesses `IsRightSubsequential` for its `runRight`.
See `SFST.isLeftSubsequential` for rationale. -/
theorem SFST.isRightSubsequential {σ : Type*} [Fintype σ] (T : SFST α β σ) :
    IsRightSubsequential T.runRight :=
  ⟨Fin (Fintype.card σ), inferInstance, T.transferEquiv (Fintype.equivFin σ), by
    funext xs; simp [SFST.runRight]⟩

/-- A function is Right-Subsequential iff its reverse-conjugate is
Left-Subsequential: the two classes are isomorphic via the involution
`f ↦ List.reverse ∘ f ∘ List.reverse`. -/
theorem isRightSubsequential_iff_left_reverse (f : List α → List β) :
    IsRightSubsequential f
      ↔ IsLeftSubsequential (fun xs => (f xs.reverse).reverse) := by
  constructor
  · rintro ⟨σ, _, T, rfl⟩
    exact ⟨σ, inferInstance, T, by funext xs; simp [SFST.runRight]⟩
  · rintro ⟨σ, _, T, hT⟩
    exact ⟨σ, inferInstance, T, by funext xs; simp [SFST.runRight, hT]⟩

/-- **Bounded delay**: a left-subsequential function can withhold only boundedly
much output. On any input `u`, everything but the terminating state's final
output is already emitted by the transitions — a prefix `p` of `f u` shared with
`f (u ++ v)` for *every* continuation `v` — so the withheld suffix `su` is at
most the longest state-final output `N`. This is the finite-look-ahead content of
determinism ([mohri-1997]) and the engine of every non-subsequentiality proof:
exhibit inputs `u`, `u ++ v` whose images diverge earlier than `(f u).length - N`
(e.g. unbounded tonal plateauing, [jardine-2016]). -/
theorem IsLeftSubsequential.bounded_delay {f : List α → List β}
    (hf : IsLeftSubsequential f) :
    ∃ N : ℕ, ∀ u v : List α, ∃ p su sv : List β,
      f u = p ++ su ∧ f (u ++ v) = p ++ sv ∧ su.length ≤ N := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨Finset.univ.sup fun s => (T.finalOutput s).length, fun u v =>
    ⟨(T.runOnList T.start u).2, T.finalOutput (T.runOnList T.start u).1,
      T.runFrom (T.runOnList T.start u).1 v, T.runFrom_eq_runOnList T.start u,
      T.runFrom_append T.start u v,
      Finset.le_sup (f := fun s => (T.finalOutput s).length) (Finset.mem_univ _)⟩⟩

/-- **Divergence criterion**: `f` is not left-subsequential if, for every candidate delay
bound `N`, some input `u` and continuation `v` have images disagreeing at a position more
than `N` symbols above the end of `f u` — inside the prefix a bounded-delay machine must
already have emitted. The working form of `bounded_delay` for impossibility proofs
(unbounded tonal plateauing [jardine-2016], sour-grapes harmony [heinz-lai-2013]). -/
theorem not_isLeftSubsequential_of_diverging {f : List α → List β}
    (h : ∀ N, ∃ (u v : List α) (i : ℕ),
      i + N < (f u).length ∧ (f u)[i]? ≠ (f (u ++ v))[i]?) :
    ¬ IsLeftSubsequential f := by
  intro hf
  obtain ⟨N, hN⟩ := hf.bounded_delay
  obtain ⟨u, v, i, hi, hne⟩ := h N
  obtain ⟨p, su, sv, hu, huv, hsu⟩ := hN u v
  have hip : i < p.length := by
    have := congrArg List.length hu
    rw [List.length_append] at this
    omega
  rw [hu, huv, List.getElem?_append_left hip, List.getElem?_append_left hip] at hne
  exact hne rfl

/-- Subsequential functions are closed under composition ([mohri-1997],
originally Schützenberger and Choffrut) — the load-bearing fact that makes
the weakly-deterministic class (composition of two subsequential functions
reading from opposite directions) well-defined. The product state `σf × σg`
inherits `Fintype` from `Mathlib.Data.Fintype.Prod`. -/
theorem IsLeftSubsequential.comp
    {g : List β → List γ} (hg : IsLeftSubsequential g)
    {f : List α → List β} (hf : IsLeftSubsequential f) :
    IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σf, _, Tf, rfl⟩ := hf
  obtain ⟨σg, _, Tg, rfl⟩ := hg
  refine ⟨σf × σg, inferInstance, Tg.compose Tf, funext fun xs => ?_⟩
  show (Tg.compose Tf).runFrom (Tf.start, Tg.start) xs = Tg.run (Tf.run xs)
  rw [SFST.compose_runFrom]; rfl

/-- Right-Subsequential closure under composition, derived from the Left-
counterpart via `isRightSubsequential_iff_left_reverse`: the reverse-conjugate
of a composition is the composition of reverse-conjugates. -/
theorem IsRightSubsequential.comp
    {g : List β → List γ} (hg : IsRightSubsequential g)
    {f : List α → List β} (hf : IsRightSubsequential f) :
    IsRightSubsequential (g ∘ f) := by
  rw [isRightSubsequential_iff_left_reverse] at hg hf ⊢
  simpa [Function.comp_def, List.reverse_reverse] using hg.comp hf

/-- Direction-parameterised composition closure: both Left- and
Right-Subsequential functions are closed under composition. Delegates to
`IsLeftSubsequential.comp` / `IsRightSubsequential.comp`. -/
theorem IsSubsequential.comp {d : Direction}
    {g : List β → List γ} (hg : IsSubsequential d g)
    {f : List α → List β} (hf : IsSubsequential d f) :
    IsSubsequential d (g ∘ f) := by
  cases d with
  | left => exact IsLeftSubsequential.comp hg hf
  | right => exact IsRightSubsequential.comp hg hf

end Subregular
