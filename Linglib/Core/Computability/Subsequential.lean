/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Subsequential`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Core.Computability.Mealy
import Linglib.Core.Data.Fintype.Transfer
import Linglib.Core.Data.List.DropRight
import Linglib.Core.Computability.Direction

/-!
# Subsequential functions and finite-state transducers

A function `f : List α → List β` is *subsequential* when it is computed by a
deterministic finite-state transducer with state-final output [schutzenberger-1977]
[mohri-1997]. Subsequential functions form a proper subclass of the rational functions
(the functional rational relations) [filiot-reynier-2016]. The class has *left* and
*right* variants by scan direction, isomorphic under reverse-conjugation.

## Main definitions

* `SubsequentialTransducer σ α β`: the machine; `run` and `runRight` are its two passes
* `SubsequentialTransducer.comp`: the product machine
* `SubsequentialTransducer.ofWindow`: the sliding-window transducer
* `Mealy.toSubsequentialTransducer`, `SubsequentialTransducer.toMealy`: mutually inverse
  views of the synchronous machines as singleton-output, empty-flush block transducers
* `IsLeftSubsequential`, `IsRightSubsequential`, `IsSubsequential d`: computability by a
  finite-state transducer in the given scan direction

## Main theorems

* `IsLeftSubsequential.comp`: closure under composition, by the product construction
  [mohri-1997]
* `isRightSubsequential_iff_left_reverse`: the left and right classes are
  reverse-conjugate
* `isLeftSubsequential_iff`, `isRightSubsequential_iff`: the universe-polymorphic
  characterizations
* `IsMealyComputable.isLeftSubsequential`: the synchronous class sits inside the block
  class
* `IsLeftSubsequential.bounded_delay`: at most a bounded suffix is withheld

## Implementation notes

The name follows [choffrut-1977] and [mohri-1997]: *sequential* without state-final
output, *subsequential* with. [sakarovitch-2009] instead calls this class *sequential*
(and the empty-flush case *pure sequential*), flagging his own usage as unconventional
(cf. [bruyere-reutenauer-1999]); we keep the Choffrut spelling. `Mealy` is the
letter-to-letter case.

`step` is total and every input is accepted, so `run` models the *total* subsequential
functions only — a sink state does not recover partiality, since out-of-domain inputs
still emit output. On empty input `run` emits `finalOutput start`; the initial-output
function of [sakarovitch-2009] is omitted. `run` and `runFrom` keep disjoint simp
normal forms, as with `DFA.eval`/`DFA.evalFrom`: switch via `simp [run]`.

## TODO

* Choffrut's theorem [choffrut-1977]: a rational function is subsequential iff it has
  bounded variation, decidably via the twinning condition; `bounded_delay` is a much
  weaker consequence. Onward, canonical forms and minimization.
* Two-way transducers; p-subsequential functions [mohri-1997].
-/

namespace Subregular

variable {σ α β : Type*}

/-- A subsequential finite-state transducer is a set of states (`σ`), a starting state
(`start`), a transition function (`step`), a per-symbol output function (`output`) and
a state-final output (`finalOutput`). -/
structure SubsequentialTransducer (σ α β : Type*) where
  /-- Starting state. -/
  start : σ
  /-- Transition function. -/
  step : σ → α → σ
  /-- The block of output symbols emitted on reading an input symbol in a state. -/
  output : σ → α → List β
  /-- Output emitted on terminating in a state. -/
  finalOutput : σ → List β

instance [Inhabited σ] : Inhabited (SubsequentialTransducer σ α β) :=
  ⟨⟨default, fun s _ => s, fun _ _ => [], fun _ => []⟩⟩

namespace SubsequentialTransducer

variable (T : SubsequentialTransducer σ α β)

/-- `T.stateAfter s x` is the state reached from `s` after consuming the input `x`. -/
def stateAfter (s : σ) : List α → σ := List.foldl T.step s

/-- `T.emitted s x` is the output emitted while consuming the input `x` from the
state `s`, without the final flush. -/
def emitted : σ → List α → List β
  | _, [] => []
  | s, x :: xs => T.output s x ++ emitted (T.step s x) xs

/-- `T.runFrom s x` runs `T` on the input `x` from the state `s`: the emitted output
followed by the final flush. -/
def runFrom (s : σ) (xs : List α) : List β :=
  T.emitted s xs ++ T.finalOutput (T.stateAfter s xs)

/-- `T.run x` runs `T` on the input `x` from the state `T.start`. -/
def run : List α → List β := T.runFrom T.start

/-- `T.runRight x` runs `T` right-to-left on the input `x`. -/
def runRight (xs : List α) : List β := (T.run xs.reverse).reverse

@[simp] theorem stateAfter_nil (s : σ) : T.stateAfter s [] = s := rfl
@[simp] theorem stateAfter_cons (s : σ) (x : α) (xs : List α) :
    T.stateAfter s (x :: xs) = T.stateAfter (T.step s x) xs := rfl
@[simp] theorem emitted_nil (s : σ) : T.emitted s [] = [] := rfl
@[simp] theorem emitted_cons (s : σ) (x : α) (xs : List α) :
    T.emitted s (x :: xs) = T.output s x ++ T.emitted (T.step s x) xs := rfl

@[simp] theorem runFrom_nil (s : σ) : T.runFrom s [] = T.finalOutput s := rfl

@[simp] theorem runFrom_cons (s : σ) (x : α) (xs : List α) :
    T.runFrom s (x :: xs) = T.output s x ++ T.runFrom (T.step s x) xs := by
  simp [runFrom]

@[simp] theorem run_nil : T.run [] = T.finalOutput T.start := rfl

@[simp] theorem runRight_nil : T.runRight [] = (T.finalOutput T.start).reverse := rfl

@[simp] theorem runRight_reverse (xs : List α) :
    T.runRight xs.reverse = (T.run xs).reverse := by simp [runRight]

theorem stateAfter_append (s : σ) (xs ys : List α) :
    T.stateAfter s (xs ++ ys) = T.stateAfter (T.stateAfter s xs) ys :=
  List.foldl_append

theorem emitted_append (s : σ) (xs ys : List α) :
    T.emitted s (xs ++ ys) = T.emitted s xs ++ T.emitted (T.stateAfter s xs) ys := by
  induction xs generalizing s <;> simp [*]

/-- Running on `xs ++ ys` emits the output over `xs`, then runs on `ys` from the
reached state. -/
theorem runFrom_append (s : σ) (xs ys : List α) :
    T.runFrom s (xs ++ ys) = T.emitted s xs ++ T.runFrom (T.stateAfter s xs) ys := by
  simp [runFrom, emitted_append, stateAfter_append]

theorem run_append (xs ys : List α) :
    T.run (xs ++ ys) = T.emitted T.start xs ++ T.runFrom (T.stateAfter T.start xs) ys :=
  T.runFrom_append T.start xs ys

/-! ### Reindexing states -/

variable {τ : Type*}

/-- Lifts an equivalence on states to an equivalence on subsequential transducers. -/
@[simps apply_start apply_step apply_output apply_finalOutput]
def reindex (g : σ ≃ τ) : SubsequentialTransducer σ α β ≃ SubsequentialTransducer τ α β where
  toFun T := {
    start := g T.start
    step := fun t x => g (T.step (g.symm t) x)
    output := fun t x => T.output (g.symm t) x
    finalOutput := fun t => T.finalOutput (g.symm t)
  }
  invFun T := {
    start := g.symm T.start
    step := fun s x => g.symm (T.step (g s) x)
    output := fun s x => T.output (g s) x
    finalOutput := fun s => T.finalOutput (g s)
  }
  left_inv T := by simp
  right_inv T := by simp

@[simp] theorem reindex_refl : reindex (Equiv.refl σ) T = T := rfl

@[simp] theorem symm_reindex (g : σ ≃ τ) :
    (reindex (α := α) (β := β) g).symm = reindex g.symm := rfl

@[simp] theorem stateAfter_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).stateAfter t xs = g (T.stateAfter (g.symm t) xs) := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem emitted_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).emitted t xs = T.emitted (g.symm t) xs := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem runFrom_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  simp [runFrom]

/-- The reindexed machine computes the same string function. -/
@[simp] theorem run_reindex (g : σ ≃ τ) : (reindex g T).run = T.run := by
  funext xs; simp [run]

@[simp] theorem runRight_reindex (g : σ ≃ τ) : (reindex g T).runRight = T.runRight := by
  funext xs; simp [runRight]

/-! ### Composition -/

section Comp

variable {γ σ' : Type*} (T₂ : SubsequentialTransducer σ' β γ) (T₁ : SubsequentialTransducer σ α β)

/-- `T₂.comp T₁` feeds each output block of `T₁` to `T₂` — the classical product
construction [mohri-1997] — computing `T₂.run ∘ T₁.run` (`run_comp`). -/
@[simps]
def comp : SubsequentialTransducer (σ' × σ) α γ where
  start := (T₂.start, T₁.start)
  step p x := (T₂.stateAfter p.1 (T₁.output p.2 x), T₁.step p.2 x)
  output p x := T₂.emitted p.1 (T₁.output p.2 x)
  finalOutput p := T₂.runFrom p.1 (T₁.finalOutput p.2)

@[simp] theorem runFrom_comp (p : σ' × σ) (xs : List α) :
    (T₂.comp T₁).runFrom p xs = T₂.runFrom p.1 (T₁.runFrom p.2 xs) := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih => simp [ih, runFrom_append]

@[simp] theorem run_comp : (T₂.comp T₁).run = T₂.run ∘ T₁.run := by
  funext xs; simp [run, Function.comp]

end Comp

/-! ### Window transducers -/

section OfWindow

variable {γ : Type*}

/-- The sliding-window transducer: the state is a window of at most `n` symbols of `γ`,
`out` emits an output block from the window and the current symbol, and `upd` chooses
what the window accumulates — `fun _ x => [x]` tracks the input, `out` itself the
output. -/
@[simps]
def ofWindow (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    SubsequentialTransducer {l : List γ // l.length ≤ n} α β where
  start := ⟨[], Nat.zero_le _⟩
  step w x := ⟨(w.val ++ upd w.val x).rtake n, List.length_rtake_le _ _⟩
  output w x := out w.val x
  finalOutput _ := []

variable {n : ℕ} {out : List γ → α → List β} {upd : List γ → α → List γ}

/-- The window transducer runs any recursion that emits `out` and extends the window by
`upd` — the master run-equality behind the ISL/OSL projections. -/
theorem runFrom_ofWindow (go : List γ → List α → List β) (hnil : ∀ w, go w [] = [])
    (hcons : ∀ w x xs, go w (x :: xs) = out w x ++ go ((w ++ upd w x).rtake n) xs) :
    ∀ (w : {l : List γ // l.length ≤ n}) (xs : List α),
      (ofWindow n out upd).runFrom w xs = go w.val xs := by
  intro w xs
  induction xs generalizing w with
  | nil => simp [hnil]
  | cons x xs ih => rw [runFrom_cons, hcons]; exact congrArg _ (ih _)

theorem run_ofWindow (go : List γ → List α → List β) (hnil : ∀ w, go w [] = [])
    (hcons : ∀ w x xs, go w (x :: xs) = out w x ++ go ((w ++ upd w x).rtake n) xs) :
    (ofWindow n out upd).run = go [] :=
  funext fun xs => runFrom_ofWindow go hnil hcons ⟨[], Nat.zero_le _⟩ xs

end OfWindow

end SubsequentialTransducer

/-! ### Synchronous machines as block transducers

A `Mealy` machine is a `SubsequentialTransducer` emitting singleton blocks with an
empty final flush; a block transducer of that shape is a `Mealy` machine. The two views
are mutually inverse. -/

section Synchronous

/-- View a synchronous transducer as a block `SubsequentialTransducer`: singleton
outputs, empty flush. -/
def Mealy.toSubsequentialTransducer (T : Mealy σ α β) : SubsequentialTransducer σ α β where
  start := T.initial
  step := T.step
  output s x := [T.output s x]
  finalOutput _ := []

@[simp] theorem Mealy.toSubsequentialTransducer_runFrom (T : Mealy σ α β) (s : σ) (xs : List α) :
    T.toSubsequentialTransducer.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [SubsequentialTransducer.runFrom_cons, Mealy.runFrom_cons, ih]; rfl

@[simp] theorem Mealy.toSubsequentialTransducer_run (T : Mealy σ α β) :
    T.toSubsequentialTransducer.run = T.run :=
  funext fun xs => T.toSubsequentialTransducer_runFrom T.initial xs

/-- View a block transducer emitting exactly one symbol per input symbol as a synchronous
machine: the singleton output block is the emitted letter. -/
@[simps]
def SubsequentialTransducer.toMealy (T : SubsequentialTransducer σ α β)
    (hs : ∀ s x, (T.output s x).length = 1) : Mealy σ α β where
  initial := T.start
  step := T.step
  output s x := (T.output s x).head (List.ne_nil_of_length_pos (by rw [hs]; omega))

@[simp] theorem Mealy.toMealy_toSubsequentialTransducer (T : Mealy σ α β) :
    T.toSubsequentialTransducer.toMealy (fun _ _ => rfl) = T := rfl

/-- The round trip in the other direction: a singleton-output transducer with no final
flush is its own synchronous view. -/
theorem SubsequentialTransducer.toSubsequentialTransducer_toMealy
    (T : SubsequentialTransducer σ α β) (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) :
    (T.toMealy hs).toSubsequentialTransducer = T := by
  obtain ⟨start, step, output, finalOutput⟩ := T
  dsimp only at hs hf ⊢
  refine SubsequentialTransducer.mk.injEq .. ▸ ⟨rfl, rfl, funext fun s => funext fun x => ?_,
    funext fun s => (hf s).symm⟩
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs s x)
  simp [SubsequentialTransducer.toMealy, ha]

theorem SubsequentialTransducer.toMealy_runFrom (T : SubsequentialTransducer σ α β)
    (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) (s : σ) (xs : List α) :
    (T.toMealy hs).runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => simp [hf]
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs s x)
    simp only [Mealy.runFrom_cons, SubsequentialTransducer.runFrom_cons, toMealy_output,
      toMealy_step, ih, ha, List.head_cons, List.singleton_append]

theorem SubsequentialTransducer.toMealy_run (T : SubsequentialTransducer σ α β)
    (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) : (T.toMealy hs).run = T.run :=
  funext fun xs => T.toMealy_runFrom hs hf T.start xs

end Synchronous

/-! ### Subsequential classification predicates -/

variable {γ : Type*} {f : List α → List β} {g : List β → List γ}

/-- A function `f : List α → List β` is *left-subsequential* if some finite-state
transducer computes it via left-to-right scan [mohri-1997]. -/
def IsLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.run = f

/-- A function `f : List α → List β` is *right-subsequential* if some finite-state
transducer computes it via right-to-left scan (`runRight`). -/
def IsRightSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.runRight = f

/-- A function `f : List α → List β` is *subsequential in direction `d`* if some
finite-state SubsequentialTransducer computes it via the corresponding scan direction. -/
def IsSubsequential (d : Direction) (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftSubsequential f
  | .right => IsRightSubsequential f

@[simp] theorem isSubsequential_left_iff :
    IsSubsequential .left f ↔ IsLeftSubsequential f := Iff.rfl

@[simp] theorem isSubsequential_right_iff :
    IsSubsequential .right f ↔ IsRightSubsequential f := Iff.rfl

/-- `f` is left-subsequential if and only if it is computed by a finite-state
transducer. This is more general than using the definition of `IsLeftSubsequential`
directly, as the state type `σ` is universe-polymorphic. -/
theorem isLeftSubsequential_iff.{v} :
    IsLeftSubsequential f
      ↔ ∃ (σ : Type v) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.run = f :=
  exists_fintype_congr
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.reindex e T, (T.run_reindex e).trans hT⟩)
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.reindex e T, (T.run_reindex e).trans hT⟩)

/-- `f` is right-subsequential if and only if it is computed via `runRight` by a
finite-state transducer. This is more general than using the definition of
`IsRightSubsequential` directly, as the state type `σ` is universe-polymorphic. -/
theorem isRightSubsequential_iff.{v} :
    IsRightSubsequential f
      ↔ ∃ (σ : Type v) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.runRight = f :=
  exists_fintype_congr
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.reindex e T, (T.runRight_reindex e).trans hT⟩)
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.reindex e T, (T.runRight_reindex e).trans hT⟩)

/-- Every finite-state transducer computes a left-subsequential function, whatever the
universe of its state type. -/
theorem SubsequentialTransducer.isLeftSubsequential {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β) :
    IsLeftSubsequential T.run :=
  isLeftSubsequential_iff.mpr ⟨σ, inferInstance, T, rfl⟩

/-- Every finite-state transducer computes a right-subsequential function via
`runRight`. -/
theorem SubsequentialTransducer.isRightSubsequential {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β) :
    IsRightSubsequential T.runRight :=
  isRightSubsequential_iff.mpr ⟨σ, inferInstance, T, rfl⟩

/-- Every finite-state transducer emitting one symbol per input symbol and flushing
nothing at the end computes a Mealy-computable function. -/
theorem SubsequentialTransducer.isMealyComputable {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β)
    (hs : ∀ s x, (T.output s x).length = 1) (hf : ∀ s, T.finalOutput s = []) :
    IsMealyComputable T.run :=
  T.toMealy_run hs hf ▸ (T.toMealy hs).isMealyComputable

/-- A Mealy-computable function is left-subsequential: `Mealy.toSubsequentialTransducer`
presents a synchronous machine as a block transducer emitting singleton blocks. -/
theorem IsMealyComputable.isLeftSubsequential (hf : IsMealyComputable f) :
    IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSubsequentialTransducer_run ▸ T.toSubsequentialTransducer.isLeftSubsequential

theorem isLeftSubsequential_map (h : α → β) : IsLeftSubsequential (List.map h) :=
  (isMealyComputable_map h).isLeftSubsequential

theorem isLeftSubsequential_id : IsLeftSubsequential (id : List α → List α) :=
  isMealyComputable_id.isLeftSubsequential

/-- A function is right-subsequential iff its reverse-conjugate is left-subsequential:
the two classes are isomorphic via the involution `f ↦ List.reverse ∘ f ∘ List.reverse`. -/
theorem isRightSubsequential_iff_left_reverse :
    IsRightSubsequential f
      ↔ IsLeftSubsequential (fun xs => (f xs.reverse).reverse) :=
  ⟨fun ⟨σ, _, T, hT⟩ => ⟨σ, inferInstance, T, by funext xs; simp [← hT]⟩,
   fun ⟨σ, _, T, hT⟩ =>
     ⟨σ, inferInstance, T, by funext xs; simp [SubsequentialTransducer.runRight, hT]⟩⟩

/-- A left-subsequential function has bounded delay: on any input `u` it has already
emitted a prefix of `f u` shared with `f (u ++ v)` for every continuation `v`,
withholding at most the longest state-final output. This is immediate from having a
state-final output at all, and is much weaker than [choffrut-1977]'s bounded-variation
characterization — it compares `u` only with its own extensions. -/
theorem IsLeftSubsequential.bounded_delay (hf : IsLeftSubsequential f) :
    ∃ N : ℕ, ∀ u v : List α, ∃ p su sv : List β,
      f u = p ++ su ∧ f (u ++ v) = p ++ sv ∧ su.length ≤ N := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨Finset.univ.sup fun s => (T.finalOutput s).length, fun u v =>
    ⟨T.emitted T.start u, T.finalOutput (T.stateAfter T.start u),
      T.runFrom (T.stateAfter T.start u) v, rfl, T.runFrom_append T.start u v,
      Finset.le_sup (f := fun s => (T.finalOutput s).length) (Finset.mem_univ _)⟩⟩

/-- The coordinate form of `bounded_delay`: coordinates of `f u` more than `N`
positions before its end are stable under extending the input. -/
theorem IsLeftSubsequential.exists_getElem?_append_eq (hf : IsLeftSubsequential f) :
    ∃ N : ℕ, ∀ u v i, i + N < (f u).length → (f u)[i]? = (f (u ++ v))[i]? := by
  obtain ⟨N, hN⟩ := hf.bounded_delay
  refine ⟨N, fun u v i hi => ?_⟩
  obtain ⟨p, su, sv, hu, huv, hsu⟩ := hN u v
  have hip : i < p.length := by
    have hlen := congrArg List.length hu
    simp only [List.length_append] at hlen
    omega
  rw [hu, huv, List.getElem?_append_left hip, List.getElem?_append_left hip]

/-- `f` is not left-subsequential if for every `N` some images `f u` and `f (u ++ v)`
disagree more than `N` positions before the end of `f u` — the contrapositive of
`bounded_delay`, since no bound on the withheld suffix can then exist. -/
theorem not_isLeftSubsequential_of_diverging
    (h : ∀ N, ∃ (u v : List α) (i : ℕ),
      i + N < (f u).length ∧ (f u)[i]? ≠ (f (u ++ v))[i]?) :
    ¬ IsLeftSubsequential f := by
  intro hf
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq
  obtain ⟨u, v, i, hi, hne⟩ := h N
  exact hne (hN u v i hi)

/-- Left-subsequential functions are closed under composition, by the classical
product construction [mohri-1997] (`SubsequentialTransducer.comp`). -/
theorem IsLeftSubsequential.comp (hg : IsLeftSubsequential g)
    (hf : IsLeftSubsequential f) : IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σ₁, _, T₁, rfl⟩ := hf
  obtain ⟨σ₂, _, T₂, rfl⟩ := hg
  exact ⟨σ₂ × σ₁, inferInstance, T₂.comp T₁, T₂.run_comp T₁⟩

/-- Right-subsequential closure under composition, derived from the left counterpart
via `isRightSubsequential_iff_left_reverse`. -/
theorem IsRightSubsequential.comp (hg : IsRightSubsequential g)
    (hf : IsRightSubsequential f) : IsRightSubsequential (g ∘ f) := by
  rw [isRightSubsequential_iff_left_reverse] at hg hf ⊢
  simpa [Function.comp_def, List.reverse_reverse] using hg.comp hf

/-- Subsequential functions are closed under composition in either scan direction. -/
theorem IsSubsequential.comp {d : Direction} (hg : IsSubsequential d g)
    (hf : IsSubsequential d f) : IsSubsequential d (g ∘ f) :=
  match d, hg, hf with
  | .left, hg, hf => IsLeftSubsequential.comp hg hf
  | .right, hg, hf => IsRightSubsequential.comp hg hf

end Subregular
