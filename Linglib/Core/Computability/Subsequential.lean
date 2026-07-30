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

A subsequential transducer is a deterministic state machine which maps strings to
strings, emitting a block of output for each input symbol and a final block determined
by the ending state [schutzenberger-1977] [mohri-1997]. The functions so computed —
*subsequential*, with left- and right-scan variants — form a proper subclass of the
rational functions [filiot-reynier-2016].

We show that each class is closed under composition, that the two are isomorphic under
reverse-conjugation, and that both contain the Mealy-computable functions; a
left-subsequential function withholds at most a bounded output suffix
(`bounded_delay`).

Like `DFA`, this definition allows for machines with infinite states; the
classification predicates require a `Fintype` instance.

## Main definitions

* `SubsequentialTransducer σ α β`: transducer over alphabets `α`, `β` and states `σ`
* `SubsequentialTransducer.run` / `SubsequentialTransducer.runRight`: the two passes
* `SubsequentialTransducer.ofWindow`: the sliding-window transducer
* `IsLeftSubsequential f`, `IsRightSubsequential f`, `IsSubsequential d f`: some
  finite-state transducer computes `f` in the given scan direction

## Implementation notes

The name follows [choffrut-1977] and [mohri-1997]: *sequential* without state-final
output, *subsequential* with. [sakarovitch-2009] calls this class *sequential* (and
the empty-flush case *pure sequential*), flagging his usage as unconventional (cf.
[bruyere-reutenauer-1999]); we keep the Choffrut spelling. `Mealy` is the
letter-to-letter case.

`step` is total, so only the *total* subsequential functions are modelled — a sink
state does not recover partiality — and the initial-output function of
[sakarovitch-2009] is omitted. There are two disjoint sets of simp lemmas, one for
`run` and another for `runFrom`; switch from the former to the latter via `simp [run]`.

## TODO

* Choffrut's theorem [choffrut-1977]: a rational function is subsequential iff it has
  bounded variation, decidably via twinning; `bounded_delay` is far weaker.
* Canonical forms and minimization; two-way transducers; p-subsequential functions.
-/

namespace Subregular

variable {σ α β : Type*}

/-- A subsequential finite-state transducer is a set of states (`σ`), a starting state
(`start`), a transition function (`step`), a per-symbol output function (`output`) and
a state-final output (`finalOutput`). -/
@[ext]
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

theorem runRight_eq_revConj_run : T.runRight = revConj T.run := rfl

section
variable (s : σ) (x : α) (xs ys : List α)

@[simp] theorem stateAfter_nil : T.stateAfter s [] = s := rfl
@[simp] theorem stateAfter_cons : T.stateAfter s (x :: xs) = T.stateAfter (T.step s x) xs := rfl
@[simp] theorem emitted_nil : T.emitted s [] = [] := rfl
@[simp] theorem emitted_cons :
    T.emitted s (x :: xs) = T.output s x ++ T.emitted (T.step s x) xs := rfl

@[simp] theorem runFrom_nil : T.runFrom s [] = T.finalOutput s := rfl

@[simp] theorem runFrom_cons :
    T.runFrom s (x :: xs) = T.output s x ++ T.runFrom (T.step s x) xs := by
  simp [runFrom]

@[simp] theorem run_nil : T.run [] = T.finalOutput T.start := rfl

@[simp] theorem runRight_nil : T.runRight [] = (T.finalOutput T.start).reverse := rfl

@[simp] theorem runRight_reverse : T.runRight xs.reverse = (T.run xs).reverse := by
  simp [runRight]

theorem stateAfter_append : T.stateAfter s (xs ++ ys) = T.stateAfter (T.stateAfter s xs) ys :=
  List.foldl_append

theorem emitted_append :
    T.emitted s (xs ++ ys) = T.emitted s xs ++ T.emitted (T.stateAfter s xs) ys := by
  induction xs generalizing s <;> simp [*]

theorem runFrom_append :
    T.runFrom s (xs ++ ys) = T.emitted s xs ++ T.runFrom (T.stateAfter s xs) ys := by
  simp [runFrom, emitted_append, stateAfter_append]

theorem run_append :
    T.run (xs ++ ys) = T.emitted T.start xs ++ T.runFrom (T.stateAfter T.start xs) ys :=
  T.runFrom_append T.start xs ys

end

/-! ### Transport along state equivalences -/

variable {τ : Type*}

/-- Transport a transducer along an equivalence on states. -/
@[simps]
def map (g : σ ≃ τ) (T : SubsequentialTransducer σ α β) : SubsequentialTransducer τ α β where
  start := g T.start
  step t x := g (T.step (g.symm t) x)
  output t x := T.output (g.symm t) x
  finalOutput t := T.finalOutput (g.symm t)

@[simp] theorem map_refl : map (Equiv.refl σ) T = T := rfl

@[simp] theorem map_map {υ : Type*} (g : σ ≃ τ) (h : τ ≃ υ) :
    map h (map g T) = map (g.trans h) T := rfl

@[simp] theorem stateAfter_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).stateAfter t xs = g (T.stateAfter (g.symm t) xs) := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem emitted_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).emitted t xs = T.emitted (g.symm t) xs := by
  induction xs generalizing t <;> simp [*]

@[simp] theorem runFrom_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  simp [runFrom]

@[simp] theorem run_map (g : σ ≃ τ) : (map g T).run = T.run := by
  funext xs; simp [run]

@[simp] theorem runRight_map (g : σ ≃ τ) : (map g T).runRight = T.runRight := by
  funext xs; simp [runRight]

/-- `map` as an equivalence of machines. -/
def reindex (g : σ ≃ τ) : SubsequentialTransducer σ α β ≃ SubsequentialTransducer τ α β where
  toFun := map g
  invFun := map g.symm
  left_inv T := by simp
  right_inv T := by simp

@[simp] theorem coe_reindex (g : σ ≃ τ) :
    ⇑(reindex (α := α) (β := β) g) = map g := rfl

@[simp] theorem symm_reindex (g : σ ≃ τ) :
    (reindex (α := α) (β := β) g).symm = reindex g.symm := rfl

/-! ### Composition -/

section Comp

variable {γ σ' : Type*} (T₂ : SubsequentialTransducer σ' β γ) (T₁ : SubsequentialTransducer σ α β)

/-- `T₂.comp T₁` feeds each output block of `T₁` to `T₂` — the classical product
construction [mohri-1997] — computing `T₂.run ∘ T₁.run`. -/
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

/-- The transducer whose state is a window of the last `n` accumulated symbols. `out`
emits from the window and the current symbol; `upd` chooses what the window accumulates
(`fun _ x => [x]` for the input, `out` for the output). -/
@[simps]
def ofWindow (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    SubsequentialTransducer {l : List γ // l.length ≤ n} α β where
  start := ⟨[], Nat.zero_le _⟩
  step w x := ⟨(w.val ++ upd w.val x).rtake n, List.length_rtake_le _ _⟩
  output w x := out w.val x
  finalOutput _ := []

/-- The window recursion computed by `ofWindow`; each step emits `out` and extends the
window by `upd`, truncated to length `n`. -/
def windowRun (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    List γ → List α → List β
  | _, [] => []
  | w, x :: xs => out w x ++ windowRun n out upd ((w ++ upd w x).rtake n) xs

variable {n : ℕ} {out : List γ → α → List β} {upd : List γ → α → List γ}

theorem runFrom_ofWindow (w : {l : List γ // l.length ≤ n}) (xs : List α) :
    (ofWindow n out upd).runFrom w xs = windowRun n out upd w.val xs := by
  induction xs generalizing w with
  | nil => simp [windowRun]
  | cons x xs ih => rw [runFrom_cons, windowRun]; exact congrArg _ (ih _)

theorem run_ofWindow : (ofWindow n out upd).run = windowRun n out upd [] :=
  funext fun xs => runFrom_ofWindow ⟨[], Nat.zero_le _⟩ xs

end OfWindow

end SubsequentialTransducer

/-! ### Letter-to-letter machines as block transducers

A `Mealy` machine is a `SubsequentialTransducer` emitting singleton blocks with an
empty final flush; `LetterToLetter` witnesses the singleton blocks, and the two views
are mutually inverse. -/

section LetterToLetter

/-- View a Mealy machine as a block `SubsequentialTransducer`: singleton outputs,
empty flush. -/
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

/-- A witness that every output block of `T` is a singleton, named by `cell`. -/
structure SubsequentialTransducer.LetterToLetter (T : SubsequentialTransducer σ α β) where
  /-- The single symbol emitted at a cell. -/
  cell : σ → α → β
  /-- Every output block is that singleton. -/
  output_eq : ∀ s x, T.output s x = [cell s x]

namespace SubsequentialTransducer.LetterToLetter

variable {T : SubsequentialTransducer σ α β}

/-- Extract a witness from a bound on block lengths. -/
def ofLength (hs : ∀ s x, (T.output s x).length = 1) : T.LetterToLetter where
  cell s x := (T.output s x).head (List.ne_nil_of_length_pos (by rw [hs]; omega))
  output_eq s x := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs s x)
    simp [ha]

/-- The Mealy machine emitting each cell's symbol. -/
@[simps]
def toMealy (w : T.LetterToLetter) : Mealy σ α β where
  initial := T.start
  step := T.step
  output := w.cell

theorem runFrom_toMealy (w : T.LetterToLetter) (hf : ∀ s, T.finalOutput s = [])
    (s : σ) (xs : List α) : w.toMealy.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => simp [hf]
  | cons x xs ih => simp [w.output_eq, ih]

theorem run_toMealy (w : T.LetterToLetter) (hf : ∀ s, T.finalOutput s = []) :
    w.toMealy.run = T.run :=
  funext fun xs => w.runFrom_toMealy hf T.start xs

/-- A letter-to-letter transducer with no final flush is the block form of its Mealy
view. -/
theorem toSubsequentialTransducer_toMealy (w : T.LetterToLetter)
    (hf : ∀ s, T.finalOutput s = []) : w.toMealy.toSubsequentialTransducer = T :=
  SubsequentialTransducer.ext rfl rfl
    (funext₂ fun s x => (w.output_eq s x).symm) (funext fun s => (hf s).symm)

/-- A finite-state letter-to-letter transducer with no final flush computes a
Mealy-computable function. -/
theorem isMealyComputable [Fintype σ] (w : T.LetterToLetter)
    (hf : ∀ s, T.finalOutput s = []) : IsMealyComputable T.run :=
  w.run_toMealy hf ▸ w.toMealy.isMealyComputable

end SubsequentialTransducer.LetterToLetter

/-- The canonical witness that a Mealy machine's block form is letter-to-letter. -/
def Mealy.letterToLetter (T : Mealy σ α β) : T.toSubsequentialTransducer.LetterToLetter :=
  ⟨T.output, fun _ _ => rfl⟩

@[simp] theorem Mealy.toMealy_letterToLetter (T : Mealy σ α β) :
    T.letterToLetter.toMealy = T := rfl

end LetterToLetter

/-! ### Subsequential classification predicates -/

variable {γ : Type*} {f : List α → List β} {g : List β → List γ}

/-- A function `f : List α → List β` is *left-subsequential* if some finite-state
transducer computes it via left-to-right scan [mohri-1997]. -/
def IsLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.run = f

/-- A function `f : List α → List β` is *right-subsequential* if its reverse-conjugate
is left-subsequential — equivalently, some finite-state transducer computes it via
right-to-left scan (`isRightSubsequential_iff`). -/
def IsRightSubsequential (f : List α → List β) : Prop :=
  IsLeftSubsequential (revConj f)

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

/-- The universe-polymorphic form of `IsLeftSubsequential`. -/
theorem isLeftSubsequential_iff.{v} :
    IsLeftSubsequential f
      ↔ ∃ (σ : Type v) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.run = f :=
  exists_fintype_congr
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.map e T, (T.run_map e).trans hT⟩)
    (fun e ⟨T, hT⟩ => ⟨SubsequentialTransducer.map e T, (T.run_map e).trans hT⟩)

/-- The universe-polymorphic form of `IsRightSubsequential`, in the `runRight` shape. -/
theorem isRightSubsequential_iff.{v} :
    IsRightSubsequential f
      ↔ ∃ (σ : Type v) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.runRight = f := by
  constructor
  · intro h
    obtain ⟨σ, _, T, hT⟩ :=
      isLeftSubsequential_iff.mp (show IsLeftSubsequential (revConj f) from h)
    exact ⟨σ, inferInstance, T, by
      rw [SubsequentialTransducer.runRight_eq_revConj_run, hT, revConj_revConj]⟩
  · rintro ⟨σ, _, T, rfl⟩
    show IsLeftSubsequential (revConj T.runRight)
    exact isLeftSubsequential_iff.mpr ⟨σ, inferInstance, T, by
      rw [SubsequentialTransducer.runRight_eq_revConj_run, revConj_revConj]⟩

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

/-- A Mealy-computable function is left-subsequential: `Mealy.toSubsequentialTransducer`
presents a Mealy machine as a block transducer emitting singleton blocks. -/
theorem IsMealyComputable.isLeftSubsequential (hf : IsMealyComputable f) :
    IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSubsequentialTransducer_run ▸ T.toSubsequentialTransducer.isLeftSubsequential

theorem isLeftSubsequential_map (h : α → β) : IsLeftSubsequential (List.map h) :=
  (isMealyComputable_map h).isLeftSubsequential

theorem isLeftSubsequential_id : IsLeftSubsequential (id : List α → List α) :=
  isMealyComputable_id.isLeftSubsequential

/-- A function is right-subsequential iff its reverse-conjugate is left-subsequential —
definitionally: the right class is the `revConj`-image of the left class. -/
theorem isRightSubsequential_iff_left_reverse :
    IsRightSubsequential f
      ↔ IsLeftSubsequential (fun xs => (f xs.reverse).reverse) :=
  Iff.rfl

/-- A left-subsequential function withholds at most the longest state-final output:
`f u` and `f (u ++ v)` share a prefix covering all but boundedly many symbols of `f u`.
Much weaker than [choffrut-1977]'s bounded-variation characterization — this compares
`u` only with its own extensions. -/
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
`bounded_delay`. -/
theorem not_isLeftSubsequential_of_diverging
    (h : ∀ N, ∃ (u v : List α) (i : ℕ),
      i + N < (f u).length ∧ (f u)[i]? ≠ (f (u ++ v))[i]?) :
    ¬ IsLeftSubsequential f := by
  intro hf
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq
  obtain ⟨u, v, i, hi, hne⟩ := h N
  exact hne (hN u v i hi)

/-- Left-subsequential functions are closed under composition, by the classical
product construction [mohri-1997]. -/
theorem IsLeftSubsequential.comp (hg : IsLeftSubsequential g)
    (hf : IsLeftSubsequential f) : IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σ₁, _, T₁, rfl⟩ := hf
  obtain ⟨σ₂, _, T₂, rfl⟩ := hg
  exact ⟨σ₂ × σ₁, inferInstance, T₂.comp T₁, T₂.run_comp T₁⟩

/-- Right-subsequential closure under composition: conjugate the left closure. -/
theorem IsRightSubsequential.comp (hg : IsRightSubsequential g)
    (hf : IsRightSubsequential f) : IsRightSubsequential (g ∘ f) := by
  show IsLeftSubsequential (revConj (g ∘ f))
  rw [revConj_comp]
  exact IsLeftSubsequential.comp hg hf

/-- Subsequential functions are closed under composition in either scan direction. -/
theorem IsSubsequential.comp {d : Direction} (hg : IsSubsequential d g)
    (hf : IsSubsequential d f) : IsSubsequential d (g ∘ f) :=
  match d, hg, hf with
  | .left, hg, hf => IsLeftSubsequential.comp hg hf
  | .right, hg, hf => IsRightSubsequential.comp hg hf

end Subregular
