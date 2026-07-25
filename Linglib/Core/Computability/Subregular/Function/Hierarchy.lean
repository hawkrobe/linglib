/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# The subregular function hierarchy

Inclusions among the directionality classes of the transducer substrate — strictly local
(`ISLRule`, `OSLRule`), synchronous (`Mealy`) and bimachine (`Bimachine`):

  `single-symbol ISL/OSL ⊆ IsMealyComputable ⊆ IsBimachineWeaklyDeterministic ⊆ IsBimachineComputable`

A synchronous transducer is the degenerate bimachine whose right automaton is trivial, so
its cell output is a *one-sided* rule — non-interacting.

## Main theorems

* `IsBimachineWeaklyDeterministic.of_mealyComputable`: synchronous ⊆ weakly deterministic
* `IsBimachineComputable.of_weaklyDeterministic`: weakly deterministic ⊆ regular
* `weaklyDeterministic_strict_subset_regular`: that inclusion is proper, witnessed by the
  conjunctive change `conjBM`, which is bimachine-computable but `RequiresBothSides`
* `isMealyComputable_of_ISLRule`, `isMealyComputable_of_OSLRule`: the single-symbol
  (length-preserving) fragment of the strictly-local classes is synchronous
* `SFST.toMealy`, `Mealy.toSFST`: singleton-output block transducers and synchronous
  machines are interchangeable, giving `IsMealyComputable.isLeftSubsequential`
* `IsMealyComputable.leftDetermined`, `IsMealyComputable.isRightMyopic`: a synchronous map
  is prefix-determined at every coordinate, hence has no look-ahead

## TODO

* `IsLeftSubsequential ⊊ IsBimachineWeaklyDeterministic`. No witness is formalized here.
  Note that non-myopia refutes only *synchronous* computability, via
  `IsMealyComputable.isRightMyopic`: a block transducer may delay its output, so its
  coordinate `i` is not fixed by the prefix, and excluding one takes the bounded-delay
  route (`IsLeftSubsequential.bounded_delay`) instead.
-/

namespace Subregular

/-! ### Synchronous ⊆ block subsequential

A `Mealy` machine is an `SFST` emitting singleton blocks with an empty final flush, so
the synchronous class embeds in the block class scanning the same direction. -/

section MealyBlock

variable {σ α β : Type*}

/-- View a synchronous transducer as a block `SFST`: singleton outputs, empty flush. -/
def Mealy.toSFST (T : Mealy σ α β) : SFST σ α β where
  start := T.initial
  step := T.step
  output s x := [T.output s x]
  finalOutput _ := []

@[simp] theorem Mealy.toSFST_runFrom (T : Mealy σ α β) (s : σ) (xs : List α) :
    T.toSFST.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [SFST.runFrom_cons, Mealy.runFrom_cons, ih]; rfl

@[simp] theorem Mealy.toSFST_run (T : Mealy σ α β) : T.toSFST.run = T.run :=
  funext fun xs => T.toSFST_runFrom T.initial xs

/-- View a block transducer emitting exactly one symbol per input symbol as a synchronous
machine: the singleton output block is the emitted letter. -/
@[simps]
def SFST.toMealy (T : SFST σ α β) (hs : ∀ s x, (T.output s x).length = 1) : Mealy σ α β where
  initial := T.start
  step := T.step
  output s x := (T.output s x).head (List.ne_nil_of_length_pos (by rw [hs]; omega))

@[simp] theorem Mealy.toMealy_toSFST (T : Mealy σ α β) :
    T.toSFST.toMealy (fun _ _ => rfl) = T := rfl

@[simp] theorem SFST.toMealy_runFrom (T : SFST σ α β) (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) (s : σ) (xs : List α) :
    (T.toMealy hs).runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => simp [hf]
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs s x)
    simp only [Mealy.runFrom_cons, SFST.runFrom_cons, toMealy_output, toMealy_step, ih, ha,
      List.head_cons, List.singleton_append]

@[simp] theorem SFST.toMealy_run (T : SFST σ α β) (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) : (T.toMealy hs).run = T.run :=
  funext fun xs => T.toMealy_runFrom hs hf T.start xs

/-- A finite block transducer with singleton outputs and no final flush computes a
Mealy-computable function: block ∩ length-preserving ⊆ synchronous. -/
theorem SFST.isMealyComputable [Fintype σ] (T : SFST σ α β)
    (hs : ∀ s x, (T.output s x).length = 1) (hf : ∀ s, T.finalOutput s = []) :
    IsMealyComputable T.run :=
  T.toMealy_run hs hf ▸ (T.toMealy hs).isMealyComputable

/-- A Mealy-computable function is left-subsequential: synchronous ⊆ block. -/
theorem IsMealyComputable.isLeftSubsequential {f : List α → List β}
    (hf : IsMealyComputable f) : IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSFST_run ▸ T.toSFST.isLeftSubsequential

end MealyBlock

/-! ### Mealy-computable maps have no look-ahead

Output coordinate `i` of a synchronous machine depends only on the input prefix
`[0..i]`. The *block* class `IsLeftSubsequential` lacks this: a length-preserving block
transducer can delay output (emit `[]` then `[x, y]`), so its output coordinate `0` can
depend on input position `1`. -/

section Footprint

variable {α β : Type*}

/-- A Mealy-computable map is left-determined at every coordinate — output `i` depends
only on the prefix `{k | k ≤ i}`. -/
theorem IsMealyComputable.leftDetermined {f : List α → List β}
    (hf : IsMealyComputable f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  intro u v hlen hag
  simp only [Set.mem_setOf_eq] at hag
  rw [T.getElem?_run u, T.getElem?_run v, hag i le_rfl,
    take_eq_of_agree fun k hk => hag k hk.le]

/-- A Mealy-computable map is right-myopic: it has no look-ahead. -/
theorem IsMealyComputable.isRightMyopic {f : List α → List β}
    (hf : IsMealyComputable f) : IsMyopicTowards f .right :=
  IsMyopicTowards.right_of_leftDetermined hf.leftDetermined

end Footprint

variable {α : Type*} [DecidableEq α]

private theorem unite_default_right (cL a : α) : unite cL a a = cL := by
  unfold unite; split_ifs <;> simp_all

/-- **Synchronous ⊆ weakly deterministic.** A Mealy-computable function is computed by a
non-interacting bimachine: the left automaton *is* the transducer, the right automaton is
trivial, so the cell output is a one-sided rule (`ωR` is the identity). -/
theorem IsBimachineWeaklyDeterministic.of_mealyComputable {f : List α → List α}
    (h : IsMealyComputable f) : IsBimachineWeaklyDeterministic f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  set B : Bimachine σ Unit α α :=
    { lInit := T.initial, lStep := T.step,
      rInit := (), rStep := fun _ _ => (), out := fun l a _ => T.output l a } with hB
  have hrun : B.run = T.run := by
    funext xs
    apply List.ext_getElem?
    intro i
    rw [Bimachine.run_getElem?, T.getElem?_run]
    rfl
  have hni : B.IsNonInteracting :=
    ⟨T.output, fun _ a => a, fun l a r => (unite_default_right _ _).symm⟩
  exact hrun ▸ isBimachineWeaklyDeterministic B hni

/-- **Weakly deterministic ⊆ regular.** A non-interacting bimachine is a bimachine. -/
theorem IsBimachineComputable.of_weaklyDeterministic {f : List α → List α}
    (h : IsBimachineWeaklyDeterministic f) : IsBimachineComputable f := by
  obtain ⟨L, R, _, _, B, rfl, _⟩ := h
  exact isBimachineComputable B

/-! ### Strictness: WD ⊊ regular

A *conjunctive* change — a symbol flipped iff a mark occurs on **both** sides — is
bimachine-computable but `RequiresBothSides`, so no non-interacting bimachine computes
it. -/

/-- Toy alphabet for the conjunctive witness: a `mark`, a `neutral` symbol, and the
`flipped` form the neutral symbol takes when both sides are marked. -/
inductive ConjSym | mark | neutral | flipped
  deriving DecidableEq, Repr

instance : Fintype ConjSym := ⟨{.mark, .neutral, .flipped}, fun x => by cases x <;> simp⟩

/-- A neutral symbol flips iff a `mark` occurs on **both** sides — a flag bimachine
(`Bimachine.ofFlags`) tracking a mark on each side, whose cell genuinely needs both
flags (`l && r`). -/
def conjBM : Bimachine Bool Bool ConjSym ConjSym :=
  .ofFlags (· == .mark) (· == .mark) fun l s r =>
    if (l && r) && s == .neutral then .flipped else s

/-- Inside the filler run of a flank word, `conjBM` flips the neutral symbol exactly when
both flanks are marks. -/
private theorem conjBM_flankWord {x y : ConjSym} {n k : ℕ} (h0 : 0 < k) (hk : k ≤ n) :
    (conjBM.run (flankWord x .neutral y n))[k]?
      = some (if x == .mark && y == .mark then .flipped else .neutral) := by
  rw [conjBM, Bimachine.ofFlags_run_getElem?, flankWord_getElem?_mid h0 hk,
    any_take_flankWord (by decide) h0 (by omega),
    any_drop_flankWord (by decide) (by omega) (by omega)]
  simp

/-- The conjunctive change requires both sides: with a mark on each flank the medial
symbol flips, and demoting either mark alone reverts it — the three-map template
(`RequiresBothSides.of_flanks`) applied to a `d`-margined flank word. -/
theorem conjBM_requiresBothSides : RequiresBothSides conjBM.run :=
  .of_flanks (fill := .neutral) (on := .flipped) (xOn := .mark) (yOn := .mark)
    (xOff := .neutral) (yOff := .neutral) (n := fun d => 2 * d + 1) (t := fun d => d + 1)
    (by decide) (fun d => ⟨by omega, by omega⟩)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)

theorem weaklyDeterministic_strict_subset_regular :
    ∃ f : List ConjSym → List ConjSym,
      IsBimachineComputable f ∧ ¬ IsBimachineWeaklyDeterministic f :=
  ⟨conjBM.run, isBimachineComputable conjBM,
   not_isBimachineWeaklyDeterministic_of_requiresBothSides conjBM_requiresBothSides⟩

/-! ### The strictly-local lower end: single-symbol ISL/OSL ⊆ synchronous

The ISL/OSL classes are block-output (length-changing) in general, so they sit outside the
length-preserving lattice. Their **single-symbol** (length-preserving) fragment embeds: the
bounded window that makes `toFinSFST` finite-state serves as the `Mealy` state, with the
lone output symbol as the letter. This extends the chain to
`single-symbol ISL/OSL ⊆ synchronous ⊆ WD ⊆ regular`. -/

/-- **Single-symbol left-ISL ⊆ synchronous**: the bounded input window that makes
`ISLRule.toFinSFST` finite-state is already the `Mealy` state. -/
theorem isMealyComputable_of_ISLRule {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  r.toFinSFST_run_eq_apply ▸ r.toFinSFST.isMealyComputable (fun w x => hs w.val x) fun _ => rfl

/-- **Single-symbol left-OSL ⊆ synchronous**, with the bounded output window as the state. -/
theorem isMealyComputable_of_OSLRule {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  r.toFinSFST_run_eq_apply ▸ r.toFinSFST.isMealyComputable (fun w x => hs w.val x) fun _ => rfl

/-- **Single-symbol left-ISL ⊆ WD** — extends the lattice down through the synchronous
class. -/
theorem IsBimachineWeaklyDeterministic.of_ISLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : ISLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_mealyComputable (isMealyComputable_of_ISLRule r hs)

/-- **Single-symbol left-OSL ⊆ WD**. -/
theorem IsBimachineWeaklyDeterministic.of_OSLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : OSLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_mealyComputable (isMealyComputable_of_OSLRule r hs)

end Subregular
