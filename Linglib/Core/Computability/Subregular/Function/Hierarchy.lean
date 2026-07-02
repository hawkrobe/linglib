/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Subregular.Function.LetterSubsequential
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# The subregular function hierarchy

Inclusions among the directionality classes of `Core/Computability/Subregular/Function/`,
assembled from the strictly-local, synchronous-subsequential (`LetterSubsequential`) and
bimachine (`Bimachine`) substrate:

  `single-symbol ISL/OSL ⊆ IsLetterLeftSubsequential ⊆ IsBimachineWeaklyDeterministic ⊆ IsBimachineComputable`

A left-subsequential transducer is the degenerate bimachine whose right automaton is
trivial, so its cell output is a *one-sided* rule — non-interacting.

## Main results

* `IsBimachineWeaklyDeterministic.of_letterLeftSubsequential` — subsequential ⊆ WD.
* `IsBimachineComputable.of_weaklyDeterministic` — WD ⊆ regular.
* `weaklyDeterministic_strict_subset_regular` — WD ⊊ regular is *proper*: the conjunctive
  change `conjBM` (a target raised iff a trigger occurs on both sides) is bimachine-computable
  but `RequiresBothSides`.
* `isLetterLeftSubsequential_of_ISLRule` / `_of_OSLRule` — single-symbol ISL/OSL ⊆
  subsequential (the bounded window as a `Mealy` state); `.of_ISLRule` / `.of_OSLRule`
  extend the chain to WD.

## TODO

* subsequential ⊊ WD is also proper, but a witness is not yet formalized here: a genuinely
  two-sided union is `IsUnboundedCircumambient`, hence not right-myopic
  (`IsLetterLeftSubsequential.isRightMyopic`), hence not left-subsequential, yet weakly
  deterministic.
-/

namespace Subregular

/-! ### Synchronous ⊆ block subsequential

A `Mealy` machine is an `SFST` emitting singleton blocks with an empty final flush, so
the synchronous class embeds in the block class scanning the same direction. -/

section MealyBlock

variable {σ α β : Type*}

/-- View a synchronous transducer as a block `SFST`: singleton outputs, empty flush. -/
def Mealy.toSFST (T : Mealy σ α β) : SFST α β σ where
  start := T.initial
  step s x := ((T.step s x).1, [(T.step s x).2])
  finalOutput _ := []

@[simp] theorem Mealy.toSFST_run (T : Mealy σ α β) : T.toSFST.run = T.run := by
  suffices h : ∀ (s : σ) (xs : List α), T.toSFST.runFrom s xs = T.runFrom s xs from
    funext fun xs => h T.initial xs
  intro s xs
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [SFST.runFrom_cons, Mealy.runFrom_cons,
      show T.toSFST.step s x = ((T.step s x).1, [(T.step s x).2]) from rfl, ih]
    rfl

/-- **Synchronous ⊆ block**: a letter-left-subsequential function is left-subsequential. -/
theorem IsLetterLeftSubsequential.isLeftSubsequential {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) : IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSFST_run ▸ T.toSFST.isLeftSubsequential

end MealyBlock

variable {α : Type*} [DecidableEq α]

private theorem unite_default_right (cL a : α) : unite cL a a = cL := by
  unfold unite; split_ifs <;> simp_all

omit [DecidableEq α] in
private theorem mealy_stateAfter_eq_foldl {σ : Type*} (T : Mealy σ α α)
    (s : σ) (pre : List α) :
    T.stateAfter s pre = pre.foldl (fun l a => (T.step l a).1) s := by
  induction pre generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [Mealy.stateAfter, List.foldl_cons, ih]

/-- **Subsequential ⊆ weakly deterministic.** A synchronous left-subsequential function is
computed by a non-interacting bimachine: the left automaton *is* the transducer, the right
automaton is trivial, so the cell output is a one-sided rule (`ωR` is the identity). -/
theorem IsBimachineWeaklyDeterministic.of_letterLeftSubsequential {f : List α → List α}
    (h : IsLetterLeftSubsequential f) : IsBimachineWeaklyDeterministic f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  set B : Bimachine σ Unit α α :=
    { lInit := T.initial, lStep := fun l a => (T.step l a).1,
      rInit := (), rStep := fun _ _ => (), out := fun l a _ => (T.step l a).2 } with hB
  have hrun : B.run = T.run := by
    funext xs
    apply List.ext_getElem?
    intro i
    rw [Bimachine.run_getElem?]
    show (xs[i]?).map
        (fun a => (T.step ((xs.take i).foldl (fun l a => (T.step l a).1) T.initial) a).2)
      = (T.run xs)[i]?
    rw [show T.run xs = T.runFrom T.initial xs from rfl, T.runFrom_getElem?,
        mealy_stateAfter_eq_foldl]
  have hni : B.IsNonInteracting :=
    ⟨fun l a => (T.step l a).2, fun _ a => a, fun l a r => (unite_default_right _ _).symm⟩
  exact hrun ▸ isBimachineWeaklyDeterministic B hni

/-- **Weakly deterministic ⊆ regular.** A non-interacting bimachine is a bimachine. -/
theorem IsBimachineComputable.of_weaklyDeterministic {f : List α → List α}
    (h : IsBimachineWeaklyDeterministic f) : IsBimachineComputable f := by
  obtain ⟨L, R, _, _, B, rfl, _⟩ := h
  exact isBimachineComputable B

/-! ### Strictness: WD ⊊ regular

A *conjunctive* change — a target raised iff a trigger occurs on **both** sides — is
bimachine-computable but `RequiresBothSides`, so no non-interacting bimachine computes
it. -/

/-- Toy alphabet for the conjunctive-change witness: a trigger, a recessive target, and
its raised form. -/
inductive ConjSym | trig | tgt | raised
  deriving DecidableEq, Repr

instance : Fintype ConjSym := ⟨{.trig, .tgt, .raised}, fun x => by cases x <;> simp⟩

/-- A target raises iff a trigger occurs on **both** sides — a flag bimachine
(`Bimachine.ofFlags`) tracking a trigger on each side, whose cell genuinely needs both
flags (`l && r`). -/
def conjBM : Bimachine Bool Bool ConjSym ConjSym :=
  .ofFlags (· == .trig) (· == .trig) fun l s r => if (l && r) && s == .tgt then .raised else s

/-- Output of `conjBM` at a `.tgt` position: `.raised` iff a trigger appears on both the
left prefix and the right suffix, else `.tgt`. -/
private theorem conjBM_run_at {w : List ConjSym} {i : ℕ} (h : w[i]? = some .tgt) :
    (conjBM.run w)[i]?
      = some (if (w.take i).any (· == .trig) && (w.drop (i + 1)).any (· == .trig)
          then .raised else .tgt) := by
  rw [conjBM, Bimachine.ofFlags_run_getElem?, h]; simp

/-- Witness word at distance `d`: a medial `.tgt` flanked by `d` neutral fillers and a
`.trig` on each end. The two perturbations replace one end's `.trig` with a filler. -/
def conjBase (d : ℕ) : List ConjSym :=
  .trig :: List.replicate d .raised ++ .tgt :: List.replicate d .raised ++ [.trig]

private theorem conjBase_getElem_tgt (d : ℕ) : (conjBase d)[d + 1]? = some .tgt := by
  simp [conjBase]

private theorem conjBase_take (d : ℕ) :
    (conjBase d).take (d + 1) = .trig :: List.replicate d .raised := by
  simp [conjBase]

private theorem conjBase_drop (d : ℕ) :
    (conjBase d).drop (d + 2) = List.replicate d .raised ++ [.trig] := by
  simp only [conjBase, List.drop_append, List.length_cons, List.length_replicate]
  simp only [show d + 2 - (d + 1) = 1 from by omega]
  simp

/-- The conjunctive spread requires both sides: the base raises a medial target (a trigger
on each side), but flipping either far trigger to a filler reverts it. The perturbations are
`List.set`s of the base, so they agree with it off the flipped index (`getElem?_set_ne`),
and the reverting cell output is read off via `conjBM_run_at`. -/
theorem conjBM_requiresBothSides : RequiresBothSides conjBM.run := by
  intro d
  refine ⟨conjBase d, d + 1, by simp [conjBase], ?_,
    ⟨(conjBase d).set 0 .raised, by simp [conjBase], ?_, ?_, ?_⟩,
    ⟨(conjBase d).set (2 * d + 2) .raised, by simp [conjBase], ?_, ?_, ?_⟩⟩
  -- base changes: both sides carry a trigger, so the medial `tgt` raises (`.raised ≠ .tgt`)
  · rw [conjBM_run_at (conjBase_getElem_tgt d), conjBase_take, conjBase_drop, conjBase_getElem_tgt]
    simp [List.any_cons, List.any_replicate, List.any_append]
  · intro k hk; exact (List.getElem?_set_ne (by omega)).symm
  · rw [List.getElem?_set_ne (by omega)]
  -- uL reverts: the left perturbation empties the prefix of triggers (`take.any = false`)
  · have h : ((conjBase d).set 0 .raised)[d + 1]? = some .tgt := by
      rw [List.getElem?_set_ne (by omega : (0 : ℕ) ≠ d + 1)]; exact conjBase_getElem_tgt d
    have htake : ((conjBase d).set 0 .raised).take (d + 1) = List.replicate (d + 1) .raised := by
      rw [List.take_set, conjBase_take]; simp [List.set_cons_zero, List.replicate_succ]
    rw [conjBM_run_at h, h, htake]; simp [List.any_replicate]
  · intro k hk; exact (List.getElem?_set_ne (by omega)).symm
  · rw [List.getElem?_set_ne (by omega)]
  -- uR reverts: the right perturbation empties the suffix of triggers (`drop.any = false`)
  · have h : ((conjBase d).set (2 * d + 2) .raised)[d + 1]? = some .tgt := by
      rw [List.getElem?_set_ne (by omega : 2 * d + 2 ≠ d + 1)]; exact conjBase_getElem_tgt d
    have hdrop : ((conjBase d).set (2 * d + 2) .raised).drop (d + 2) = List.replicate (d + 1) .raised := by
      rw [show (2 * d + 2 : ℕ) = d + 2 + d from by omega, ← List.set_drop, conjBase_drop,
          List.set_append_right d ConjSym.raised (by simp)]
      simp [List.replicate_succ']
    rw [conjBM_run_at h, h, hdrop]; simp [List.any_replicate]

theorem weaklyDeterministic_strict_subset_regular :
    ∃ f : List ConjSym → List ConjSym,
      IsBimachineComputable f ∧ ¬ IsBimachineWeaklyDeterministic f :=
  ⟨conjBM.run, isBimachineComputable conjBM,
   not_isBimachineWeaklyDeterministic_of_requiresBothSides conjBM_requiresBothSides⟩

/-! ### The strictly-local lower end: single-symbol ISL/OSL ⊆ subsequential

The ISL/OSL classes are block-output (length-changing) in general, so they sit outside the
length-preserving lattice. Their **single-symbol** (length-preserving) fragment embeds: the
same bounded window that makes `toFinSFST` finite-state serves as a `Mealy` state, with
the lone output symbol as the letter. This extends the chain to
`single-symbol ISL/OSL ⊆ subsequential ⊆ WD ⊆ regular`. -/

/-- A length-preserving (single-symbol) left-ISL rule as a synchronous transducer: the
bounded input window is the state, the lone output symbol the letter. -/
def ISLRule.toMealy {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    Mealy {l : List α // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x := (⟨(w.val ++ [x]).rtake (k - 1), List.length_rtake_le _ _⟩,
    (r.windowOutput w.val x).head (by have := hs w.val x; exact List.ne_nil_of_length_pos (by omega)))

theorem ISLRule.toMealy_run_eq_apply {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : (r.toMealy hs).run = r.apply := by
  rw [← r.toFinSFST_run_eq_apply]
  funext input
  suffices h : ∀ w : {l : List α // l.length ≤ k - 1},
      Mealy.runFrom (r.toMealy hs) w input = SFST.runFrom r.toFinSFST w input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [Mealy.runFrom_cons, SFST.runFrom_cons, ISLRule.toMealy,
      ISLRule.toFinSFST]
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs w.val x)
    simp only [ha, List.head_cons, List.singleton_append]
    exact congrArg (a :: ·) (ih _)

/-- **Single-symbol left-ISL ⊆ left-subsequential.** -/
theorem isLetterLeftSubsequential_of_ISLRule {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsLetterLeftSubsequential r.apply :=
  by rw [← r.toMealy_run_eq_apply hs]; exact (r.toMealy hs).isLetterLeftSubsequential

/-- A length-preserving (single-symbol) left-OSL rule as a synchronous transducer: the
bounded output window is the state. -/
def OSLRule.toMealy {α β : Type*} {k : ℕ} (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    Mealy {l : List β // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x := (⟨(w.val ++ r.windowOutput w.val x).rtake (k - 1), List.length_rtake_le _ _⟩,
    (r.windowOutput w.val x).head (by have := hs w.val x; exact List.ne_nil_of_length_pos (by omega)))

theorem OSLRule.toMealy_run_eq_apply {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : (r.toMealy hs).run = r.apply := by
  rw [← r.toFinSFST_run_eq_apply]
  funext input
  suffices h : ∀ w : {l : List β // l.length ≤ k - 1},
      Mealy.runFrom (r.toMealy hs) w input = SFST.runFrom r.toFinSFST w input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [Mealy.runFrom_cons, SFST.runFrom_cons, OSLRule.toMealy,
      OSLRule.toFinSFST]
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs w.val x)
    simp only [ha, List.head_cons, List.singleton_append]
    exact congrArg (a :: ·) (ih _)

/-- **Single-symbol left-OSL ⊆ left-subsequential.** -/
theorem isLetterLeftSubsequential_of_OSLRule {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsLetterLeftSubsequential r.apply :=
  by rw [← r.toMealy_run_eq_apply hs]; exact (r.toMealy hs).isLetterLeftSubsequential

/-- **Single-symbol left-ISL ⊆ WD** — extends the lattice down through subsequential. -/
theorem IsBimachineWeaklyDeterministic.of_ISLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : ISLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_letterLeftSubsequential (isLetterLeftSubsequential_of_ISLRule r hs)

/-- **Single-symbol left-OSL ⊆ WD**. -/
theorem IsBimachineWeaklyDeterministic.of_OSLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : OSLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_letterLeftSubsequential (isLetterLeftSubsequential_of_OSLRule r hs)

end Subregular
