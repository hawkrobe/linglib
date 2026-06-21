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
* `weaklyDeterministic_strict_subset_regular` — the second inclusion is *proper*.
* `isLetterLeftSubsequential_of_ISLRule` / `_of_OSLRule` — single-symbol ISL/OSL ⊆
  subsequential (the bounded window as a `LetterSFST` state); `.of_ISLRule` / `.of_OSLRule`
  extend the chain to WD.

## Strictness

Both inclusions are proper:

* **WD ⊊ regular** — `weaklyDeterministic_strict_subset_regular`: the conjunctive spread
  `conjBM` (a target raised iff a trigger occurs on *both* sides) is bimachine-computable
  but `RequiresBothSides`. Tutrugbu ATR is the attested instance
  (`McCollumEtAl2020.tutrugbu_not_weaklyDeterministic`).
* **subsequential ⊊ WD** — Maasai ATR (`MeinhardtEtAl2024.maasai_not_letterLeftSubsequential`)
  is a genuinely two-sided union, `IsUnboundedCircumambient` hence not right-myopic hence
  not left-subsequential, yet WD.
-/

namespace Subregular.Function

variable {α : Type*} [DecidableEq α]

private theorem unite_default_right (cL a : α) : unite cL a a = cL := by
  unfold unite; split_ifs <;> simp_all

omit [DecidableEq α] in
private theorem letterSFST_stateAfter_eq_foldl {σ : Type*} (T : LetterSFST σ α α)
    (s : σ) (pre : List α) :
    T.stateAfter s pre = pre.foldl (fun l a => (T.step l a).1) s := by
  induction pre generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [LetterSFST.stateAfter, List.foldl_cons, ih]

/-- **Subsequential ⊆ weakly deterministic.** A synchronous left-subsequential function is
computed by a non-interacting bimachine: the left automaton *is* the transducer, the right
automaton is trivial, so the cell output is a one-sided rule (`ωR` is the identity). -/
theorem IsBimachineWeaklyDeterministic.of_letterLeftSubsequential {f : List α → List α}
    (h : IsLetterLeftSubsequential f) : IsBimachineWeaklyDeterministic f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  refine ⟨σ, Unit, inferInstance, inferInstance,
    { lInit := T.initial, lStep := fun l a => (T.step l a).1,
      rInit := (), rStep := fun _ _ => (), out := fun l a _ => (T.step l a).2 }, ?_, ?_⟩
  · funext xs
    apply List.ext_getElem?
    intro i
    rw [Bimachine.run_getElem?]
    show (xs[i]?).map
        (fun a => (T.step ((xs.take i).foldl (fun l a => (T.step l a).1) T.initial) a).2)
      = (T.run xs)[i]?
    rw [show T.run xs = T.runFrom T.initial xs from rfl, T.runFrom_getElem?,
        letterSFST_stateAfter_eq_foldl]
  · exact ⟨fun l a => (T.step l a).2, fun _ a => a, fun l a r => (unite_default_right _ _).symm⟩

/-- **Weakly deterministic ⊆ regular.** A non-interacting bimachine is a bimachine. -/
theorem IsBimachineComputable.of_weaklyDeterministic {f : List α → List α}
    (h : IsBimachineWeaklyDeterministic f) : IsBimachineComputable f := by
  obtain ⟨L, R, _, _, B, hrun, _⟩ := h
  exact ⟨L, R, inferInstance, inferInstance, B, hrun⟩

/-! ### Strictness: WD ⊊ regular

A *conjunctive* spread — a target raised iff a trigger occurs on **both** sides — is
bimachine-computable but `RequiresBothSides`, so no non-interacting bimachine computes
it. (Tutrugbu ATR is the attested instance; `McCollumEtAl2020.tutrugbu_not_weaklyDeterministic`.) -/

/-- Toy alphabet for the conjunctive-spread witness: a trigger, a recessive target, and
its raised form. -/
inductive ConjSym | trig | tgt | raised
  deriving DecidableEq, Repr

instance : Fintype ConjSym := ⟨{.trig, .tgt, .raised}, fun x => by cases x <;> simp⟩

/-- A target raises iff a trigger occurs on **both** sides — left/right states track a
trigger seen on each side, and the cell genuinely needs both (`l && r`). -/
def conjBM : Bimachine Bool Bool ConjSym ConjSym where
  lInit := false
  lStep l s := l || (s == .trig)
  rInit := false
  rStep r s := r || (s == .trig)
  out l s r := if (l && r) && s == .tgt then .raised else s

private theorem conjBM_lState (xs : List ConjSym) :
    conjBM.lState xs = xs.any (· == .trig) := by
  show xs.foldl (fun l s => l || (s == .trig)) false = _
  have key : ∀ (acc : Bool) (ys : List ConjSym),
      ys.foldl (fun l s => l || (s == .trig)) acc = (acc || ys.any (· == .trig)) := by
    intro acc ys; induction ys generalizing acc with
    | nil => simp
    | cons y ys ih => simp [ih, Bool.or_assoc]
  simpa using key false xs

private theorem conjBM_rState (xs : List ConjSym) :
    conjBM.rState xs = xs.any (· == .trig) := by
  show xs.foldr (fun s r => r || (s == .trig)) false = _
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [ih, Bool.or_comm]

/-- Witness word at distance `d`: a medial `tgt` flanked by `d` neutral fillers and a
`trig` on each end. -/
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

/-- The conjunctive spread requires both sides: the base raises a medial target (trigger
on each side), but removing either far trigger reverts it. -/
theorem conjBM_requiresBothSides : RequiresBothSides conjBM.run := by
  intro d
  refine ⟨conjBase d, d + 1, by simp [conjBase], ?_,
    ⟨(conjBase d).set 0 .raised, by simp [conjBase], ?_, ?_, ?_⟩,
    ⟨(conjBase d).set (2 * d + 2) .raised, by simp [conjBase], ?_, ?_, ?_⟩⟩
  -- Goal 1: base changes at d+1 (both sides have a trigger → tgt raises to .raised ≠ .tgt)
  · rw [conjBM.run_getElem?, conjBM_lState, conjBM_rState,
        conjBase_getElem_tgt, conjBase_take d, conjBase_drop d]
    simp [List.any_cons, List.any_replicate, List.any_append, conjBM]
  -- Goal 2: uL AgreeFrom — set at 0 differs only at 0, so agree from (d+1)-d = 1 ≤ k
  · intro k hk
    exact (List.getElem?_set_ne (by omega)).symm
  -- Goal 3: uL[d+1]? = base[d+1]? since d+1 ≠ 0
  · rw [List.getElem?_set_ne (by omega)]
  -- Goal 4: uL revert — lState = false (no trigger in take) → cell outputs .tgt
  · have htake_uL : ((conjBase d).set 0 .raised).take (d + 1) = List.replicate (d + 1) .raised := by
      rw [List.take_set, conjBase_take]
      simp [List.set_cons_zero, List.replicate_succ]
    have hdrop_uL : ((conjBase d).set 0 .raised).drop (d + 2) =
        List.replicate d .raised ++ [.trig] := by
      rw [List.drop_set_of_lt (by omega), conjBase_drop]
    rw [conjBM.run_getElem?, conjBM_lState, conjBM_rState,
        List.getElem?_set_ne (by omega : (0 : ℕ) ≠ d + 1), conjBase_getElem_tgt,
        htake_uL, hdrop_uL]
    simp [List.any_replicate, List.any_append, List.any_cons, conjBM]
  -- Goal 5: uR AgreeUpto — set at 2*d+2 differs only there, so agree upto (d+1)+d = 2*d+1 < 2*d+2
  · intro k hk
    exact (List.getElem?_set_ne (by omega)).symm
  -- Goal 6: uR[d+1]? = base[d+1]? since d+1 ≠ 2*d+2
  · rw [List.getElem?_set_ne (by omega)]
  -- Goal 7: uR revert — rState = false (no trigger in drop) → cell outputs .tgt
  · have htake_uR : ((conjBase d).set (2 * d + 2) .raised).take (d + 1) =
        .trig :: List.replicate d .raised := by
      rw [List.take_set_of_le (by omega), conjBase_take]
    have hdrop_uR : ((conjBase d).set (2 * d + 2) .raised).drop (d + 2) =
        List.replicate (d + 1) .raised := by
      rw [show (2 * d + 2 : ℕ) = d + 2 + d from by omega, ← List.set_drop, conjBase_drop]
      rw [List.set_append_right d ConjSym.raised (by simp)]
      simp [List.replicate_succ']
    rw [conjBM.run_getElem?, conjBM_lState, conjBM_rState,
        List.getElem?_set_ne (by omega : 2 * d + 2 ≠ d + 1), conjBase_getElem_tgt,
        htake_uR, hdrop_uR]
    simp [List.any_replicate, List.any_cons, conjBM]

theorem weaklyDeterministic_strict_subset_regular :
    ∃ f : List ConjSym → List ConjSym,
      IsBimachineComputable f ∧ ¬ IsBimachineWeaklyDeterministic f :=
  ⟨conjBM.run, ⟨Bool, Bool, inferInstance, inferInstance, conjBM, rfl⟩,
   not_isBimachineWeaklyDeterministic_of_requiresBothSides conjBM_requiresBothSides⟩

/-! ### The strictly-local lower end: single-symbol ISL/OSL ⊆ subsequential

The ISL/OSL classes are block-output (length-changing) in general, so they sit outside the
length-preserving lattice. Their **single-symbol** (length-preserving) fragment — the
harmony-relevant case (e.g. `MeinhardtEtAl2024.rightwardATR_osl`) — embeds: the same
bounded window that makes `toFinSFST` finite-state serves as a `LetterSFST` state, with the
lone output symbol as the letter. This extends the chain to
`single-symbol ISL/OSL ⊆ subsequential ⊆ WD ⊆ regular`. -/

/-- A length-preserving (single-symbol) left-ISL rule as a synchronous transducer: the
bounded input window is the state, the lone output symbol the letter. -/
def ISLRule.toLetterSFST {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    LetterSFST {l : List α // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x := (⟨lastN (k - 1) (w.val ++ [x]), lastN_length_le _ _⟩,
    (r.windowOutput w.val x).head (by have := hs w.val x; exact List.ne_nil_of_length_pos (by omega)))

theorem ISLRule.toLetterSFST_run_eq_apply {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : (r.toLetterSFST hs).run = r.apply := by
  rw [← r.toFinSFST_run_eq_apply]
  funext input
  suffices h : ∀ w : {l : List α // l.length ≤ k - 1},
      LetterSFST.runFrom (r.toLetterSFST hs) w input = SFST.runFrom r.toFinSFST w input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [LetterSFST.runFrom_cons, SFST.runFrom_cons, ISLRule.toLetterSFST,
      ISLRule.toFinSFST]
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs w.val x)
    simp only [ha, List.head_cons, List.singleton_append]
    exact congrArg (a :: ·) (ih _)

/-- **Single-symbol left-ISL ⊆ left-subsequential.** -/
theorem isLetterLeftSubsequential_of_ISLRule {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsLetterLeftSubsequential r.apply :=
  by rw [← r.toLetterSFST_run_eq_apply hs]; exact (r.toLetterSFST hs).isLetterLeftSubsequential

/-- A length-preserving (single-symbol) left-OSL rule as a synchronous transducer: the
bounded output window is the state. -/
def OSLRule.toLetterSFST {α β : Type*} {k : ℕ} (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    LetterSFST {l : List β // l.length ≤ k - 1} α β where
  initial := ⟨[], Nat.zero_le _⟩
  step w x := (⟨lastN (k - 1) (w.val ++ r.windowOutput w.val x), lastN_length_le _ _⟩,
    (r.windowOutput w.val x).head (by have := hs w.val x; exact List.ne_nil_of_length_pos (by omega)))

theorem OSLRule.toLetterSFST_run_eq_apply {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : (r.toLetterSFST hs).run = r.apply := by
  rw [← r.toFinSFST_run_eq_apply]
  funext input
  suffices h : ∀ w : {l : List β // l.length ≤ k - 1},
      LetterSFST.runFrom (r.toLetterSFST hs) w input = SFST.runFrom r.toFinSFST w input from h _
  intro w
  induction input generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [LetterSFST.runFrom_cons, SFST.runFrom_cons, OSLRule.toLetterSFST,
      OSLRule.toFinSFST]
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs w.val x)
    simp only [ha, List.head_cons, List.singleton_append]
    exact congrArg (a :: ·) (ih _)

/-- **Single-symbol left-OSL ⊆ left-subsequential.** -/
theorem isLetterLeftSubsequential_of_OSLRule {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsLetterLeftSubsequential r.apply :=
  by rw [← r.toLetterSFST_run_eq_apply hs]; exact (r.toLetterSFST hs).isLetterLeftSubsequential

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

end Subregular.Function
