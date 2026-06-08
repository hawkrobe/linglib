/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.LetterSubsequential
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# The subregular function hierarchy

Inclusions among the directionality classes of `Core/Computability/Subregular/Function/`,
assembled from the synchronous-subsequential (`LetterSubsequential`) and bimachine
(`Bimachine`) substrate:

  `IsLetterLeftSubsequential ⊆ IsBimachineWeaklyDeterministic ⊆ IsBimachineComputable`

A left-subsequential transducer is the degenerate bimachine whose right automaton is
trivial, so its cell output is a *one-sided* rule — non-interacting.

## Main results

* `IsBimachineWeaklyDeterministic.of_letterLeftSubsequential` — subsequential ⊆ WD.
* `IsBimachineComputable.of_weaklyDeterministic` — WD ⊆ regular.

## Strictness

The inclusions are *proper*, witnessed by attested harmony patterns formalized in
`Studies/` (not imported here — Core stays study-agnostic):

* **WD ⊊ regular**: Tutrugbu ATR (`McCollumEtAl2020.tutrugbu_not_weaklyDeterministic`)
  `RequiresBothSides`, so no non-interacting bimachine computes it.
* **subsequential ⊊ WD**: Maasai ATR (`MeinhardtEtAl2024.maasai_weaklyDeterministic`) is a
  genuinely two-sided union — `IsUnboundedCircumambient`, hence not right-myopic, hence
  not left-subsequential (`IsLetterLeftSubsequential.isRightMyopic`) — yet WD.
-/

namespace Core.Computability.Subregular.Function

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

end Core.Computability.Subregular.Function
