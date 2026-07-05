/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Linearization.Cyclic

/-!
# Fox & Pesetsky 2005: cyclic linearization

[fox-pesetsky-2005]'s worked examples, kernel-checked against the
`Minimalist.Linearization` spell-out order: the two movement scenarios ((13), (14)),
successive-cyclic *wh*-movement ((3)–(8)), order-preserving simultaneous movement,
and Holmberg's Generalization (§3) — plus the paper's central architectural claim,
that convergence is a property of the derivational history rather than of the
output string (`history_dependence`).
-/

namespace FoxPesetsky2005

open Minimalist.Linearization

/-- Scenario 1 ([fox-pesetsky-2005] (13)): leftward movement from a left-edge
    position. `X` was at the left edge of `D`; moving further left in `D′` is
    consistent with the order established at `D`. -/
theorem edge_movement_consistent :
    Consistent [["X", "Y", "Z"], ["X", "α", "Y", "Z"]] := by decide

/-- Scenario 2 ([fox-pesetsky-2005] (14)): leftward movement from a non-edge
    position. `Y` was not at the left edge of `D`, so moving it left in `D′`
    contradicts the order established at `D`. -/
theorem non_edge_movement_contradiction :
    ¬ Consistent [["X", "Y", "Z"], ["Y", "α", "X", "Z"]] := by decide

/-- Successive-cyclic *wh*-movement ([fox-pesetsky-2005] (6)–(8)): *to whom* moves
    through the VP edge before Spec,CP, preserving VP-internal order. -/
theorem successive_cyclic_ok :
    Consistent [["to_whom", "gave", "the_book"],
                ["to_whom", "that", "Mary", "gave", "the_book"]] := by decide

/-- Non-successive-cyclic movement ([fox-pesetsky-2005] (3)–(5)): *to whom* skips
    the VP edge, contradicting VP-internal order. -/
theorem non_successive_cyclic_bad :
    ¬ Consistent [["gave", "the_book", "to_whom"],
                  ["to_whom", "that", "Mary", "gave", "the_book"]] := by decide

/-- **The paper's central architectural claim**: convergence is a property of the
    derivational history, not the output — the same final Spell-out converges after
    successive-cyclic movement through the VP edge and crashes without it. The
    spell-out order does not factor through the final string. -/
theorem history_dependence :
    Consistent [["to_whom", "gave", "the_book"],
                ["to_whom", "that", "Mary", "gave", "the_book"]] ∧
    ¬ Consistent [["gave", "the_book", "to_whom"],
                  ["to_whom", "that", "Mary", "gave", "the_book"]] :=
  ⟨successive_cyclic_ok, non_successive_cyclic_bad⟩

/-- Simultaneous movement preserving relative order creates no contradiction
    (the configuration behind Malayic object extraction,
    `Studies/ErlewineSommerlot2025.lean`). -/
theorem simultaneous_order_preserving :
    Consistent [["A", "B", "C"], ["A", "B", "D", "C"]] := by decide

/-- Simultaneous movement reversing relative order contradicts. -/
theorem simultaneous_order_reversing :
    ¬ Consistent [["B", "A", "C"], ["A", "B", "D", "C"]] := by decide

/-- A purely transitive ordering cycle also crashes: the crash condition is
    acyclicity of the full spell-out order, not the absence of a directly
    contradicting pair. -/
theorem transitive_cycle_crashes :
    ¬ Consistent [["a", "b"], ["b", "c"], ["c", "a"]] := by decide

/-! ### Holmberg's Generalization ([fox-pesetsky-2005] §3)

Object Shift in Scandinavian is possible only when the verb also moves out of VP:
VP Spell-out establishes V < Obj, and a shifted object with an in-situ verb reverses
it at the higher domain. -/

/-- Baseline: no Object Shift, verb moves to I. -/
theorem no_object_shift :
    Consistent [["V", "Obj"], ["Subj", "V", "Neg", "Obj"]] := by decide

/-- Object Shift with verb movement: V < Obj is preserved past Neg. -/
theorem object_shift_with_verb_movement :
    Consistent [["V", "Obj"], ["Subj", "V", "Obj", "Neg"]] := by decide

/-- Object Shift without verb movement reverses V < Obj — this crash **is**
    Holmberg's Generalization, derived from cyclic linearization. -/
theorem object_shift_without_verb_movement :
    ¬ Consistent [["V", "Obj"], ["Subj", "Obj", "Neg", "V"]] := by decide

end FoxPesetsky2005
