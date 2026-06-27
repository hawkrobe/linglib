/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Optimization.Evaluation

/-!
# Directional Tableau — Term-Order EVAL
[eisner-2000] [eisner-2002] [lamont-2022b]

A constraint's violations form a **monomial** over the form's positions, and
EVAL compares candidates by a **term (monomial) order** on it: `degree` (total
violations — parallel OT), `lex` (`*FLOAT^→`), `revLex` (`*FLOAT^←`). Each
constraint carries its *own* order ([lamont-2022b]: directionality is a property
of EVAL), so a single tableau mixes counting and directional constraints.

The term order is encoded computably as `Constraint.key` (the order-flattened
violation vector); the whole ranked comparison is then `LexLE` on the
concatenated keys (`profile`), so this is the variable-length analogue of
`Core.Optimization.Evaluation.LexMinProblem`. The bridge to mathlib's
`MonomialOrder.lex` is `Core.Optimization.Evaluation.lexLE_ofFn`.

## Main definitions

* `Constraint C` — a violation function `C → List Nat` plus its `TermOrder`.
* `DirectionalTableau C` — a finite candidate set ranked by such constraints.
* `DirectionalTableau.optima` — the `Finset` of EVAL winners.

## Main results

* `DirectionalTableau.mem_optima_iff` — membership characterisation.
* `DirectionalTableau.optima_nonempty` — a winner exists (uniform-length keys).
-/

namespace OptimalityTheory
open Constraints
open Core.Optimization.Evaluation

/-! ### Constraints carrying a term order -/

/-- A directional OT constraint: a violation vector plus the `TermOrder` EVAL
    compares it under. `degree` recovers a counting constraint; `lex`/`revLex`
    are the directional `[eisner-2000]`/`[lamont-2022b]` ones. -/
structure Constraint (C : Type*) where
  name : String := ""
  family : Family
  eval : C → List Nat
  order : TermOrder

variable {C : Type*}

/-- A counting (`degree`-order) constraint whose violation is a single tally —
    the parallel-OT degenerate case. -/
def Constraint.ofCount (name : String) (family : Family)
    (count : C → Nat) : Constraint C :=
  { name, family, eval := λ c => [count c], order := .degree }

/-- The constraint's comparison **key**: the violation vector flattened by its
    term order, so that `LexLE` on keys realises `TermOrder.le`. -/
def Constraint.key (con : Constraint C) (c : C) : List Nat :=
  match con.order with
  | .degree => [(con.eval c).sum]
  | .lex    => con.eval c
  | .revLex => (con.eval c).reverse

/-- `LexLE` on a singleton reduces to `≤` on the entry. -/
theorem lexLE_singleton (a b : Nat) : LexLE [a] [b] ↔ a ≤ b := by
  rw [lexLE_cons_cons_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    exacts [le_of_lt h, le_of_eq h]
  · intro h
    rcases lt_or_eq_of_le h with h | h
    exacts [Or.inl h, Or.inr ⟨h, lexLE_nil _⟩]

/-- `LexLE` on keys is exactly the constraint's term order on its violations. -/
theorem Constraint.key_le_iff (con : Constraint C) (a b : C) :
    LexLE (con.key a) (con.key b) ↔ con.order.le (con.eval a) (con.eval b) := by
  unfold Constraint.key
  cases con.order
  · simpa using lexLE_singleton (con.eval a).sum (con.eval b).sum
  · simp [TermOrder.le]
  · simp [TermOrder.le]

/-! ### The tableau and its optimal set -/

variable [DecidableEq C]

/-- A finite candidate set ranked by term-ordered constraints. The ranked
    comparison is `LexLE` on the concatenated keys; with all constraints of
    `degree` order this is parallel OT, with `*FLOAT` of `lex` order it is
    directional HS. -/
structure DirectionalTableau (C : Type*) [DecidableEq C] where
  candidates : Finset C
  ranking : List (Constraint C)
  nonempty : candidates.Nonempty

namespace DirectionalTableau

variable (t : DirectionalTableau C)

/-- The candidate's full violation profile: each constraint's key, concatenated
    in ranking order. EVAL compares profiles by `LexLE`. -/
def profile (c : C) : List Nat := (t.ranking.map (·.key c)).flatten

/-- `c` is **optimal** iff its profile is `LexLE`-least among the candidates. -/
def IsOptimal (c : C) : Prop :=
  c ∈ t.candidates ∧ ∀ d ∈ t.candidates, LexLE (t.profile c) (t.profile d)

instance (c : C) : Decidable (t.IsOptimal c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The optimal set, as an `argMinSet` over `LexLE`. Computable. -/
def optima : Finset C :=
  argMinSet t.candidates t.profile LexLE

theorem mem_optima_iff (c : C) : c ∈ t.optima ↔ t.IsOptimal c := mem_argMinSet

/-- Profiles have equal length when every constraint's violation vectors do
    (each `key` preserves length: `degree` keys are singletons, `lex`/`revLex`
    keys preserve length). -/
theorem profile_length_eq {a b : C}
    (h : ∀ con ∈ t.ranking, (con.eval a).length = (con.eval b).length) :
    (t.profile a).length = (t.profile b).length := by
  have key_len : ∀ con ∈ t.ranking, (con.key a).length = (con.key b).length := by
    intro con hcon
    unfold Constraint.key
    split <;> simp [h con hcon]
  simp only [profile, List.length_flatten, List.map_map]
  exact congrArg List.sum (List.map_congr_left
    (λ con hcon => by simpa using key_len con hcon))

/-- **A winner exists** when every constraint assigns equal-length violation
    vectors across the candidates (so profiles are `LexLE`-comparable). Delegates
    to `exists_lexLE_minimum`. -/
theorem optima_nonempty
    (uniform : ∀ con ∈ t.ranking, ∀ a ∈ t.candidates, ∀ b ∈ t.candidates,
      (con.eval a).length = (con.eval b).length) :
    t.optima.Nonempty := by
  obtain ⟨m, hm, hmin⟩ := exists_lexLE_minimum t.candidates.toList
    (by simp only [ne_eq, Finset.toList_eq_nil]; exact t.nonempty.ne_empty) t.profile
    (λ a ha b hb => t.profile_length_eq
      (λ con hcon => uniform con hcon a (Finset.mem_toList.mp ha) b (Finset.mem_toList.mp hb)))
  exact ⟨m, (mem_optima_iff t m).mpr
    ⟨Finset.mem_toList.mp hm, λ d hd => hmin d (Finset.mem_toList.mpr hd)⟩⟩

end DirectionalTableau

/-! ### Smoke test (paper, fig. 3 — the divergent tie) -/

section SmokeTest

/-- Three depth-1 candidates of `/H₀ H₁ H₂/`: delete the floating H at position
    0, 1, or 2. -/
inductive DemoCand | deletedAt0 | deletedAt1 | deletedAt2
  deriving DecidableEq, Repr

open DemoCand in
/-- `*FLOAT`: indicator of the remaining floating H positions. -/
def demoFloat : Constraint DemoCand :=
  { name := "*FLOAT", family := .markedness, order := .lex
    eval := λ | deletedAt0 => [0,1,1] | deletedAt1 => [1,0,1] | deletedAt2 => [1,1,0] }

def demoCands : Finset DemoCand := {.deletedAt0, .deletedAt1, .deletedAt2}

/-- Parallel (`degree`) ties all three — the divergent tie. -/
example : (DirectionalTableau.mk demoCands [{ demoFloat with order := .degree }]
    (by decide)).optima = demoCands := by decide

/-- Directional `*FLOAT^→` (`lex`) breaks the tie: delete the leftmost. -/
example : (DirectionalTableau.mk demoCands [demoFloat] (by decide)).optima
    = {DemoCand.deletedAt0} := by decide

/-- `*FLOAT^←` (`revLex`): delete the rightmost. -/
example : (DirectionalTableau.mk demoCands [{ demoFloat with order := .revLex }]
    (by decide)).optima = {DemoCand.deletedAt2} := by decide

end SmokeTest

end OptimalityTheory
