import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/-!
# Variable assignments

A *variable assignment* maps variables to values. Three registers share
this file: total assignments (Tarski-style, [heim-kratzer-1998],
[henkin-monk-tarski-1971]), partial assignments (variables may be
unvalued, [spector-2025], [beaver-krahmer-2001]), and plural assignments
(sets of partial assignments — the information states of plural dynamic
semantics, [van-den-berg-1996], [brasoveanu-2008],
[haug-dalrymple-2020]).

## Main definitions

* `Assignment E`: total assignments `ℕ → E`, on the Heim–Kratzer
  ℕ-register.
* `PartialAssign Var D`: partial assignments `Var → Option D`.
* `PluralAssign Var D`: sets of partial assignments, with the
  [spector-2025] / [haug-dalrymple-2020] operators `restrict`,
  `singularAt`, `singular`, `sumDref`.

## Implementation notes

* `PartialAssign` is the decidable counterpart of mathlib's partial
  functions `Var →. D`: `Part`-valued partiality would forfeit
  `DecidableEq` on assignments, which `Finset`-state systems (QBSML) and
  `decide`-checked studies need.
* Update is mathlib's `Function.update`; `PartialAssign.update` only
  fuses the `some` (cf. `Finsupp.update`), and its lemmas are one-step
  consequences of the `Function.update_*` laws. Definedness is
  `(g x).isSome` — there is no wrapper predicate. The Heim–Kratzer
  notation `g[n ↦ x]` for total update is declared in
  `Semantics/Intensional/Variables.lean`.
* Use these names only for the variable-binding role — the state that
  quantifiers `update` and free variables look up. A `ℕ → E` that is not
  variable-binding state (interpretation tables, lookup arrays) should
  stay a plain function type.
-/

/-! ### Total assignments -/

/-- Total variable assignment on the ℕ-register: instantiated at the
    entity type for entity pronouns, at indices for situation pronouns, at
    `Time` for temporal variables. Update is `Function.update` directly —
    no parallel API. -/
abbrev Assignment (E : Type*) := Nat → E

/-! ### Partial assignments -/

/-- Partial assignment: `g x = none` means `x` is unvalued. Trivalent
    systems read the gap as the third value; state-based systems
    (`QBSML.Index`) carry one per world–assignment index. -/
abbrev PartialAssign (Var D : Type*) := Var → Option D

namespace PartialAssign

variable {Var D : Type*} [DecidableEq Var]

/-- The assignment valuing no variables. -/
def empty : PartialAssign Var D := fun _ => none

/-- Update at `x`: `Function.update` with the value wrapped in `some`. -/
def update (g : PartialAssign Var D) (x : Var) (d : D) :
    PartialAssign Var D :=
  Function.update g x (some d)

@[simp] theorem update_at (g : PartialAssign Var D) (x : Var) (d : D) :
    g.update x d x = some d :=
  Function.update_self ..

@[simp] theorem update_ne (g : PartialAssign Var D) {x y : Var} (d : D)
    (h : y ≠ x) : g.update x d y = g y :=
  Function.update_of_ne h ..

/-- Updating at `x` to its existing value is a no-op — the
    partial-assignment face of `Function.update_eq_self`, for proofs that
    recover the witness as `(g x).get`. -/
theorem update_self {g : PartialAssign Var D} {x : Var} {a : D}
    (h : g x = some a) : g.update x a = g := by
  rw [update, ← h]; exact Function.update_eq_self x g

end PartialAssign

/-! ### Plural assignments -/

/-- Plural assignment: a set of partial assignments, the plural
    information state of [van-den-berg-1996]-style dynamic semantics
    (Plural CDRT, PPCDRT) and of [spector-2025]'s static reuse. The full
    `Set` API applies: `∅`, `Set.univ`, `{g}`, `∪`, `⊆`,
    `Set.Nonempty`, … -/
abbrev PluralAssign (Var D : Type*) := Set (PartialAssign Var D)

namespace PluralAssign

variable {Var D : Type*}

/-- The assignments in `G` mapping `x` to `a` ([spector-2025] §6.2:
    `G_{x=a}`). -/
def restrict (G : PluralAssign Var D) (x : Var) (a : D) :
    PluralAssign Var D :=
  {g ∈ G | g x = some a}

/-- `G` assigns `x` uniquely to `d`: some assignment maps `x` to `d`, and
    every assignment valuing `x` agrees ([spector-2025] §6.2). Assignments
    leaving `x` unvalued may coexist — only the valued rows must agree,
    which is the reading Spector's static reuse needs. -/
def singularAt (G : PluralAssign Var D) (x : Var) (d : D) : Prop :=
  (∃ g ∈ G, g x = some d) ∧ ∀ g ∈ G, (g x).isSome → g x = some d

/-- `G` assigns `x` uniquely to some value — [spector-2025]'s `atomic(x)`. -/
def singular (G : PluralAssign Var D) (x : Var) : Prop :=
  ∃ d, G.singularAt x d

/-- The values `x` takes across `G` — [haug-dalrymple-2020]'s `∪u`
    operator. -/
def sumDref (G : PluralAssign Var D) (x : Var) : Set D :=
  {d | ∃ g ∈ G, g x = some d}

end PluralAssign
