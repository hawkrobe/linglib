import Linglib.Core.Logic.Truth3

/-!
# Duality
@cite{barwise-cooper-1981}

Universal vs existential operators as the ∃ ⊣ Δ ⊣ ∀ adjunction.

## § 1. Truth3 Aggregation

- `DualityType`: existential vs universal classification
- `aggregate`: aggregate list by duality type (sup/inf over Truth3)

## § 2. Prop-valued Quantifier Projection

- `DualityType.project`: parametric projection by duality type (∃ vs ∀)

The `Prop`-valued counterparts of `existsAny`/`forallAll` are just `∃`/`∀`
from Lean core. De Morgan duality uses `not_forall`/`not_exists` from
Mathlib. See the instance table in § 2's docstring for how parameterized
semantic theories instantiate these.
-/

namespace Core.Duality

/-- Existential vs universal classification. -/
inductive DualityType where
  | existential
  | universal
  deriving Repr, DecidableEq, Inhabited

/-- Existential is robust: one witness suffices. -/
def DualityType.isRobust : DualityType → Bool
  | .existential => true
  | .universal => false

/-- Universal is fragile: one counterexample breaks. -/
def DualityType.isFragile : DualityType → Bool
  | .existential => false
  | .universal => true

/-- Swap existential and universal. -/
def DualityType.dual : DualityType → DualityType
  | .existential => .universal
  | .universal => .existential

theorem dual_involutive (d : DualityType) : d.dual.dual = d := by
  cases d <;> rfl

/-- Aggregate a list according to duality type. -/
def aggregate (d : DualityType) (l : List Truth3) : Truth3 :=
  match d with
  | .existential => l.foldl (· ⊔ ·) ⊥  -- sup = ∃-like
  | .universal => l.foldl (· ⊓ ·) ⊤    -- inf = ∀-like

/-- Existential aggregation: true if ANY true. -/
def existsAny (l : List Truth3) : Truth3 := aggregate .existential l

/-- Universal aggregation: true only if ALL true. -/
def forallAll (l : List Truth3) : Truth3 := aggregate .universal l

theorem foldl_sup_of_true (l : List Truth3) : l.foldl (· ⊔ ·) Truth3.true = .true := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Truth3.true_sup, ih]

theorem foldl_inf_of_false (l : List Truth3) : l.foldl (· ⊓ ·) Truth3.false = .false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Truth3.false_inf, ih]

theorem foldl_sup_mem_true (l : List Truth3) (acc : Truth3) (h : Truth3.true ∈ l) :
    l.foldl (· ⊔ ·) acc = .true := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Truth3.sup_true, foldl_sup_of_true]
    | inr hmem =>
      exact ih (acc ⊔ hd) hmem

theorem foldl_inf_mem_false (l : List Truth3) (acc : Truth3) (h : Truth3.false ∈ l) :
    l.foldl (· ⊓ ·) acc = .false := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Truth3.inf_false, foldl_inf_of_false]
    | inr hmem =>
      exact ih (acc ⊓ hd) hmem

theorem existential_robust (l : List Truth3) (h : l.any (· == .true)) :
    existsAny l = .true := by
  simp only [existsAny, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | true => exact foldl_sup_mem_true l ⊥ hx_mem
  | false => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

theorem universal_fragile (l : List Truth3) (h : l.any (· == .false)) :
    forallAll l = .false := by
  simp only [forallAll, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | false => exact foldl_inf_mem_false l ⊤ hx_mem
  | true => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

def const {α : Type*} (t : Truth3) : α → Truth3 := λ _ => t

def exists' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  existsAny (l.map P)

def forall' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  forallAll (l.map P)

-- ════════════════════════════════════════════════════
-- § 2. Prop-valued Quantifier Projection
-- ════════════════════════════════════════════════════

/-! The `Truth3` aggregation above (§ 1) is the decidable/three-valued
    version of quantifier projection. The classical `Prop`-valued
    counterparts are just `∃` and `∀` from Lean core — the left and
    right adjoints to the diagonal in the adjunction ∃ ⊣ Δ ⊣ ∀.

    Many parameterized semantic theories (comparison classes, precisifications,
    accessible worlds, variable assignments) project out a hidden index
    via one of these two operations:

    | Theory                 | Index I              | ∃-projection       | ∀-projection    | Mathlib hook                           |
    |------------------------|----------------------|--------------------|-----------------|----------------------------------------|
    | @cite{klein-1980}      | comparison class C   | comparative (more) | at-least-as     | `measureDelineation_mono_in_class`     |
    | @cite{fine-1975}       | precisification      | sub-truth          | super-truth     | `Preorder SpecSpace`, stability        |
    | @cite{caie-2023}       | comp. context        | disjunctive update | —               | `disjunctiveUpdate_mono_interp`        |
    | @cite{kratzer-1981}    | accessible world     | ◇ (possibility)    | □ (necessity)   | `GaloisConnection` (Proposition.lean)  |
    | @cite{kamp-1975}       | completion           | strict comparative | at-least-as     | `Antitone` in S (via `kampPreorder`)   |

    The projections themselves are just `∃`/`∀`. De Morgan duality uses
    `not_forall` / `not_exists` from Lean core. The deeper Mathlib
    connections are on the **parameter spaces**: `Monotone`/`Antitone`
    for how the projections vary as the parameter space changes,
    `IsLeast`/`IsGreatest` for monotone collapse, and `GaloisConnection`
    for the extension/intension adjunction.

    See `ParameterizedUpdate.lean` for the shared framework (monotone
    collapse via `IsLeast`/`IsGreatest` + `Antitone`, borderline region
    characterization, sequential update with pruning).
-/

variable {I : Type*}

/-- Project by duality type: existential uses ∃, universal uses ∀. -/
def DualityType.project (d : DualityType) (P : I → Prop) : Prop :=
  match d with
  | .existential => ∃ i, P i
  | .universal => ∀ i, P i

end Core.Duality
