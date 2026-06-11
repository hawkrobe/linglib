import Mathlib.ModelTheory.Semantics
import Linglib.Core.Logic.FirstOrder.Binders

/-!
# Constant-domain first-order Kripke structures and modal formulas

Mathlib's `ModelTheory` is classical: one structure, no accessibility. A
`KripkeStructure L W M` is a `W`-indexed family of `L`-structures on a
constant domain `M` together with `Finset`-valued accessibility — the shape
`Semantics/Composition/Model.lean` (without accessibility) and
`Core/Logic/Modal/QBSML/Defs.lean` already instantiate. On top,
`ModalFormula L α` layers `□` and named quantifiers over embedded classical
`L.Formula`s, and `ModalFormula.Realize` is Kripke satisfaction
`K, w ⊨_v φ`. Upstream candidates.

## Main declarations

* `KripkeStructure` — accessibility plus a world-indexed family of
  first-order structures on a constant domain.
* `KripkeStructure.RealizeAt` — classical satisfaction at a world, with the
  transported `Formula.realize_*` simp set.
* `ModalFormula`, `ModalFormula.Realize` — modal formulas over embedded
  classical formulas, and Kripke satisfaction; `ModalFormula.dia` is the
  derived `◇ := ¬□¬`.

## Implementation notes

* Structures are carried as **terms**, not instances — a world-indexed
  family cannot be instance-based — so interfacing with instance-based
  mathlib API (`Formula.Realize`) threads `letI := K.interp w`.
* Accessibility is `Finset`-valued (computability-first, matching the
  team-semantics consumers); generalize to a `Prop`-valued relation when a
  consumer needs infinite branching.
* `ModalFormula` quantifiers bind **named** variables with
  `Function.update` semantics (the `Formula.all₁` / `ex₁` convention of
  `Core/Logic/FirstOrder/Binders.lean`), not de Bruijn indices: the modal
  layer's consumers carry named variables, and the embedding of classical
  formulas via `ofFormula` makes satisfaction commute by construction
  (`ModalFormula.realize_ofFormula` is `Iff.rfl`).
-/

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} {W M : Type*} {α : Type*}

/-- A constant-domain first-order Kripke structure: `Finset`-valued
    accessibility plus a `W`-indexed family of `L`-structures on the
    domain `M`. -/
structure KripkeStructure (L : Language.{u, v}) (W : Type*) (M : Type*) where
  /-- Accessibility relation (per-world set of accessible worlds). -/
  access : W → Finset W
  /-- World-indexed interpretation of the signature. -/
  interp : W → L.Structure M

namespace KripkeStructure

/-- Classical first-order satisfaction at a world — `K, w ⊨_v ψ`, mathlib's
    `Formula.Realize` in the structure the Kripke structure carries
    at `w`. -/
def RealizeAt (K : KripkeStructure L W M) (w : W) (ψ : L.Formula α)
    (v : α → M) : Prop :=
  @Formula.Realize _ _ (K.interp w) _ ψ v

@[simp] theorem realizeAt_not (K : KripkeStructure L W M) (w : W)
    (ψ : L.Formula α) (v : α → M) :
    K.RealizeAt w ψ.not v ↔ ¬ K.RealizeAt w ψ v := by
  letI := K.interp w
  exact Formula.realize_not

@[simp] theorem realizeAt_inf (K : KripkeStructure L W M) (w : W)
    (ψ₁ ψ₂ : L.Formula α) (v : α → M) :
    K.RealizeAt w (ψ₁ ⊓ ψ₂) v ↔
      K.RealizeAt w ψ₁ v ∧ K.RealizeAt w ψ₂ v := by
  letI := K.interp w
  exact Formula.realize_inf

@[simp] theorem realizeAt_sup (K : KripkeStructure L W M) (w : W)
    (ψ₁ ψ₂ : L.Formula α) (v : α → M) :
    K.RealizeAt w (ψ₁ ⊔ ψ₂) v ↔
      K.RealizeAt w ψ₁ v ∨ K.RealizeAt w ψ₂ v := by
  letI := K.interp w
  exact Formula.realize_sup

section Binders

variable [DecidableEq α]

@[simp] theorem realizeAt_all₁ (K : KripkeStructure L W M) (w : W) (x : α)
    (ψ : L.Formula α) (v : α → M) :
    K.RealizeAt w (Formula.all₁ x ψ) v ↔
      ∀ d : M, K.RealizeAt w ψ (Function.update v x d) := by
  letI := K.interp w
  exact Formula.realize_all₁

@[simp] theorem realizeAt_ex₁ (K : KripkeStructure L W M) (w : W) (x : α)
    (ψ : L.Formula α) (v : α → M) :
    K.RealizeAt w (Formula.ex₁ x ψ) v ↔
      ∃ d : M, K.RealizeAt w ψ (Function.update v x d) := by
  letI := K.interp w
  exact Formula.realize_ex₁

end Binders

end KripkeStructure

/-- Modal formulas over `L` with named free variables `α`: classical
    `L.Formula`s embedded wholesale via `ofFormula`, closed under the
    connectives, `□`, and named quantifiers (`◇` is derived —
    `ModalFormula.dia`). -/
inductive ModalFormula (L : Language.{u, v}) (α : Type*) where
  /-- An embedded classical (modal-free) formula. -/
  | ofFormula : L.Formula α → ModalFormula L α
  /-- Negation. -/
  | not : ModalFormula L α → ModalFormula L α
  /-- Conjunction. -/
  | inf : ModalFormula L α → ModalFormula L α → ModalFormula L α
  /-- Disjunction. -/
  | sup : ModalFormula L α → ModalFormula L α → ModalFormula L α
  /-- Necessity. -/
  | box : ModalFormula L α → ModalFormula L α
  /-- Universal quantification of a named variable. -/
  | all : α → ModalFormula L α → ModalFormula L α
  /-- Existential quantification of a named variable. -/
  | ex : α → ModalFormula L α → ModalFormula L α

namespace ModalFormula

/-- Possibility, derived: `◇φ := ¬□¬φ`. -/
def dia (φ : ModalFormula L α) : ModalFormula L α :=
  .not (.box (.not φ))

variable [DecidableEq α]

/-- Kripke satisfaction `K, w ⊨_v φ`: classical formulas evaluate at the
    world's structure, `□` quantifies over accessible worlds, and named
    quantifiers update the valuation. -/
def Realize (K : KripkeStructure L W M) :
    W → ModalFormula L α → (α → M) → Prop
  | w, .ofFormula ψ, v => K.RealizeAt w ψ v
  | w, .not φ, v => ¬ Realize K w φ v
  | w, .inf φ ψ, v => Realize K w φ v ∧ Realize K w ψ v
  | w, .sup φ ψ, v => Realize K w φ v ∨ Realize K w ψ v
  | w, .box φ, v => ∀ w' ∈ K.access w, Realize K w' φ v
  | w, .all x φ, v => ∀ d : M, Realize K w φ (Function.update v x d)
  | w, .ex x φ, v => ∃ d : M, Realize K w φ (Function.update v x d)

variable (K : KripkeStructure L W M) (w : W) (v : α → M)

/-- Embedded classical formulas realize classically — by construction. -/
@[simp] theorem realize_ofFormula (ψ : L.Formula α) :
    (ofFormula ψ : ModalFormula L α).Realize K w v ↔ K.RealizeAt w ψ v :=
  Iff.rfl

@[simp] theorem realize_not (φ : ModalFormula L α) :
    (ModalFormula.not φ).Realize K w v ↔ ¬ φ.Realize K w v :=
  Iff.rfl

@[simp] theorem realize_inf (φ ψ : ModalFormula L α) :
    (ModalFormula.inf φ ψ).Realize K w v ↔
      φ.Realize K w v ∧ ψ.Realize K w v :=
  Iff.rfl

@[simp] theorem realize_sup (φ ψ : ModalFormula L α) :
    (ModalFormula.sup φ ψ).Realize K w v ↔
      φ.Realize K w v ∨ ψ.Realize K w v :=
  Iff.rfl

@[simp] theorem realize_box (φ : ModalFormula L α) :
    (ModalFormula.box φ).Realize K w v ↔
      ∀ w' ∈ K.access w, φ.Realize K w' v :=
  Iff.rfl

@[simp] theorem realize_all (x : α) (φ : ModalFormula L α) :
    (ModalFormula.all x φ).Realize K w v ↔
      ∀ d : M, φ.Realize K w (Function.update v x d) :=
  Iff.rfl

@[simp] theorem realize_ex (x : α) (φ : ModalFormula L α) :
    (ModalFormula.ex x φ).Realize K w v ↔
      ∃ d : M, φ.Realize K w (Function.update v x d) :=
  Iff.rfl

@[simp] theorem realize_dia (φ : ModalFormula L α) :
    (dia φ).Realize K w v ↔ ∃ w' ∈ K.access w, φ.Realize K w' v := by
  simp only [dia, realize_not, realize_box, not_forall, not_not, exists_prop]

end ModalFormula

end FirstOrder.Language
