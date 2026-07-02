/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Logic.WordModel
import Mathlib.Data.Finset.Basic
import Linglib.Core.Order.IterateFixedPoint

/-!
# The vectorial modal μ-calculus on words

The modal μ-calculus ([kozen-1983]) interpreted over word models, in the **vectorial**
presentation of [yolyan-comer-2026] §4: a finite system of equations `Xⱼ = θⱼ` between
quantifier-free modal formulas plus a designated variable, evaluated as the least fixed
point of the induced monotone operator (Knaster–Tarski). By Bekić's theorem the
vectorial form is equivalent to nested `μ`-binders; formalizing it directly avoids
binder bookkeeping and matches the paper's own proofs.

Formulas here are the negation-free fragment `μML꜀₊` — the ambient of
[yolyan-comer-2026] Thm. 8 — extended with negated *label* atoms (`nlabel`), which keeps
negation off recursion variables (so monotonicity is structural) while covering
processes like Warao nasal spreading `N′ = μX.(N ∨ (¬T ∧ ♦X))`.

`◇` (`dia`) is the forward modality reading the successor position, `♦` (`bdia`) the
backward modality reading the predecessor.

## Main definitions

* `ModalMu.Formula` — quantifier-free modal formulas over labels `α` and `n` recursion
  variables; `Formula.Realize` — satisfaction at a pointed word under a valuation.
* `ModalMu.System` — a vectorial formula; `System.op` — its monotone operator on
  valuations; `System.sem` — the least-fixed-point valuation; `System.Sat` — pointed
  satisfaction of the designated variable.

## Main results

* `Formula.Realize.mono` — satisfaction is monotone in the valuation (negation-free).
* `System.op_sem` — `sem` is a fixed point; `System.sem_eq_iterate` — the iteration
  certificate (via `OrderHom.lfp_eq_iterate_bot`), the computable route to `sem`.
-/

namespace Subregular.Logic.ModalMu

variable {α : Type*} {n : ℕ}

/-- Quantifier-free modal formulas over labels `α` and `n` recursion variables: the
negation-free fragment, with negation on **class atoms** only (`nlabel`) — so recursion
variables occur only positively and monotonicity is structural. `label`/`nlabel` test
the current position's symbol against a `Finset` class (featural predicates like V or N
are single atoms; a symbol test is the singleton case). `initial`/`final` are the edge
tests (the literature's `min`/`max`); `dia` (`◇`) reads the successor position, `bdia`
(`♦`) the predecessor. -/
inductive Formula (α : Type*) (n : ℕ) where
  | tru
  | fls
  | initial
  | final
  | label (s : Finset α)
  | nlabel (s : Finset α)
  | var (X : Fin n)
  | and (φ ψ : Formula α n)
  | or (φ ψ : Formula α n)
  | dia (φ : Formula α n)
  | bdia (φ : Formula α n)
  deriving DecidableEq

/-- Satisfaction at a pointed word `(w, i)` under a valuation `U` of the recursion
variables. -/
def Formula.Realize (w : WordModel α) (U : Fin n → Set ℕ) : ℕ → Formula α n → Prop
  | _, .tru => True
  | _, .fls => False
  | i, .initial => i = 0
  | i, .final => i + 1 = w.length
  | i, .label s => ∃ a ∈ s, w[i]? = some a
  | i, .nlabel s => ∀ a ∈ s, w[i]? ≠ some a
  | i, .var X => i ∈ U X
  | i, .and φ ψ => φ.Realize w U i ∧ ψ.Realize w U i
  | i, .or φ ψ => φ.Realize w U i ∨ ψ.Realize w U i
  | i, .dia φ => ∃ j, w.succ? i = some j ∧ φ.Realize w U j
  | i, .bdia φ => ∃ j, w.pred? i = some j ∧ φ.Realize w U j

section RealizeSimp

variable {w : WordModel α} {U : Fin n → Set ℕ} {i : ℕ} {s : Finset α} {φ ψ : Formula α n}

@[simp] theorem Formula.realize_tru : (Formula.tru : Formula α n).Realize w U i := trivial

@[simp] theorem Formula.realize_fls : ¬ (Formula.fls : Formula α n).Realize w U i :=
  not_false

@[simp] theorem Formula.realize_initial :
    (Formula.initial : Formula α n).Realize w U i ↔ i = 0 := .rfl

@[simp] theorem Formula.realize_final :
    (Formula.final : Formula α n).Realize w U i ↔ i + 1 = w.length := .rfl

@[simp] theorem Formula.realize_label :
    (Formula.label s : Formula α n).Realize w U i ↔ ∃ a ∈ s, w[i]? = some a := .rfl

@[simp] theorem Formula.realize_nlabel :
    (Formula.nlabel s : Formula α n).Realize w U i ↔ ∀ a ∈ s, w[i]? ≠ some a := .rfl

@[simp] theorem Formula.realize_var {X : Fin n} :
    (Formula.var X : Formula α n).Realize w U i ↔ i ∈ U X := .rfl

@[simp] theorem Formula.realize_and :
    (φ.and ψ).Realize w U i ↔ φ.Realize w U i ∧ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_or :
    (φ.or ψ).Realize w U i ↔ φ.Realize w U i ∨ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_dia :
    φ.dia.Realize w U i ↔ ∃ j, w.succ? i = some j ∧ φ.Realize w U j := .rfl

@[simp] theorem Formula.realize_bdia :
    φ.bdia.Realize w U i ↔ ∃ j, w.pred? i = some j ∧ φ.Realize w U j := .rfl

end RealizeSimp

instance Formula.instDecidableRealize [DecidableEq α] (w : WordModel α)
    (U : Fin n → Set ℕ) [∀ X, DecidablePred (· ∈ U X)] :
    ∀ (i : ℕ) (φ : Formula α n), Decidable (φ.Realize w U i)
  | _, .tru => .isTrue trivial
  | _, .fls => .isFalse not_false
  | i, .initial => inferInstanceAs (Decidable (i = 0))
  | i, .final => inferInstanceAs (Decidable (i + 1 = w.length))
  | i, .label s => inferInstanceAs (Decidable (∃ a ∈ s, w[i]? = some a))
  | i, .nlabel s => inferInstanceAs (Decidable (∀ a ∈ s, w[i]? ≠ some a))
  | i, .var X => inferInstanceAs (Decidable (i ∈ U X))
  | i, .and φ ψ =>
      @instDecidableAnd _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .or φ ψ =>
      @instDecidableOr _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .dia φ =>
      match h : w.succ? i with
      | none => .isFalse (by simp [Formula.realize_dia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_dia, h])
            (instDecidableRealize w U j φ)
  | i, .bdia φ =>
      match h : w.pred? i with
      | none => .isFalse (by simp [Formula.realize_bdia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_bdia, h])
            (instDecidableRealize w U j φ)

/-- Satisfaction is monotone in the valuation: recursion variables occur only
positively. -/
theorem Formula.Realize.mono {w : WordModel α} {U V : Fin n → Set ℕ} (hUV : U ≤ V) :
    ∀ {φ : Formula α n} {i : ℕ}, φ.Realize w U i → φ.Realize w V i
  | .tru, _, h => h
  | .fls, _, h => h
  | .initial, _, h => h
  | .final, _, h => h
  | .label _, _, h => h
  | .nlabel _, _, h => h
  | .var X, _, h => hUV X h
  | .and _ _, _, h => ⟨h.1.mono hUV, h.2.mono hUV⟩
  | .or _ _, _, h => h.imp (·.mono hUV) (·.mono hUV)
  | .dia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩
  | .bdia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩

/-- A vectorial formula ([yolyan-comer-2026] §4): a finite system of equations
`Xⱼ = θⱼ` plus a designated variable. -/
structure System (α : Type*) (n : ℕ) where
  /-- The right-hand side of each equation. -/
  eqs : Fin n → Formula α n
  /-- The designated variable whose satisfaction is the system's. -/
  out : Fin n

namespace System

variable (χ : System α n) (w : WordModel α)

/-- The monotone operator a system induces on valuations (the paper's `F_w^χ`). -/
def op : (Fin n → Set ℕ) →o (Fin n → Set ℕ) where
  toFun U X := {i | (χ.eqs X).Realize w U i}
  monotone' _ _ hUV _ _ h := h.mono hUV

@[simp] theorem mem_op {U : Fin n → Set ℕ} {X : Fin n} {i : ℕ} :
    i ∈ χ.op w U X ↔ (χ.eqs X).Realize w U i := .rfl

/-- The least-fixed-point valuation (Knaster–Tarski). -/
noncomputable def sem : Fin n → Set ℕ := OrderHom.lfp (χ.op w)

/-- `sem` is a fixed point of the system operator. -/
theorem op_sem : χ.op w (χ.sem w) = χ.sem w := (χ.op w).map_lfp

/-- `sem` is below every prefixed point. -/
theorem sem_le {U : Fin n → Set ℕ} (hU : χ.op w U ≤ U) : χ.sem w ≤ U :=
  (χ.op w).lfp_le hU

/-- **Iteration certificate**: an iterate of `⊥` fixed by the operator is `sem`. The
computable route to the least fixed point — no continuity needed. -/
theorem sem_eq_iterate {k : ℕ} (h : χ.op w ((χ.op w)^[k] ⊥) = (χ.op w)^[k] ⊥) :
    χ.sem w = (χ.op w)^[k] ⊥ :=
  OrderHom.lfp_eq_iterate_bot _ h

/-- `w, i ⊨ χ`: the designated variable holds at `i` in the least fixed point. -/
def Sat (i : ℕ) : Prop := i ∈ χ.sem w χ.out

end System

end Subregular.Logic.ModalMu
