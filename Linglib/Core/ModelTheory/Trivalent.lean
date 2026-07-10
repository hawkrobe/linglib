/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.Consequence

/-!
# Trivalent propositional logic

Propositional syntax (`Trivalent.Formula`) evaluated into `Truth3` by the strong Kleene
tables (`Formula.eval`), with realization at a `Truth3.Designation` threshold
(`Formula.Realize`, notation `M ⊨[d] φ`) and consequence instantiating
`Core.Logic.Consequence.MixedConsequence`. The `k3` diagonal is strong Kleene logic and
the `lp` diagonal Priest's Logic of Paradox — same tables, different designated values
([cobreros-etal-2012]).

The API mirrors `Mathlib.ModelTheory` (`Realize`, per-constructor `@[simp]` lemmas, `⊨`
notation); consequence follows linglib's list-based `MixedConsequence` rather than
`Set`-based theories, matching the [cobreros-etal-2012] framework its consumers use.

## Main results

- `Formula.realize_neg` — the K3/LP duality: negation swaps the standards.
- `k3_no_tautologies`, `lp_all_satisfiable` — the all-`indet` model gives K3 no
  tautologies and LP no unsatisfiable formulas ([cobreros-etal-2012], Theorem 2).
- `lp_no_explosion` — LP is paraconsistent: `{φ ∧ ¬φ} ⊭ ψ`.

## References

[kleene-1952] [cobreros-etal-2012]
-/

namespace Trivalent

open Core.Logic.Consequence (MixedConsequence)

/-- Propositional formulas over an atom type
(`Semantics.Supervaluation.TCSFormula` instantiates it). -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom

/-- A trivalent model: a truth value for each atom. -/
abbrev Model (Atom : Type*) := Atom → Truth3

namespace Formula

variable {Atom : Type*}

/-- Evaluation by the strong Kleene tables — the semantic core shared by K3 and LP,
which differ only in designation. -/
def eval (M : Model Atom) : Formula Atom → Truth3
  | .atom a => M a
  | .neg φ => Truth3.neg (eval M φ)
  | .conj φ ψ => eval M φ ⊓ eval M ψ

@[simp] theorem eval_atom (M : Model Atom) (a : Atom) : eval M (.atom a) = M a := rfl

@[simp] theorem eval_neg (M : Model Atom) (φ : Formula Atom) :
    eval M (.neg φ) = Truth3.neg (eval M φ) := rfl

@[simp] theorem eval_conj (M : Model Atom) (φ ψ : Formula Atom) :
    eval M (.conj φ ψ) = eval M φ ⊓ eval M ψ := rfl

/-- Realization at a designation standard: the evaluation clears the threshold.
`Realize M .k3` is strong Kleene satisfaction, `Realize M .lp` Priest's LP. -/
def Realize (M : Model Atom) (d : Truth3.Designation) (φ : Formula Atom) : Prop :=
  Truth3.designated d (eval M φ)

@[inherit_doc] scoped notation:50 M " ⊨[" d "] " φ => Formula.Realize M d φ

@[simp] theorem realize_atom (M : Model Atom) (d : Truth3.Designation) (a : Atom) :
    (M ⊨[d] Formula.atom a) ↔ Truth3.designated d (M a) := Iff.rfl

/-- The K3/LP duality at formula level: negation swaps the standards. -/
@[simp] theorem realize_neg (M : Model Atom) (d : Truth3.Designation) (φ : Formula Atom) :
    (M ⊨[d] Formula.neg φ) ↔ ¬(M ⊨[d.dual] φ) := by
  have h := Truth3.designated_neg_iff d.dual (eval M φ)
  rwa [Truth3.Designation.dual_dual] at h

/-- Realization distributes over conjunction at either standard. -/
@[simp] theorem realize_conj (M : Model Atom) (d : Truth3.Designation)
    (φ ψ : Formula Atom) :
    (M ⊨[d] Formula.conj φ ψ) ↔ (M ⊨[d] φ) ∧ (M ⊨[d] ψ) :=
  Truth3.designated_inf d (eval M φ) (eval M ψ)

end Formula

open scoped Formula in
/-- Mixed consequence over designation standards: premises at `m`, conclusion at `n`. -/
abbrev Consequence {Atom : Type*} (m n : Truth3.Designation)
    (Γ : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  MixedConsequence (Formula.Realize (Atom := Atom)) m n Γ φ

/-! ### Meta-theorems -/

open scoped Formula

variable {Atom : Type*}

/-- In the all-indeterminate model every formula evaluates to `indet`. -/
theorem eval_allIndet (φ : Formula Atom) :
    Formula.eval (λ _ : Atom => Truth3.indet) φ = Truth3.indet := by
  induction φ with
  | atom _ => rfl
  | neg ψ ih => simp [ih, Truth3.neg]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ]

/-- K3 has no tautologies: nothing is designated in the all-indeterminate model
([cobreros-etal-2012], Theorem 2). -/
theorem k3_no_tautologies [Nonempty Atom] (φ : Formula Atom) :
    ¬(∀ M : Model Atom, M ⊨[.k3] φ) := by
  intro h
  have := h (λ _ => Truth3.indet)
  simp [Formula.Realize, eval_allIndet] at this

/-- Every formula is LP-satisfiable: the all-indeterminate model designates everything
([cobreros-etal-2012], Theorem 2). -/
theorem lp_all_satisfiable (φ : Formula Atom) :
    (λ _ : Atom => Truth3.indet) ⊨[.lp] φ := by
  simp [Formula.Realize, eval_allIndet]

/-- Explosion fails in LP: `{a ∧ ¬a} ⊭ b`, with countermodel `M a = indet`,
`M b = false`. -/
theorem lp_no_explosion :
    ∃ (φ ψ : Formula Bool), ¬Consequence .lp .lp [.conj φ (.neg φ)] ψ := by
  refine ⟨.atom Bool.true, .atom Bool.false, ?_⟩
  intro h
  have := h (λ b => if b then Truth3.indet else Truth3.false)
    (λ γ hγ => by
      simp at hγ; subst hγ
      simp [Formula.Realize, Truth3.neg])
  simp [Formula.Realize] at this

end Trivalent
