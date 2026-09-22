/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Trivalent
import Linglib.Logic.Consequence

/-!
# Trivalent propositional logic

Propositional syntax (`Trivalent.Formula`) evaluated into `Trivalent` by the strong Kleene
tables (`Formula.eval`), with realization at a `Trivalent.Designation` threshold
(`Formula.Realize`, notation `M ⊨[d] φ`) and consequence instantiating
`Consequence.MixedConsequence`. The `k3` diagonal is strong Kleene logic and
the `lp` diagonal Priest's Logic of Paradox — same tables, different designated values
([cobreros-etal-2012]).

The API mirrors `Mathlib.ModelTheory` (`Realize`, per-constructor `@[simp]` lemmas, `⊨`
notation); consequence follows linglib's list-based `MixedConsequence` rather than
`Set`-based theories, matching the [cobreros-etal-2012] framework its consumers use.

## Main results

- `Formula.realize_neg` — the K3/LP duality: negation swaps the standards.
- `Formula.realize_ofBool` — on a Boolean model both standards are classical truth
  (`Formula.evalBool`).
- `k3_no_tautologies`, `lp_all_satisfiable` — the all-`indet` model gives K3 no
  tautologies and LP no unsatisfiable formulas ([cobreros-etal-2012], Theorem 2).
- `lp_no_explosion` — LP is paraconsistent: `{φ ∧ ¬φ} ⊭ ψ`.

## References

[kleene-1952] [cobreros-etal-2012]
-/

namespace Trivalent

open Consequence (MixedConsequence)

/-- Propositional formulas over an atom type (`CobrerosEtAl2012.Formula` instantiates it). -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom

/-- A trivalent model: a truth value for each atom. -/
abbrev Model (Atom : Type*) := Atom → Trivalent

namespace Formula

variable {Atom : Type*}

/-- Evaluation by the strong Kleene tables — the semantic core shared by K3 and LP,
which differ only in designation. -/
def eval (M : Model Atom) : Formula Atom → Trivalent
  | .atom a => M a
  | .neg φ => Trivalent.neg (eval M φ)
  | .conj φ ψ => eval M φ ⊓ eval M ψ

@[simp] theorem eval_atom (M : Model Atom) (a : Atom) : eval M (.atom a) = M a := rfl

@[simp] theorem eval_neg (M : Model Atom) (φ : Formula Atom) :
    eval M (.neg φ) = Trivalent.neg (eval M φ) := rfl

@[simp] theorem eval_conj (M : Model Atom) (φ ψ : Formula Atom) :
    eval M (.conj φ ψ) = eval M φ ⊓ eval M ψ := rfl

/-- Classical evaluation on a Boolean valuation. -/
def evalBool (v : Atom → Bool) : Formula Atom → Bool
  | .atom a => v a
  | .neg φ => !evalBool v φ
  | .conj φ ψ => evalBool v φ && evalBool v ψ

@[simp] theorem evalBool_atom (v : Atom → Bool) (a : Atom) : evalBool v (.atom a) = v a := rfl

@[simp] theorem evalBool_neg (v : Atom → Bool) (φ : Formula Atom) :
    evalBool v (.neg φ) = !evalBool v φ := rfl

@[simp] theorem evalBool_conj (v : Atom → Bool) (φ ψ : Formula Atom) :
    evalBool v (.conj φ ψ) = (evalBool v φ && evalBool v ψ) := rfl

/-- On a Boolean model the strong Kleene tables are the classical ones. -/
theorem eval_ofBool (v : Atom → Bool) (φ : Formula Atom) :
    eval (Trivalent.ofBool ∘ v) φ = Trivalent.ofBool (evalBool v φ) := by
  induction φ with
  | atom a => rfl
  | neg φ ih => simp [ih, Trivalent.neg_ofBool]
  | conj φ ψ ihφ ihψ => simp [ihφ, ihψ]

/-- Realization at a designation standard: the evaluation clears the threshold.
`Realize M .k3` is strong Kleene satisfaction, `Realize M .lp` Priest's LP. -/
def Realize (M : Model Atom) (d : Trivalent.Designation) (φ : Formula Atom) : Prop :=
  Trivalent.designated d (eval M φ)

@[inherit_doc] scoped notation:50 M " ⊨[" d "] " φ => Formula.Realize M d φ

@[simp] theorem realize_atom (M : Model Atom) (d : Trivalent.Designation) (a : Atom) :
    (M ⊨[d] Formula.atom a) ↔ Trivalent.designated d (M a) := Iff.rfl

/-- The K3/LP duality at formula level: negation swaps the standards. -/
@[simp] theorem realize_neg (M : Model Atom) (d : Trivalent.Designation) (φ : Formula Atom) :
    (M ⊨[d] Formula.neg φ) ↔ ¬(M ⊨[d.dual] φ) := by
  have h := Trivalent.designated_neg_iff d.dual (eval M φ)
  rwa [Trivalent.Designation.dual_dual] at h

/-- On a Boolean model every standard is classical truth. -/
theorem realize_ofBool (v : Atom → Bool) (d : Trivalent.Designation) (φ : Formula Atom) :
    (Trivalent.ofBool ∘ v ⊨[d] φ) ↔ evalBool v φ = Bool.true := by
  rw [Realize, eval_ofBool, Trivalent.designated_ofBool]

/-- Realization distributes over conjunction at either standard. -/
@[simp] theorem realize_conj (M : Model Atom) (d : Trivalent.Designation)
    (φ ψ : Formula Atom) :
    (M ⊨[d] Formula.conj φ ψ) ↔ (M ⊨[d] φ) ∧ (M ⊨[d] ψ) :=
  Trivalent.designated_inf d (eval M φ) (eval M ψ)

/-- Disjunction, defined classically from negation and conjunction. -/
def disj (φ ψ : Formula Atom) : Formula Atom := .neg (.conj (.neg φ) (.neg ψ))

/-- The material conditional `¬(φ ∧ ¬ψ)`. -/
def imp (φ ψ : Formula Atom) : Formula Atom := .neg (.conj φ (.neg ψ))

@[simp] theorem realize_disj (M : Model Atom) (d : Trivalent.Designation) (φ ψ : Formula Atom) :
    (M ⊨[d] φ.disj ψ) ↔ (M ⊨[d] φ) ∨ (M ⊨[d] ψ) := by
  simp [disj, or_iff_not_imp_left]

/-- A conditional is realized at `d` iff its consequent is whenever its antecedent is realized
at the dual standard. -/
@[simp] theorem realize_imp (M : Model Atom) (d : Trivalent.Designation) (φ ψ : Formula Atom) :
    (M ⊨[d] φ.imp ψ) ↔ ((M ⊨[d.dual] φ) → (M ⊨[d] ψ)) := by
  simp [imp]

end Formula

open scoped Formula in
/-- Mixed consequence over designation standards: premises at `m`, conclusion at `n`. -/
abbrev Consequence {Atom : Type*} (m n : Trivalent.Designation)
    (Γ : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  MixedConsequence (Formula.Realize (Atom := Atom)) m n Γ φ

/-! ### Meta-theorems -/

open scoped Formula

variable {Atom : Type*}

/-- In the all-indeterminate model every formula evaluates to `indet`. -/
theorem eval_allIndet (φ : Formula Atom) :
    Formula.eval (λ _ : Atom => Trivalent.indet) φ = Trivalent.indet := by
  induction φ with
  | atom _ => rfl
  | neg ψ ih => simp [ih, Trivalent.neg]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ]

/-- K3 has no tautologies: nothing is designated in the all-indeterminate model
([cobreros-etal-2012], Theorem 2). -/
theorem k3_no_tautologies [Nonempty Atom] (φ : Formula Atom) :
    ¬(∀ M : Model Atom, M ⊨[.k3] φ) := by
  intro h
  have := h (λ _ => Trivalent.indet)
  simp [Formula.Realize, eval_allIndet] at this

/-- Every formula is LP-satisfiable: the all-indeterminate model designates everything
([cobreros-etal-2012], Theorem 2). -/
theorem lp_all_satisfiable (φ : Formula Atom) :
    (λ _ : Atom => Trivalent.indet) ⊨[.lp] φ := by
  simp [Formula.Realize, eval_allIndet]

/-- Explosion fails in LP: `{a ∧ ¬a} ⊭ b`, with countermodel `M a = indet`,
`M b = false`. -/
theorem lp_no_explosion :
    ∃ (φ ψ : Formula Bool), ¬Consequence .lp .lp [.conj φ (.neg φ)] ψ := by
  refine ⟨.atom Bool.true, .atom Bool.false, ?_⟩
  intro h
  have := h (λ b => if b then Trivalent.indet else Trivalent.false)
    (λ γ hγ => by
      simp at hγ; subst hγ
      simp [Formula.Realize, Trivalent.neg])
  simp [Formula.Realize] at this

end Trivalent
