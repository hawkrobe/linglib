/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Consequence

/-!
# Trivalent propositional logic

Propositional formulas built from atoms by negation and conjunction are evaluated into `SignType`
by Kleene's strong tables. A formula is realized at a designation standard when its value is
designated: K3 designates only `1` and LP also `0`, so one evaluation yields both logics, and mixed
consequence takes premises at one standard and conclusions at another, as Cobreros, Égré, Ripley
and van Rooij do.

## Main definitions

* `Trivalent.Formula`, `Trivalent.Formula.eval`: formulas and their strong Kleene values.
* `Trivalent.Formula.Realize`: realization at a designation standard, written `M ⊨[d] φ`.
* `Trivalent.Consequence`: mixed consequence over designation standards.

## Main results

* `Trivalent.Formula.realize_neg`, `Trivalent.Formula.isDual`: negation swaps the standards.
* `Trivalent.consequence_iff_dual`: `Γ ⊨ Δ` in K3 iff `¬Δ ⊨ ¬Γ` in LP.
* `Trivalent.Formula.realize_ofProp`: on a Boolean model both standards are classical truth.
* `Trivalent.k3_no_tautologies`, `Trivalent.lp_all_satisfiable`: the model sending every atom to
  `0` gives K3 no tautologies and LP no unsatisfiable formula.
* `Trivalent.lp_no_explosion`: LP is paraconsistent.

## Implementation notes

The API mirrors `Mathlib.ModelTheory` (`Realize`, per-constructor `@[simp]` lemmas, `⊨` notation),
and consequence is the multiple-conclusion, list-based `MixedConsequence` rather than theories as
sets.

## References

* [kleene-1952]
* [cobreros-etal-2012]
-/

@[expose] public section

namespace Trivalent

open SignType

open Consequence (IsDual MixedConsequence mixedConsequence_iff_dual)

/-- Propositional formulas over an atom type (`CobrerosEtAl2012.Formula` instantiates it). -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom

/-- A trivalent model assigns a value to each atom. -/
abbrev Model (Atom : Type*) := Atom → SignType

namespace Formula

variable {Atom : Type*}

/-- Evaluation by the strong Kleene tables — the semantic core shared by K3 and LP,
which differ only in designation. -/
def eval (M : Model Atom) : Formula Atom → SignType
  | .atom a => M a
  | .neg φ => -eval M φ
  | .conj φ ψ => eval M φ ⊓ eval M ψ

@[simp] theorem eval_atom (M : Model Atom) (a : Atom) : eval M (.atom a) = M a := rfl

@[simp] theorem eval_neg (M : Model Atom) (φ : Formula Atom) :
    eval M (.neg φ) = -eval M φ := rfl

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
theorem eval_ofProp (v : Atom → Bool) (φ : Formula Atom) :
    eval (fun a ↦ ofProp (v a)) φ = ofProp (evalBool v φ) := by
  induction φ with
  | atom a => rfl
  | neg φ ih => rw [eval_neg, evalBool_neg, ih]; cases evalBool v φ <;> decide
  | conj φ ψ ihφ ihψ =>
    rw [eval_conj, evalBool_conj, ihφ, ihψ]; cases evalBool v φ <;> cases evalBool v ψ <;> decide

/-- A formula is realized at a designation standard when its value clears the threshold, so
`Realize M .k3` is strong Kleene satisfaction and `Realize M .lp` is Priest's LP. -/
def Realize (M : Model Atom) (d : Trivalent.Designation) (φ : Formula Atom) : Prop :=
  d.threshold ≤ eval M φ

@[inherit_doc] scoped notation:50 M " ⊨[" d "] " φ => Formula.Realize M d φ

@[simp] theorem realize_atom (M : Model Atom) (d : Trivalent.Designation) (a : Atom) :
    (M ⊨[d] Formula.atom a) ↔ d.threshold ≤ M a := Iff.rfl

/-- Negation swaps the designation standards at the level of formulas. -/
@[simp] theorem realize_neg (M : Model Atom) (d : Trivalent.Designation) (φ : Formula Atom) :
    (M ⊨[d] Formula.neg φ) ↔ ¬(M ⊨[d.dual] φ) := by
  have h := Trivalent.Designation.dual_threshold_le_neg_iff d.dual (eval M φ)
  rwa [Trivalent.Designation.dual_dual] at h

/-- Each standard is dual to the other along negation ([cobreros-etal-2012], Definition 20). -/
theorem isDual (d : Trivalent.Designation) :
    IsDual Formula.neg (fun M : Model Atom ↦ Realize M d.dual) (Realize · d) := fun _ _ ↦ by
  simp

/-- On a Boolean model every standard is classical truth. -/
theorem realize_ofProp (v : Atom → Bool) (d : Trivalent.Designation) (φ : Formula Atom) :
    ((fun a ↦ ofProp (v a)) ⊨[d] φ) ↔ evalBool v φ = Bool.true := by
  rw [Realize, eval_ofProp, Trivalent.Designation.threshold_le_ofProp_iff]

/-- Realization distributes over conjunction at either standard. -/
@[simp] theorem realize_conj (M : Model Atom) (d : Trivalent.Designation)
    (φ ψ : Formula Atom) :
    (M ⊨[d] Formula.conj φ ψ) ↔ (M ⊨[d] φ) ∧ (M ⊨[d] ψ) :=
  le_inf_iff

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

/-- Mixed consequence takes premises at standard `m` and conclusions at standard `n`. -/
abbrev Consequence {Atom : Type*} (m n : Trivalent.Designation)
    (Γ Δ : List (Formula Atom)) : Prop :=
  MixedConsequence (Formula.Realize · m) (Formula.Realize · n) Γ Δ

/-! ### Meta-theorems -/

open scoped Formula

variable {Atom : Type*}

/-- Negation dualizes consequence, so `Γ ⊨ Δ` at `m, n` iff `¬Δ ⊨ ¬Γ` at the dual standards, and
K3 and LP are each other's duals ([cobreros-etal-2012], Lemma 6). -/
theorem consequence_iff_dual {m n : Trivalent.Designation} {Γ Δ : List (Formula Atom)} :
    Consequence m n Γ Δ ↔ Consequence n.dual m.dual (Δ.map .neg) (Γ.map .neg) :=
  mixedConsequence_iff_dual (Formula.isDual m) (Formula.isDual n)

/-- In the model sending every atom to `0` every formula evaluates to `0`. -/
theorem eval_const_zero (φ : Formula Atom) :
    Formula.eval (fun _ : Atom ↦ 0) φ = 0 := by
  induction φ with
  | atom _ => rfl
  | neg ψ ih => simp [ih]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ]

/-- K3 has no tautologies, since nothing is designated in the model sending every atom to `0`
([cobreros-etal-2012], Theorem 2). -/
theorem k3_no_tautologies [Nonempty Atom] (φ : Formula Atom) :
    ¬(∀ M : Model Atom, M ⊨[.k3] φ) := by
  intro h
  have := h fun _ ↦ 0
  simp [Formula.Realize, eval_const_zero] at this

/-- Every formula is LP-satisfiable, since the model sending every atom to `0` designates
everything ([cobreros-etal-2012], Theorem 2). -/
theorem lp_all_satisfiable (φ : Formula Atom) :
    (fun _ : Atom ↦ 0) ⊨[.lp] φ := by
  simp [Formula.Realize, eval_const_zero]

/-- Explosion fails in LP, since `{a ∧ ¬a} ⊭ b` with countermodel `M a = 0` and `M b = -1`. -/
theorem lp_no_explosion :
    ∃ (φ ψ : Formula Bool), ¬Consequence .lp .lp [.conj φ (.neg φ)] [ψ] := by
  refine ⟨.atom Bool.true, .atom Bool.false, fun h ↦ ?_⟩
  have := h (fun b ↦ if b then 0 else -1) fun γ hγ ↦ by
    simp only [List.mem_singleton] at hγ; subst hγ
    simp [Formula.Realize]
  simp [Formula.Realize] at this

end Trivalent
