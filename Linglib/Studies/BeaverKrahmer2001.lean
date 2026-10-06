/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Prod.Lex
public import Linglib.Logic.Trivalent.Propositional
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Data.Examples.BeaverKrahmer2001

/-!
# Beaver and Krahmer's partial account of presupposition projection

This file formalizes Beaver and Krahmer's defense of trivalent presupposition projection:
a lexical trigger contributes its complement through Blamey's transplication, and the
strong, middle and weak Kleene connectives each make rigid, distinct projection
predictions, none of which fits all of Soames's disjunctions. Flexibility is restored by
the assertion operator — the floating-A theory derives cancellation as the preferred
placement of meta-assertions — and a Stalnakerian update relation turns the partial
semantics into a dynamic account of accommodation.

## Main statements

- `strong_conditional_presupposition`, `middle_conditional_filters`,
  `weak_conditional_cumulative`: the three conditionals project a disjunctively weakened,
  a filtered, and a cumulative presupposition.
- `no_disjunction_table_projects_and_cancels`, `no_kleene_fits_soames_disjunctions`: no
  trivalent disjunction covers both projection and cancellation, and each of the three
  logics mispredicts some printed example.
- `printed_predictions`, `printed_verdicts`: the presuppositions the paper prints for each
  logic are the ones the semantics computes, and its verdicts are agreement with the
  intuitive presupposition.
- `KingOfFrance.denial_presupposes_nothing`, `StoppedOrStarted.basic_undefined`,
  `regret_conditional_presupposes_nothing`, `floating_a_rows`: the floating-A theory's
  preferred translations are unique and derive the cancellation readings.
- `update_iff`, `hearer_update_filters_then_asserts`, `monologue`: the paper's update
  relation is the substrate's Heimian partial update of a trivalent proposition, hearer
  accommodation is its image over candidate common grounds, and a monologue composes by
  sequencing.

## Implementation notes

* Atomic formulas are bivalent, as the paper's valuations are, so a formula is undefined
  only through presupposition failure. The three logics index one connective constructor,
  so that the floating-A machinery counts surface occurrences; the paper's definitions of
  the middle and weak connectives in strong Kleene terms are theorems.
* Transplication is defined by the paper's own interdefinability formula over ∂; the
  assertion and denial operators at the value level are `Trivalent.metaAssert` and its
  composite with negation.
* Incoherence counts non-presuppositional subformula occurrences. Reproducing the paper's
  printed degrees requires not substituting inside the argument of an assertion operator,
  which the text leaves open; the literal reading changes the degrees but no preference
  verdict. The preference order reads "optimal, then fewest assertions" lexicographically.
* The schematizations of the Soames disjunctions follow the paper's own schema for the
  stopped-or-started example; the judgments and printed predictions are the rows of
  `Data/Examples/BeaverKrahmer2001.json`.
* Not modelled: the partial type theory of §3 (partial assignments live in
  `Logic/Assignment.lean`), the Montagovian fragment of §4 and the appendix's optimal
  trees, and the plausibility grading sketched for the weighing-scale example.

## TODO

* The quantifier rows of the paper's Fact 2: meta-assertion commutes with the strong
  Kleene quantifiers, but a strong Kleene universal as an infimum over `Trivalent` has no
  substrate home yet.

## References

* [D. Beaver, E. Krahmer, *A Partial Account of Presupposition Projection*
  (2001)][beaver-krahmer-2001]
* [S. Blamey, *Partial Logic* (1986)][blamey-1986]
* [D. A. Bochvar, *On a Three-valued Logical Calculus and Its Application to the Analysis
  of the Paradoxes of the Classical Extended Functional Calculus* (1937)][bochvar-1937]
* [D. Beaver, *The Kinematics of Presupposition* (1992)][beaver-1992]
* [S. C. Kleene, *Introduction to Metamathematics* (1952)][kleene-1952]
* [S. Peters, *A Truth-Conditional Formulation of Karttunen's Account of Presupposition*
  (1975)][peters-1975]
* [E. Krahmer, *Partiality and Dynamics* (1994)][krahmer-1994]
* [D. T. Langendoen, H. B. Savin, *The Projection Problem for Presuppositions*
  (1971)][langendoen-savin-1971]
* [S. Soames, *A Projection Problem for Speaker Presuppositions* (1979)][soames-1979]
* [G. Link, *Prespie in Pragmatic Wonderland or: The Projection Problem for
  Presuppositions Revisited* (1986)][link-1986]
* [L. Karttunen, *Presuppositions of Compound Sentences* (1973)][karttunen-1973]
* [D. Lewis, *Scorekeeping in a Language Game* (1979)][lewis-1979]
* [R. C. Stalnaker, *Pragmatic Presuppositions* (1974)][stalnaker-1974]
* [I. Heim, *On the Projection Problem for Presuppositions* (1983)][heim-1983]
* [D. Beaver, *Presupposition and Assertion in Dynamic Semantics* (2001)][beaver-2001]
* [R. Muskens, *Meaning and Partiality* (1995)][muskens-1995]
-/

@[expose] public section

namespace BeaverKrahmer2001

open Trivalent (metaAssert presuppose meetMiddle joinMiddle meetWeak joinWeak ofBool Prop3)

/-! ### Transplication, assertion, denial

The binary presupposition operator is [blamey-1986]'s transplication; the unary ∂ it is
interdefinable with is Beaver's ([beaver-1992], `Trivalent.presuppose`), and the assertion
operator is Bochvar's ([bochvar-1937], `Trivalent.metaAssert`). -/

/-- Transplication `φ⟨π⟩` attaches the elementary presupposition `π` to `φ`, by the
paper's interdefinability formula `(∂π ∧ φ) ∨ ¬∂π` over the strong Kleene connectives. -/
def transplicate (a p : Trivalent) : Trivalent :=
  (presuppose p ⊓ a) ⊔ Trivalent.neg (presuppose p)

theorem transplicate_eq_true_iff (a p : Trivalent) :
    transplicate a p = .true ↔ p = .true ∧ a = .true := by cases a <;> cases p <;> decide

theorem transplicate_eq_false_iff (a p : Trivalent) :
    transplicate a p = .false ↔ p = .true ∧ a = .false := by cases a <;> cases p <;> decide

theorem transplicate_eq_indet_iff (a p : Trivalent) :
    transplicate a p = .indet ↔ p ≠ .true ∨ a = .indet := by cases a <;> cases p <;> decide

/-- Meta-denial asserts falsity: `D = A ∘ ¬`. -/
def metaDeny (a : Trivalent) : Trivalent := metaAssert (Trivalent.neg a)

/-- The maximal presupposition of a value is that it is defined: `P = A ∨ D`. -/
def presupVal (a : Trivalent) : Trivalent := metaAssert a ⊔ metaDeny a

theorem presupVal_eq_true_iff (a : Trivalent) : presupVal a = .true ↔ a ≠ .indet := by
  cases a <;> decide

/-- The maximal presupposition is a classical value. -/
theorem presupVal_ne_indet (a : Trivalent) : presupVal a ≠ .indet := by cases a <;> decide

/-! ### The three Kleene logics

Strong Kleene is the lattice structure of `Trivalent`; the middle (Peters) and weak
(Bochvar-internal) connectives are `Trivalent.meetMiddle` and `Trivalent.meetWeak` with
their joins ([peters-1975]; the name *middle Kleene* is [krahmer-1994]'s). The conditional
of each logic is the derived form `¬a ∨ b`. -/

inductive Kleene | strong | middle | weak
  deriving DecidableEq, Fintype, Repr

inductive Connective | conj | disj | imp
  deriving DecidableEq, Fintype, Repr

/-- The conjunction of each logic. -/
def Kleene.meet : Kleene → Trivalent → Trivalent → Trivalent
  | .strong => (· ⊓ ·)
  | .middle => meetMiddle
  | .weak => meetWeak

/-- The disjunction of each logic. -/
def Kleene.join : Kleene → Trivalent → Trivalent → Trivalent
  | .strong => (· ⊔ ·)
  | .middle => joinMiddle
  | .weak => joinWeak

/-- The truth table of a connective in a logic, with the conditional the derived
`¬a ∨ b`; the tables match the paper's for all three logics. -/
def Connective.eval : Connective → Kleene → Trivalent → Trivalent → Trivalent
  | .conj, k => k.meet
  | .disj, k => k.join
  | .imp, k => fun a b ↦ k.join (Trivalent.neg a) b

/-- The middle conjunction in strong Kleene terms. -/
theorem meetMiddle_eq (a b : Trivalent) :
    meetMiddle a b = (a ⊓ b) ⊔ (a ⊓ Trivalent.neg a) := by
  cases a <;> cases b <;> decide

/-- The middle disjunction in strong Kleene terms. -/
theorem joinMiddle_eq (a b : Trivalent) :
    joinMiddle a b = (a ⊔ b) ⊓ (a ⊔ Trivalent.neg a) := by
  cases a <;> cases b <;> decide

/-- The middle conditional in strong Kleene terms. -/
theorem impMiddle_eq (a b : Trivalent) :
    Connective.eval .imp .middle a b = (Trivalent.neg a ⊔ b) ⊓ (a ⊔ Trivalent.neg a) := by
  cases a <;> cases b <;> decide

/-- The weak conjunction in strong Kleene terms. -/
theorem meetWeak_eq (a b : Trivalent) :
    meetWeak a b = (a ⊓ b) ⊔ (a ⊓ Trivalent.neg a) ⊔ (b ⊓ Trivalent.neg b) := by
  cases a <;> cases b <;> decide

/-- The weak disjunction in strong Kleene terms. -/
theorem joinWeak_eq (a b : Trivalent) :
    joinWeak a b = (a ⊔ b) ⊓ (a ⊔ Trivalent.neg a) ⊓ (b ⊔ Trivalent.neg b) := by
  cases a <;> cases b <;> decide

/-- The weak conditional in strong Kleene terms. -/
theorem impWeak_eq (a b : Trivalent) :
    Connective.eval .imp .weak a b =
      (Trivalent.neg a ⊔ b) ⊓ (a ⊔ Trivalent.neg a) ⊓ (b ⊔ Trivalent.neg b) := by
  cases a <;> cases b <;> decide

/-! ### Projection at the value level -/

/-- Negation projects: `P¬φ = Pφ`. -/
theorem presupVal_neg (a : Trivalent) : presupVal (Trivalent.neg a) = presupVal a := by
  cases a <;> decide

/-- A transplication presupposes its subscript and whatever its body presupposes:
`P(φ⟨π⟩) = Aπ ∧ Pφ`. -/
theorem presupVal_transplicate (a p : Trivalent) :
    presupVal (transplicate a p) = metaAssert p ⊓ presupVal a := by
  cases a <;> cases p <;> decide

theorem presupVal_imp_strong (a b : Trivalent) :
    presupVal (Connective.eval .imp .strong a b) =
      (presupVal a ⊔ metaAssert b) ⊓ (metaDeny a ⊔ presupVal b) := by
  cases a <;> cases b <;> decide

theorem presupVal_imp_middle (a b : Trivalent) :
    presupVal (Connective.eval .imp .middle a b) =
      presupVal a ⊓ (metaDeny a ⊔ presupVal b) := by
  cases a <;> cases b <;> decide

theorem presupVal_imp_weak (a b : Trivalent) :
    presupVal (Connective.eval .imp .weak a b) = presupVal a ⊓ presupVal b := by
  cases a <;> cases b <;> decide

/-- The strong disjunction projects conditionalized presuppositions. -/
theorem presupVal_join_strong (a b : Trivalent) :
    presupVal (a ⊔ b) = (presupVal a ⊔ metaAssert b) ⊓ (presupVal b ⊔ metaAssert a) := by
  cases a <;> cases b <;> decide

/-- The middle disjunction projects the left disjunct's presupposition. -/
theorem presupVal_join_middle (a b : Trivalent) :
    presupVal (joinMiddle a b) = presupVal a ⊓ (metaAssert a ⊔ presupVal b) := by
  cases a <;> cases b <;> decide

/-- The weak disjunction projects every presupposition. -/
theorem presupVal_join_weak (a b : Trivalent) :
    presupVal (joinWeak a b) = presupVal a ⊓ presupVal b := by
  cases a <;> cases b <;> decide

/-- Bochvar's cancelling (external) negation. -/
def cancelNeg : Trivalent → Trivalent
  | .true => .false
  | .false => .true
  | .indet => .true

/-- Cancelling negation is ordinary negation over an assertion: `∼φ = ¬Aφ`. -/
theorem cancelNeg_eq_neg_metaAssert (a : Trivalent) :
    cancelNeg a = Trivalent.neg (metaAssert a) := by
  cases a <;> rfl

/-- No single trivalent disjunction both projects the left disjunct's presupposition and
cancels it against a denying right disjunct, on the paper's own schema for the Soames
disjunctions. -/
theorem no_disjunction_table_projects_and_cancels :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent,
      (∀ π γ δ : Bool,
        f (transplicate (ofBool γ) (ofBool π)) (ofBool δ) ≠ .indet ↔ π = true) ∧
      ∀ π γ : Bool,
        f (transplicate (ofBool γ) (ofBool π)) (Trivalent.neg (ofBool π)) ≠ .indet := by
  rintro ⟨f, h18, h21⟩
  have h1 := h18 false true true
  have h2 := h21 false true
  simp [transplicate, ofBool, presuppose, Trivalent.neg] at h1 h2
  exact h2 h1

/-! ### Formulas

One language hosts all three logics: a connective node carries its `Kleene` index, so the
floating-A machinery below counts occurrences of the surface form rather than of a
strong Kleene expansion. Valuations are bivalent, so only presupposition failure makes a
formula undefined. -/

inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conn : Connective → Kleene → Formula Atom → Formula Atom → Formula Atom
  | transpl : Formula Atom → Formula Atom → Formula Atom
  | assert : Formula Atom → Formula Atom
  deriving DecidableEq, Repr

/-- A bivalent valuation of the atoms. -/
abbrev Valuation (Atom : Type*) := Atom → Bool

namespace Formula

variable {Atom : Type*}

/-- Evaluation into three-valued truth. -/
def eval (V : Valuation Atom) : Formula Atom → Trivalent
  | atom a => ofBool (V a)
  | neg φ => Trivalent.neg (eval V φ)
  | conn c k φ ψ => c.eval k (eval V φ) (eval V ψ)
  | transpl φ π => transplicate (eval V φ) (eval V π)
  | assert φ => metaAssert (eval V φ)

@[simp] theorem eval_atom (V : Valuation Atom) (a : Atom) :
    eval V (atom a) = ofBool (V a) := rfl
@[simp] theorem eval_neg (V : Valuation Atom) (φ : Formula Atom) :
    eval V (neg φ) = Trivalent.neg (eval V φ) := rfl
@[simp] theorem eval_conn (V : Valuation Atom) (c k) (φ ψ : Formula Atom) :
    eval V (conn c k φ ψ) = c.eval k (eval V φ) (eval V ψ) := rfl
@[simp] theorem eval_transpl (V : Valuation Atom) (φ π : Formula Atom) :
    eval V (transpl φ π) = transplicate (eval V φ) (eval V π) := rfl
@[simp] theorem eval_assert (V : Valuation Atom) (φ : Formula Atom) :
    eval V (assert φ) = metaAssert (eval V φ) := rfl

/-- The substrate's strong Kleene formulas embed. -/
def ofFormula : Trivalent.Formula Atom → Formula Atom
  | .atom a => atom a
  | .neg φ => neg (ofFormula φ)
  | .conj φ ψ => conn .conj .strong (ofFormula φ) (ofFormula ψ)

/-- On a bivalent valuation the embedding evaluates as the substrate does on the
corresponding trivalent model. -/
theorem eval_ofFormula (V : Valuation Atom) (φ : Trivalent.Formula Atom) :
    eval V (ofFormula φ) = Trivalent.Formula.eval (ofBool ∘ V) φ := by
  induction φ with
  | atom a => rfl
  | neg φ ih => simp [ofFormula, ih]
  | conj φ ψ ih₁ ih₂ => simp [ofFormula, ih₁, ih₂, Connective.eval, Kleene.meet]

/-- Meta-denial at formula level is `Dφ = A¬φ`. -/
def deny (φ : Formula Atom) : Formula Atom := assert (neg φ)

/-- The maximal presupposition as a formula is `Pφ = Aφ ∨ Dφ`. -/
def presup (φ : Formula Atom) : Formula Atom := conn .disj .strong (assert φ) (deny φ)

theorem eval_presup (V : Valuation Atom) (φ : Formula Atom) :
    eval V (presup φ) = presupVal (eval V φ) := rfl

/-- The maximal presupposition evaluates classically, so rewriting by the assertion
algebra yields a transplication-free formula. -/
theorem presup_ne_indet (V : Valuation Atom) (φ : Formula Atom) :
    eval V (presup φ) ≠ .indet := by
  rw [eval_presup]; exact presupVal_ne_indet _

/-- Two formulas are equivalent when they evaluate alike at every valuation. -/
def Equiv (φ ψ : Formula Atom) : Prop := ∀ V, eval V φ = eval V ψ

/-- Entailment preserves truth. -/
def Entails (φ ψ : Formula Atom) : Prop := ∀ V, eval V φ = .true → eval V ψ = .true

/-- `φ` presupposes `π` when `φ` is undefined wherever `π` is untrue. -/
def Presupposes (φ π : Formula Atom) : Prop := ∀ V, eval V π ≠ .true → eval V φ = .indet

section DecidableDefs
variable [Fintype Atom] [DecidableEq Atom]

instance {φ ψ : Formula Atom} : Decidable (Equiv φ ψ) := inferInstanceAs (Decidable (∀ _, _))
instance {φ ψ : Formula Atom} : Decidable (Entails φ ψ) := inferInstanceAs (Decidable (∀ _, _))
instance {φ ψ : Formula Atom} : Decidable (Presupposes φ ψ) :=
  inferInstanceAs (Decidable (∀ _, _))

end DecidableDefs

/-- Disjunction is derived in the strong logic: `φ ∨ ψ = ¬(¬φ ∧ ¬ψ)`. -/
theorem disj_strong_eq (φ ψ : Formula Atom) :
    Equiv (conn .disj .strong φ ψ) (neg (conn .conj .strong (neg φ) (neg ψ))) := fun V ↦ by
  simp [Connective.eval, Kleene.join, Kleene.meet]

/-- The conditional of every logic is `¬φ ∨ ψ` in that logic. -/
theorem imp_eq (k : Kleene) (φ ψ : Formula Atom) :
    Equiv (conn .imp k φ ψ) (conn .disj k (neg φ) ψ) := fun _ ↦ rfl

/-- The middle conjunction is a strong Kleene compound of its arguments. -/
theorem conj_middle_eq (φ ψ : Formula Atom) :
    Equiv (conn .conj .middle φ ψ)
      (conn .disj .strong (conn .conj .strong φ ψ) (conn .conj .strong φ (neg φ))) :=
  fun V ↦ by
    simp only [eval_conn, eval_neg, Connective.eval, Kleene.meet, Kleene.join]
    exact meetMiddle_eq _ _

/-- The weak conjunction is a strong Kleene compound of its arguments. -/
theorem conj_weak_eq (φ ψ : Formula Atom) :
    Equiv (conn .conj .weak φ ψ)
      (conn .disj .strong (conn .disj .strong (conn .conj .strong φ ψ)
        (conn .conj .strong φ (neg φ))) (conn .conj .strong ψ (neg ψ))) := fun V ↦ by
  simp only [eval_conn, eval_neg, Connective.eval, Kleene.meet, Kleene.join]
  exact meetWeak_eq _ _

/-- Semantic presupposition is entailment by the disjunction of truth and falsity
conditions: `φ` presupposes `π` iff `φ ∨ ¬φ ⊨ π`. -/
theorem presupposes_iff_entails (φ π : Formula Atom) :
    Presupposes φ π ↔ Entails (conn .disj .strong φ (neg φ)) π := by
  simp only [Presupposes, Entails, eval_neg, eval_conn, Connective.eval, Kleene.join]
  refine forall_congr' fun V ↦ ?_
  generalize eval V φ = a
  generalize eval V π = b
  cases a <;> cases b <;> decide

/-- `Pφ` is a presupposition of `φ`. -/
theorem presupposes_presup (φ : Formula Atom) : Presupposes φ (presup φ) := fun V h ↦ by
  by_contra hne
  exact h ((presupVal_eq_true_iff _).2 hne)

/-- `Pφ` is the maximal presupposition: it entails every presupposition of `φ`. -/
theorem presup_strongest {φ π : Formula Atom} (h : Presupposes φ π) :
    Entails (presup φ) π := fun V hV ↦ by
  rw [eval_presup, presupVal_eq_true_iff] at hV
  by_contra hne
  exact hV (h V hne)

/-! ### The assertion algebra

The twelve equivalences of the paper's Fact 1 rewrite `A` and `D` through every
constructor, so `Pφ` reduces to a transplication-free classical formula. -/

theorem assert_atom (a : Atom) : Equiv (assert (atom a)) (atom a) := fun V ↦ by
  show metaAssert (ofBool (V a)) = ofBool (V a)
  cases V a <;> rfl

theorem deny_atom (a : Atom) : Equiv (deny (atom a)) (neg (atom a)) := fun V ↦ by
  show metaAssert (Trivalent.neg (ofBool (V a))) = Trivalent.neg (ofBool (V a))
  cases V a <;> rfl

theorem assert_neg (φ : Formula Atom) : Equiv (assert (neg φ)) (deny φ) := fun _ ↦ rfl

theorem deny_neg (φ : Formula Atom) : Equiv (deny (neg φ)) (assert φ) := fun V ↦ by
  show metaAssert (Trivalent.neg (Trivalent.neg (eval V φ))) = metaAssert (eval V φ)
  rw [Trivalent.neg_neg]

theorem assert_conj (φ ψ : Formula Atom) :
    Equiv (assert (conn .conj .strong φ ψ)) (conn .conj .strong (assert φ) (assert ψ)) :=
  fun V ↦ by simp [Connective.eval, Kleene.meet, Trivalent.metaAssert_inf]

theorem deny_conj (φ ψ : Formula Atom) :
    Equiv (deny (conn .conj .strong φ ψ)) (conn .disj .strong (deny φ) (deny ψ)) := fun V ↦ by
  simp only [deny, eval_assert, eval_neg, eval_conn, Connective.eval, Kleene.meet, Kleene.join]
  generalize eval V φ = a
  generalize eval V ψ = b
  cases a <;> cases b <;> decide

theorem assert_disj (φ ψ : Formula Atom) :
    Equiv (assert (conn .disj .strong φ ψ)) (conn .disj .strong (assert φ) (assert ψ)) :=
  fun V ↦ by simp [Connective.eval, Kleene.join, Trivalent.metaAssert_sup]

theorem deny_disj (φ ψ : Formula Atom) :
    Equiv (deny (conn .disj .strong φ ψ)) (conn .conj .strong (deny φ) (deny ψ)) := fun V ↦ by
  simp only [deny, eval_assert, eval_neg, eval_conn, Connective.eval, Kleene.meet, Kleene.join]
  generalize eval V φ = a
  generalize eval V ψ = b
  cases a <;> cases b <;> decide

theorem assert_imp (φ ψ : Formula Atom) :
    Equiv (assert (conn .imp .strong φ ψ)) (conn .disj .strong (deny φ) (assert ψ)) :=
  fun V ↦ by
    simp only [deny, eval_assert, eval_neg, eval_conn, Connective.eval, Kleene.join]
    generalize eval V φ = a
    generalize eval V ψ = b
    cases a <;> cases b <;> decide

theorem deny_imp (φ ψ : Formula Atom) :
    Equiv (deny (conn .imp .strong φ ψ)) (conn .conj .strong (assert φ) (deny ψ)) :=
  fun V ↦ by
    simp only [deny, eval_assert, eval_neg, eval_conn, Connective.eval, Kleene.meet,
      Kleene.join]
    generalize eval V φ = a
    generalize eval V ψ = b
    cases a <;> cases b <;> decide

theorem assert_transpl (φ π : Formula Atom) :
    Equiv (assert (transpl φ π)) (conn .conj .strong (assert π) (assert φ)) := fun V ↦ by
  simp only [eval_assert, eval_transpl, eval_conn, Connective.eval, Kleene.meet]
  generalize eval V φ = a
  generalize eval V π = b
  cases a <;> cases b <;> decide

theorem deny_transpl (φ π : Formula Atom) :
    Equiv (deny (transpl φ π)) (conn .conj .strong (assert π) (deny φ)) := fun V ↦ by
  simp only [deny, eval_assert, eval_neg, eval_transpl, eval_conn, Connective.eval,
    Kleene.meet]
  generalize eval V φ = a
  generalize eval V π = b
  cases a <;> cases b <;> decide

/-- Cancelling negation at formula level is negation over an assertion. -/
theorem eval_neg_assert (V : Valuation Atom) (φ : Formula Atom) :
    eval V (neg (assert φ)) = cancelNeg (eval V φ) := by
  rw [eval_neg, eval_assert, cancelNeg_eq_neg_metaAssert]

/-! ### Projection at formula level -/

/-- Negation projects presuppositions unchanged. -/
theorem presup_neg (φ : Formula Atom) : Equiv (presup (neg φ)) (presup φ) := fun V ↦ by
  simp [eval_presup, presupVal_neg]

/-- A transplication presupposes its subscript on top of its body's presupposition. -/
theorem presup_transpl (φ π : Formula Atom) :
    Equiv (presup (transpl φ π)) (conn .conj .strong (assert π) (presup φ)) := fun V ↦ by
  simp only [eval_presup, eval_transpl, eval_conn, eval_assert, Connective.eval,
    Kleene.meet, presupVal_transplicate]

/-- The strong conditional projects only a disjunctively weakened presupposition: the
famous too-weak prediction for a presupposing antecedent. -/
theorem strong_conditional_presupposition (φ ψ : Formula Atom) :
    Equiv (presup (conn .imp .strong φ ψ))
      (conn .conj .strong (conn .disj .strong (presup φ) (assert ψ))
        (conn .disj .strong (deny φ) (presup ψ))) := fun V ↦ by
  simp only [eval_presup, eval_conn, Connective.eval, Kleene.meet, Kleene.join,
    eval_assert, deny, eval_neg]
  exact presupVal_imp_strong _ _

/-- The middle conditional filters: the antecedent's presupposition projects intact, the
consequent's survives unless the antecedent is denied. -/
theorem middle_conditional_filters (φ ψ : Formula Atom) :
    Equiv (presup (conn .imp .middle φ ψ))
      (conn .conj .strong (presup φ) (conn .disj .strong (deny φ) (presup ψ))) := fun V ↦ by
  simp only [eval_presup, eval_conn, Connective.eval, Kleene.meet, Kleene.join,
    eval_assert, deny, eval_neg]
  exact presupVal_imp_middle _ _

/-- The weak conditional is cumulative: every elementary presupposition projects, the
analysis of [langendoen-savin-1971]. -/
theorem weak_conditional_cumulative (φ ψ : Formula Atom) :
    Equiv (presup (conn .imp .weak φ ψ)) (conn .conj .strong (presup φ) (presup ψ)) :=
  fun V ↦ by
    simp only [eval_presup, eval_conn, Connective.eval, Kleene.meet]
    exact presupVal_imp_weak _ _

/-! ### The floating-A theory

A sentence's translation set keeps or meta-asserts each transplication; the preferred
translations are the defined ones of least incoherence, and of those the ones with fewest
assertions ([link-1986] supplies the ingredients). Incoherence counts the
non-presuppositional subformula occurrences whose replacement by a tautology or a
contradiction preserves the truth conditions; occurrences inside a subscript or inside an
assertion are not substituted. -/

/-- The translation set keeps or meta-asserts each transplication. -/
def translations : Formula Atom → List (Formula Atom)
  | atom a => [atom a]
  | neg φ => (translations φ).map neg
  | conn c k φ ψ => (translations φ).flatMap fun φ' ↦ (translations ψ).map (conn c k φ')
  | transpl φ π =>
      let ts := (translations φ).flatMap fun φ' ↦ (translations π).map (transpl φ')
      ts ++ ts.map assert
  | assert φ => (translations φ).map assert

/-- The number of assertion operators. -/
def assertCount : Formula Atom → ℕ
  | atom _ => 0
  | neg φ => assertCount φ
  | conn _ _ φ ψ => assertCount φ + assertCount ψ
  | transpl φ π => assertCount φ + assertCount π
  | assert φ => assertCount φ + 1

/-- `contexts` lists the one-hole contexts at the non-presuppositional occurrences:
subscripts and asserted material are not substitution sites. -/
def contexts : Formula Atom → List (Formula Atom → Formula Atom)
  | atom _ => [id]
  | neg φ => id :: (contexts φ).map (neg ∘ ·)
  | conn c k φ ψ =>
      id :: ((contexts φ).map (fun k' χ ↦ conn c k (k' χ) ψ) ++
        (contexts ψ).map (fun k' χ ↦ conn c k φ (k' χ)))
  | transpl φ π => id :: (contexts φ).map (fun k' χ ↦ transpl (k' χ) π)
  | assert _ => [id]

/-- The language's own tautology. -/
def top [Inhabited Atom] : Formula Atom :=
  conn .disj .strong (atom default) (neg (atom default))

/-- The language's own contradiction. -/
def bot [Inhabited Atom] : Formula Atom := neg top

theorem eval_top [Inhabited Atom] (V : Valuation Atom) : eval V top = .true := by
  simp only [top, eval_conn, eval_neg, eval_atom, Connective.eval, Kleene.join]
  cases V default <;> decide

theorem eval_bot [Inhabited Atom] (V : Valuation Atom) : eval V bot = .false := by
  simp [bot, eval_top]

/-- Two formulas are true together at every valuation. -/
def TrueIff (φ ψ : Formula Atom) : Prop := ∀ V, eval V φ = .true ↔ eval V ψ = .true

variable [Inhabited Atom] [Fintype Atom] [DecidableEq Atom]

instance {φ ψ : Formula Atom} : Decidable (TrueIff φ ψ) := inferInstanceAs (Decidable (∀ _, _))

/-- How many substitution sites are redundant: replacement by the tautology preserves the
truth conditions. -/
def nonInformativity (φ : Formula Atom) : ℕ :=
  (contexts φ).countP fun k ↦ decide (TrueIff φ (k top))

/-- How many substitution sites are inconsistent: replacement by the contradiction
preserves the truth conditions. -/
def inconsistency (φ : Formula Atom) : ℕ :=
  (contexts φ).countP fun k ↦ decide (TrueIff φ (k bot))

/-- Total incoherence is the sum of the two degrees. -/
def incoherence (φ : Formula Atom) : ℕ := nonInformativity φ + inconsistency φ

/-- A formula is defined when it is somewhere classical. -/
def Defined (φ : Formula Atom) : Prop := ∃ V, eval V φ ≠ .indet

instance {φ : Formula Atom} : Decidable (Defined φ) := inferInstanceAs (Decidable (∃ _, _))

/-- A translation is optimal when it is defined and of least incoherence among the
defined. -/
def Optimal (S : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  Defined φ ∧ ∀ ψ ∈ S, Defined ψ → incoherence φ ≤ incoherence ψ

instance {S : List (Formula Atom)} {φ : Formula Atom} : Decidable (Optimal S φ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The preference rank orders by optimality first and then by the number of assertions,
lexicographically. -/
def rank (S : List (Formula Atom)) (φ : Formula Atom) : Bool ×ₗ ℕ :=
  toLex (decide (¬ Optimal S φ), assertCount φ)

/-- `Prefers` is the paper's `γ ≺ δ`. -/
def Prefers (S : List (Formula Atom)) (γ δ : Formula Atom) : Prop := rank S γ < rank S δ

/-- A translation is preferred when nothing in the set is preferred over it. -/
def Preferred (S : List (Formula Atom)) (γ : Formula Atom) : Prop :=
  γ ∈ S ∧ ∀ δ ∈ S, ¬ Prefers S δ γ

instance {S : List (Formula Atom)} {γ δ : Formula Atom} : Decidable (Prefers S γ δ) :=
  inferInstanceAs (Decidable (_ < _))
instance {S : List (Formula Atom)} {γ : Formula Atom} : Decidable (Preferred S γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Formula

/-! ### The paper's atoms and worked cancellations

One four-element atom type hosts every schematized example; the subscript atom is `p`
throughout, the prejacent bodies are `q` and `r`. -/

inductive Atom | p | q | r | s
  deriving DecidableEq, Fintype, Repr, Inhabited

open Formula

/-! *The king of France is not bald, since there is no king of France* denies a
presupposing sentence and its presupposition together. -/
namespace KingOfFrance

/-- The basic translation `¬(q⟨p⟩) ∧̈ ¬p`, nowhere true and incoherent. -/
def basic : Formula Atom :=
  conn .conj .weak (neg (transpl (atom .q) (atom .p))) (neg (atom .p))

/-- The preferred translation meta-asserts the presupposing conjunct. -/
def preferred : Formula Atom :=
  conn .conj .weak (neg (assert (transpl (atom .q) (atom .p)))) (neg (atom .p))

/-- The preferred translation of the denial presupposes nothing: cancellation derived. -/
theorem denial_presupposes_nothing : ∀ V, eval V (presup preferred) = .true := by decide

end KingOfFrance

/-! In *Either Bill has just stopped smoking, or else he's just started smoking* the two
disjuncts carry inconsistent presuppositions. -/
namespace StoppedOrStarted

/-- The basic translation `q⟨p⟩ ∨̈ r⟨¬p⟩`. -/
def basic : Formula Atom :=
  conn .disj .weak (transpl (atom .q) (atom .p)) (transpl (atom .r) (neg (atom .p)))

/-- The preferred translation meta-asserts both disjuncts. -/
def preferred : Formula Atom :=
  conn .disj .weak (assert (transpl (atom .q) (atom .p)))
    (assert (transpl (atom .r) (neg (atom .p))))

/-- The basic translation presupposes a contradiction: it is nowhere defined. -/
theorem basic_undefined : ¬ Defined basic := by decide

end StoppedOrStarted

/-! In *If Mary is sad, then Bill regrets that Mary is sad* the antecedent satisfies the
consequent's presupposition. -/
namespace SadRegret

/-- The basic translation `p →̈ q⟨p⟩`. -/
def basic : Formula Atom := conn .imp .weak (atom .p) (transpl (atom .q) (atom .p))

/-- The preferred translation meta-asserts the consequent. -/
def preferred : Formula Atom :=
  conn .imp .weak (atom .p) (assert (transpl (atom .q) (atom .p)))

/-- The preferred translation presupposes nothing, although the weak conditional is
cumulative: the conditional's apparent presupposition is filtered by preference. -/
theorem regret_conditional_presupposes_nothing : ∀ V, eval V (presup preferred) = .true := by
  decide

end SadRegret

/-- The paper's printed degrees under the assertion-opaque reading: the king-of-France
denial's preferred translation is incoherent to degree two, and half-asserting the
stopped-or-started disjunction leaves degree one. -/
example : incoherence KingOfFrance.preferred = 2 := by decide
example : incoherence (conn .disj .weak (assert (transpl (atom .q) (atom .p)))
    (transpl (atom .r) (neg (atom .p))) : Formula Atom) = 1 := by decide

/-- Preference is not a total order: two optimal translations with equally many
assertions tie. -/
theorem prefers_not_total :
    ∃ (S : List (Formula Atom)) (γ δ : Formula Atom), γ ≠ δ ∧ γ ∈ S ∧ δ ∈ S ∧
      ¬ Prefers S γ δ ∧ ¬ Prefers S δ γ := by
  refine ⟨[atom .p, atom .q], atom .p, atom .q, ?_⟩
  decide

/-! ### Update and accommodation

The paper's `update` relation is the substrate's Heimian partial update of a trivalent
proposition (`CCP.Partial.ofProp3`), its domain condition the presupposition operator and
its output the meta-asserted content; the hearer-side `update⋆` over candidate common
grounds is its `PFun.image`, and a monologue composes by sequencing. Accommodation, after
[lewis-1979] and [stalnaker-1974], is the filtering this image performs. -/

section Update

open DynamicSemantics

variable {W : Type*}

/-- The paper's `update ξ σ τ` says, in its own vocabulary, that `σ` supports the
presupposition `P ∘ ξ` throughout and that `τ` is `σ` intersected with the asserted
content `A ∘ ξ`. -/
theorem update_iff (ξ : Prop3 W) (σ τ : Set W) :
    (σ, τ) ∈ (CCP.Partial.ofProp3 ξ).graph' ↔
      σ ⊆ {i | presupVal (ξ i) = .true} ∧ τ = σ ∩ {i | metaAssert (ξ i) = .true} := by
  show τ ∈ CCP.Partial.ofProp3 ξ σ ↔ _
  rw [CCP.Partial.mem_ofProp3]
  refine and_congr (forall₂_congr fun i _ ↦ ?_) ?_
  · rw [Set.mem_ofPred_eq, presupVal_eq_true_iff]
  · have e : {w ∈ σ | ξ w = .true} = σ ∩ {i | metaAssert (ξ i) = .true} :=
      Set.ext fun i ↦ by simp [Trivalent.metaAssert_eq_true_iff]
    rw [e]

/-- `update⋆` is the image: a candidate output common ground is the update of some
candidate input. -/
theorem hearer_update (ξ : Prop3 W) (cgs : Set (Set W)) (τ : Set W) :
    τ ∈ (CCP.Partial.ofProp3 ξ).image cgs ↔
      ∃ σ ∈ cgs, (σ, τ) ∈ (CCP.Partial.ofProp3 ξ).graph' :=
  PFun.mem_image _ _ _

/-- The two-stage procedure filters out the candidate common grounds incompatible with
the presuppositions, then updates each remaining one with the assertion. -/
theorem hearer_update_filters_then_asserts (ξ : Prop3 W) (cgs : Set (Set W)) :
    (CCP.Partial.ofProp3 ξ).image cgs =
      (fun σ ↦ σ ∩ ξ.posExt) '' {σ ∈ cgs | (CCP.Partial.ofProp3 ξ).Admits σ} := by
  ext τ
  rw [PFun.mem_image]
  constructor
  · rintro ⟨σ, hσ, h⟩
    rw [CCP.Partial.mem_ofProp3] at h
    exact ⟨σ, ⟨hσ, h.1⟩, h.2.symm⟩
  · rintro ⟨σ, ⟨hσ, hd⟩, rfl⟩
    exact ⟨σ, hσ, (CCP.Partial.mem_ofProp3 ..).2 ⟨hd, rfl⟩⟩

/-- A hearer making no assumptions updates from the full powerset; two sentences compose
by sequencing the updates. -/
theorem monologue (ξ₁ ξ₂ : Prop3 W) :
    (CCP.Partial.ofProp3 ξ₂).image ((CCP.Partial.ofProp3 ξ₁).image Set.univ) =
      (PartialUpdate.seq (CCP.Partial.ofProp3 ξ₁) (CCP.Partial.ofProp3 ξ₂)).image
        Set.univ :=
  (PartialUpdate.image_seq _ _ _).symm

end Update

/-! ### The paper's judgments

The rows with a `schema` feature are the paper's schematized examples; `intuitive` names
the presupposition the paper reports, the per-logic `…Predicts` features the ones it
prints, and the `…Verdict` features its correctness judgments. The rows with `basic` and
`preferred` features are the floating-A cancellations. -/

/-- The schema a row's `schema` feature names, at each logic. -/
def schemas (k : Kleene) : List (String × Formula Atom) :=
  [("q<p>", transpl (atom .q) (atom .p)),
   ("~q<p>", neg (transpl (atom .q) (atom .p))),
   ("q<p> -> r", conn .imp k (transpl (atom .q) (atom .p)) (atom .r)),
   ("p -> q<p>", conn .imp k (atom .p) (transpl (atom .q) (atom .p))),
   ("q<p> | r", conn .disj k (transpl (atom .q) (atom .p)) (atom .r)),
   ("r | q<p>", conn .disj k (atom .r) (transpl (atom .q) (atom .p))),
   ("q<p> | ~p", conn .disj k (transpl (atom .q) (atom .p)) (neg (atom .p))),
   ("q<p> | r<~p>",
     conn .disj k (transpl (atom .q) (atom .p)) (transpl (atom .r) (neg (atom .p)))),
   ("p -> q<r>", conn .imp k (atom .p) (transpl (atom .q) (atom .r)))]

/-- The presupposition a row's `intuitive` or `…Predicts` feature names. -/
def presups : List (String × Formula Atom) :=
  [("p", atom .p), ("r", atom .r),
   ("p | r", conn .disj .strong (atom .p) (atom .r)),
   ("p -> r", conn .imp .strong (atom .p) (atom .r)),
   ("none", Formula.top)]

/-- A verdict feature read as agreement with the intuitive presupposition. -/
def verdictTable : List (String × Bool) := [("correct", true), ("incorrect", false)]

/-- The basic and preferred translations a row's floating-A features name. -/
def translationsTable : List (String × Formula Atom) :=
  [("~(q<p>) &w ~p", KingOfFrance.basic), ("~A(q<p>) &w ~p", KingOfFrance.preferred),
   ("q<p> |w r<~p>", StoppedOrStarted.basic),
   ("A(q<p>) |w A(r<~p>)", StoppedOrStarted.preferred),
   ("p ->w q<p>", SadRegret.basic), ("p ->w A(q<p>)", SadRegret.preferred)]

/-- The prediction feature of each logic. -/
def Kleene.predictsKey : Kleene → String
  | .strong => "strongPredicts"
  | .middle => "middlePredicts"
  | .weak => "weakPredicts"

/-- The verdict feature of each logic. -/
def Kleene.verdictKey : Kleene → String
  | .strong => "strongVerdict"
  | .middle => "middleVerdict"
  | .weak => "weakVerdict"

/-- The presupposition the paper prints for each logic is the maximal presupposition the
semantics computes. -/
theorem printed_predictions : ∀ k : Kleene, ∀ row ∈ Examples.all,
    ∀ φ ∈ row.parse? "schema" (schemas k), ∀ π ∈ row.parse? k.predictsKey presups,
      Formula.Equiv (Formula.presup φ) π := by
  decide +kernel

/-- The paper's verdicts compare the predicted with the intuitive presupposition. -/
theorem printed_verdicts : ∀ k : Kleene, ∀ row ∈ Examples.all,
    ∀ φ ∈ row.parse? "schema" (schemas k), ∀ ι ∈ row.parse? "intuitive" presups,
    ∀ v ∈ row.parse? k.verdictKey verdictTable,
      (v = true ↔ Formula.Equiv (Formula.presup φ) ι) := by
  decide +kernel

/-- No single logic fits the Soames disjunction data: each of the three mispredicts the
intuitive presupposition of some printed example ([soames-1979];
[van-der-sandt-1989]'s conclusion, which the paper accepts before restoring flexibility
with the floating A). -/
theorem no_kleene_fits_soames_disjunctions : ∀ k : Kleene, ∃ row ∈ Examples.all,
    ∃ φ ∈ row.parse? "schema" (schemas k), ∃ ι ∈ row.parse? "intuitive" presups,
      ¬ Formula.Equiv (Formula.presup φ) ι := by
  decide +kernel

/-- The floating-A winners the paper names are the preferred translations, uniquely. -/
theorem floating_a_rows : ∀ row ∈ Examples.all,
    ∀ φ ∈ row.parse? "basic" translationsTable,
    ∀ γ ∈ row.parse? "preferred" translationsTable,
      Formula.Preferred (Formula.translations φ) γ ∧
        ∀ δ ∈ Formula.translations φ, Formula.Preferred (Formula.translations φ) δ → δ = γ := by
  decide +kernel

end BeaverKrahmer2001
