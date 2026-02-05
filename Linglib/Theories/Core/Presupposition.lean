import Linglib.Core.Kleene
import Linglib.Core.Proposition

/-!
# Presupposition

Presuppositional propositions and projection mechanisms.

`PrProp` decomposes a proposition into presupposition + assertion.
Filtering connectives (Heim 1983, Schlenker 2009) model how presuppositions
project through logical operators.

## References

- Heim, I. (1983). On the Projection Problem for Presuppositions.
- Schlenker, P. (2009). Local Contexts.
- von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context Dependency.
-/

namespace Core.Presupposition

open Core.Kleene
open Core.Proposition

/-- A presuppositional proposition: assertion + presupposition. -/
structure PrProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W -> Bool
  /-- The at-issue content (assertion). -/
  assertion : W -> Bool

namespace PrProp

variable {W : Type*}

/-- Evaluate a presuppositional proposition to three-valued truth. -/
def eval (p : PrProp W) : Prop3 W := λ w =>
  if p.presup w then TVal.ofBool (p.assertion w) else TVal.unk

/-- A PrProp is defined at w iff its presupposition holds at w. -/
def isDefinedAt (p : PrProp W) (w : W) : Prop := p.presup w = true

/-- The set of worlds where p is defined. -/
def definedWorlds (p : PrProp W) : W -> Prop := λ w => p.presup w = true

/-- Evaluation is defined iff presupposition holds. -/
theorem eval_isDefined (p : PrProp W) (w : W) :
    (p.eval w).isDefined = p.presup w := by
  simp only [eval, TVal.isDefined]
  cases hp : p.presup w <;> simp [TVal.ofBool, Option.isSome]

/-- Classical negation of a presuppositional proposition. -/
def neg (p : PrProp W) : PrProp W :=
  { presup := p.presup
  , assertion := λ w => !p.assertion w }

/-- Classical conjunction: both presuppositions must hold. -/
def and (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => p.assertion w && q.assertion w }

/-- Classical disjunction: both presuppositions must hold. -/
def or (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => p.assertion w || q.assertion w }

/-- Classical implication: both presuppositions must hold. -/
def imp (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => !p.assertion w || q.assertion w }

/-- Filtering conjunction: antecedent can satisfy consequent's presupposition. -/
def andFilter (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && (!p.assertion w || q.presup w)
  , assertion := λ w => p.assertion w && q.assertion w }

/-- Filtering implication: antecedent can satisfy consequent's presupposition. -/
def impFilter (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && (!p.assertion w || q.presup w)
  , assertion := λ w => !p.assertion w || q.assertion w }

/-- Filtering disjunction: disjuncts can satisfy each other's presuppositions. -/
def orFilter (p q : PrProp W) : PrProp W :=
  { presup := λ w =>
      (!p.assertion w || q.presup w) &&
      (!q.assertion w || p.presup w) &&
      (p.presup w || q.presup w)
  , assertion := λ w => p.assertion w || q.assertion w }

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

/-- Negation preserves presupposition. -/
theorem neg_presup (p : PrProp W) : (neg p).presup = p.presup := rfl

/-- Double negation preserves assertion. -/
theorem neg_neg_assertion (p : PrProp W) (w : W) :
    (neg (neg p)).assertion w = p.assertion w := by
  simp [neg, Bool.not_not]

/-- Filtering implication eliminates presupposition when antecedent entails it. -/
theorem impFilter_eliminates_presup (p q : PrProp W)
    (h : forall w, p.assertion w = true -> q.presup w = true) :
    (impFilter p q).presup = p.presup := by
  funext w
  simp only [impFilter]
  cases hp : p.presup w
  · simp
  · simp only [Bool.true_and]
    cases ha : p.assertion w
    · simp
    · simp [h w ha]

/-- When A(p) = P(q), filtering implication has trivial presupposition. -/
theorem impFilter_trivializes_presup (p q : PrProp W)
    (h : p.assertion = q.presup) :
    (impFilter p q).presup = p.presup := by
  funext w
  simp only [impFilter, h]
  cases hp : p.presup w
  · simp
  · simp only [Bool.true_and]
    cases hq : q.presup w <;> simp

/-- Create a presuppositionless proposition from a BProp. -/
def ofBProp (p : BProp W) : PrProp W :=
  { presup := λ _ => true
  , assertion := p }

/-- Create a tautological presupposition. -/
def top : PrProp W :=
  { presup := λ _ => true
  , assertion := λ _ => true }

/-- Create a contradictory presupposition. -/
def bot : PrProp W :=
  { presup := λ _ => true
  , assertion := λ _ => false }

/-- Create a presupposition failure (never defined). -/
def undefined : PrProp W :=
  { presup := λ _ => false
  , assertion := λ _ => false }

/-- ofBProp creates presuppositionless propositions. -/
theorem ofBProp_no_presup (p : BProp W) (w : W) : (ofBProp p).presup w = true := rfl

/-- ofBProp preserves assertion. -/
theorem ofBProp_assertion (p : BProp W) (w : W) : (ofBProp p).assertion w = p w := rfl

/-- Negation evaluation. -/
theorem eval_neg (p : PrProp W) (w : W) :
    (neg p).eval w = TVal.neg (p.eval w) := by
  simp only [eval, neg]
  split
  · simp [TVal.neg_ofBool]
  · rfl

/-- Classical conjunction evaluation (both defined). -/
theorem eval_and (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (and p q).eval w = TVal.and (p.eval w) (q.eval w) := by
  simp only [eval, and, hp, hq, Bool.true_and, ite_true, TVal.and_ofBool]

/-- Filtering implication when antecedent false: result is true. -/
theorem eval_impFilter_antecedent_false (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = false) :
    (impFilter p q).eval w = TVal.tt := by
  simp only [eval, impFilter, hp, ha, Bool.true_and, Bool.not_false, Bool.true_or,
             TVal.ofBool, TVal.tt, ite_true]

/-- Filtering implication when antecedent true: depends on consequent. -/
theorem eval_impFilter_antecedent_true (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = true) (hq : q.presup w = true) :
    (impFilter p q).eval w = TVal.ofBool (q.assertion w) := by
  simp only [eval, impFilter, hp, ha, hq, Bool.true_and, Bool.not_true, Bool.false_or,
             TVal.ofBool, ite_true]

/-- Strong entailment: p entails q at all worlds where both are defined. -/
def strongEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> q.presup w = true ->
    p.assertion w = true -> q.assertion w = true

/-- Strawson entailment: p entails q at worlds where p is defined and true. -/
def strawsonEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> p.assertion w = true ->
    q.presup w = true /\ (q.presup w = true -> q.assertion w = true)

/-- Presupposition projection: get the presupposition as a classical proposition. -/
def projectPresup (p : PrProp W) : BProp W := p.presup

/-- Assertion extraction: get the assertion as a classical proposition. -/
def projectAssertion (p : PrProp W) : BProp W := p.assertion

end PrProp

end Core.Presupposition
