import Linglib.Core.Logic.Truth3
import Linglib.Core.Semantics.Proposition

/-!
# Partial Propositions (PrProp)
@cite{heim-1983} @cite{schlenker-2009} @cite{von-fintel-1999} @cite{geurts-2005} @cite{belnap-1970}

`PrProp W` is linglib's canonical representation of **partial propositions** —
propositions that may be undefined at some worlds. The two fields are:
- `presup` (= defined/assertive): whether the proposition says anything at w
- `assertion` (= content): what it says when defined

This general type has multiple linguistic interpretations:
- **Presupposition**: `presup` = presupposition holds; failure = undefined
  (@cite{heim-1983}, @cite{schlenker-2009})
- **Conditional assertion**: `presup` = assertive; failure = nonassertive
  (@cite{belnap-1970}: "(A/B) is assertive_w just in case A is true_w")
- **Homogeneity**: `presup` = all atoms agree; failure = truth-value gap
  (@cite{kriz-2016})

The choice of **connective system** (how gaps behave under ∧/∨) is
orthogonal to `PrProp` itself — see `Truth3.GapPolicy`:
- Classical (`PrProp.and`): both must be defined
- Filtering (`PrProp.andFilter`): one can satisfy the other's presupposition
- Belnap (`PrProp.andBelnap`): gaps are skipped, defined operands contribute

-/

namespace Core.Presupposition

open Core.Duality
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
  if p.presup w then Truth3.ofBool (p.assertion w) else .indet

/-- A PrProp is defined at w iff its presupposition holds at w. -/
def isDefinedAt (p : PrProp W) (w : W) : Prop := p.presup w = true

/-- The set of worlds where p is defined. -/
def definedWorlds (p : PrProp W) : W -> Prop := λ w => p.presup w = true

/-- Evaluation is defined iff presupposition holds. -/
theorem eval_isDefined (p : PrProp W) (w : W) :
    (p.eval w).isDefined = p.presup w := by
  simp only [eval]
  cases hp : p.presup w
  · simp [Truth3.isDefined]
  · cases p.assertion w <;> simp [Truth3.ofBool, Truth3.isDefined]

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
    (neg p).eval w = Truth3.neg (p.eval w) := by
  simp only [eval, neg]
  split
  · simp [Truth3.neg_ofBool]
  · rfl

/-- Classical conjunction evaluation (both defined). -/
theorem eval_and (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (and p q).eval w = Truth3.meet (p.eval w) (q.eval w) := by
  simp only [eval, and, hp, hq, Bool.true_and, ite_true, Truth3.meet_ofBool]

/-- Filtering implication when antecedent false: result is true. -/
theorem eval_impFilter_antecedent_false (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = false) :
    (impFilter p q).eval w = .true := by
  simp only [eval, impFilter, hp, ha, Bool.true_and, Bool.not_false, Bool.true_or,
             Truth3.ofBool, ite_true]

/-- Filtering implication when antecedent true: depends on consequent. -/
theorem eval_impFilter_antecedent_true (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = true) (hq : q.presup w = true) :
    (impFilter p q).eval w = Truth3.ofBool (q.assertion w) := by
  simp only [eval, impFilter, hp, ha, hq, Bool.true_and, Bool.not_true, Bool.false_or,
             Truth3.ofBool, ite_true]

/-- Strong entailment: p entails q at all worlds where both are defined. -/
def strongEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> q.presup w = true ->
    p.assertion w = true -> q.assertion w = true

/-- Strawson entailment: p entails q at worlds where p is defined and true. -/
def strawsonEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> p.assertion w = true ->
    q.presup w = true /\ (q.presup w = true -> q.assertion w = true)

/-- Strawson equivalence: mutual Strawson entailment. -/
def strawsonEquiv (p q : PrProp W) : Prop :=
  strawsonEntails p q ∧ strawsonEntails q p

/-- Flexible accommodation disjunction.

Each disjunct is evaluated only against worlds where its own presupposition
holds. The overall presupposition is the disjunction of the individual
presuppositions. This handles conflicting presuppositions (p ∧ q = ⊥):
standard disjunction and filtering disjunction both fail for this case,
but flexible accommodation correctly predicts presupposition p ∨ q and
allows the disjunction to be false.

Formally, this is the static counterpart of Yagi's dynamic update:
  s[φ ∨ ψ] = s[χ][φ] ∪ s[ω][ψ], where s[χ] ∪ s[ω] = s
When presuppositions conflict, χ = ¬q and ω = ¬p, giving pointwise:
  (p(w) ∧ φ(w)) ∨ (q(w) ∧ ψ(w))
-/
def orFlex (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w || q.presup w
  , assertion := λ w => (p.presup w && p.assertion w) || (q.presup w && q.assertion w) }

/-- orFlex reduces to standard disjunction when both presuppositions hold. -/
theorem orFlex_eq_or_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (orFlex p q).assertion w = (or p q).assertion w := by
  simp only [orFlex, or, hp, hq, Bool.true_and]

/-- orFlex presupposition is weaker than or's (p ∨ q vs p ∧ q). -/
theorem orFlex_presup_weaker (p q : PrProp W) (w : W)
    (h : (or p q).presup w = true) :
    (orFlex p q).presup w = true := by
  simp only [or, orFlex] at *
  cases hp : p.presup w <;> cases hq : q.presup w <;> simp_all

/-- Presupposition projection: get the presupposition as a classical proposition. -/
def projectPresup (p : PrProp W) : BProp W := p.presup

/-- Assertion extraction: get the assertion as a classical proposition. -/
def projectAssertion (p : PrProp W) : BProp W := p.assertion

-- ════════════════════════════════════════════════════════════════
-- Belnap Conditional Assertion Reading
-- @cite{belnap-1970}
-- ════════════════════════════════════════════════════════════════

/-- Alias for `presup` under the Belnap reading: whether the proposition
    is **assertive** at w (asserts something, vs nonassertive/silent). -/
abbrev assertive (p : PrProp W) : BProp W := p.presup

/-- Belnap's conditional assertion (A/B): assert B on condition A.

    Assertive_w iff A is true at w; what is asserted = B.
    @cite{belnap-1970}, (3): "(A/B) is assertive_w just in case
    A is true_w. (A/B)_w = B_w." -/
def condAssert (A B : BProp W) : PrProp W :=
  { presup := A, assertion := B }

/-- Belnap conjunction: assertive iff at least one conjunct is assertive.
    What it asserts = conjunction of assertive conjuncts' content.

    @cite{belnap-1970}, (8). Contrast with classical `PrProp.and` (both
    must be defined) and filtering `PrProp.andFilter` (left-to-right). -/
def andBelnap (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w || q.presup w
  , assertion := λ w =>
      (if p.presup w then p.assertion w else true) &&
      (if q.presup w then q.assertion w else true) }

/-- Belnap disjunction: assertive iff at least one disjunct is assertive.
    What it asserts = disjunction of assertive disjuncts' content.

    @cite{belnap-1970}, (9). -/
def orBelnap (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w || q.presup w
  , assertion := λ w =>
      (if p.presup w then p.assertion w else false) ||
      (if q.presup w then q.assertion w else false) }

/-- Belnap conjunction evaluates to `Truth3.meetBelnap` pointwise. -/
theorem eval_andBelnap (p q : PrProp W) (w : W) :
    (andBelnap p q).eval w = Truth3.meetBelnap (p.eval w) (q.eval w) := by
  simp only [eval, andBelnap, Truth3.meetBelnap, Truth3.meet, Truth3.ofBool]
  cases p.presup w <;> cases q.presup w <;>
    simp <;> cases p.assertion w <;> cases q.assertion w <;> rfl

/-- Belnap disjunction evaluates to `Truth3.joinBelnap` pointwise. -/
theorem eval_orBelnap (p q : PrProp W) (w : W) :
    (orBelnap p q).eval w = Truth3.joinBelnap (p.eval w) (q.eval w) := by
  simp only [eval, orBelnap, Truth3.joinBelnap, Truth3.join, Truth3.ofBool]
  cases p.presup w <;> cases q.presup w <;>
    simp <;> cases p.assertion w <;> cases q.assertion w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- Round-trip: Prop3 ↔ PrProp
-- ════════════════════════════════════════════════════════════════

/-- Convert a three-valued proposition to a PrProp.

    Inverse of `PrProp.eval`: defined ↔ value ≠ indet,
    assertion ↔ value = true. -/
def ofProp3 (p : Prop3 W) : PrProp W :=
  { presup := λ w => (p w).isDefined
  , assertion := λ w => (p w).toBoolOrFalse }

/-- `Prop3 → PrProp → Prop3` round-trip is the identity. -/
theorem eval_ofProp3 (p : Prop3 W) : (ofProp3 p).eval = p := by
  funext w
  simp only [eval, ofProp3]
  cases p w <;> rfl

end PrProp

end Core.Presupposition
