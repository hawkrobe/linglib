import Linglib.Core.Logic.Truth3
import Linglib.Core.Semantics.Proposition

/-!
# Partial Propositions (PrProp)
@cite{heim-1983} @cite{schlenker-2009} @cite{von-fintel-1999} @cite{geurts-2005} @cite{belnap-1970}

`PrProp W` is linglib's canonical representation of **partial propositions** —
propositions that may be undefined at some evaluation points. The type
parameter `W` is the evaluation domain: worlds, possibilities, events,
world-assignment pairs, or any other type. The two fields are:
- `presup` (= definedness): whether the proposition says anything at this point
- `assertion` (= content): what it says when defined

## Domain generality

`PrProp W` is parametric over `W`. Common instantiations:
- `PrProp World` — classical presupposition over possible worlds
- `PrProp (Possibility W E)` — dynamic presupposition over world-assignment pairs
- `PrProp (W × Event)` — event presuppositions (preconditions on events)
- `PrProp (W × Time)` — temporal presuppositions

All operations (filtering connectives, `eval`, accommodation) work
uniformly across domains because they are pointwise over `W`.

## Satisfaction relations

Two satisfaction relations connect PrProp to CCP's `updateFromSat`:
- `PrProp.defined w p` — presupposition holds at w (definedness test)
- `PrProp.holds w p` — both presupposition and assertion hold (full satisfaction)

These enable structural integration with the dynamic semantics layer:
`updateFromSat PrProp.holds p` produces a `CCP W` that is eliminative,
distributive, and supports the Galois connection — all by construction.

## Linguistic interpretations

- **Presupposition**: `presup` = presupposition holds; failure = undefined
  (@cite{heim-1983}, @cite{schlenker-2009})
- **Conditional assertion**: `presup` = assertive; failure = nonassertive
  (@cite{belnap-1970}: "(A/B) is assertive_w just in case A is true_w")
- **Homogeneity**: `presup` = all atoms agree; failure = truth-value gap
  (@cite{kriz-2016})

## Connective systems

The choice of connective system (how gaps behave under ∧/∨) is orthogonal
to `PrProp` itself — see `Truth3.GapPolicy`:
- Classical (`PrProp.and`): both must be defined
- Filtering (`PrProp.andFilter`): one can satisfy the other's presupposition
- Belnap (`PrProp.andBelnap`): gaps are skipped, defined operands contribute
- Belnap lift (`PrProp.belnapLift`): uniform construction parameterized by
  a binary Boolean function `f` and its identity element `id`. All Belnap
  and flex connectives are instances: `orBelnap = belnapLift (·||·) false`,
  `andBelnap = belnapLift (·&&·) true`, and `orFlex`/`andFlex` are the same

## Structural joints

Everything in the presupposition system derives from `.presup` and `.assertion`:
- Heritage function for `p → q` = `(impFilter p q).presup` (by construction)
- CCP update = `updateFromSat PrProp.holds p` (from CCP infrastructure)
- Presupposition test = `updateFromSat PrProp.defined p`
- Accommodation = intersect context with `{w | PrProp.defined w p}`
- Local context satisfaction = `supportOf PrProp.defined s p`

-/

namespace Core.Presupposition

open Core.Duality
open Core.Proposition

/-- A presupposed value: a value that is only defined when its
presupposition holds.

`PrValue W α` generalizes `PrProp W` (= `PrValue W Bool`): the
presupposition is always `W → Bool`, but the at-issue content can be
any type — a truth value (`Bool`), a degree (`ℚ`), a measure, etc.

Linguistic motivation: many presupposition triggers return non-boolean
values. The revised *per* entry (@cite{bale-schwarz-2022}, eq. 43)
returns a presupposed pure number (`ℚ`). Definite descriptions return
presupposed entities. `PrValue` handles all of these uniformly. -/
structure PrValue (W : Type*) (α : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Bool
  /-- The at-issue content (value). -/
  value : W → α

namespace PrValue

variable {W : Type*} {α : Type*}

/-- A presupposed value is defined at w iff its presupposition holds. -/
def defined (w : W) (pv : PrValue W α) : Prop := pv.presup w = true

/-- Create a presuppositionless value (always defined). -/
def pure (a : W → α) : PrValue W α where
  presup := fun _ => true
  value := a

end PrValue

/-- A presuppositional proposition: assertion + presupposition. -/
structure PrProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W -> Bool
  /-- The at-issue content (assertion). -/
  assertion : W -> Bool

namespace PrProp

variable {W : Type*}

/-- Convert a presupposed Bool value (`PrValue W Bool`) to `PrProp W`. -/
def ofPrValue (pv : PrValue W Bool) : PrProp W where
  presup := pv.presup
  assertion := pv.value

/-- Convert a `PrProp` to a `PrValue W Bool`. -/
def toPrValue (p : PrProp W) : PrValue W Bool where
  presup := p.presup
  value := p.assertion

/-- Evaluate a presuppositional proposition to three-valued truth. -/
def eval (p : PrProp W) : Prop3 W := λ w =>
  if p.presup w then Truth3.ofBool (p.assertion w) else .indet

/-- Definedness relation: presupposition holds at the evaluation point.

    Argument order `(w : W) (p : PrProp W)` matches `updateFromSat`:
    `updateFromSat PrProp.defined p` gives the presupposition test CCP. -/
def defined (w : W) (p : PrProp W) : Prop := p.presup w = true

/-- Full satisfaction relation: both presupposition and assertion hold.

    `updateFromSat PrProp.holds p` gives the full CCP (presupposition
    test + assertion filter). This CCP is automatically eliminative and
    distributive via CCP's `updateFromSat` infrastructure. -/
def holds (w : W) (p : PrProp W) : Prop := p.presup w = true ∧ p.assertion w = true

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

/-- K&P two-dimensional disjunction (@cite{karttunen-peters-1979}).

    Π(φ ∨ ψ) = (¬A(ψ) → Π(φ)) ∧ (¬A(φ) → Π(ψ))
             = (A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))
    A(φ ∨ ψ) = A(φ) ∨ A(ψ)

    Uses the symmetric version from @cite{yagi-2025} Definition 2
    (cf. @cite{kalomoiros-schwarz-2021} for experimental support of
    symmetry). Differs from `orFilter`, which encodes the Heim/Schlenker
    filtering rule (A(φ) → Π(ψ)) ∧ (A(ψ) → Π(φ)) ∧ (Π(φ) ∨ Π(ψ)). -/
def orKP (p q : PrProp W) : PrProp W :=
  { presup := λ w => (q.assertion w || p.presup w) && (p.assertion w || q.presup w)
  , assertion := λ w => p.assertion w || q.assertion w }

/-- When presuppositions conflict at w, K&P's presupposition entails the
    assertion: defined → true, so the disjunction can never be both defined
    and false. @cite{yagi-2025} §2.2 -/
theorem orKP_presup_entails_when_conflicting (p q : PrProp W) (w : W)
    (h_conflict : ¬(p.presup w = true ∧ q.presup w = true))
    (h_presup : (orKP p q).presup w = true) :
    (orKP p q).assertion w = true := by
  simp only [orKP] at h_presup ⊢
  cases hp : p.presup w <;> cases hq : q.presup w <;>
    cases hpa : p.assertion w <;> cases hqa : q.assertion w <;>
    simp_all

/-- Exclusive disjunction: both presuppositions must hold (no filtering).

    Under Strong Kleene, `Truth3.xor` propagates undefinedness
    unconditionally (`xor_indet_iff`), so exclusive disjunction never
    filters presupposition failure from either disjunct.
    @cite{wang-davidson-2026} -/
def xor (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => p.assertion w ^^ q.assertion w }

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

/-- Exclusive disjunction evaluation matches `Truth3.xor` when both defined. -/
theorem eval_xor (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (xor p q).eval w = Truth3.xor (p.eval w) (q.eval w) := by
  simp only [eval, xor, hp, hq, Bool.true_and, ite_true]
  cases p.assertion w <;> cases q.assertion w <;> rfl

/-- Exclusive disjunction never filters: when either presupposition fails,
    the result is undefined. @cite{wang-davidson-2026} -/
theorem eval_xor_no_filter (p q : PrProp W) (w : W)
    (hq : q.presup w = false) :
    (xor p q).eval w = .indet := by
  simp only [eval, xor, hq, Bool.and_false]; rfl

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

/-- Flexible accommodation conjunction.

Each conjunct is evaluated only against worlds where its own presupposition
holds. Undefined conjuncts are vacuously true (the identity element for ∧),
so they don't constrain the result. Dual of `orFlex`. -/
def andFlex (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w || q.presup w
  , assertion := λ w => (!p.presup w || p.assertion w) && (!q.presup w || q.assertion w) }

/-- andFlex reduces to standard conjunction when both presuppositions hold. -/
theorem andFlex_eq_and_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (andFlex p q).assertion w = (and p q).assertion w := by
  simp only [andFlex, and, hp, hq, Bool.not_true, Bool.false_or]

/-- andFlex presupposition is weaker than and's (p ∨ q vs p ∧ q). -/
theorem andFlex_presup_weaker (p q : PrProp W) (w : W)
    (h : (and p q).presup w = true) :
    (andFlex p q).presup w = true := by
  simp only [and, andFlex] at *
  cases hp : p.presup w <;> cases hq : q.presup w <;> simp_all

/-- Weak Kleene disjunction: undefined iff either operand undefined.
    Both disjuncts must be defined for the disjunction to be defined.

    @cite{kleene-1952}: indet is absorbing for both ∧ and ∨. -/
def orWeak (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => p.assertion w || q.assertion w }

/-- Weak Kleene conjunction. -/
def andWeak (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w && q.presup w
  , assertion := λ w => p.assertion w && q.assertion w }

/-- `orWeak` evaluates to `Truth3.joinWeak` pointwise. -/
theorem eval_orWeak (p q : PrProp W) (w : W) :
    (orWeak p q).eval w = Truth3.joinWeak (p.eval w) (q.eval w) := by
  simp only [eval, orWeak, Truth3.joinWeak, Truth3.ofBool]
  cases p.presup w <;> cases q.presup w <;>
    simp <;> cases p.assertion w <;> cases q.assertion w <;> rfl

/-- `orWeak` agrees with `or` — they have the same definition for inclusive
    disjunction, since both require both presuppositions. -/
theorem orWeak_eq_or (p q : PrProp W) : orWeak p q = or p q := rfl

/-- `andWeak` agrees with `and` — they have the same definition for
    conjunction, since both require both presuppositions. -/
theorem andWeak_eq_and (p q : PrProp W) : andWeak p q = and p q := rfl

-- ════════════════════════════════════════════════════════════════
-- Genuineness
-- @cite{zimmermann-2000} @cite{geurts-2005} @cite{katzir-singh-2012}
-- ════════════════════════════════════════════════════════════════

/-- **Genuineness** for disjunction: both disjuncts are "live possibilities"
    in a state. Each disjunct must be true (defined and asserted) at some
    world, and false (or undefined) at another, making the disjunction
    informative.

    @cite{zimmermann-2000}: disjunction requires that each disjunct be a
    "live possibility." @cite{yagi-2025} Definition 8: genuineness requires
    worlds w, w' in the result of the update where each disjunct is solely
    responsible for truth.

    This static version checks that the input state s has witness worlds
    for each disjunct. The full dynamic version (@cite{yagi-2025}
    Definition 8) additionally requires the witnesses to survive the
    update, i.e., w ∈ s[φ ∨ ψ]. -/
def genuineness (p q : PrProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.eval w = .true) ∧
  (∃ w ∈ s, q.eval w = .true)

/-- Genuineness is symmetric. -/
theorem genuineness_comm (p q : PrProp W) (s : Finset W) :
    genuineness p q s ↔ genuineness q p s := by
  simp only [genuineness, and_comm]

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

/-- **Belnap lift**: uniform construction for conditional assertion connectives.

    Given a binary Boolean function `f` and its identity element `id`,
    constructs a PrProp connective where:
    - Defined (assertive) iff at least one operand is defined
    - Assertion applies `f` to each operand's content, substituting `id`
      for undefined operands (making them "silent")

    @cite{belnap-1970}: undefined operands contribute the identity element,
    as if they weren't there. This is the uniform principle behind both
    Belnap's conditional assertion connectives and Geurts/Aloni's flexible
    accommodation — the two constructions are the same (`orFlex_eq_belnapLift`,
    `andFlex_eq_belnapLift`).

    Defined instances:
    - `belnapLift (· || ·) false` = `orBelnap` = `orFlex` (false is identity for ∨)
    - `belnapLift (· && ·) true` = `andBelnap` = `andFlex` (true is identity for ∧)

    The pattern extends to other connectives (e.g., ⊕ with id = false,
    → with left-id = true), but we define instances only when there
    is a downstream consumer. -/
def belnapLift (f : Bool → Bool → Bool) (id : Bool)
    (p q : PrProp W) : PrProp W :=
  { presup := λ w => p.presup w || q.presup w
  , assertion := λ w => f (if p.presup w then p.assertion w else id)
                          (if q.presup w then q.assertion w else id) }

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

/-- Flexible accommodation disjunction is Belnap's conditional assertion
    disjunction. The two concepts, developed independently
    (@cite{belnap-1970} vs @cite{geurts-2005}/@cite{aloni-2022}), produce
    identical truth conditions: each disjunct contributes its content only
    when its presupposition is met, and the overall presupposition is
    the disjunction of the component presuppositions. -/
theorem orFlex_eq_orBelnap (p q : PrProp W) : orFlex p q = orBelnap p q := by
  simp only [orFlex, orBelnap]
  congr 1; funext w
  cases p.presup w <;> cases q.presup w <;> simp

/-- `orFlex` evaluates to `Truth3.joinBelnap` pointwise.
    Corollary of `orFlex_eq_orBelnap` + `eval_orBelnap`. -/
theorem eval_orFlex (p q : PrProp W) (w : W) :
    (orFlex p q).eval w = Truth3.joinBelnap (p.eval w) (q.eval w) := by
  rw [orFlex_eq_orBelnap]; exact eval_orBelnap p q w

/-- `andFlex` evaluates to `Truth3.meetBelnap` pointwise. -/
theorem eval_andFlex (p q : PrProp W) (w : W) :
    (andFlex p q).eval w = Truth3.meetBelnap (p.eval w) (q.eval w) := by
  simp only [eval, andFlex, Truth3.meetBelnap, Truth3.meet, Truth3.ofBool]
  cases p.presup w <;> cases q.presup w <;>
    simp <;> cases p.assertion w <;> cases q.assertion w <;> rfl

-- ════════════════════════════════════════════════════════════════
-- Belnap Lift: Unification
-- ════════════════════════════════════════════════════════════════

/-- `orBelnap` is the Belnap lift of `(· || ·)` with identity `false`. -/
theorem orBelnap_eq_belnapLift (p q : PrProp W) :
    orBelnap p q = belnapLift (· || ·) false p q := rfl

/-- `andBelnap` is the Belnap lift of `(· && ·)` with identity `true`. -/
theorem andBelnap_eq_belnapLift (p q : PrProp W) :
    andBelnap p q = belnapLift (· && ·) true p q := rfl

/-- `orFlex` is the Belnap lift of `(· || ·)` with identity `false`.
    Corollary: flexible accommodation = conditional assertion = Belnap lift,
    all three for any binary connective. -/
theorem orFlex_eq_belnapLift (p q : PrProp W) :
    orFlex p q = belnapLift (· || ·) false p q :=
  orFlex_eq_orBelnap p q

/-- Flexible accommodation conjunction IS Belnap conjunction.
    Extends `orFlex_eq_orBelnap`: the flex = Belnap identity holds for
    all binary connectives, not just disjunction. -/
theorem andFlex_eq_andBelnap (p q : PrProp W) : andFlex p q = andBelnap p q := by
  simp only [andFlex, andBelnap]
  congr 1; funext w
  cases p.presup w <;> cases q.presup w <;> simp

/-- `andFlex` is the Belnap lift of `(· && ·)` with identity `true`. -/
theorem andFlex_eq_belnapLift (p q : PrProp W) :
    andFlex p q = belnapLift (· && ·) true p q :=
  andFlex_eq_andBelnap p q

/-- Belnap lift reduces to the classical operation when both presuppositions hold.
    The identity element is never used — both operands contribute directly. -/
theorem belnapLift_eq_classical (f : Bool → Bool → Bool) (id : Bool)
    (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (belnapLift f id p q).assertion w = f (p.assertion w) (q.assertion w) := by
  simp [belnapLift, hp, hq]

/-- When only the left operand is defined and `id` is a right identity,
    belnapLift returns the left operand's value: the right operand is
    invisible. -/
theorem belnapLift_right_undefined (f : Bool → Bool → Bool) (id : Bool)
    (hid : ∀ b, f b id = b) (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = false) :
    (belnapLift f id p q).assertion w = p.assertion w := by
  simp [belnapLift, hp, hq, hid]

/-- When only the right operand is defined and `id` is a left identity,
    belnapLift returns the right operand's value. -/
theorem belnapLift_left_undefined (f : Bool → Bool → Bool) (id : Bool)
    (hid : ∀ b, f id b = b) (p q : PrProp W) (w : W)
    (hp : p.presup w = false) (hq : q.presup w = true) :
    (belnapLift f id p q).assertion w = q.assertion w := by
  simp [belnapLift, hp, hq, hid]

/-- belnapLift is commutative when `f` is commutative. -/
theorem belnapLift_comm (f : Bool → Bool → Bool)
    (hcomm : ∀ a b, f a b = f b a) (id : Bool) (p q : PrProp W) :
    belnapLift f id p q = belnapLift f id q p := by
  simp only [belnapLift]
  congr 1
  · funext w; exact Bool.or_comm (p.presup w) (q.presup w)
  · funext w; exact hcomm _ _

-- ════════════════════════════════════════════════════════════════
-- Collapse: All connective families agree when both defined
-- ════════════════════════════════════════════════════════════════

/-- When both presuppositions hold at w, ALL disjunction connectives
    agree on assertion: classical = filtering = K&P = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_or_agree_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (or p q).assertion w = (orFilter p q).assertion w ∧
    (or p q).assertion w = (orKP p q).assertion w ∧
    (or p q).assertion w = (orFlex p q).assertion w ∧
    (or p q).assertion w = (orBelnap p q).assertion w ∧
    (or p q).assertion w = (orWeak p q).assertion w := by
  simp [or, orFilter, orKP, orFlex, orBelnap, orWeak, hp, hq]

/-- When both presuppositions hold at w, ALL conjunction connectives
    agree on assertion: classical = filtering = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_and_agree_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (and p q).assertion w = (andFilter p q).assertion w ∧
    (and p q).assertion w = (andFlex p q).assertion w ∧
    (and p q).assertion w = (andBelnap p q).assertion w ∧
    (and p q).assertion w = (andWeak p q).assertion w := by
  simp [and, andFilter, andFlex, andBelnap, andWeak, hp, hq]

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
