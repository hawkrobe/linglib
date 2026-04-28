import Linglib.Core.Logic.Truth3
import Mathlib.Data.Finset.Basic

/-!
# Partial Propositions
@cite{heim-1983} @cite{schlenker-2009} @cite{von-fintel-1999} @cite{geurts-2005} @cite{belnap-1970}

Partial propositions — propositions that may be undefined at some evaluation
points.

**`PrProp W`**: `presup : W → Prop`, `assertion : W → Prop`. The canonical type
for partial propositions. Following the Mathlib convention, fields are
Prop-valued; use `open Classical` + `by_cases` for case splits. For
finite worlds with `DecidableEq`, the predicates are auto-decidable and
`PrProp.eval` reduces via `if_pos`/`if_neg`.

**`PrValue W α`** (Bool-based presupposition, polymorphic value): a separate
type for presupposed non-boolean values (degrees, entities, etc.).

## Domain generality

`PrProp W` is parametric over `W`. Common instantiations:
- `PrProp World` — classical presupposition over possible worlds
- `PrProp (Possibility W E)` — dynamic presupposition over world-assignment pairs

## Satisfaction relations

- `PrProp.defined w p` — presupposition holds at w
- `PrProp.holds w p` — both presupposition and assertion hold

## Connective systems

The choice of connective system (how gaps behave under ∧/∨) is orthogonal
to the representation type — see `Truth3.GapPolicy`. The full set is provided:
classical, filtering (Karttunen), Belnap, flexible, Weak Kleene, K&P.
-/

namespace Core.Presupposition

open Core.Duality

/-- A presupposed value: a value that is only defined when its
presupposition holds.

`PrValue W α` generalizes presuppositional propositions: the
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

-- ════════════════════════════════════════════════════════════════
-- PrProp: Prop-based partial propositions
-- ════════════════════════════════════════════════════════════════

/-- A presuppositional proposition: assertion + presupposition.

    Fields are `Prop`-valued following the Mathlib convention. Construct
    directly with `{ presup := ..., assertion := ... }`; for finite worlds
    with `DecidableEq`, the predicates are auto-decidable. -/
@[ext]
structure PrProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (assertion). -/
  assertion : W → Prop

namespace PrProp

open Classical

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════
-- Constructors
-- ════════════════════════════════════════════════════════════════

/-- Create a presuppositionless proposition from a `W → Prop`. -/
def ofProp' (p : W → Prop) : PrProp W where
  presup := fun _ => True
  assertion := p

/-- Convert a three-valued proposition to a PrProp.
    Inverse of `PrProp.eval`: defined iff value ≠ indet,
    assertion iff value = true. -/
def ofProp3 (p : Prop3 W) : PrProp W where
  presup := fun w => p w ≠ .indet
  assertion := fun w => p w = .true

/-- Convert a presupposed Bool value (`PrValue W Bool`) to `PrProp W`. -/
def ofPrValue (pv : PrValue W Bool) : PrProp W where
  presup := fun w => pv.presup w = true
  assertion := fun w => pv.value w = true

/-- Convert a `PrProp` to a `PrValue W Bool` (noncomputable — requires
    deciding Props to produce Bool values). -/
noncomputable def toPrValue (p : PrProp W) : PrValue W Bool where
  presup := fun w => decide (p.presup w)
  value := fun w => decide (p.assertion w)

/-- Belnap's conditional assertion (A/B): assert B on condition A.

    Assertive_w iff A is true at w; what is asserted = B.
    @cite{belnap-1970}, (3): "(A/B) is assertive_w just in case
    A is true_w. (A/B)_w = B_w." -/
def condAssert (A B : W → Prop) : PrProp W where
  presup := A
  assertion := B

-- ════════════════════════════════════════════════════════════════
-- Satisfaction Relations
-- ════════════════════════════════════════════════════════════════

/-- Full satisfaction relation: both presupposition and assertion hold.

    Argument order `(w : W) (p : PrProp W)` supports `updateFromSat`:
    `updateFromSat PrProp.holds p` gives the full CCP (presupposition
    test + assertion filter). -/
def holds (w : W) (p : PrProp W) : Prop := p.presup w ∧ p.assertion w

/-- Definedness relation: presupposition holds at the evaluation point.

    Argument order `(w : W) (p : PrProp W)` supports `updateFromSat`:
    `updateFromSat PrProp.defined p` gives the presupposition test CCP. -/
def defined (w : W) (p : PrProp W) : Prop := p.presup w

-- ════════════════════════════════════════════════════════════════
-- Constants
-- ════════════════════════════════════════════════════════════════

/-- Create a tautological presupposition. -/
def top : PrProp W where
  presup := fun _ => True
  assertion := fun _ => True

/-- Create a contradictory presupposition. -/
def bot : PrProp W where
  presup := fun _ => True
  assertion := fun _ => False

/-- Create a presupposition failure (never defined). -/
def undefined : PrProp W where
  presup := fun _ => False
  assertion := fun _ => False

-- ════════════════════════════════════════════════════════════════
-- Evaluation
-- ════════════════════════════════════════════════════════════════

/-- Evaluate a presuppositional proposition to three-valued truth.
    Noncomputable because it decides Prop-valued presupposition and
    assertion via classical logic. -/
noncomputable def eval (p : PrProp W) : Prop3 W := fun w =>
  if p.presup w then
    if p.assertion w then .true else .false
  else .indet

-- ════════════════════════════════════════════════════════════════
-- Classical Connectives
-- ════════════════════════════════════════════════════════════════

/-- Classical (internal / choice) negation: a hole.
    Lets the presupposition through unchanged. -/
def neg (p : PrProp W) : PrProp W where
  presup := p.presup
  assertion := fun w => ¬p.assertion w

/-- Bochvar's truth operator `t`: a plug-as-affirmation.
    Always defined; maps presupposition failure to `False`.
    @cite{karttunen-1973} §10 footnote 18: `t(A)` has truth-table
    `T → T`, `F → F`, `# → F`. Composing classical negation with `t`
    yields external negation: `negExt p = neg (truthOp p)`. -/
def truthOp (p : PrProp W) : PrProp W where
  presup := fun _ => True
  assertion := fun w => p.presup w ∧ p.assertion w

/-- Bochvar external (exclusion) negation: a plug.
    Always defined; true when `p` is false or undefined, false only when
    `p` is true. Equals `neg (truthOp p)` per @cite{karttunen-1973} §10
    fn 18: `⌜¬A⌝ ≡ ⌜~t(A)⌝`. -/
def negExt (p : PrProp W) : PrProp W := neg (truthOp p)

/-- Classical conjunction: both presuppositions must hold. -/
def and (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Classical disjunction: both presuppositions must hold. -/
def or (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- Classical implication: both presuppositions must hold. -/
def imp (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w → q.assertion w

/-- Exclusive disjunction: both presuppositions must hold (no filtering).

    Under Strong Kleene, `Truth3.xor` propagates undefinedness
    unconditionally (`xor_indet_iff`), so exclusive disjunction never
    filters presupposition failure from either disjunct.
    @cite{wang-davidson-2026} -/
def xor (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => (p.assertion w ∧ ¬q.assertion w) ∨ (¬p.assertion w ∧ q.assertion w)

-- ════════════════════════════════════════════════════════════════
-- Filtering Connectives (Karttunen)
-- ════════════════════════════════════════════════════════════════

/-- Filtering conjunction: antecedent can satisfy consequent's presupposition. -/
def andFilter (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Filtering implication: antecedent can satisfy consequent's presupposition. -/
def impFilter (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w → q.assertion w

/-- Filtering disjunction: disjuncts can satisfy each other's presuppositions. -/
def orFilter (p q : PrProp W) : PrProp W where
  presup := fun w =>
    (p.assertion w → q.presup w) ∧
    (q.assertion w → p.presup w) ∧
    (p.presup w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

-- ════════════════════════════════════════════════════════════════
-- K&P Two-Dimensional Disjunction
-- ════════════════════════════════════════════════════════════════

/-- K&P two-dimensional disjunction (@cite{karttunen-peters-1979}).

    Π(φ ∨ ψ) = (A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))
    A(φ ∨ ψ) = A(φ) ∨ A(ψ)

    Uses the symmetric version from @cite{yagi-2025} Definition 2
    (cf. @cite{kalomoiros-schwarz-2021} for experimental support of
    symmetry). -/
def orKP (p q : PrProp W) : PrProp W where
  presup := fun w => (q.assertion w ∨ p.presup w) ∧ (p.assertion w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

-- ════════════════════════════════════════════════════════════════
-- Weak Kleene
-- ════════════════════════════════════════════════════════════════

/-- Weak Kleene disjunction: undefined iff either operand undefined.
    Both disjuncts must be defined for the disjunction to be defined.

    @cite{kleene-1952}: indet is absorbing for both ∧ and ∨. -/
def orWeak (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- Weak Kleene conjunction. -/
def andWeak (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∧ q.assertion w

-- ════════════════════════════════════════════════════════════════
-- Flexible Accommodation
-- ════════════════════════════════════════════════════════════════

/-- Flexible accommodation disjunction.

Each disjunct is evaluated only against worlds where its own presupposition
holds. The overall presupposition is the disjunction of the individual
presuppositions. This handles conflicting presuppositions (p ∧ q = ⊥):
standard disjunction and filtering disjunction both fail for this case,
but flexible accommodation correctly predicts presupposition p ∨ q and
allows the disjunction to be false.

Formally, this is the static counterpart of @cite{yagi-2025}'s dynamic update.
-/
def orFlex (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-- Flexible accommodation conjunction.

Each conjunct is evaluated only against worlds where its own presupposition
holds. Undefined conjuncts are vacuously true (the identity element for ∧),
so they don't constrain the result. Dual of `orFlex`. -/
def andFlex (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

-- ════════════════════════════════════════════════════════════════
-- Belnap Conditional Assertion
-- @cite{belnap-1970}
-- ════════════════════════════════════════════════════════════════

/-- Alias for `presup` under the Belnap reading: whether the proposition
    is **assertive** at w (asserts something, vs nonassertive/silent). -/
abbrev assertive (p : PrProp W) : W → Prop := p.presup

/-- Belnap conjunction: assertive iff at least one conjunct is assertive.
    What it asserts = conjunction of assertive conjuncts' content.

    @cite{belnap-1970}, (8). Contrast with classical `PrProp.and` (both
    must be defined) and filtering `PrProp.andFilter` (left-to-right). -/
def andBelnap (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- Belnap disjunction: assertive iff at least one disjunct is assertive.
    What it asserts = disjunction of assertive disjuncts' content.

    @cite{belnap-1970}, (9). -/
def orBelnap (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-- **Belnap lift**: uniform construction for conditional assertion connectives.

    Given a binary Prop function `f` and its identity element `id`,
    constructs a PrProp connective where:
    - Defined (assertive) iff at least one operand is defined
    - Assertion applies `f` to each operand's content, substituting `id`
      for undefined operands (making them "silent")

    @cite{belnap-1970}: undefined operands contribute the identity element.
    Noncomputable because it uses classical `if` on Props.

    Defined instances:
    - `belnapLift (· ∨ ·) False` = `orBelnap` = `orFlex` (False is identity for ∨)
    - `belnapLift (· ∧ ·) True` = `andBelnap` = `andFlex` (True is identity for ∧)
    -/
noncomputable def belnapLift (f : Prop → Prop → Prop) (id : Prop)
    (p q : PrProp W) : PrProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => f (if p.presup w then p.assertion w else id)
                          (if q.presup w then q.assertion w else id)

-- ════════════════════════════════════════════════════════════════
-- Entailment Relations
-- ════════════════════════════════════════════════════════════════

/-- Strong entailment: p entails q at all worlds where both are defined. -/
def strongEntails (p q : PrProp W) : Prop :=
  ∀ w, p.presup w → q.presup w → p.assertion w → q.assertion w

/-- Strawson entailment: p entails q at worlds where p is defined and true. -/
def strawsonEntails (p q : PrProp W) : Prop :=
  ∀ w, p.presup w → p.assertion w → q.presup w ∧ (q.presup w → q.assertion w)

/-- Strawson equivalence: mutual Strawson entailment. -/
def strawsonEquiv (p q : PrProp W) : Prop :=
  strawsonEntails p q ∧ strawsonEntails q p

-- ════════════════════════════════════════════════════════════════
-- Genuineness / Liveness
-- @cite{zimmermann-2000} @cite{geurts-2005} @cite{katzir-singh-2012}
-- ════════════════════════════════════════════════════════════════

/-- **Liveness** for disjunction: each disjunct is satisfied (presupposition
    AND assertion hold) at some world of the state.

    This is the singleton-survival side of @cite{yagi-2025} Definition 8:
    `{w}[φ] = {w}` for some `w ∈ s`. The disjunction-update side
    (`w ∈ s[φ ∨ ψ]`) is the additional constraint expressed by
    `genuineness` below. -/
def liveness (p q : PrProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.holds w) ∧
  (∃ w ∈ s, q.holds w)

/-- **Genuineness** for disjunction (@cite{yagi-2025} Definition 8, after
    @cite{zimmermann-2000}). A disjunction `p ∨ q`, with disjunction-update
    realised by the connective `disj`, follows genuineness in a state `s` iff
    there are worlds `w, w' ∈ s` such that:

    - `{w}[p] = {w}` AND `w ∈ s[p ∨ q]` — the left disjunct's witness survives
      both its own update (= `p.holds w`) and the disjunction's update
      (= `disj.holds w`).
    - `{w'}[q] = {w'}` AND `w' ∈ s[p ∨ q]` — analogously for the right disjunct.

    The disjunction-update side rules out witnesses that survive the local
    presupposition+assertion update but are eliminated by the joint update —
    a vacuous addition under `orFlex`/`orBelnap` (`liveness_implies_genuineness_orFlex`),
    but the substantive constraint @cite{yagi-2025} §3.2 invokes for dynamic
    negation: genuineness must hold even within the scope of negation, where
    "we end up negating both disjuncts".

    The `disj` argument is parametric so the substrate stays
    framework-neutral; consumers supply the disjunction connective whose
    update they wish to test against (orFlex / orBelnap / classical or /
    Geurts modal split). -/
def genuineness (p q : PrProp W) (s : Finset W) (disj : PrProp W) : Prop :=
  (∃ w ∈ s, p.holds w ∧ disj.holds w) ∧
  (∃ w ∈ s, q.holds w ∧ disj.holds w)

/-- Under `orFlex`, `liveness` implies `genuineness`: each witness for
    `p.holds`/`q.holds` automatically survives the disjunction's update,
    because `(orFlex p q).holds w` reduces to `p.holds w ∨ q.holds w`. -/
theorem liveness_implies_genuineness_orFlex (p q : PrProp W) (s : Finset W)
    (h : liveness p q s) : genuineness p q s (orFlex p q) := by
  obtain ⟨⟨w, hw, hp⟩, ⟨w', hw', hq⟩⟩ := h
  refine ⟨⟨w, hw, hp, ?_⟩, ⟨w', hw', hq, ?_⟩⟩
  · exact ⟨Or.inl hp.1, Or.inl hp⟩
  · exact ⟨Or.inr hq.1, Or.inr hq⟩

-- ════════════════════════════════════════════════════════════════
-- Projections
-- ════════════════════════════════════════════════════════════════

/-- Presupposition projection: get the presupposition as a `W → Prop`. -/
def projectPresup (p : PrProp W) : W → Prop := p.presup

/-- Assertion extraction: get the assertion as a `W → Prop`. -/
def projectAssertion (p : PrProp W) : W → Prop := p.assertion

-- ════════════════════════════════════════════════════════════════
-- Extensionality
-- ════════════════════════════════════════════════════════════════

/-- Extensionality for PrProp via pointwise ↔. -/
theorem ext_pointwise {p q : PrProp W}
    (h₁ : ∀ w, p.presup w ↔ q.presup w)
    (h₂ : ∀ w, p.assertion w ↔ q.assertion w) : p = q := by
  cases p; cases q; simp only [mk.injEq]
  exact ⟨funext fun w => propext (h₁ w), funext fun w => propext (h₂ w)⟩

-- ════════════════════════════════════════════════════════════════
-- Negation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Negation preserves presupposition. -/
theorem neg_presup (p : PrProp W) : (neg p).presup = p.presup := rfl

/-- Presupposition projects through negation (by construction). -/
theorem neg_presup_eq (p : PrProp W) (w : W) :
    (neg p).presup w ↔ p.presup w := Iff.rfl

/-- Double negation restores assertion (classical). -/
theorem neg_neg_assertion (p : PrProp W) (w : W) :
    (neg (neg p)).assertion w ↔ p.assertion w := Classical.not_not

/-- Double negation identity. -/
theorem neg_neg (p : PrProp W) : neg (neg p) = p :=
  ext_pointwise (fun _ => Iff.rfl) (fun _ => Classical.not_not)

/-- The truth operator is always defined (it's a plug). -/
@[simp] theorem truthOp_presup (p : PrProp W) (w : W) :
    (truthOp p).presup w := trivial

/-- External negation is always defined (it's a plug). -/
@[simp] theorem negExt_presup (p : PrProp W) (w : W) :
    (negExt p).presup w := trivial

/-- Internal and external negation agree on assertion when the presupposition
    holds. They diverge only at presupposition failure: `neg p` is undefined,
    `negExt p` is true. @cite{karttunen-1973} §10 fn 18. -/
theorem neg_assertion_iff_negExt_assertion_when_defined (p : PrProp W) (w : W)
    (h : p.presup w) :
    (neg p).assertion w ↔ (negExt p).assertion w := by
  simp only [neg, negExt, truthOp, h, true_and]

/-- External negation has the dual assertion to the truth operator at every
    world: `negExt = ¬truthOp` extensionally, by definition (negExt = neg ∘ truthOp
    and neg is `¬` on assertion). -/
theorem negExt_assertion (p : PrProp W) (w : W) :
    (negExt p).assertion w ↔ ¬(truthOp p).assertion w := Iff.rfl

/-- Karttunen §10 fn 18 truth table for external negation, presup-failure case:
    when `p`'s presupposition fails, `negExt p` is true (the plug behavior). -/
theorem negExt_assertion_of_presup_failure (p : PrProp W) (w : W)
    (h : ¬p.presup w) :
    (negExt p).assertion w := by
  simp only [negExt, neg, truthOp, h, false_and, not_false_eq_true]

-- ════════════════════════════════════════════════════════════════
-- Filtering Theorems
-- ════════════════════════════════════════════════════════════════

/-- Filtering implication eliminates presupposition when antecedent entails it. -/
theorem impFilter_eliminates_presup (p q : PrProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (impFilter p q).presup = p.presup := by
  funext w; simp only [impFilter]
  exact propext ⟨fun ⟨hp, _⟩ => hp, fun hp => ⟨hp, h w⟩⟩

/-- When A(p) = P(q), filtering implication has trivial presupposition. -/
theorem impFilter_trivializes_presup (p q : PrProp W)
    (h : p.assertion = q.presup) :
    (impFilter p q).presup = p.presup :=
  impFilter_eliminates_presup p q (fun _ ha => h ▸ ha)

/-- The filtering presupposition of `impFilter` and `andFilter` are identical.
    This is the formal content of @cite{karttunen-1973} §8: the filtering
    rules for *if A then B* and *A and B* coincide because both reduce to
    `p.presup ∧ (p.assertion → q.presup)`. -/
theorem impFilter_presup_eq_andFilter_presup (p q : PrProp W) :
    (impFilter p q).presup = (andFilter p q).presup := rfl

-- ════════════════════════════════════════════════════════════════
-- Evaluation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Evaluation is defined iff presupposition holds. -/
theorem eval_isDefined (p : PrProp W) (w : W) :
    (p.eval w).isDefined ↔ p.presup w := by
  simp only [eval]
  by_cases hp : p.presup w
  · simp only [if_pos hp]
    by_cases ha : p.assertion w
    · simp only [if_pos ha]; exact iff_of_true trivial hp
    · simp only [if_neg ha]; exact iff_of_true trivial hp
  · simp only [if_neg hp]; exact iff_of_false (by decide) hp

/-- Negation evaluation. -/
theorem eval_neg (p : PrProp W) (w : W) :
    (neg p).eval w = Truth3.neg (p.eval w) := by
  simp only [eval, neg]
  by_cases hp : p.presup w
  · simp only [if_pos hp]
    by_cases ha : p.assertion w
    · simp [if_pos ha, if_neg (not_not.mpr ha), Truth3.neg]
    · simp [if_neg ha, if_pos ha, Truth3.neg]
  · simp [if_neg hp, Truth3.neg]

/-- Classical conjunction evaluation (both defined). -/
theorem eval_and (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (and p q).eval w = Truth3.meet (p.eval w) (q.eval w) := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, and, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.meet]

/-- Filtering implication when antecedent false: result is true. -/
theorem eval_impFilter_antecedent_false (p q : PrProp W) (w : W)
    (hp : p.presup w) (ha : ¬p.assertion w) :
    (impFilter p q).eval w = .true := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun h => absurd h ha⟩
  have hassert : (impFilter p q).assertion w := fun h => absurd h ha
  simp only [eval, if_pos hpresup, if_pos hassert]

/-- Filtering implication when antecedent true: depends on consequent. -/
theorem eval_impFilter_antecedent_true (p q : PrProp W) (w : W)
    (hp : p.presup w) (ha : p.assertion w) (hq : q.presup w) :
    (impFilter p q).eval w =
      if q.assertion w then .true else .false := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun _ => hq⟩
  by_cases hqa : q.assertion w
  · have hass : (impFilter p q).assertion w := fun _ => hqa
    simp only [eval, if_pos hpresup, if_pos hass, if_pos hqa]
  · have hass : ¬(impFilter p q).assertion w := fun h => hqa (h ha)
    simp only [eval, if_pos hpresup, if_neg hass, if_neg hqa]

/-- Exclusive disjunction evaluation matches `Truth3.xor` when both defined. -/
theorem eval_xor (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (xor p q).eval w = Truth3.xor (p.eval w) (q.eval w) := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, xor, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.xor, not_not]

/-- Exclusive disjunction never filters: when either presupposition fails,
    the result is undefined. @cite{wang-davidson-2026} -/
theorem eval_xor_no_filter (p q : PrProp W) (w : W)
    (hq : ¬q.presup w) :
    (xor p q).eval w = .indet := by
  have : ¬(xor p q).presup w := fun ⟨_, hq'⟩ => hq hq'
  simp [eval, if_neg this]

-- ════════════════════════════════════════════════════════════════
-- orKP Theorem
-- ════════════════════════════════════════════════════════════════

/-- When presuppositions conflict at w, K&P's presupposition entails the
    assertion: defined → true, so the disjunction can never be both defined
    and false. @cite{yagi-2025} §2.2 -/
theorem orKP_presup_entails_when_conflicting (p q : PrProp W) (w : W)
    (h_conflict : ¬(p.presup w ∧ q.presup w))
    (h_presup : (orKP p q).presup w) :
    (orKP p q).assertion w := by
  simp only [orKP] at h_presup ⊢
  obtain ⟨h1, h2⟩ := h_presup
  by_cases hp : p.presup w
  · have hq : ¬q.presup w := fun hq => h_conflict ⟨hp, hq⟩
    exact Or.inl (h2.resolve_right hq)
  · exact Or.inr (h1.resolve_right hp)

-- ════════════════════════════════════════════════════════════════
-- Flex / Belnap Equality Theorems
-- ════════════════════════════════════════════════════════════════

/-- Flexible accommodation disjunction IS Belnap disjunction.
    The two concepts, developed independently
    (@cite{belnap-1970} vs @cite{geurts-2005}/@cite{aloni-2022}), produce
    identical truth conditions. -/
theorem orFlex_eq_orBelnap (p q : PrProp W) : orFlex p q = orBelnap p q := rfl

/-- Flexible accommodation conjunction IS Belnap conjunction.
    Extends `orFlex_eq_orBelnap`: the flex = Belnap identity holds for
    all binary connectives, not just disjunction. -/
theorem andFlex_eq_andBelnap (p q : PrProp W) : andFlex p q = andBelnap p q := rfl

/-- `orWeak` agrees with `or` — they have the same definition for inclusive
    disjunction, since both require both presuppositions. -/
theorem orWeak_eq_or (p q : PrProp W) : orWeak p q = or p q := rfl

/-- `andWeak` agrees with `and` — they have the same definition for
    conjunction, since both require both presuppositions. -/
theorem andWeak_eq_and (p q : PrProp W) : andWeak p q = and p q := rfl

/-- orFlex reduces to standard disjunction when both presuppositions hold. -/
theorem orFlex_eq_or_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (orFlex p q).assertion w ↔ (or p q).assertion w := by
  simp only [orFlex, or]
  constructor
  · rintro (⟨_, ha⟩ | ⟨_, ha⟩) <;> [exact Or.inl ha; exact Or.inr ha]
  · rintro (ha | ha) <;> [exact Or.inl ⟨hp, ha⟩; exact Or.inr ⟨hq, ha⟩]

/-- orFlex presupposition is weaker than or's (p ∨ q vs p ∧ q). -/
theorem orFlex_presup_weaker (p q : PrProp W) (w : W)
    (h : (or p q).presup w) :
    (orFlex p q).presup w := by
  exact Or.inl h.1

/-- andFlex reduces to standard conjunction when both presuppositions hold. -/
theorem andFlex_eq_and_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (andFlex p q).assertion w ↔ (and p q).assertion w := by
  simp only [andFlex, and]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨h1 hp, h2 hq⟩
  · intro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩

/-- andFlex presupposition is weaker than and's (p ∨ q vs p ∧ q). -/
theorem andFlex_presup_weaker (p q : PrProp W) (w : W)
    (h : (and p q).presup w) :
    (andFlex p q).presup w := by
  exact Or.inl h.1

-- ════════════════════════════════════════════════════════════════
-- Eval: Weak Kleene / Belnap / Flex
-- ════════════════════════════════════════════════════════════════

/-- `orWeak` evaluates to `Truth3.joinWeak` pointwise. -/
theorem eval_orWeak (p q : PrProp W) (w : W) :
    (orWeak p q).eval w = Truth3.joinWeak (p.eval w) (q.eval w) := by
  simp only [eval, orWeak, Truth3.joinWeak]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.join, Truth3.ofBool]

/-- Belnap conjunction evaluates to `Truth3.meetBelnap` pointwise. -/
theorem eval_andBelnap (p q : PrProp W) (w : W) :
    (andBelnap p q).eval w = Truth3.meetBelnap (p.eval w) (q.eval w) := by
  simp only [eval, andBelnap, Truth3.meetBelnap, Truth3.meet]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.ofBool]

/-- Belnap disjunction evaluates to `Truth3.joinBelnap` pointwise. -/
theorem eval_orBelnap (p q : PrProp W) (w : W) :
    (orBelnap p q).eval w = Truth3.joinBelnap (p.eval w) (q.eval w) := by
  simp only [eval, orBelnap, Truth3.joinBelnap, Truth3.join]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.ofBool]

/-- `orFlex` evaluates to `Truth3.joinBelnap` pointwise.
    Corollary of `orFlex_eq_orBelnap` + `eval_orBelnap`. -/
theorem eval_orFlex (p q : PrProp W) (w : W) :
    (orFlex p q).eval w = Truth3.joinBelnap (p.eval w) (q.eval w) := by
  rw [orFlex_eq_orBelnap]; exact eval_orBelnap p q w

/-- `andFlex` evaluates to `Truth3.meetBelnap` pointwise. -/
theorem eval_andFlex (p q : PrProp W) (w : W) :
    (andFlex p q).eval w = Truth3.meetBelnap (p.eval w) (q.eval w) := by
  rw [andFlex_eq_andBelnap]; exact eval_andBelnap p q w

-- ════════════════════════════════════════════════════════════════
-- Belnap Lift: Unification
-- ════════════════════════════════════════════════════════════════

/-- `orBelnap` is the Belnap lift of `(· ∨ ·)` with identity `False`. -/
theorem orBelnap_eq_belnapLift (p q : PrProp W) :
    orBelnap p q = belnapLift (· ∨ ·) False p q :=
  ext_pointwise (fun _ => Iff.rfl) (fun w => by
    simp only [orBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- `andBelnap` is the Belnap lift of `(· ∧ ·)` with identity `True`. -/
theorem andBelnap_eq_belnapLift (p q : PrProp W) :
    andBelnap p q = belnapLift (· ∧ ·) True p q :=
  ext_pointwise (fun _ => Iff.rfl) (fun w => by
    simp only [andBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- `orFlex` is the Belnap lift of `(· ∨ ·)` with identity `False`.
    Corollary: flexible accommodation = conditional assertion = Belnap lift,
    all three for any binary connective. -/
theorem orFlex_eq_belnapLift (p q : PrProp W) :
    orFlex p q = belnapLift (· ∨ ·) False p q :=
  orFlex_eq_orBelnap p q ▸ orBelnap_eq_belnapLift p q

/-- `andFlex` is the Belnap lift of `(· ∧ ·)` with identity `True`. -/
theorem andFlex_eq_belnapLift (p q : PrProp W) :
    andFlex p q = belnapLift (· ∧ ·) True p q :=
  andFlex_eq_andBelnap p q ▸ andBelnap_eq_belnapLift p q

/-- Belnap lift reduces to the classical operation when both presuppositions hold.
    The identity element is never used — both operands contribute directly. -/
theorem belnapLift_eq_classical (f : Prop → Prop → Prop) (id : Prop)
    (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (belnapLift f id p q).assertion w = f (p.assertion w) (q.assertion w) := by
  simp only [belnapLift, if_pos hp, if_pos hq]

/-- When only the left operand is defined and `id` is a right identity,
    belnapLift returns the left operand's value: the right operand is
    invisible. -/
theorem belnapLift_right_undefined (f : Prop → Prop → Prop) (id : Prop)
    (hid : ∀ b, f b id = b) (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : ¬q.presup w) :
    (belnapLift f id p q).assertion w = p.assertion w := by
  simp only [belnapLift, if_pos hp, if_neg hq, hid]

/-- When only the right operand is defined and `id` is a left identity,
    belnapLift returns the right operand's value. -/
theorem belnapLift_left_undefined (f : Prop → Prop → Prop) (id : Prop)
    (hid : ∀ b, f id b = b) (p q : PrProp W) (w : W)
    (hp : ¬p.presup w) (hq : q.presup w) :
    (belnapLift f id p q).assertion w = q.assertion w := by
  simp only [belnapLift, if_neg hp, if_pos hq, hid]

/-- belnapLift is commutative when `f` is commutative. -/
theorem belnapLift_comm (f : Prop → Prop → Prop)
    (hcomm : ∀ a b, f a b = f b a) (id : Prop) (p q : PrProp W) :
    belnapLift f id p q = belnapLift f id q p :=
  ext_pointwise
    (fun _ => or_comm)
    (fun w => Iff.of_eq (by simp only [belnapLift]; exact hcomm _ _))

-- ════════════════════════════════════════════════════════════════
-- Collapse: All connective families agree when both defined
-- ════════════════════════════════════════════════════════════════

/-- When both presuppositions hold at w, ALL disjunction connectives
    agree on assertion: classical = filtering = K&P = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_or_agree_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((or p q).assertion w ↔ (orFilter p q).assertion w) ∧
    ((or p q).assertion w ↔ (orKP p q).assertion w) ∧
    ((or p q).assertion w ↔ (orFlex p q).assertion w) ∧
    ((or p q).assertion w ↔ (orBelnap p q).assertion w) ∧
    ((or p q).assertion w ↔ (orWeak p q).assertion w) := by
  refine ⟨Iff.rfl, Iff.rfl, ?_, ?_, Iff.rfl⟩
  · exact (orFlex_eq_or_when_both_defined p q w hp hq).symm
  · exact (orFlex_eq_or_when_both_defined p q w hp hq).symm

/-- When both presuppositions hold at w, ALL conjunction connectives
    agree on assertion: classical = filtering = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_and_agree_when_both_defined (p q : PrProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((and p q).assertion w ↔ (andFilter p q).assertion w) ∧
    ((and p q).assertion w ↔ (andFlex p q).assertion w) ∧
    ((and p q).assertion w ↔ (andBelnap p q).assertion w) ∧
    ((and p q).assertion w ↔ (andWeak p q).assertion w) := by
  refine ⟨?_, ?_, ?_, Iff.rfl⟩
  · exact Iff.rfl
  · exact (andFlex_eq_and_when_both_defined p q w hp hq).symm
  · exact (andFlex_eq_and_when_both_defined p q w hp hq).symm

-- ════════════════════════════════════════════════════════════════
-- Round-trip: Prop3 ↔ PrProp
-- ════════════════════════════════════════════════════════════════

/-- `Prop3 → PrProp → Prop3` round-trip is the identity. -/
theorem eval_ofProp3 (p : Prop3 W) : (ofProp3 p).eval = p := by
  funext w; simp only [eval, ofProp3]
  by_cases h1 : p w ≠ .indet
  · rw [if_pos h1]
    by_cases h2 : p w = .true
    · rw [if_pos h2, h2]
    · rw [if_neg h2]; symm
      exact match p w, h1, h2 with | .false, _, _ => rfl
  · rw [if_neg h1]; symm; exact not_not.mp h1

-- ════════════════════════════════════════════════════════════════
-- Genuineness
-- ════════════════════════════════════════════════════════════════

/-- Liveness is symmetric. -/
theorem liveness_comm (p q : PrProp W) (s : Finset W) :
    liveness p q s ↔ liveness q p s := by
  simp only [liveness, and_comm]

/-- Genuineness is symmetric whenever the supplied disjunction connective is
    symmetric in its operands. -/
theorem genuineness_comm (p q : PrProp W) (s : Finset W) (disj : PrProp W) :
    genuineness p q s disj ↔ genuineness q p s disj := by
  simp only [genuineness, and_comm]

-- ════════════════════════════════════════════════════════════════
-- Embedding Combinators
-- @cite{heim-1992} @cite{karttunen-1973} @cite{delpinal-bassi-sauerland-2024}
-- ════════════════════════════════════════════════════════════════

/-- Asymmetric filtering disjunction: plain proposition ∨ PrProp.

    For "A ∨ B_ψ" where only B carries a presupposition ψ, the overall
    presupposition is ¬A → ψ (Karttunen's generalization for disjunction).
    The assertion is A ∨ B.

    This is the standard projection rule for presuppositions in the second
    disjunct of a disjunction. @cite{karttunen-1973}, @cite{heim-1983} -/
def disjFilterLeft (firstDisjunct : W → Prop) (second : PrProp W) :
    PrProp W where
  assertion := fun w => firstDisjunct w ∨ second.assertion w
  presup := fun w => ¬firstDisjunct w → second.presup w

/-- Embedding under a negative factive (e.g., "is unaware that").

    "x is unaware that p" presupposes p and asserts ¬Bel_x(p).
    When the complement is a PrProp, the factive presupposes both
    the assertion and presupposition of its complement (i.e., full
    satisfaction), and asserts that the subject doesn't believe the
    assertive component.

    @cite{heim-1992}: factives presuppose their complement.
    @cite{delpinal-bassi-sauerland-2024} §3: this is what makes pex
    solve the presupposed FC puzzle — the homogeneity presupposition
    projects through the factive independently of the belief content. -/
def negFactive (complement : PrProp W)
    (believes : (W → Prop) → (W → Prop)) : PrProp W where
  assertion := fun w => ¬(believes complement.assertion w)
  presup := fun w => complement.holds w

/-- When the first disjunct is false, `disjFilterLeft` recovers full
    satisfaction of the second disjunct. -/
theorem disjFilterLeft_recovers (firstDisjunct : W → Prop) (sp : PrProp W)
    (w : W) (hFirst : ¬firstDisjunct w)
    (hFiltered : (disjFilterLeft firstDisjunct sp).holds w) :
    sp.holds w := by
  obtain ⟨hPresup, hAssert⟩ := hFiltered
  exact ⟨hPresup hFirst, hAssert.resolve_left hFirst⟩

/-- When `¬A` entails `q`'s presupposition pointwise, `disjFilterLeft A q`
    is presuppositionless (the filtering condition is satisfied at every
    world). The substrate-side fact behind @cite{karttunen-1973}'s
    asymmetric disjunction filtering rule (24b), p. 181: "A or B" carries
    no residual presupposition from B when ¬A entails it. -/
theorem disjFilterLeft_eliminates_presup_when_neg_entails
    (A : W → Prop) (q : PrProp W)
    (h : ∀ w, ¬A w → q.presup w) :
    (disjFilterLeft A q).presup = fun _ => True := by
  funext w
  simp only [disjFilterLeft, eq_iff_iff, iff_true]
  exact h w

/-- Presupposition of `negFactive` is full satisfaction of the complement. -/
theorem negFactive_presup_eq (complement : PrProp W)
    (believes : (W → Prop) → (W → Prop)) :
    (negFactive complement believes).presup = complement.holds := rfl

/-- Universal presupposition projection: presuppositions project
    universally from the scope of a universal quantifier.

    For ∀x ∈ S, φ(x) where φ(x) is a PrProp:
    - asserts: ∀x ∈ S, assertion(φ(x))
    - presupposes: ∀x ∈ S, presup(φ(x))

    @cite{chemla-2009a}, @cite{fox-2013}, @cite{mayr-sauerland-2015}:
    presuppositions triggered in the scope of a universal quantifier
    tend to project universally. -/
def forallPr {α : Type*} (S : α → Prop) (φ : α → PrProp W) : PrProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∀ x, S x → (φ x).assertion w

/-- Existential presupposition projection (universal presup, existential assert).

    For ∃x ∈ S, φ(x): presuppositions still project universally,
    but the assertion is existential.

    This models the pattern where ∃x ∈ S(φ(x)) presupposes
    ∀x ∈ S(presup(φ(x))) — the "universal projection from existential
    quantifier" pattern supported by @cite{chemla-2009a}. -/
def existsPrUniv {α : Type*} (S : α → Prop) (φ : α → PrProp W) : PrProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- Negated existential with universal presupposition projection.

    For ¬∃x ∈ S, φ(x): equivalent to ∀x ∈ S, ¬φ(x).
    Presuppositions project universally. -/
def negExistsPr {α : Type*} (S : α → Prop) (φ : α → PrProp W) : PrProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ¬∃ x, S x ∧ (φ x).assertion w

/-- `forallPr` holds iff every member satisfies both presupposition and assertion. -/
theorem forallPr_holds {α : Type*} (S : α → Prop) (φ : α → PrProp W) (w : W) :
    (forallPr S φ).holds w ↔
      (∀ x, S x → (φ x).presup w) ∧ (∀ x, S x → (φ x).assertion w) :=
  Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § Definite-Description Combinator
-- ════════════════════════════════════════════════════════════════

/-- The canonical definite-description combinator. Given:

- `referent : W → Option E` — a partial selector returning the referent at
  each world (or `none` when no unique referent is determined),
- `scope : E → W → Bool` — what is asserted of the chosen referent,

build the `PrProp` that presupposes referent definedness and asserts the
scope of the referent. This is the single source of truth for all definite
denotations in the library: uniqueness-based (`russellIotaList domain R`),
familiarity-based (`russellIotaList dc.salient R`), anaphoric
(`russellIotaList domain (R ∧ Q)`), and Donnellan's attributive
(`attributiveContent domain R`) all instantiate the selector slot. -/
def presupOfReferent {E : Type*} (referent : W → Option E)
    (scope : E → W → Bool) : PrProp W where
  presup := fun w => (referent w).isSome
  assertion := fun w => match referent w with
    | some e => scope e w
    | none => false

/-- `presupOfReferent` is defined iff a referent is selected at `w`. -/
@[simp] theorem presupOfReferent_presup {E : Type*}
    (referent : W → Option E) (scope : E → W → Bool) (w : W) :
    (presupOfReferent referent scope).presup w = (referent w).isSome := rfl

/-- When a referent is selected, the assertion is the scope applied to it. -/
theorem presupOfReferent_assertion_some {E : Type*}
    (referent : W → Option E) (scope : E → W → Bool) (w : W) (e : E)
    (h : referent w = some e) :
    (presupOfReferent referent scope).assertion w = scope e w := by
  simp [presupOfReferent, h]

/-- Without a referent, the assertion is `false`. -/
theorem presupOfReferent_assertion_none {E : Type*}
    (referent : W → Option E) (scope : E → W → Bool) (w : W)
    (h : referent w = none) :
    (presupOfReferent referent scope).assertion w = false := by
  simp [presupOfReferent, h]

end PrProp

end Core.Presupposition
