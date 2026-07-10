import Linglib.Core.Logic.Truth3
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Part

/-!
# Partial Propositions

Partial propositions — propositions that may be undefined at some evaluation
points. References: [heim-1983], [schlenker-2009], [von-fintel-1999],
[geurts-2005], [belnap-1970], [karttunen-1973],
[karttunen-peters-1979], [bochvar-1937].

## Main declarations

* `PartialProp W` — partial proposition with `presup, assertion : W → Prop`.
  The canonical type for partial propositions. Fields are `Prop`-valued
  following the mathlib convention.
* `PartialValue W α` — presupposed value polymorphic in the at-issue content
  type (`α = ℚ` for degrees, `α = E` for entities). Presupposition is
  also `W → Prop`.
* Connective families on `PartialProp W`: classical (`and`, `or`, `imp`, `xor`),
  filtering / Karttunen (`andFilter`, `impFilter`, `orFilter`), K&P
  symmetric disjunction (`orKPSymmetric`), positive-antecedent
  disjunction (`orPositive`, a documented rival), Strong Kleene
  (`andStrong`, `orStrong` — the `Truth3` lattice meet/join), and Belnap
  conditional assertion (`andBelnap`, `orBelnap`; the
  flexible-accommodation `andFlex`/`orFlex` are definitionally the same
  operators). Classical `and`/`or` are simultaneously Weak Kleene; the
  filtering connectives are Peters' middle Kleene ([peters-1979],
  `eval_andFilter`/`eval_orFilter`).
* `belnapLift` — unifier showing Belnap = flexible accommodation for any
  binary `Prop` operator with an identity.
* `eval` — evaluation into `Prop3 W`, with the simp-normal interface
  `eval_eq_true_iff`/`eval_eq_false_iff`/`eval_eq_indet_iff`;
  `eval_surjective`/`eval_eq_eval_iff` make precise that `PartialProp` is the
  total-representative presentation of `Prop3` (values outside the
  presupposition are inert).
* `strawsonEntails`, `strongEntails` — entailment relations: the
  canonical [von-fintel-1999] form (presup-as-premise; not transitive,
  `strawsonEntails_not_trans`) and the stronger variant that additionally
  requires `q`'s presupposition to project from `p`'s satisfaction.
* `liveness`, `genuineness` — [yagi-2025] disjunction-update conditions.
* `presupOfReferent` — definite-description combinator (single source of
  truth for singular definite denotations).

## Implementation notes

`PartialProp W` is parametric over the evaluation point. Common instantiations:
`PartialProp World` (classical possible worlds), `PartialProp (Possibility W E)`
(dynamic world-assignment pairs).

The choice of connective system (how gaps behave under ∧/∨) is orthogonal
to the representation type — see `Truth3.GapPolicy`. Connectives are
paired with `eval_*` bridge theorems mapping each to the corresponding
`Truth3` operator on the evaluation.

`open Classical` is in scope at the namespace level because most
theorems case-split on `Prop`-valued fields. Mathlib uses the same
idiom in logic-heavy files such as `Mathlib/Order/Filter/Basic.lean`.

## Todo

* `PartialProp W = PartialValue W Prop` unification: `PartialValue` already generalizes
  `PartialProp` at the type level; unifying would let the connective zoo lift
  to arbitrary at-issue carriers.
* `evalLift : (Truth3 → Truth3 → Truth3) → (PartialProp W → PartialProp W → PartialProp W)`
  would collapse `xor`, `andBelnap`, `orBelnap` into
  one definition each, with one bridge theorem instead of eight.
-/

namespace Semantics.Presupposition

open Trivalent

/-- A presupposed value: a value that is only defined when its
presupposition holds.

`PartialValue W α` generalizes presuppositional propositions: the
presupposition is `W → Prop`, and the at-issue content is any type — a
truth value (`Bool`), a degree (`ℚ`), a measure, etc.

Linguistic motivation: many presupposition triggers return non-boolean
values. The revised *per* entry ([bale-schwarz-2022], eq. 43)
returns a presupposed pure number (`ℚ`). Definite descriptions return
presupposed entities. `PartialValue` handles all of these uniformly. -/
structure PartialValue (W : Type*) (α : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (value). -/
  value : W → α

namespace PartialValue

variable {W : Type*} {α : Type*}

/-- A presupposed value is defined at w iff its presupposition holds. -/
def defined (w : W) (pv : PartialValue W α) : Prop := pv.presup w

/-- The mathlib rendering: pointwise, a presupposed value is a `Part`-valued function, the
presupposition as domain. `PartialValue` is the *total-representative* presentation — the
record carries a value everywhere (no proof-carrying `Part.get`); `toPart` forgets the
values outside the presupposition. -/
def toPart (pv : PartialValue W α) : W → Part α := λ w => ⟨pv.presup w, λ _ => pv.value w⟩

open Classical in
/-- Every `Part`-valued function has a total representative: `toPart` is surjective, so the
two presentations differ only by the (linguistically inert) values outside the
presupposition. -/
theorem toPart_surjective [Inhabited α] :
    Function.Surjective (toPart : PartialValue W α → W → Part α) := λ f =>
  ⟨⟨λ w => (f w).Dom, λ w => if h : (f w).Dom then (f w).get h else default⟩, by
    funext w
    exact Part.ext' Iff.rfl (λ h₁ _ => dif_pos h₁)⟩

end PartialValue

/-! ### `PartialProp`: Prop-based partial propositions -/

/-- A presuppositional proposition: assertion + presupposition.

    Fields are `Prop`-valued following the Mathlib convention. Construct
    directly with `{ presup := ..., assertion := ... }`; for finite worlds
    with `DecidableEq`, the predicates are auto-decidable. -/
@[ext]
structure PartialProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (assertion). -/
  assertion : W → Prop

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Constructors -/

/-- Create a presuppositionless proposition from a `W → Prop`. -/
def ofProp (p : W → Prop) : PartialProp W where
  presup := fun _ => True
  assertion := p

/-- Convert a three-valued proposition to a PartialProp.
    Inverse of `PartialProp.eval`: defined iff value ≠ indet,
    assertion iff value = true. -/
def ofProp3 (p : Prop3 W) : PartialProp W where
  presup := fun w => p w ≠ .indet
  assertion := fun w => p w = .true

/-- Belnap's conditional assertion (A/B): assert B on condition A.

    Assertive_w iff A is true at w; what is asserted = B.
    [belnap-1970], (3): "(A/B) is assertive_w just in case
    A is true_w. (A/B)_w = B_w." -/
def condAssert (A B : W → Prop) : PartialProp W where
  presup := A
  assertion := B

/-! ### Satisfaction relations -/

/-- Full satisfaction relation: both presupposition and assertion hold.

    Argument order `(w : W) (p : PartialProp W)` supports `updateFromSat`:
    `updateFromSat PartialProp.holds p` gives the full CCP (presupposition
    test + assertion filter). -/
def holds (w : W) (p : PartialProp W) : Prop := p.presup w ∧ p.assertion w

/-- Definedness relation: presupposition holds at the evaluation point.

    Argument order `(w : W) (p : PartialProp W)` supports `updateFromSat`:
    `updateFromSat PartialProp.defined p` gives the presupposition test CCP. -/
def defined (w : W) (p : PartialProp W) : Prop := p.presup w

/-! ### Constants -/

/-- Create a tautological presupposition. -/
def top : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => True

/-- Create a contradictory presupposition. -/
def bot : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => False

/-- Create a presupposition failure (never defined). -/
def undefined : PartialProp W where
  presup := fun _ => False
  assertion := fun _ => False

/-! ### Evaluation -/

/-- Evaluate a presuppositional proposition to three-valued truth.
    Noncomputable because it decides Prop-valued presupposition and
    assertion via classical logic. -/
noncomputable def eval (p : PartialProp W) : Prop3 W := fun w =>
  if p.presup w then
    if p.assertion w then .true else .false
  else .indet

/-! The simp-normal interface to `eval`: consumers reason through the three value
characterizations rather than the classical `if`-nest. -/

@[simp] theorem eval_eq_true_iff (p : PartialProp W) (w : W) :
    p.eval w = .true ↔ p.presup w ∧ p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_false_iff (p : PartialProp W) (w : W) :
    p.eval w = .false ↔ p.presup w ∧ ¬p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_indet_iff (p : PartialProp W) (w : W) :
    p.eval w = .indet ↔ ¬p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

/-! ### Classical connectives -/

/-- Classical (internal / choice) negation: a hole.
    Lets the presupposition through unchanged. -/
def neg (p : PartialProp W) : PartialProp W where
  presup := p.presup
  assertion := fun w => ¬p.assertion w

/-- Bochvar's truth operator `t`: a plug-as-affirmation ([bochvar-1937]).
    Always defined; maps presupposition failure to `False`.
    [karttunen-1973] §10 fn 18: `t(A)` has truth-table
    `T → T`, `F → F`, `# → F`. Composing classical negation with `t`
    yields external negation: `negExt p = neg (truthOp p)`. -/
def truthOp (p : PartialProp W) : PartialProp W where
  presup := fun _ => True
  assertion := fun w => p.presup w ∧ p.assertion w

/-- Bochvar external (exclusion) negation: a plug.
    Always defined; true when `p` is false or undefined, false only when
    `p` is true. Equals `neg (truthOp p)` per [karttunen-1973] §10
    fn 18: `⌜¬A⌝ ≡ ⌜~t(A)⌝`. -/
def negExt (p : PartialProp W) : PartialProp W := neg (truthOp p)

/-- Classical conjunction: both presuppositions must hold. This is also
    Weak Kleene conjunction ([kleene-1952]: indet is absorbing). -/
def and (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Classical disjunction: both presuppositions must hold. This is also
    Weak Kleene disjunction ([kleene-1952]: indet is absorbing) — see
    `eval_or`. -/
def or (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- Classical implication: both presuppositions must hold. -/
def imp (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => p.assertion w → q.assertion w

/-- Exclusive disjunction: both presuppositions must hold (no filtering).

    Under Strong Kleene, `Truth3.xor` propagates undefinedness
    unconditionally (`xor_indet_iff`), so exclusive disjunction never
    filters presupposition failure from either disjunct.
    [wang-davidson-2026] -/
def xor (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ q.presup w
  assertion := fun w => (p.assertion w ∧ ¬q.assertion w) ∨ (¬p.assertion w ∧ q.assertion w)

/-! ### Filtering connectives (Karttunen) -/

/-- Filtering conjunction ([karttunen-1973], [peters-1979]): the first
    conjunct can satisfy the second's presupposition. -/
def andFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∧ q.assertion w

/-- Filtering implication ([karttunen-1973], [peters-1979]): the
    antecedent can satisfy the consequent's presupposition. -/
def impFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (p.assertion w → q.presup w)
  assertion := fun w => p.assertion w → q.assertion w

/-- Filtering disjunction (asymmetric, [karttunen-1973]): the *negation*
    of the first disjunct can satisfy the second's presupposition —
    *Either there is no bathroom or the bathroom is upstairs* is defined
    because the second disjunct's bathroom presupposition is required
    only at worlds where the first disjunct is false.

    Generalizes `disjFilterLeft` to a presuppositional first disjunct
    (`orFilter_ofProp`). The symmetric K&P variant is `orKPSymmetric`;
    the positive-antecedent variant is `orPositive`. -/
def orFilter (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∧ (¬p.assertion w → q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

/-! ### Positive-antecedent symmetric disjunction -/

/-- Positive-antecedent symmetric disjunction: each disjunct's
    presupposition is required where the *other disjunct's assertion
    holds*, plus at least one disjunct defined. This is NOT Karttunen
    filtering (`orFilter`): it demands the second disjunct's
    presupposition exactly where the first is *true*, un-filtering
    bathroom-sentence data. Retained as a documented rival:
    [sharvit-2025] identifies it as the root cause of K/P-style failure
    (`Studies/Sharvit2025.lean`), and [yagi-2025] §2.2 discusses the
    `Π(φ) ∨ Π(ψ)` conjunct as a candidate fix (`Studies/Yagi2025.lean`). -/
def orPositive (p q : PartialProp W) : PartialProp W where
  presup := fun w =>
    (p.assertion w → q.presup w) ∧
    (q.assertion w → p.presup w) ∧
    (p.presup w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

/-! ### K&P two-dimensional disjunction -/

/-- Symmetric two-dimensional disjunction in the K&P
    ([karttunen-peters-1979]) tradition:

    Π(φ ∨ ψ) = (A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))
    A(φ ∨ ψ) = A(φ) ∨ A(ψ)

    The name carries the `Symmetric` suffix because the literal K&P 1979
    formulation was *asymmetric* (it would project the first disjunct's
    presupposition unconditionally; [yagi-2025] fn 2). This is the
    symmetrized variant standard in post-2021 literature, matching
    [yagi-2025] Definition 2 (cf. [kalomoiros-schwarz-2021] for
    experimental support of symmetry). -/
def orKPSymmetric (p q : PartialProp W) : PartialProp W where
  presup := fun w => (q.assertion w ∨ p.presup w) ∧ (p.assertion w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

/-! ### Strong Kleene -/

/-- Strong Kleene disjunction ([kleene-1952]): defined iff both disjuncts
    are defined or either is defined-and-true (`T ∨ # = T`, `F ∨ # = #`).
    This is the `Truth3` lattice join — see `eval_orStrong`. -/
def orStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-- Strong Kleene conjunction: defined iff both conjuncts are defined or
    either is defined-and-false (`F ∧ # = F`, `T ∧ # = #`). This is the
    `Truth3` lattice meet — see `eval_andStrong`. -/
def andStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ ¬p.assertion w) ∨ (q.presup w ∧ ¬q.assertion w)
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-! ### Belnap conditional assertion ([belnap-1970])

Under the Belnap reading, `presup` is the **assertive** field — whether the
proposition asserts something at `w` (vs being nonassertive / silent). -/

/-- Belnap conjunction: assertive iff at least one conjunct is assertive.
    What it asserts = conjunction of assertive conjuncts' content.

    [belnap-1970], (8). Contrast with classical `PartialProp.and` (both
    must be defined) and filtering `PartialProp.andFilter` (left-to-right). -/
def andBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- Belnap disjunction: assertive iff at least one disjunct is assertive.
    What it asserts = disjunction of assertive disjuncts' content.

    [belnap-1970], (9). -/
def orBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-! ### Flexible accommodation

The flexible-accommodation connectives of the pragmatic tradition
([geurts-2005], [aloni-2022], the static counterpart of [yagi-2025]'s
dynamic update) are *definitionally* the Belnap connectives: each operand
is evaluated only against worlds where its own presupposition holds, which
handles conflicting presuppositions (where classical and filtering
disjunction both fail). The two traditions differ in the *accommodation
theory* surrounding the operator (default ⊤ vs unconditional assertive),
not in the operator itself — see [yagi-2025] §3.2 for the distinction. -/

/-- Flexible accommodation disjunction = `orBelnap`. -/
abbrev orFlex : PartialProp W → PartialProp W → PartialProp W := orBelnap

/-- Flexible accommodation conjunction = `andBelnap`. -/
abbrev andFlex : PartialProp W → PartialProp W → PartialProp W := andBelnap

/-- **Belnap lift**: uniform construction for conditional assertion connectives.

    Given a binary Prop function `f` and its identity element `unit`,
    constructs a PartialProp connective where:
    - Defined (assertive) iff at least one operand is defined
    - Assertion applies `f` to each operand's content, substituting `unit`
      for undefined operands (making them "silent")

    [belnap-1970]: undefined operands contribute the identity element.
    Noncomputable because it uses classical `if` on Props.

    Defined instances:
    - `belnapLift (· ∨ ·) False` = `orBelnap` = `orFlex` (False is identity for ∨)
    - `belnapLift (· ∧ ·) True` = `andBelnap` = `andFlex` (True is identity for ∧)
    -/
noncomputable def belnapLift (f : Prop → Prop → Prop) (unit : Prop)
    (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => f (if p.presup w then p.assertion w else unit)
                          (if q.presup w then q.assertion w else unit)

/-! ### Entailment relations -/

/-- Strawson entailment ([von-fintel-1999]): `p` entails `q` at every
    world where both presuppositions hold. The conclusion `q`'s
    presupposition is a *premise* added to the entailment, not something
    the entailment delivers. The same notion on bilateral-update
    denotations is `ElliottSudo2025.strawsonEntails`. -/
def strawsonEntails (p q : PartialProp W) : Prop :=
  ∀ w, p.presup w → q.presup w → p.assertion w → q.assertion w

/-- Strawson entailment is **not** transitive — an undefined middle term discharges both
    premises vacuously, the well-known failure of [von-fintel-1999]'s notion — so
    `strawsonEntails` supports no `Preorder` instance. -/
theorem strawsonEntails_not_trans :
    ¬ ∀ p q r : PartialProp Unit,
        strawsonEntails p q → strawsonEntails q r → strawsonEntails p r :=
  λ h =>
    (h top undefined bot (λ _ _ hq _ => hq.elim) (λ _ hq _ _ => hq.elim))
      () trivial trivial trivial

/-- Strong (Strawson-projecting) entailment: at every world where `p` is
    defined and true, `q` is *both* defined and true. Stronger than
    `strawsonEntails`: this variant also requires that `q`'s
    presupposition projects from `p`'s satisfaction (so it embeds a
    presupposition-projection burden the canonical von Fintel form
    exempts). -/
def strongEntails (p q : PartialProp W) : Prop :=
  ∀ w, p.presup w → p.assertion w → q.presup w ∧ q.assertion w

/-- Strawson equivalence: mutual Strawson entailment. -/
def strawsonEquiv (p q : PartialProp W) : Prop :=
  strawsonEntails p q ∧ strawsonEntails q p

/-! ### Genuineness / liveness ([zimmermann-2000], [geurts-2005], [katzir-singh-2012]) -/

/-- **Liveness** for disjunction: each disjunct is satisfied (presupposition
    AND assertion hold) at some world of the state.

    This is the singleton-survival side of [yagi-2025] Definition 8:
    `{w}[φ] = {w}` for some `w ∈ s`. The disjunction-update side
    (`w ∈ s[φ ∨ ψ]`) is the additional constraint expressed by
    `genuineness` below. -/
def liveness (p q : PartialProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.holds w) ∧
  (∃ w ∈ s, q.holds w)

/-- **Genuineness** for disjunction ([yagi-2025] Definition 8, after
    [zimmermann-2000]). A disjunction `p ∨ q`, with disjunction-update
    realised by the connective `disj`, follows genuineness in a state `s` iff
    there are worlds `w, w' ∈ s` such that:

    - `{w}[p] = {w}` AND `w ∈ s[p ∨ q]` — the left disjunct's witness survives
      both its own update (= `p.holds w`) and the disjunction's update
      (= `disj.holds w`).
    - `{w'}[q] = {w'}` AND `w' ∈ s[p ∨ q]` — analogously for the right disjunct.

    The disjunction-update side rules out witnesses that survive the local
    presupposition+assertion update but are eliminated by the joint update —
    a vacuous addition under `orFlex`/`orBelnap` (`liveness_implies_genuineness_orFlex`),
    but the substantive constraint [yagi-2025] §3.2 invokes for dynamic
    negation: genuineness must hold even within the scope of negation, where
    "we end up negating both disjuncts".

    The `disj` argument is parametric so the substrate stays
    framework-neutral; consumers supply the disjunction *connective* whose
    update they wish to test against (orFlex / classical or / Geurts
    modal split). -/
def genuineness (disj : PartialProp W → PartialProp W → PartialProp W)
    (p q : PartialProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.holds w ∧ (disj p q).holds w) ∧
  (∃ w ∈ s, q.holds w ∧ (disj p q).holds w)

/-- Under `orFlex`, `liveness` implies `genuineness`: each witness for
    `p.holds`/`q.holds` automatically survives the disjunction's update,
    because `(orFlex p q).holds w` reduces to `p.holds w ∨ q.holds w`. -/
theorem liveness_implies_genuineness_orFlex (p q : PartialProp W) (s : Finset W)
    (h : liveness p q s) : genuineness orFlex p q s := by
  obtain ⟨⟨w, hw, hp⟩, ⟨w', hw', hq⟩⟩ := h
  refine ⟨⟨w, hw, hp, ?_⟩, ⟨w', hw', hq, ?_⟩⟩
  · exact ⟨Or.inl hp.1, Or.inl hp⟩
  · exact ⟨Or.inr hq.1, Or.inr hq⟩

/-! ### Negation theorems -/

/-- Negation preserves presupposition. -/
@[simp] theorem neg_presup (p : PartialProp W) : (neg p).presup = p.presup := rfl

/-- Double negation restores assertion (classical). -/
theorem neg_neg_assertion (p : PartialProp W) (w : W) :
    (neg (neg p)).assertion w ↔ p.assertion w := Classical.not_not

/-- Double negation identity. -/
@[simp] theorem neg_neg (p : PartialProp W) : neg (neg p) = p :=
  PartialProp.ext rfl (funext fun _ => propext Classical.not_not)

/-- The truth operator is always defined (it's a plug). -/
@[simp] theorem truthOp_presup (p : PartialProp W) (w : W) :
    (truthOp p).presup w := trivial

/-- External negation is always defined (it's a plug). -/
@[simp] theorem negExt_presup (p : PartialProp W) (w : W) :
    (negExt p).presup w := trivial

/-- Internal and external negation agree on assertion when the presupposition
    holds. They diverge only at presupposition failure: `neg p` is undefined,
    `negExt p` is true. [karttunen-1973] §10 fn 18. -/
theorem neg_assertion_iff_negExt_assertion_when_defined (p : PartialProp W) (w : W)
    (h : p.presup w) :
    (neg p).assertion w ↔ (negExt p).assertion w := by
  simp only [neg, negExt, truthOp, h, true_and]

/-- External negation has the dual assertion to the truth operator at every
    world: `negExt = ¬truthOp` extensionally, by definition (negExt = neg ∘ truthOp
    and neg is `¬` on assertion). -/
theorem negExt_assertion (p : PartialProp W) (w : W) :
    (negExt p).assertion w ↔ ¬(truthOp p).assertion w := Iff.rfl

/-- Karttunen §10 fn 18 truth table for external negation, presup-failure case:
    when `p`'s presupposition fails, `negExt p` is true (the plug behavior). -/
theorem negExt_assertion_of_presup_failure (p : PartialProp W) (w : W)
    (h : ¬p.presup w) :
    (negExt p).assertion w := by
  simp only [negExt, neg, truthOp, h, false_and, not_false_eq_true]

/-! ### Filtering theorems -/

/-- Filtering implication eliminates presupposition when antecedent entails it. -/
theorem impFilter_eliminates_presup (p q : PartialProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (impFilter p q).presup = p.presup := by
  funext w; simp only [impFilter]
  exact propext ⟨fun ⟨hp, _⟩ => hp, fun hp => ⟨hp, h w⟩⟩

/-- When A(p) = P(q), filtering implication has trivial presupposition. -/
theorem impFilter_trivializes_presup (p q : PartialProp W)
    (h : p.assertion = q.presup) :
    (impFilter p q).presup = p.presup :=
  impFilter_eliminates_presup p q (fun _ ha => h ▸ ha)

/-- The filtering presupposition of `impFilter` and `andFilter` are identical.
    This is the formal content of [karttunen-1973] §8: the filtering
    rules for *if A then B* and *A and B* coincide because both reduce to
    `p.presup ∧ (p.assertion → q.presup)`. -/
theorem impFilter_presup_eq_andFilter_presup (p q : PartialProp W) :
    (impFilter p q).presup = (andFilter p q).presup := rfl

/-! ### Evaluation theorems -/

/-- Evaluation is defined iff presupposition holds. -/
@[simp] theorem eval_isDefined (p : PartialProp W) (w : W) :
    (p.eval w).isDefined ↔ p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, hp, ha, Truth3.isDefined]

/-- Negation evaluation. -/
theorem eval_neg (p : PartialProp W) (w : W) :
    (neg p).eval w = Truth3.neg (p.eval w) := by
  simp only [eval, neg]
  by_cases hp : p.presup w
  · simp only [if_pos hp]
    by_cases ha : p.assertion w
    · simp [if_pos ha, if_neg (not_not.mpr ha), Truth3.neg]
    · simp [if_neg ha, if_pos ha, Truth3.neg]
  · simp [if_neg hp, Truth3.neg]

/-- Classical conjunction evaluation (both defined). -/
theorem eval_and (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (and p q).eval w = p.eval w ⊓ q.eval w := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, and, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- Filtering implication when antecedent false: result is true. -/
theorem eval_impFilter_antecedent_false (p q : PartialProp W) (w : W)
    (hp : p.presup w) (ha : ¬p.assertion w) :
    (impFilter p q).eval w = .true := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun h => absurd h ha⟩
  have hassert : (impFilter p q).assertion w := fun h => absurd h ha
  simp only [eval, if_pos hpresup, if_pos hassert]

/-- Filtering implication when antecedent true: depends on consequent. -/
theorem eval_impFilter_antecedent_true (p q : PartialProp W) (w : W)
    (hp : p.presup w) (ha : p.assertion w) (hq : q.presup w) :
    (impFilter p q).eval w =
      if q.assertion w then .true else .false := by
  have hpresup : (impFilter p q).presup w := ⟨hp, fun _ => hq⟩
  by_cases hqa : q.assertion w
  · have hass : (impFilter p q).assertion w := fun _ => hqa
    simp only [eval, if_pos hpresup, if_pos hass, if_pos hqa]
  · have hass : ¬(impFilter p q).assertion w := fun h => hqa (h ha)
    simp only [eval, if_pos hpresup, if_neg hass, if_neg hqa]

/-- `orStrong` evaluates to the `Truth3` lattice join pointwise: Strong
    Kleene disjunction is ⊔ in the `false < indet < true` order,
    unconditionally. -/
theorem eval_orStrong (p q : PartialProp W) (w : W) :
    (orStrong p q).eval w = p.eval w ⊔ q.eval w := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, orStrong, hp, hq, ha, hb] <;> decide

/-- `andStrong` evaluates to the `Truth3` lattice meet pointwise,
    unconditionally. -/
theorem eval_andStrong (p q : PartialProp W) (w : W) :
    (andStrong p q).eval w = p.eval w ⊓ q.eval w := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, andStrong, hp, hq, ha, hb] <;> decide

/-- **Karttunen filtering conjunction is Peters' middle Kleene**
    ([peters-1979]): `andFilter` evaluates to the asymmetric
    `Truth3.meetMiddle` on both dimensions, unconditionally. -/
theorem eval_andFilter (p q : PartialProp W) (w : W) :
    (andFilter p q).eval w = Truth3.meetMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, andFilter, Truth3.meetMiddle, hp, hq, ha, hb] <;> decide

/-- **Karttunen filtering disjunction is Peters' middle Kleene**
    ([peters-1979]): `orFilter` evaluates to the asymmetric
    `Truth3.joinMiddle` on both dimensions, unconditionally. -/
theorem eval_orFilter (p q : PartialProp W) (w : W) :
    (orFilter p q).eval w = Truth3.joinMiddle (p.eval w) (q.eval w) := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, orFilter, Truth3.joinMiddle, hp, hq, ha, hb] <;> decide

/-- Exclusive disjunction evaluation matches `Truth3.xor` when both defined. -/
theorem eval_xor (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (xor p q).eval w = Truth3.xor (p.eval w) (q.eval w) := by
  have hpq : p.presup w ∧ q.presup w := ⟨hp, hq⟩
  simp only [eval, xor, if_pos hp, if_pos hq, if_pos hpq]
  by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb, Truth3.xor]

/-- Exclusive disjunction never filters: when either presupposition fails,
    the result is undefined. [wang-davidson-2026] -/
theorem eval_xor_no_filter (p q : PartialProp W) (w : W)
    (hq : ¬q.presup w) :
    (xor p q).eval w = .indet := by
  have : ¬(xor p q).presup w := fun ⟨_, hq'⟩ => hq hq'
  simp [eval, if_neg this]

/-! ### `orKPSymmetric` theorem -/

/-- When presuppositions conflict at w, the symmetric K&P presupposition
    entails the assertion: defined → true, so the disjunction can never be
    both defined and false. [yagi-2025] §2.2 -/
theorem orKPSymmetric_presup_entails_when_conflicting (p q : PartialProp W) (w : W)
    (h_conflict : ¬(p.presup w ∧ q.presup w))
    (h_presup : (orKPSymmetric p q).presup w) :
    (orKPSymmetric p q).assertion w := by
  simp only [orKPSymmetric] at h_presup ⊢
  obtain ⟨h1, h2⟩ := h_presup
  by_cases hp : p.presup w
  · have hq : ¬q.presup w := fun hq => h_conflict ⟨hp, hq⟩
    exact Or.inl (h2.resolve_right hq)
  · exact Or.inr (h1.resolve_right hp)

/-! ### Flex collapse theorems -/

/-- orFlex reduces to standard disjunction when both presuppositions hold. -/
theorem orFlex_eq_or_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (orFlex p q).assertion w ↔ (or p q).assertion w := by
  simp only [orFlex, or]
  constructor
  · rintro (⟨_, ha⟩ | ⟨_, ha⟩) <;> [exact Or.inl ha; exact Or.inr ha]
  · rintro (ha | ha) <;> [exact Or.inl ⟨hp, ha⟩; exact Or.inr ⟨hq, ha⟩]

/-- orFlex presupposition is weaker than or's (p ∨ q vs p ∧ q). -/
theorem orFlex_presup_weaker (p q : PartialProp W) (w : W)
    (h : (or p q).presup w) :
    (orFlex p q).presup w := by
  exact Or.inl h.1

/-- andFlex reduces to standard conjunction when both presuppositions hold. -/
theorem andFlex_eq_and_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (andFlex p q).assertion w ↔ (and p q).assertion w := by
  simp only [andFlex, and]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨h1 hp, h2 hq⟩
  · intro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩

/-- andFlex presupposition is weaker than and's (p ∨ q vs p ∧ q). -/
theorem andFlex_presup_weaker (p q : PartialProp W) (w : W)
    (h : (and p q).presup w) :
    (andFlex p q).presup w := by
  exact Or.inl h.1

/-! ### Eval: Weak Kleene / Belnap -/

/-- `or` evaluates to `Truth3.joinWeak` pointwise (classical disjunction
    is Weak Kleene). -/
theorem eval_or (p q : PartialProp W) (w : W) :
    (or p q).eval w = Truth3.joinWeak (p.eval w) (q.eval w) := by
  simp only [eval, or, Truth3.joinWeak]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- Belnap conjunction evaluates to `Truth3.meetBelnap` pointwise. -/
theorem eval_andBelnap (p q : PartialProp W) (w : W) :
    (andBelnap p q).eval w = Truth3.meetBelnap (p.eval w) (q.eval w) := by
  simp only [eval, andBelnap, Truth3.meetBelnap]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- Belnap disjunction evaluates to `Truth3.joinBelnap` pointwise. -/
theorem eval_orBelnap (p q : PartialProp W) (w : W) :
    (orBelnap p q).eval w = Truth3.joinBelnap (p.eval w) (q.eval w) := by
  simp only [eval, orBelnap, Truth3.joinBelnap]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-! ### Belnap lift: unification -/

/-- `orBelnap` is the Belnap lift of `(· ∨ ·)` with identity `False`. -/
theorem orBelnap_eq_belnapLift (p q : PartialProp W) :
    orBelnap p q = belnapLift (· ∨ ·) False p q :=
  PartialProp.ext rfl (funext fun w => by
    simp only [orBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- `andBelnap` is the Belnap lift of `(· ∧ ·)` with identity `True`. -/
theorem andBelnap_eq_belnapLift (p q : PartialProp W) :
    andBelnap p q = belnapLift (· ∧ ·) True p q :=
  PartialProp.ext rfl (funext fun w => by
    simp only [andBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- Belnap lift reduces to the classical operation when both presuppositions hold.
    The identity element is never used — both operands contribute directly. -/
theorem belnapLift_eq_classical (f : Prop → Prop → Prop) (unit : Prop)
    (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (belnapLift f unit p q).assertion w = f (p.assertion w) (q.assertion w) := by
  simp only [belnapLift, if_pos hp, if_pos hq]

/-- When only the left operand is defined and `unit` is a right identity,
    belnapLift returns the left operand's value: the right operand is
    invisible. -/
theorem belnapLift_right_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f b unit = b) (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : ¬q.presup w) :
    (belnapLift f unit p q).assertion w = p.assertion w := by
  simp only [belnapLift, if_pos hp, if_neg hq, hunit]

/-- When only the right operand is defined and `unit` is a left identity,
    belnapLift returns the right operand's value. -/
theorem belnapLift_left_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f unit b = b) (p q : PartialProp W) (w : W)
    (hp : ¬p.presup w) (hq : q.presup w) :
    (belnapLift f unit p q).assertion w = q.assertion w := by
  simp only [belnapLift, if_neg hp, if_pos hq, hunit]

/-- belnapLift is commutative when `f` is commutative. -/
theorem belnapLift_comm (f : Prop → Prop → Prop)
    (hcomm : ∀ a b, f a b = f b a) (unit : Prop) (p q : PartialProp W) :
    belnapLift f unit p q = belnapLift f unit q p :=
  PartialProp.ext
    (funext fun _ => propext or_comm)
    (funext fun w => by simp only [belnapLift]; exact hcomm _ _)

/-! ### Collapse: all connective families agree when both defined -/

/-- When both presuppositions hold at w, ALL disjunction connectives
    agree on assertion: classical = filtering = K&P = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_or_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((or p q).assertion w ↔ (orFilter p q).assertion w) ∧
    ((or p q).assertion w ↔ (orPositive p q).assertion w) ∧
    ((or p q).assertion w ↔ (orKPSymmetric p q).assertion w) ∧
    ((or p q).assertion w ↔ (orFlex p q).assertion w) := by
  refine ⟨Iff.rfl, Iff.rfl, Iff.rfl, ?_⟩
  exact (orFlex_eq_or_when_both_defined p q w hp hq).symm

/-- When both presuppositions hold at w, ALL conjunction connectives
    agree on assertion: classical = filtering = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_and_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((and p q).assertion w ↔ (andFilter p q).assertion w) ∧
    ((and p q).assertion w ↔ (andFlex p q).assertion w) := by
  refine ⟨Iff.rfl, ?_⟩
  exact (andFlex_eq_and_when_both_defined p q w hp hq).symm

/-! ### Round-trip: `Prop3` ↔ `PartialProp` -/

/-- `Prop3 → PartialProp → Prop3` round-trip is the identity. -/
theorem eval_ofProp3 (p : Prop3 W) : (ofProp3 p).eval = p := by
  funext w; simp only [eval, ofProp3]
  by_cases h1 : p w ≠ .indet
  · rw [if_pos h1]
    by_cases h2 : p w = .true
    · rw [if_pos h2, h2]
    · rw [if_neg h2]; symm
      exact match p w, h1, h2 with | .false, _, _ => rfl
  · rw [if_neg h1]; symm; exact not_not.mp h1

/-- `eval` is surjective — every three-valued proposition has a total representative,
    `ofProp3` being a section. -/
theorem eval_surjective : Function.Surjective (eval : PartialProp W → Prop3 W) :=
  λ p => ⟨ofProp3 p, eval_ofProp3 p⟩

/-- `eval` identifies exactly agreement on definedness and, where defined, on assertion:
    `PartialProp` is the *total-representative* presentation of `Prop3 W`, carrying
    (linguistically inert) assertion values outside the presupposition that `eval`
    forgets — so `ofProp3 ∘ eval` is not the identity, only `eval ∘ ofProp3` is
    (`eval_ofProp3`). -/
theorem eval_eq_eval_iff (p q : PartialProp W) :
    p.eval = q.eval ↔
      ∀ w, (p.presup w ↔ q.presup w) ∧ (p.presup w → (p.assertion w ↔ q.assertion w)) := by
  constructor
  · intro h w
    have hw : p.eval w = q.eval w := congrFun h w
    have hpq : p.presup w ↔ q.presup w := by
      rw [← eval_isDefined p w, ← eval_isDefined q w, hw]
    refine ⟨hpq, λ hp => ⟨λ ha => ?_, λ ha => ?_⟩⟩
    · exact ((eval_eq_true_iff q w).mp
        (hw.symm.trans ((eval_eq_true_iff p w).mpr ⟨hp, ha⟩))).2
    · exact ((eval_eq_true_iff p w).mp
        (hw.trans ((eval_eq_true_iff q w).mpr ⟨hpq.mp hp, ha⟩))).2
  · intro h
    funext w
    obtain ⟨hpq, himp⟩ := h w
    by_cases hp : p.presup w
    · by_cases ha : p.assertion w
      · simp [eval, hp, ha, hpq.mp hp, (himp hp).mp ha]
      · have hqa : ¬q.assertion w := λ hqa => ha ((himp hp).mpr hqa)
        simp [eval, hp, ha, hpq.mp hp, hqa]
    · have hq : ¬q.presup w := λ hq => hp (hpq.mpr hq)
      simp [eval, hp, hq]

/-! ### Genuineness theorems -/

/-- Liveness is symmetric. -/
theorem liveness_comm (p q : PartialProp W) (s : Finset W) :
    liveness p q s ↔ liveness q p s := by
  simp only [liveness, and_comm]

/-- Genuineness is symmetric whenever the supplied disjunction connective is
    symmetric in its operands. -/
theorem genuineness_comm (disj : PartialProp W → PartialProp W → PartialProp W)
    (p q : PartialProp W) (s : Finset W) (hcomm : disj p q = disj q p) :
    genuineness disj p q s ↔ genuineness disj q p s := by
  unfold genuineness
  rw [hcomm, and_comm]

/-! ### Embedding combinators ([heim-1992], [karttunen-1973], [delpinal-bassi-sauerland-2024]) -/

/-- Asymmetric filtering disjunction: plain proposition ∨ PartialProp.

    For "A ∨ B_ψ" where only B carries a presupposition ψ, the overall
    presupposition is ¬A → ψ (Karttunen's generalization for disjunction).
    The assertion is A ∨ B.

    This is the standard projection rule for presuppositions in the second
    disjunct of a disjunction. [karttunen-1973], [heim-1983] -/
def disjFilterLeft (firstDisjunct : W → Prop) (second : PartialProp W) :
    PartialProp W where
  assertion := fun w => firstDisjunct w ∨ second.assertion w
  presup := fun w => ¬firstDisjunct w → second.presup w

/-- `orFilter` with a presuppositionless first disjunct is `disjFilterLeft`. -/
theorem orFilter_ofProp (A : W → Prop) (q : PartialProp W) :
    orFilter (ofProp A) q = disjFilterLeft A q :=
  PartialProp.ext (funext fun _ => propext (and_iff_right trivial)) rfl

/-- Embedding under a negative factive (e.g., "is unaware that").

    "x is unaware that p" presupposes p and asserts ¬Bel_x(p).

    The choice of `complement.holds` (presupposition AND assertion) for the
    factive's presupposition is the [delpinal-bassi-sauerland-2024]
    treatment, where projection-through-factive requires both the trigger's
    presupposition and the at-issue complement to be carried. The
    [heim-1992] standard for atomic complements is `complement.assertion`
    alone; the two coincide when `complement` itself carries no presupposition
    but diverge when the complement contains its own embedded presupposition
    trigger (the case Del Pinal-Bassi-Sauerland use to handle presupposed
    free choice). -/
def negFactive (complement : PartialProp W)
    (believes : (W → Prop) → (W → Prop)) : PartialProp W where
  assertion := fun w => ¬(believes complement.assertion w)
  presup := fun w => complement.holds w

/-- When the first disjunct is false, `disjFilterLeft` recovers full
    satisfaction of the second disjunct. -/
theorem disjFilterLeft_recovers (firstDisjunct : W → Prop) (sp : PartialProp W)
    (w : W) (hFirst : ¬firstDisjunct w)
    (hFiltered : (disjFilterLeft firstDisjunct sp).holds w) :
    sp.holds w := by
  obtain ⟨hPresup, hAssert⟩ := hFiltered
  exact ⟨hPresup hFirst, hAssert.resolve_left hFirst⟩

/-- When `¬A` entails `q`'s presupposition pointwise, `disjFilterLeft A q`
    is presuppositionless (the filtering condition is satisfied at every
    world). The substrate-side fact behind [karttunen-1973]'s
    asymmetric disjunction filtering rule (24b), p. 181: "A or B" carries
    no residual presupposition from B when ¬A entails it. -/
theorem disjFilterLeft_eliminates_presup_when_neg_entails
    (A : W → Prop) (q : PartialProp W)
    (h : ∀ w, ¬A w → q.presup w) :
    (disjFilterLeft A q).presup = fun _ => True := by
  funext w
  simp only [disjFilterLeft, eq_iff_iff, iff_true]
  exact h w

/-- Presupposition of `negFactive` is full satisfaction of the complement. -/
theorem negFactive_presup_eq (complement : PartialProp W)
    (believes : (W → Prop) → (W → Prop)) :
    (negFactive complement believes).presup = complement.holds := rfl

/-- Universal presupposition projection: presuppositions project
    universally from the scope of a universal quantifier.

    For ∀x ∈ S, φ(x) where φ(x) is a PartialProp:
    - asserts: ∀x ∈ S, assertion(φ(x))
    - presupposes: ∀x ∈ S, presup(φ(x))

    [chemla-2009-quantified], [fox-2013]: presuppositions triggered in
    the scope of a universal quantifier tend to project universally.
    ([mayr-sauerland-2015] dissent: semantic projection is existential,
    pragmatically strengthened — cf. [spector-sudo-2017].) -/
def forallPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∀ x, S x → (φ x).assertion w

/-- Existential presupposition projection — universal presup, existential
    assert.

    For ∃x ∈ S, φ(x): presuppositions project *universally*, but the
    assertion is existential. This is the projection choice supported
    experimentally by [chemla-2009-quantified]; whether it is the right
    default is empirically contested — see [spector-sudo-2017] for
    conditions under which a non-universal (existential) reading is
    preferred. Consumers committing to a projection theory should pick
    `existsPartialUniv` or `existsPartialExist` explicitly. -/
def existsPartialUniv {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- Existential presupposition projection — existential presup, existential
    assert. The non-universal alternative to `existsPartialUniv`; see
    [spector-sudo-2017] for the empirical debate. -/
def existsPartialExist {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∃ x, S x ∧ (φ x).presup w
  assertion := fun w => ∃ x, S x ∧ (φ x).assertion w

/-- Negated existential with universal presupposition projection.

    For ¬∃x ∈ S, φ(x): equivalent to ∀x ∈ S, ¬φ(x).
    Presuppositions project universally. -/
def negExistsPartial {α : Type*} (S : α → Prop) (φ : α → PartialProp W) : PartialProp W where
  presup := fun w => ∀ x, S x → (φ x).presup w
  assertion := fun w => ¬∃ x, S x ∧ (φ x).assertion w

/-- `forallPartial` holds iff every member satisfies both presupposition and assertion. -/
theorem forallPartial_holds {α : Type*} (S : α → Prop) (φ : α → PartialProp W) (w : W) :
    (forallPartial S φ).holds w ↔
      (∀ x, S x → (φ x).presup w) ∧ (∀ x, S x → (φ x).assertion w) :=
  Iff.rfl

/-! ### Definite-description combinator -/

/-- The canonical definite-description combinator. Given:

- `referent : W → Option E` — a partial selector returning the referent at
  each world (or `none` when no unique referent is determined),
- `scope : E → W → Prop` — what is asserted of the chosen referent,

build the `PartialProp` that presupposes referent definedness and asserts the
scope of the referent. This is the single source of truth for all definite
denotations in the library: uniqueness-based (`russellIotaList domain R`),
familiarity-based (`russellIotaList dc.salient R`), anaphoric
(`russellIotaList domain (R ∧ Q)`), and Donnellan's attributive
(`attributiveContent domain R`) all instantiate the selector slot. -/
def presupOfReferent {E : Type*} (referent : W → Option E)
    (scope : E → W → Prop) : PartialProp W where
  presup := fun w => (referent w).isSome
  assertion := fun w => match referent w with
    | some e => scope e w
    | none => False

/-- `presupOfReferent` is defined iff a referent is selected at `w`. -/
@[simp] theorem presupOfReferent_presup {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W) :
    (presupOfReferent referent scope).presup w = (referent w).isSome := rfl

/-- When a referent is selected, the assertion is the scope applied to it. -/
theorem presupOfReferent_assertion_some {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W) (e : E)
    (h : referent w = some e) :
    (presupOfReferent referent scope).assertion w = scope e w := by
  simp only [presupOfReferent, h]

/-- Without a referent, the assertion is `False`. -/
theorem presupOfReferent_assertion_none {E : Type*}
    (referent : W → Option E) (scope : E → W → Prop) (w : W)
    (h : referent w = none) :
    (presupOfReferent referent scope).assertion w = False := by
  simp only [presupOfReferent, h]

end PartialProp

end Semantics.Presupposition
