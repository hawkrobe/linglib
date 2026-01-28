/-
# Three-Valued Logic and Presupposition Projection

Theory-neutral infrastructure for presuppositions in formal semantics.

## Key Concepts

1. **Three-Valued Truth (Strong Kleene via WithBot Bool)**
   - `some true`: true
   - `some false`: false
   - `none` (= ⊥): undefined (presupposition failure)

2. **Presuppositional Propositions (PrProp)**
   - Combines presupposition (definedness condition) with assertion (at-issue content)
   - Evaluates to three-valued truth

3. **Projection Algorithm (Kracht 2003, Table 14)**
   - Classical connectives: both presuppositions must hold
   - Filtering connectives: antecedent can satisfy consequent's presupposition

## The Key Insight

Natural language connectives "filter" presuppositions:

  "If the king exists, the king is bald"
  -> Does NOT presuppose king exists!

  P(phi ->' chi) = P(phi) /\ (A(phi) -> P(chi))
                  ^^^^^^^^^^^^^^^^^^^^^^^^
                  Antecedent entails presup -> presup satisfied!

## Mathlib Integration

We use `WithBot Bool` from Mathlib which provides:
- BoundedOrder instance (⊥ = none, ⊤ = some true)
- Lattice operations via Option's instances
- This lets us leverage Mathlib's order-theoretic infrastructure

## References

- Kracht (2003). Mathematics of Language, Section 4.7, Table 14
- Heim (1983). On the projection problem for presuppositions
- Karttunen (1974). Presupposition and linguistic context
- Beaver & Geurts (2014). Presupposition (SEP entry)
-/

import Mathlib.Order.WithBot
import Linglib.Core.Proposition

namespace Core.Presupposition

open Core.Proposition

-- ============================================================================
-- PART 1: Three-Valued Truth via WithBot Bool
-- ============================================================================

/--
Three-valued truth values using Mathlib's `WithBot Bool`.

- `some true`: true (presupposition satisfied, assertion true)
- `some false`: false (presupposition satisfied, assertion false)
- `none` (= ⊥): undefined (presupposition failure)

This gives us BoundedOrder, Lattice instances from Mathlib for free.
-/
abbrev TVal := WithBot Bool

namespace TVal

/-- The true value -/
abbrev tt : TVal := some true

/-- The false value -/
abbrev ff : TVal := some false

/-- The undefined value (presupposition failure) -/
abbrev unk : TVal := none

/-- Convert Bool to TVal -/
def ofBool (b : Bool) : TVal := some b

/-- Check if defined (not ⊥) -/
def isDefined (v : TVal) : Bool := v.isSome

/-- Convert to Bool if defined, else default to false -/
def toBoolOrFalse : TVal -> Bool
  | some b => b
  | none => false

-- ============================================================================
-- Strong Kleene Operations
-- ============================================================================

/--
Strong Kleene negation: ⊥ stays ⊥, otherwise negate.
-/
def neg : TVal -> TVal
  | some b => some (!b)
  | none => none

/--
Strong Kleene conjunction: ff dominates, ⊥ propagates.

Truth table:
    | tt  ff  ⊥
----+------------
 tt | tt  ff  ⊥
 ff | ff  ff  ff
 ⊥  | ⊥   ff  ⊥

Note: This is NOT lattice inf! Strong Kleene has ff as absorbing.
-/
def and : TVal -> TVal -> TVal
  | some false, _ => ff
  | _, some false => ff
  | some true, some true => tt
  | _, _ => unk

/--
Strong Kleene disjunction: tt dominates, ⊥ propagates.

Truth table:
    | tt  ff  ⊥
----+------------
 tt | tt  tt  tt
 ff | tt  ff  ⊥
 ⊥  | tt  ⊥   ⊥

Note: This is NOT lattice sup! Strong Kleene has tt as absorbing.
-/
def or : TVal -> TVal -> TVal
  | some true, _ => tt
  | _, some true => tt
  | some false, some false => ff
  | _, _ => unk

-- ============================================================================
-- Properties of Strong Kleene Operations
-- ============================================================================

/-- Negation is involutive -/
theorem neg_neg (v : TVal) : neg (neg v) = v := by
  cases v with
  | none => rfl
  | some b => simp [neg, Bool.not_not]

/-- Negation preserves ⊥ -/
theorem neg_unk : neg unk = unk := rfl

/-- Conjunction is commutative -/
theorem and_comm (a b : TVal) : and a b = and b a := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rfl

/-- Disjunction is commutative -/
theorem or_comm (a b : TVal) : or a b = or b a := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rfl

/-- ff is absorbing for conjunction -/
theorem and_ff_left (a : TVal) : and ff a = ff := rfl
theorem and_ff_right (a : TVal) : and a ff = ff := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- tt is absorbing for disjunction -/
theorem or_tt_left (a : TVal) : or tt a = tt := rfl
theorem or_tt_right (a : TVal) : or a tt = tt := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- tt is identity for conjunction -/
theorem and_tt_left (a : TVal) : and tt a = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl
theorem and_tt_right (a : TVal) : and a tt = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- ff is identity for disjunction -/
theorem or_ff_left (a : TVal) : or ff a = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl
theorem or_ff_right (a : TVal) : or a ff = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- ⊥ propagates in conjunction (when not dominated by ff) -/
theorem and_unk_left (a : TVal) (h : a ≠ ff) : and unk a = unk := by
  cases a with
  | none => rfl
  | some b => cases b with
    | true => rfl
    | false => simp [ff] at h

/-- ⊥ propagates in disjunction (when not dominated by tt) -/
theorem or_unk_left (a : TVal) (h : a ≠ tt) : or unk a = unk := by
  cases a with
  | none => rfl
  | some b => cases b with
    | false => rfl
    | true => simp [tt] at h

/-- Conjunction agrees with Bool when both defined -/
theorem and_ofBool (a b : Bool) :
    and (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Disjunction agrees with Bool when both defined -/
theorem or_ofBool (a b : Bool) :
    or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- Negation agrees with Bool -/
theorem neg_ofBool (a : Bool) : neg (ofBool a) = ofBool (!a) := rfl

/-- Conjunction is associative -/
theorem and_assoc (a b c : TVal) : and (and a b) c = and a (and b c) := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;> rfl

/-- Disjunction is associative -/
theorem or_assoc (a b c : TVal) : or (or a b) c = or a (or b c) := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;> rfl

end TVal

-- ============================================================================
-- PART 2: Three-Valued Propositions
-- ============================================================================

/-- Three-valued propositions: functions from worlds to TVal -/
abbrev Prop3 (W : Type*) := W -> TVal

namespace Prop3

variable {W : Type*}

/-- Pointwise negation -/
def neg (p : Prop3 W) : Prop3 W := fun w => TVal.neg (p w)

/-- Pointwise Strong Kleene conjunction -/
def and (p q : Prop3 W) : Prop3 W := fun w => TVal.and (p w) (q w)

/-- Pointwise Strong Kleene disjunction -/
def or (p q : Prop3 W) : Prop3 W := fun w => TVal.or (p w) (q w)

/-- Always true -/
def top : Prop3 W := fun _ => TVal.tt

/-- Always false -/
def bot : Prop3 W := fun _ => TVal.ff

/-- Always undefined -/
def unk : Prop3 W := fun _ => TVal.unk

/-- Convert BProp to Prop3 (always defined) -/
def ofBProp (p : BProp W) : Prop3 W := fun w => TVal.ofBool (p w)

end Prop3

-- ============================================================================
-- PART 3: Presuppositional Propositions
-- ============================================================================

/--
A presuppositional proposition: assertion + presupposition.

The presupposition is the definedness condition that must hold for the
assertion to have a truth value. When the presupposition fails, the
proposition is undefined.

Example: "The king is bald"
- presup: there exists a unique king
- assertion: that king is bald
-/
structure PrProp (W : Type*) where
  /-- The presupposition (must hold for definedness) -/
  presup : W -> Bool
  /-- The at-issue content (assertion) -/
  assertion : W -> Bool

namespace PrProp

variable {W : Type*}

-- ============================================================================
-- Evaluation to Three-Valued
-- ============================================================================

/--
Evaluate a presuppositional proposition to three-valued truth.

If presupposition fails -> ⊥ (unk)
If presupposition holds -> assertion's truth value
-/
def eval (p : PrProp W) : Prop3 W := fun w =>
  if p.presup w then TVal.ofBool (p.assertion w) else TVal.unk

/-- A PrProp is defined at w iff its presupposition holds at w -/
def isDefinedAt (p : PrProp W) (w : W) : Prop := p.presup w = true

/-- The set of worlds where p is defined -/
def definedWorlds (p : PrProp W) : W -> Prop := fun w => p.presup w = true

/-- Evaluation is defined iff presupposition holds -/
theorem eval_isDefined (p : PrProp W) (w : W) :
    (p.eval w).isDefined = p.presup w := by
  simp only [eval, TVal.isDefined]
  cases hp : p.presup w <;> simp [TVal.ofBool, Option.isSome]

-- ============================================================================
-- PART 4: Classical Connectives (Both presuppositions required)
-- ============================================================================

/--
Classical negation of a presuppositional proposition.

The presupposition is preserved, only the assertion is negated.

P(not p) = P(p)
A(not p) = not A(p)
-/
def neg (p : PrProp W) : PrProp W :=
  { presup := p.presup
  , assertion := fun w => !p.assertion w }

/--
Classical conjunction: both presuppositions must hold.

P(p and q) = P(p) and P(q)
A(p and q) = A(p) and A(q)
-/
def and (p q : PrProp W) : PrProp W :=
  { presup := fun w => p.presup w && q.presup w
  , assertion := fun w => p.assertion w && q.assertion w }

/--
Classical disjunction: both presuppositions must hold.

P(p or q) = P(p) and P(q)
A(p or q) = A(p) or A(q)
-/
def or (p q : PrProp W) : PrProp W :=
  { presup := fun w => p.presup w && q.presup w
  , assertion := fun w => p.assertion w || q.assertion w }

/--
Classical implication: both presuppositions must hold.

P(p -> q) = P(p) and P(q)
A(p -> q) = A(p) -> A(q)
-/
def imp (p q : PrProp W) : PrProp W :=
  { presup := fun w => p.presup w && q.presup w
  , assertion := fun w => !p.assertion w || q.assertion w }

-- ============================================================================
-- PART 5: Filtering Connectives (Kracht 2003 Table 14)
-- ============================================================================

/--
**Filtering conjunction**: antecedent can satisfy consequent's presupposition.

This is the key insight from Heim (1983) and Karttunen (1974):
"If P holds, and Q" can have Q's presupposition satisfied by P.

P(p and' q) = P(p) and (A(p) -> P(q))
A(p and' q) = A(p) and A(q)

Example: "John knows it's raining and he's upset about it"
- "He's upset about it" presupposes "it's raining"
- "John knows it's raining" asserts "it's raining"
- Therefore the whole conjunction has no net presupposition about rain!
-/
def andFilter (p q : PrProp W) : PrProp W :=
  { presup := fun w => p.presup w && (!p.assertion w || q.presup w)
  , assertion := fun w => p.assertion w && q.assertion w }

/--
**Filtering implication**: antecedent can satisfy consequent's presupposition.

This is the canonical example from presupposition theory:
"If the king exists, the king is bald" has NO presupposition!

P(p ->' q) = P(p) and (A(p) -> P(q))
A(p ->' q) = A(p) -> A(q)

When A(p) entails P(q), the presupposition P(q) is "filtered out" or
"locally satisfied" by the antecedent.
-/
def impFilter (p q : PrProp W) : PrProp W :=
  { presup := fun w => p.presup w && (!p.assertion w || q.presup w)
  , assertion := fun w => !p.assertion w || q.assertion w }

/--
**Filtering disjunction**: disjuncts can satisfy each other's presuppositions.

P(p or' q) = (A(p) -> P(q)) and (A(q) -> P(p)) and (P(p) or P(q))
A(p or' q) = A(p) or A(q)

This is the symmetric case: either disjunct can satisfy the other's presupposition.
-/
def orFilter (p q : PrProp W) : PrProp W :=
  { presup := fun w =>
      (!p.assertion w || q.presup w) &&
      (!q.assertion w || p.presup w) &&
      (p.presup w || q.presup w)
  , assertion := fun w => p.assertion w || q.assertion w }

-- Notation for filtering connectives
scoped infixl:65 " /\\' " => andFilter
scoped infixr:55 " ->' " => impFilter
scoped infixl:60 " \\/' " => orFilter

-- ============================================================================
-- PART 6: Key Theorems About Filtering
-- ============================================================================

/--
**Negation preserves presupposition**.

The presupposition of "not P" is the same as the presupposition of "P".
-/
theorem neg_presup (p : PrProp W) : (neg p).presup = p.presup := rfl

/--
**Double negation preserves assertion**.

The assertion of "not not P" is equivalent to the assertion of "P".
-/
theorem neg_neg_assertion (p : PrProp W) (w : W) :
    (neg (neg p)).assertion w = p.assertion w := by
  simp [neg, Bool.not_not]

/--
**Filtering implication eliminates presupposition when antecedent entails it**.

This is the key theorem: when A(phi) -> P(chi) holds at all worlds,
the resulting presupposition is just P(phi).

Given: for all w, p.assertion w = true -> q.presup w = true
Then: (p ->' q).presup = p.presup
-/
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

/--
**When antecedent's assertion equals consequent's presupposition,
filtering implication has trivial presupposition**.

Special case: if A(phi) = P(chi) exactly, then P(phi ->' chi) = P(phi).
-/
theorem impFilter_trivializes_presup (p q : PrProp W)
    (h : p.assertion = q.presup) :
    (impFilter p q).presup = p.presup := by
  funext w
  simp only [impFilter, h]
  cases hp : p.presup w
  · simp
  · simp only [Bool.true_and]
    cases hq : q.presup w <;> simp

-- ============================================================================
-- PART 7: Constructors for Common Patterns
-- ============================================================================

/--
Create a presuppositionless proposition from a BProp.
The presupposition is trivially true everywhere.
-/
def ofBProp (p : BProp W) : PrProp W :=
  { presup := fun _ => true
  , assertion := p }

/--
Create a tautological presupposition (always defined, always true).
-/
def top : PrProp W :=
  { presup := fun _ => true
  , assertion := fun _ => true }

/--
Create a contradictory presupposition (always defined, always false).
-/
def bot : PrProp W :=
  { presup := fun _ => true
  , assertion := fun _ => false }

/--
Create a presupposition failure (never defined).
-/
def undefined : PrProp W :=
  { presup := fun _ => false
  , assertion := fun _ => false }

/-- ofBProp creates presuppositionless propositions -/
theorem ofBProp_no_presup (p : BProp W) (w : W) : (ofBProp p).presup w = true := rfl

/-- ofBProp preserves assertion -/
theorem ofBProp_assertion (p : BProp W) (w : W) : (ofBProp p).assertion w = p w := rfl

-- ============================================================================
-- PART 8: Evaluation Theorems
-- ============================================================================

/-- Negation evaluation -/
theorem eval_neg (p : PrProp W) (w : W) :
    (neg p).eval w = TVal.neg (p.eval w) := by
  simp only [eval, neg]
  split
  · simp [TVal.neg_ofBool]
  · rfl

/-- Classical conjunction evaluation (both defined) -/
theorem eval_and (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (hq : q.presup w = true) :
    (and p q).eval w = TVal.and (p.eval w) (q.eval w) := by
  simp only [eval, and, hp, hq, Bool.true_and, ite_true, TVal.and_ofBool]

/-- Filtering implication when antecedent false: result is true -/
theorem eval_impFilter_antecedent_false (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = false) :
    (impFilter p q).eval w = TVal.tt := by
  simp only [eval, impFilter, hp, ha, Bool.true_and, Bool.not_false, Bool.true_or,
             TVal.ofBool, TVal.tt, ite_true]

/-- Filtering implication when antecedent true: depends on consequent -/
theorem eval_impFilter_antecedent_true (p q : PrProp W) (w : W)
    (hp : p.presup w = true) (ha : p.assertion w = true) (hq : q.presup w = true) :
    (impFilter p q).eval w = TVal.ofBool (q.assertion w) := by
  simp only [eval, impFilter, hp, ha, hq, Bool.true_and, Bool.not_true, Bool.false_or,
             TVal.ofBool, ite_true]

-- ============================================================================
-- PART 9: Semantic Entailment for PrProp
-- ============================================================================

/--
Strong entailment: p entails q at all worlds where both are defined.
-/
def strongEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> q.presup w = true ->
    p.assertion w = true -> q.assertion w = true

/--
Strawson entailment: p entails q at worlds where p is defined and true.
(q's presupposition may be satisfied by p)
-/
def strawsonEntails (p q : PrProp W) : Prop :=
  forall w, p.presup w = true -> p.assertion w = true ->
    q.presup w = true /\ (q.presup w = true -> q.assertion w = true)

/--
Presupposition projection: get the presupposition as a classical proposition.
-/
def projectPresup (p : PrProp W) : BProp W := p.presup

/--
Assertion extraction: get the assertion as a classical proposition.
-/
def projectAssertion (p : PrProp W) : BProp W := p.assertion

end PrProp

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Three-Valued Truth (TVal = WithBot Bool)
- `TVal.tt` = `some true`: true
- `TVal.ff` = `some false`: false
- `TVal.unk` = `none`: undefined (presupposition failure)
- `TVal.neg`, `TVal.and`, `TVal.or` - Strong Kleene operations
- Proofs that these agree with Bool when defined
- Uses Mathlib's WithBot for BoundedOrder instance

### Three-Valued Propositions (Prop3)
- `Prop3 W` = `W -> TVal`
- Pointwise operations

### Presuppositional Propositions (PrProp)
- `PrProp W` = { presup : W -> Bool, assertion : W -> Bool }
- `PrProp.eval : PrProp W -> Prop3 W` - evaluation to three-valued

### Classical Connectives
- `PrProp.neg`, `PrProp.and`, `PrProp.or`, `PrProp.imp`
- Both presuppositions must hold

### Filtering Connectives (Kracht Table 14)
- `PrProp.andFilter` (/\') - conjunction with filtering
- `PrProp.impFilter` (->')  - implication with filtering
- `PrProp.orFilter`  (\/') - disjunction with filtering

### Key Theorems
- `neg_presup`: Negation preserves presupposition
- `impFilter_eliminates_presup`: Filtering eliminates satisfied presuppositions
- `impFilter_trivializes_presup`: Special case when A(p) = P(q)

### Connection to Other Modules
- `Core.Proposition`: Classical BProp used for presuppositions and assertions
- `Montague.Entailment.Polarity`: Polarity affects projection (see PresuppositionPolarity)
- `NeoGricean.Presuppositions`: Integration with implicature derivation
-/

end Core.Presupposition
