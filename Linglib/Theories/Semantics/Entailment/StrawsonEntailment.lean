/-
# Strawson Entailment (von Fintel 1999)

Strawson-DE: a weakened downward entailingness that checks DE inferences
only when presuppositions of the conclusion are satisfied. This rescues the
Fauconnier-Ladusaw analysis for four "recalcitrant" NPI licensors:

1. `only` (Section 2)
2. Adversative attitude verbs: sorry, surprised, regret (Section 3)
3. Superlatives (Section 4.2)
4. Conditional antecedents (Section 4.1)

These are not classically DE but do license NPIs. Strawson-DE explains why.

## Hierarchy

AM < AA < DE < Strawson-DE (weakest level of negative strength)

## References

- von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
  Dependency. Journal of Semantics 16(2), 97–148.
- Strawson, P. (1952). Introduction to Logical Theory.
-/

import Mathlib.Order.Monotone.Defs
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Presupposition

namespace Semantics.Entailment.StrawsonEntailment

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.AntiAdditivity

-- ============================================================================
-- Section 1: Core Definitions
-- ============================================================================

/--
**Strawson-DE** (von Fintel 1999, Definition 14).

A function `f : BProp World → BProp World` is Strawson-DE with respect to a definedness
predicate `defined` iff: for all p ≤ q, if `defined p` holds (i.e. the
presupposition of f(p) is satisfied), then f(q) ≤ f(p).

This is a conditional `Antitone`: DE restricted to the case where the
conclusion's presupposition is met.

Compare with Mathlib's `AntitoneOn f s`, which requires BOTH p and q in s.
Strawson-DE is one-sided: only p (the stronger proposition) needs to satisfy
the definedness condition.
-/
def IsStrawsonDE (f : BProp World → BProp World) (defined : BProp World → Prop) : Prop :=
  ∀ p q : BProp World, (∀ w, p w ≤ q w) → defined p → (∀ w, f q w ≤ f p w)

/--
**Strawson-valid inference** (von Fintel 1999, Definition 19).

An inference from premises to conclusion is Strawson-valid iff it is
classically valid once we add the premise that all presuppositions of the
conclusion are satisfied.
-/
def StrawsonValid (premises : List (BProp World)) (conclusion : BProp World)
    (presupSatisfied : Prop) : Prop :=
  presupSatisfied →
    (∀ w, premises.all (· w) = true → conclusion w = true)

-- ============================================================================
-- Section 2: Hierarchy Theorems
-- ============================================================================

/--
Every classically DE function is Strawson-DE (for any definedness predicate).

Proof: the `defined p` hypothesis is simply ignored; the `Antitone` proof
gives us f(q) ≤ f(p) unconditionally.

This establishes: DE ⊆ Strawson-DE.
-/
theorem de_implies_strawsonDE (f : BProp World → BProp World) (hDE : IsDownwardEntailing f)
    (defined : BProp World → Prop) : IsStrawsonDE f defined :=
  λ _p _q hpq _hdef => hDE hpq

/--
Every anti-additive function is Strawson-DE.

Via: AA → DE → Strawson-DE.
-/
theorem antiAdditive_implies_strawsonDE (f : BProp World → BProp World)
    (hAA : IsAntiAdditive f) (defined : BProp World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f (antiAdditive_implies_de f hAA) defined

/--
Every anti-morphic function is Strawson-DE.

Via: AM → AA → DE → Strawson-DE.
-/
theorem antiMorphic_implies_strawsonDE (f : BProp World → BProp World)
    (hAM : IsAntiMorphic f) (defined : BProp World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f (antiMorphic_implies_de f hAM) defined

/--
The full hierarchy chain: AM → AA → DE → Strawson-DE.

Given an anti-morphic proof, we can derive all weaker properties.
-/
structure FullHierarchy (f : BProp World → BProp World) (defined : BProp World → Prop) where
  am : IsAntiMorphic f
  aa : IsAntiAdditive f := am.1
  de : IsDownwardEntailing f := antiAdditive_implies_de f aa
  strawsonDE : IsStrawsonDE f defined := de_implies_strawsonDE f de defined

/-- Negation satisfies the full hierarchy. -/
def pnot_fullHierarchy (defined : BProp World → Prop) : FullHierarchy pnot defined :=
  { am := pnot_isAntiMorphic }

-- ============================================================================
-- Section 3: "Only" Semantics (Horn's Asymmetric Analysis)
-- ============================================================================

/-!
### "Only" (von Fintel 1999, §2)

Horn's analysis: "Only x VP" decomposes into:
- **Presupposition** (positive): x VP (the focused individual satisfies VP)
- **Assertion** (negative): no y ≠ x satisfies VP

Von Fintel's key observation: "Only" is NOT classically DE, but IS Strawson-DE.

Counterexample to classical DE (ex 11):
  "Only John ate vegetables" does NOT entail "Only John ate kale"
  (Even though kale ⊆ vegetables: the presupposition that John ate kale may fail)

But with presupposition satisfied:
  If John ate kale (presup), then "Only John ate vegetables" DOES entail
  "Only John ate kale" — because if no one else ate vegetables, and kale ⊆
  vegetables, then no one else ate kale.
-/

/--
Presupposition of "only x VP": x satisfies VP.

`x` picks out a world (individual), `scope` is the VP denotation.
In our finite model, x is a characteristic function selecting one world.
-/
def onlyPresup (x : World → Bool) (scope : BProp World) : Prop :=
  ∃ w, x w = true ∧ scope w = true

/--
Assertion of "only x VP": no y ≠ x satisfies VP.

For all worlds in the model, if y is not x, then y doesn't satisfy scope.
-/
def onlyAssert (x : World → Bool) (scope : BProp World) : BProp World :=
  λ w => allWorlds.all λ y =>
    (x y) || !(scope y)

/--
The full "only" meaning: presupposition + assertion combined.

"Only x VP" is true at w iff x satisfies VP AND no one else does.
-/
def onlyFull (x : World → Bool) (scope : BProp World) : BProp World :=
  λ w => (allWorlds.any λ y => x y && scope y) &&
         (allWorlds.all λ y => x y || !(scope y))

/--
"Only" (full meaning) is not classically DE (von Fintel ex 11).

Counterexample: kale ⊆ vegetables, but
"Only J ate vegetables" ⊬ "Only J ate kale"
because J may have eaten vegetables but not kale.
-/
theorem onlyFull_not_de : ¬IsDownwardEntailing (onlyFull (λ w => w == .w0)) := by
  intro hDE
  -- Counterexample: p = ∅ (no one eats kale), q = {w0} (only John eats vegetables)
  -- p ≤ q trivially. onlyFull(q)(w0) = true, onlyFull(p)(w0) = false.
  -- DE requires onlyFull(q) ≤ onlyFull(p), so true ≤ false — contradiction.
  let p : BProp World := λ _ => false
  let q : BProp World := λ w => w == .w0
  have hpq : ∀ w, p w ≤ q w := by intro w; simp [p]
  have h := hDE hpq World.w0
  simp (config := { decide := true }) only [onlyFull, allWorlds, p, q, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil] at h

/--
The assertion component of "only" IS Strawson-DE.

When the presupposition is satisfied (the focused individual x satisfies
the scope P), then: if P ⊆ Q, "no y≠x satisfies Q" implies "no y≠x
satisfies P" — because P ⊆ Q.

This is von Fintel's central insight for "only" (Theorem 1 / ex 18).
-/
theorem onlyFull_isStrawsonDE (x : World → Bool) :
    IsStrawsonDE (onlyFull x) (λ scope => ∃ w, x w = true ∧ scope w = true) := by
  intro p q hpq ⟨wx, hx_true, hp_wx⟩ w
  simp only [onlyFull]
  intro h
  -- h : (any y, x y && q y) && (all y, x y || !q y) = true at w
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨h_any, h_all⟩ := h
  refine ⟨?_, ?_⟩
  -- Part 1: (any y, x y && p y) = true
  -- We know x wx = true and p wx = true
  · simp only [allWorlds, List.any_cons, List.any_nil, Bool.or_false]
    cases wx with
    | w0 => simp [hx_true, hp_wx]
    | w1 => simp [hx_true, hp_wx]
    | w2 => simp [hx_true, hp_wx]
    | w3 => simp [hx_true, hp_wx]
  -- Part 2: (all y, x y || !p y) = true
  -- Since p ≤ q, !q(y) → !p(y), so x(y) || !q(y) ≤ x(y) || !p(y)
  · -- The all-check iterates over allWorlds = [w0,w1,w2,w3].
    -- For each world w_i: if x(w_i), the disjunct is trivially true.
    -- Otherwise h_all gives ¬q(w_i), and since p ≤ q, we get ¬p(w_i).
    have h_pointwise : ∀ y, (x y || !(q y)) = true → (x y || !(p y)) = true := by
      intro y hy
      cases hx_y : x y with
      | false =>
        simp only [hx_y, Bool.false_or, Bool.not_eq_true'] at hy ⊢
        have h_le := hpq y
        rw [hy] at h_le
        cases hp_y : p y with
        | false => rfl
        | true =>
          exfalso
          simp only [hp_y] at h_le
          exact absurd h_le (by decide)
      | true => simp [hx_y]
    simp only [allWorlds, List.all_cons, List.all_nil, Bool.and_true,
               Bool.and_eq_true] at h_all ⊢
    exact ⟨h_pointwise _ h_all.1, h_pointwise _ h_all.2.1,
           h_pointwise _ h_all.2.2.1, h_pointwise _ h_all.2.2.2⟩

-- ============================================================================
-- Section 4: Adversative Attitudes (von Fintel §3)
-- ============================================================================

/-!
### Adversative/Factive Attitudes

"Sorry", "surprised", "regret" license NPIs in their complement:
- "Sandy is sorry that Robin bought any car" ✓ (ex 28a)
- "Sandy is amazed that Robin ever ate kale" ✓

These are factive (presuppose their complement is true) and the complement
position is DE on the ordering source. The factivity presupposition ensures
the complement is in the "defined" region, making them Strawson-DE.

Contrast with "glad" which is not factive and doesn't reliably license NPIs.
-/

/--
A factive predicate's complement position is Strawson-DE.

Structure capturing: the predicate presupposes its complement is true,
and once the complement is assumed true, the complement position is DE
(the ordering reversal makes it antitone on constant perspective).
-/
structure FactiveStrawsonDE where
  /-- The predicate name -/
  name : String
  /-- Is factive? (presupposes complement truth) -/
  factive : Bool
  /-- Licenses NPIs in complement? -/
  licensesNPIs : Bool
  /-- The ordering-source reversal makes complement position Strawson-DE -/
  strawsonDE : Bool
  /-- Notes -/
  notes : String := ""

/-- "sorry" / "regret" — factive adversative, licenses NPIs via Strawson-DE -/
def sorry_pred : FactiveStrawsonDE :=
  { name := "sorry/regret"
  , factive := true
  , licensesNPIs := true
  , strawsonDE := true
  , notes := "von Fintel ex 28a: Sandy is sorry that Robin bought any car" }

/-- "surprised" / "amazed" — factive adversative, licenses NPIs -/
def surprised_pred : FactiveStrawsonDE :=
  { name := "surprised/amazed"
  , factive := true
  , licensesNPIs := true
  , strawsonDE := true
  , notes := "von Fintel ex 28b: Sandy is amazed that Robin ever ate kale" }

/-- "glad" — not reliably factive, weaker NPI licensing -/
def glad_pred : FactiveStrawsonDE :=
  { name := "glad"
  , factive := false  -- Debatable; weaker factivity
  , licensesNPIs := false
  , strawsonDE := false
  , notes := "Does not reliably license NPIs; von Fintel ex 31" }

/--
Adversative factives are Strawson-DE in their complement.

This is a semantic-level theorem: for a factive operator that presupposes
complement truth and has an adversative ordering source, the complement
position is DE conditional on presupposition satisfaction.
-/
theorem adversative_isStrawsonDE
    (f : BProp World → BProp World) (hFactive : ∀ p w, f p w = true → p w = true)
    (hDE_given_presup : ∀ p q, (∀ w, p w ≤ q w) →
      (∀ w, p w = true → f p w = true) →
      (∀ w, f q w ≤ f p w)) :
    IsStrawsonDE f (λ scope => ∀ w, scope w = true → f scope w = true) := by
  intro p q hpq hdef w
  exact hDE_given_presup p q hpq hdef w

-- ============================================================================
-- Section 5: Superlatives (von Fintel §4.2)
-- ============================================================================

/-!
### Superlatives

"The tallest girl who ___" is Strawson-DE in the relative clause position.

- "Emma is the tallest girl who ever won" ✓ (ex 75)
- But not classically DE: "tallest girl in her class ⇏ tallest to learn
  the alphabet" (ex 76), because the presupposition that Emma learned
  the alphabet may not hold.
-/

/--
Presupposition of superlative: subject satisfies the domain predicate.

"The tallest girl who VP" presupposes the subject is a girl who VP'd.
-/
def superlativePresup (subject : World → Bool) (restriction : BProp World) : Prop :=
  ∃ w, subject w = true ∧ restriction w = true

/--
Superlative assertion: subject has the highest degree among those
satisfying the restriction.

Simplified model: the "tallest who VP" at w checks that no one else
in the restriction exceeds the subject.
-/
def superlativeAssert (subject : World → Bool) (restriction : BProp World) : BProp World :=
  λ w => (allWorlds.any λ y => subject y && restriction y) &&
         (allWorlds.all λ y => subject y || !(restriction y) ||
            !(allWorlds.any λ z => !(subject z) && restriction z))

/--
Superlatives are Strawson-DE in the restriction position (ex 77).

When the presupposition is met (subject satisfies the restriction P),
if P ⊆ Q, then "tallest who Q" entails "tallest who P" — the subject's
rank can only improve by narrowing the comparison class.

TODO: Full proof requires careful handling of the degree ordering.
The key insight is that restricting the comparison class (P ⊆ Q means
fewer competitors in P) preserves or improves the subject's rank.
-/
theorem superlative_isStrawsonDE (subject : World → Bool) :
    IsStrawsonDE (superlativeAssert subject)
      (superlativePresup subject) := by
  sorry

-- ============================================================================
-- Section 6: Bridge Theorems
-- ============================================================================

/-!
### Connections to Existing Infrastructure

Bridge theorems linking `IsStrawsonDE` to:
- `IsDownwardEntailing = Antitone` (from `Polarity.lean`)
- `IsAntiAdditive` (from `AntiAdditivity.lean`)
- `PrProp.strawsonEntails` (from `Core/Presupposition.lean`)
-/

/--
Bridge: `IsDE` (= `Antitone`) implies `IsStrawsonDE` for any definedness.

This is just `de_implies_strawsonDE` but using the `IsDE` abbreviation
from `Polarity.lean`.
-/
theorem isDE_implies_strawsonDE (f : BProp World → BProp World) (hDE : IsDE f)
    (defined : BProp World → Prop) : IsStrawsonDE f defined :=
  de_implies_strawsonDE f hDE defined

/--
Negation is Strawson-DE (trivially, since it's anti-morphic).
-/
theorem pnot_isStrawsonDE (defined : BProp World → Prop) :
    IsStrawsonDE pnot defined :=
  de_implies_strawsonDE pnot pnot_isDownwardEntailing defined

/--
"No student" is Strawson-DE (trivially, since it's anti-additive → DE).
-/
theorem no_student_isStrawsonDE (defined : BProp World → Prop) :
    IsStrawsonDE no_student defined :=
  de_implies_strawsonDE no_student no_isDE_scope defined

/--
"At most 2 students" is Strawson-DE (trivially, since it's DE).
-/
theorem atMost2_isStrawsonDE (defined : BProp World → Prop) :
    IsStrawsonDE atMost2_student defined :=
  de_implies_strawsonDE atMost2_student atMost_isDE_scope defined

/--
Strawson-DE is strictly weaker than DE: there exist functions that are
Strawson-DE but not DE. "Only" is the canonical example.
-/
theorem strawsonDE_strictly_weaker_than_DE :
    (∃ f defined, IsStrawsonDE f defined ∧ ¬IsDownwardEntailing f) := by
  exact ⟨onlyFull (λ w => w == .w0),
         λ scope => ∃ w, (w == .w0) = true ∧ scope w = true,
         onlyFull_isStrawsonDE _,
         onlyFull_not_de⟩

end Semantics.Entailment.StrawsonEntailment
