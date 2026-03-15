/-
# Strawson Entailment

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

-/

import Mathlib.Order.Monotone.Defs
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Semantics.Presupposition

namespace Semantics.Entailment.StrawsonEntailment

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.AntiAdditivity

-- ============================================================================
-- Section 1: Core Definitions
-- ============================================================================

/--
**Strawson-DE** (@cite{von-fintel-1999}, Definition 14).

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
**Strawson-valid inference** (@cite{von-fintel-1999}, Definition 19).

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
### "Only"
@cite{von-fintel-1999} @cite{strawson-1952}

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
"Only x VP" as a `PrProp`: Horn's asymmetric decomposition.

- **Presupposition**: the focused individual x satisfies VP
- **Assertion**: no y ≠ x satisfies VP

Uses `Core.Presupposition.PrProp` directly, making the presupposition/assertion
split structural rather than ad-hoc.
-/
def onlyPrProp (x : World → Bool) (scope : BProp World) : Core.Presupposition.PrProp World where
  presup := λ _ => allWorlds.any λ y => x y && scope y
  assertion := λ _ => allWorlds.all λ y => x y || !(scope y)

/--
The full "only" meaning: presupposition + assertion combined.

"Only x VP" is true at w iff x satisfies VP AND no one else does.
Equivalent to `(onlyPrProp x scope).presup w && (onlyPrProp x scope).assertion w`.
-/
def onlyFull (x : World → Bool) (scope : BProp World) : BProp World :=
  λ w => (allWorlds.any λ y => x y && scope y) &&
         (allWorlds.all λ y => x y || !(scope y))

/-- `onlyFull` equals the conjunction of `onlyPrProp`'s components. -/
theorem onlyFull_eq_prprop (x : World → Bool) (scope : BProp World) (w : World) :
    onlyFull x scope w = ((onlyPrProp x scope).presup w && (onlyPrProp x scope).assertion w) :=
  rfl

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
@cite{von-fintel-1999} @cite{kratzer-1981}

"Sorry", "surprised", "regret" license NPIs in their complement.
Von Fintel's analysis (§3.2): these attitudes quantify over "best worlds"
(worlds optimal according to the agent's preferences). The complement
position's monotonicity is *derived* from the preference structure.

Key insight: `sorry that p` ≈ `want that ¬p` — adversative attitudes
negate the complement relative to the preference ordering. This makes the
complement position Strawson-DE (DE conditional on factivity presupposition).

Contrast: `glad that p` ≈ `want that p` — the complement position is UE,
so `glad` does NOT license NPIs.

The `bestOf` parameter corresponds to `bestWorlds f g` from
`Modality/Kratzer.lean` (Kratzer's modal base + ordering source).
The two modules use different `World` types, so the connection is
structural rather than via direct import.
-/

/--
`sorry` denotation: adversative factive attitude.

"α is sorry that p" = in α's preferred worlds, p is NOT true.
`bestOf w` returns the "best" accessible worlds from w — intended to be
instantiated with `Kratzer.bestWorlds f g` from `Modality/Kratzer.lean`.
-/
def sorryDen (bestOf : World → List World) (p : BProp World) : BProp World :=
  λ w => (bestOf w).all λ w' => !p w'

/--
`glad` denotation: non-adversative factive attitude.

"α is glad that p" = in α's preferred worlds, p IS true.
Same structure as `sorryDen` but without negation.
-/
def gladDen (bestOf : World → List World) (p : BProp World) : BProp World :=
  λ w => (bestOf w).all λ w' => p w'

/--
`sorry` is Strawson-DE in its complement.

The definedness condition is factivity: the complement p holds at all
preferred worlds. Given factivity and p ⊆ q, contraposition (¬q ⊆ ¬p)
gives the Strawson-DE inference.
-/
theorem sorryDen_isStrawsonDE (bestOf : World → List World) :
    IsStrawsonDE (sorryDen bestOf)
      (λ p => ∀ w w', w' ∈ bestOf w → p w' = true) := by
  intro p q hpq hdef w
  simp only [sorryDen]
  intro hAll
  apply List.all_eq_true.mpr
  intro w' hw'
  have hpw' : p w' = true := hdef w w' hw'
  have hqw' : q w' = true := le_antisymm le_top (hpw' ▸ hpq w')
  simp only [Bool.not_eq_true'] at hAll ⊢
  exact absurd hqw' (by
    have := List.all_eq_true.mp hAll w' hw'
    simp only [Bool.not_eq_true'] at this; rw [this]; decide)

/--
`glad` is NOT Strawson-DE — it is upward entailing (UE).

If p ⊆ q, and all preferred worlds satisfy p, then they satisfy q.
This means `glad` preserves entailment direction — it does NOT license NPIs.
-/
theorem gladDen_isUE (bestOf : World → List World) :
    ∀ p q : BProp World, (∀ w, p w ≤ q w) →
      ∀ w, gladDen bestOf p w ≤ gladDen bestOf q w := by
  intro p q hpq w
  simp only [gladDen]
  intro hAll
  apply List.all_eq_true.mpr
  intro w' hw'
  have hpw' := List.all_eq_true.mp hAll w' hw'
  exact le_antisymm le_top (hpw' ▸ hpq w')

/--
Abstract adversative Strawson-DE: any factive operator whose complement
position is DE given presupposition satisfaction is Strawson-DE.
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

Proof strategy: Part 1 (existential) follows from the presupposition.
Part 2 (universal) case-splits on whether any non-subject satisfies P:
if not, the disjunct `¬C(P)` is trivially true; if so, monotonicity
gives `C(Q)`, and the pointwise fact for Q transfers to P via `p ≤ q`.
-/
theorem superlative_isStrawsonDE (subject : World → Bool) :
    IsStrawsonDE (superlativeAssert subject)
      (superlativePresup subject) := by
  intro p q hpq ⟨wx, hsubj_wx, hp_wx⟩ w
  simp only [superlativeAssert]
  intro h
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨h_any_q, h_all_q⟩ := h
  refine ⟨?_, ?_⟩
  -- Part 1: ∃ y ∈ allWorlds, subject y ∧ p y — from presupposition
  · have hmem : wx ∈ allWorlds := by cases wx <;> simp [allWorlds]
    exact List.any_eq_true.mpr ⟨wx, hmem, by simp [hsubj_wx, hp_wx]⟩
  -- Part 2: ∀ y, subject y ∨ ¬(p y) ∨ ¬C(p)
  · apply List.all_eq_true.mpr
    intro y hy
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hCp : (allWorlds.any fun z => !(subject z) && p z) = true
    · -- C(p) holds: some non-subject satisfies p. By p ≤ q, C(q) holds too.
      have hCq : (allWorlds.any fun z => !(subject z) && q z) = true := by
        obtain ⟨z, hz_mem, hz_val⟩ := List.any_eq_true.mp hCp
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hz_val
        exact List.any_eq_true.mpr ⟨z, hz_mem, by
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          exact ⟨hz_val.1, le_antisymm le_top (hz_val.2 ▸ hpq z)⟩⟩
      -- With C(q) true, h_all_q gives: subject y ∨ ¬(q y) for each y
      have h_y_q := List.all_eq_true.mp h_all_q y hy
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at h_y_q
      left
      rcases h_y_q with h_inner | h_false
      · rcases h_inner with h | h
        · left; exact h
        · -- q y = false, and p ≤ q, so p y = false
          right
          by_cases hp : p y = true
          · exact absurd (le_antisymm le_top (hp ▸ hpq y)) (by rw [h]; decide)
          · exact Bool.eq_false_iff.mpr hp
      · exact absurd hCq (by rw [h_false]; decide)
    · -- C(p) is false: no non-subject satisfies p — third disjunct holds
      right; exact Bool.eq_false_iff.mpr hCp

-- ============================================================================
-- Section 5b: Conditional Antecedents (von Fintel §4.1)
-- ============================================================================

/-!
### Conditional Antecedents
@cite{von-fintel-1999} @cite{kratzer-1986}

If-clauses license NPIs: "If you've *ever* been to Paris, you know the Louvre."
Under the restrictor analysis (@cite{kratzer-1986}), "if α, must β" =
necessity over the α-restricted modal base. The antecedent position is
classically DE: strengthening the antecedent can only shrink the domain,
making the universal check easier to satisfy.

`condNecessity` corresponds to `conditionalNecessity f emptyBackground α β`
from `Conditionals/Restrictor.lean` (with empty ordering source, where
best worlds = accessible worlds). The two modules use different `World`
types, so the correspondence is structural.
-/

/--
Conditional necessity via domain restriction.

"If α, must β" is true at w iff β holds at all α-worlds accessible from w.
`domain w` returns accessible worlds — intended to be instantiated with
`Kratzer.accessibleWorlds f` from `Modality/Kratzer.lean`.
-/
def condNecessity (domain : World → List World) (α β : BProp World) : BProp World :=
  λ w => ((domain w).filter α).all β

/--
The antecedent position of `condNecessity` is classically DE.

If α₁ ⊆ α₂, then "if α₂, must β" entails "if α₁, must β": the α₁-worlds
are a subset of the α₂-worlds, so the `.all β` check passes on the smaller
set whenever it passes on the larger.
-/
theorem conditional_antecedent_DE (domain : World → List World) (β : BProp World) :
    IsDownwardEntailing (λ α => condNecessity domain α β) := by
  intro α₁ α₂ hle w
  simp only [condNecessity]
  intro h
  apply List.all_eq_true.mpr
  intro w' hw'
  have ⟨hw'_mem, hw'_α₁⟩ := List.mem_filter.mp hw'
  have hw'_α₂ : α₂ w' = true := le_antisymm le_top (hw'_α₁ ▸ hle w')
  exact List.all_eq_true.mp h w' (List.mem_filter.mpr ⟨hw'_mem, hw'_α₂⟩)

/--
Conditional antecedent is Strawson-DE (trivially, since it is classically DE).
-/
theorem conditional_antecedent_strawsonDE (domain : World → List World) (β : BProp World)
    (defined : BProp World → Prop) :
    IsStrawsonDE (λ α => condNecessity domain α β) defined :=
  de_implies_strawsonDE _ (conditional_antecedent_DE domain β) defined

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
