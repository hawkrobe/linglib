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

## World-relativized definedness

The `defined` predicate in `IsStrawsonDE` is world-relativized:
`defined : Prop' World → World → Prop`. This correctly captures von Fintel's
Definition 14, where "f(x) is defined" means the presupposition of f(x) is
satisfied *at the world of evaluation*. For "only" the presupposition is
world-independent (existential), but for factive attitudes the factivity
presupposition `p w` is inherently world-relative.

-/

import Mathlib.Order.Monotone.Defs
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Semantics.Presupposition

namespace Semantics.Entailment.StrawsonEntailment

open Core.Proposition (Prop')
open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.AntiAdditivity

-- ============================================================================
-- Section 1: Core Definitions
-- ============================================================================

/--
**Strawson-DE** (@cite{von-fintel-1999}, Definition 14).

A function `f : Prop' World → Prop' World` is Strawson-DE with respect to a
world-relativized definedness predicate `defined` iff: for all p ≤ q, at
every world w where `defined p w` holds (i.e. the presupposition of f(p) is
satisfied at w), we have f(q)(w) ≤ f(p)(w).

The definedness predicate is world-relativized because presuppositions are
world-relative: "sorry that p" presupposes p at the evaluation world, not
at all worlds. For "only" the presupposition happens to be world-independent,
but the type must accommodate factive attitudes.
-/
def IsStrawsonDE (f : Prop' World → Prop' World) (defined : Prop' World → World → Prop) : Prop :=
  ∀ p q : Prop' World, (∀ w, p w → q w) → ∀ w, defined p w → f q w → f p w

/--
**Strawson-valid inference** (@cite{von-fintel-1999}, Definition 19).

An inference from premises to conclusion is Strawson-valid iff it is
classically valid once we add the premise that all presuppositions of the
conclusion are satisfied.
-/
def StrawsonValid (premises : List (Prop' World)) (conclusion : Prop' World)
    (presupSatisfied : Prop) : Prop :=
  presupSatisfied →
    (∀ w, (∀ p ∈ premises, p w) → conclusion w)

-- ============================================================================
-- Section 2: Hierarchy Theorems
-- ============================================================================

/--
Every classically DE function is Strawson-DE (for any definedness predicate).

Proof: the `defined p w` hypothesis is simply ignored; the `Antitone` proof
gives us f(q) ≤ f(p) unconditionally.

This establishes: DE ⊆ Strawson-DE.
-/
theorem de_implies_strawsonDE (f : Prop' World → Prop' World) (hDE : IsDownwardEntailing f)
    (defined : Prop' World → World → Prop) : IsStrawsonDE f defined :=
  λ _p _q hpq w _hdef => hDE hpq w

/--
Every anti-additive function is Strawson-DE.

Via: AA → DE → Strawson-DE.
-/
theorem antiAdditive_implies_strawsonDE (f : Prop' World → Prop' World)
    (hAA : IsAntiAdditive f) (defined : Prop' World → World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f (antiAdditive_implies_de f hAA) defined

/--
Every anti-morphic function is Strawson-DE.

Via: AM → AA → DE → Strawson-DE.
-/
theorem antiMorphic_implies_strawsonDE (f : Prop' World → Prop' World)
    (hAM : IsAntiMorphic f) (defined : Prop' World → World → Prop) :
    IsStrawsonDE f defined :=
  de_implies_strawsonDE f (antiMorphic_implies_de f hAM) defined

/--
The full hierarchy chain: AM → AA → DE → Strawson-DE.

Given an anti-morphic proof, we can derive all weaker properties.
-/
structure FullHierarchy (f : Prop' World → Prop' World) (defined : Prop' World → World → Prop) where
  am : IsAntiMorphic f
  aa : IsAntiAdditive f := am.1
  de : IsDownwardEntailing f := antiAdditive_implies_de f aa
  strawsonDE : IsStrawsonDE f defined := de_implies_strawsonDE f de defined

/-- Negation satisfies the full hierarchy. -/
def pnot_fullHierarchy (defined : Prop' World → World → Prop) : FullHierarchy pnot defined :=
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
def onlyPrProp (x : World → Bool) (scope : Prop' World) : Core.Presupposition.PrProp World where
  presup := λ _ => ∃ y ∈ allWorlds, x y = true ∧ scope y
  assertion := λ _ => ∀ y ∈ allWorlds, x y = true ∨ ¬ scope y

/--
The full "only" meaning: presupposition + assertion combined.

"Only x VP" is true at w iff x satisfies VP AND no one else does.
Equivalent to `(onlyPrProp x scope).presup w ∧ (onlyPrProp x scope).assertion w`.
-/
def onlyFull (x : World → Bool) (scope : Prop' World) : Prop' World :=
  λ _w => (∃ y ∈ allWorlds, x y = true ∧ scope y) ∧
          (∀ y ∈ allWorlds, x y = true ∨ ¬ scope y)

/-- `onlyFull` equals the conjunction of `onlyPrProp`'s components. -/
theorem onlyFull_eq_prprop (x : World → Bool) (scope : Prop' World) (w : World) :
    onlyFull x scope w ↔
    (onlyPrProp x scope).presup w ∧ (onlyPrProp x scope).assertion w := Iff.rfl

/--
"Only" (full meaning) is not classically DE (von Fintel ex 11).

Counterexample: kale ⊆ vegetables, but
"Only J ate vegetables" ⊬ "Only J ate kale"
because J may have eaten vegetables but not kale.
-/
theorem onlyFull_not_de : ¬IsDownwardEntailing (onlyFull (λ w => w == .w0)) := by
  intro hDE
  -- Counterexample: p = ⊥ (no one eats kale), q = {w0} (only John eats vegetables)
  -- p → q trivially. onlyFull(q)(w0) holds, onlyFull(p)(w0) fails.
  let p : Prop' World := λ _ => False
  let q : Prop' World := λ w => w = .w0
  -- Build the antitone hypothesis in pointwise form
  have hle : p ≤ q := fun _ h => h.elim
  have hq_only : onlyFull (λ w => w == .w0) q World.w0 := by
    refine ⟨⟨World.w0, by decide, by decide, rfl⟩, ?_⟩
    intro y _hy
    cases y <;> simp [q]
  have h := hDE hle World.w0 hq_only
  rcases h with ⟨⟨_, _, _, hp_y⟩, _⟩
  exact hp_y

/--
The assertion component of "only" IS Strawson-DE.

When the presupposition is satisfied (the focused individual x satisfies
the scope P), then: if P ⊆ Q, "no y≠x satisfies Q" implies "no y≠x
satisfies P" — because P ⊆ Q.

This is von Fintel's central insight for "only" (Theorem 1 / ex 18).

The definedness predicate is world-independent (existential presupposition),
so the extra world argument is unused.
-/
theorem onlyFull_isStrawsonDE (x : World → Bool) :
    IsStrawsonDE (onlyFull x) (λ scope _w => ∃ w', x w' = true ∧ scope w') := by
  intro p q hpq w ⟨wx, hx_true, hp_wx⟩ h
  obtain ⟨_h_any, h_all⟩ := h
  refine ⟨?_, ?_⟩
  -- Part 1: presup-witness wx satisfies x and p
  · exact ⟨wx, by cases wx <;> simp [allWorlds], hx_true, hp_wx⟩
  -- Part 2: every y is x or ¬p y; from x or ¬q y plus p ≤ q
  · intro y hy
    rcases h_all y hy with hxy | hnq
    · left; exact hxy
    · right; intro hpy; exact hnq (hpq y hpy)

-- ============================================================================
-- Section 4: Adversative Attitudes (von Fintel §3)
-- ============================================================================

/-!
### Adversative/Factive Attitudes
@cite{von-fintel-1999} @cite{heim-1992}

Von Fintel's analysis (§3): "sorry", "surprised", "regret" license NPIs in
their complement position. The full denotation includes the factivity
presupposition: "sorry that p" = "p holds AND the agent's preferred worlds
have ¬p" (the agent wishes p weren't true).

Key insight: the full operator is NOT classically DE — narrowing p to
p' ⊆ p may fail because the factivity presupposition (p' holds at the
evaluation world) isn't guaranteed. But with Strawson-DE, adding the
factivity presupposition of the conclusion makes the DE inference go
through: if p' holds at w, then q(w) → p(w) for the factivity part,
and ¬q → ¬p by contraposition for the preference part.

Contrast: "glad that p" = "p holds AND the agent's preferred worlds have p."
This is UE in the complement — so "glad" does NOT license NPIs.

The `bestOf` parameter corresponds to `bestWorlds f g` from
`Modality/Kratzer.lean` (Kratzer's modal base + ordering source).
The two modules use different `World` types, so the connection is
structural rather than via direct import.
-/

/--
`sorry` denotation: adversative factive attitude (full operator).

"α is sorry that p" = p holds at w (factivity) AND in α's preferred
worlds, p is NOT true (adversative preference).

`bestOf w` returns the "best" accessible worlds from w — intended to be
instantiated with `Kratzer.bestWorlds f g` from `Modality/Kratzer.lean`.

Unlike the assertion-only version (which would be trivially DE by
contraposition), this full operator includes the positive factivity
component, which is what blocks classical DE.
-/
def sorryFull (bestOf : World → List World) (p : Prop' World) : Prop' World :=
  λ w => p w ∧ ∀ w' ∈ bestOf w, ¬ p w'

/--
`glad` denotation: non-adversative factive attitude (full operator).

"α is glad that p" = p holds at w (factivity) AND in α's preferred
worlds, p IS true (congruent preference).
-/
def gladFull (bestOf : World → List World) (p : Prop' World) : Prop' World :=
  λ w => p w ∧ ∀ w' ∈ bestOf w, p w'

/--
`sorry` (full meaning) is NOT classically DE.

The factivity presupposition (positive component `p w`) blocks DE:
narrowing the scope from q to p ⊆ q may fail because `p w = true` is
not guaranteed by `q w = true`.

Counterexample: p = ∅, q = {w0}. sorry(q)(w0) = true (w0 satisfies q,
and best worlds have ¬q). sorry(p)(w0) = false (w0 doesn't satisfy p).
DE would require true ≤ false.
-/
theorem sorryFull_not_de : ¬IsDownwardEntailing (sorryFull (λ _ => [World.w1])) := by
  intro hDE
  let p : Prop' World := λ _ => False
  let q : Prop' World := λ w => w = .w0
  have hle : p ≤ q := fun _ h => h.elim
  have hq_sorry : sorryFull (λ _ => [World.w1]) q World.w0 := by
    refine ⟨rfl, ?_⟩
    intro w' hw'
    rcases List.mem_singleton.mp hw' with rfl
    intro h; cases h
  have h := hDE hle World.w0 hq_sorry
  exact h.1

/--
`sorry` IS Strawson-DE in its complement.

The definedness condition is factivity at the evaluation world:
`p w = true` (p holds at the world where we're checking the inference).

Given factivity (p w = true) and p ⊆ q:
1. `q w = true` follows from p ≤ q — factivity of q is inherited
2. For all best worlds w': if ¬q(w') (from sorry(q)), then ¬p(w')
   by contraposition of p ≤ q

So sorry(q)(w) = true implies sorry(p)(w) = true, when p(w) = true.
-/
theorem sorryFull_isStrawsonDE (bestOf : World → List World) :
    IsStrawsonDE (sorryFull bestOf) (λ p w => p w) := by
  intro p q hpq w hpw h
  obtain ⟨_, hAllNotQ⟩ := h
  refine ⟨hpw, ?_⟩
  intro w' hw' hpw'
  exact hAllNotQ w' hw' (hpq w' hpw')

/--
`sorry` is Strawson-DE but NOT DE — the canonical adversative example.
-/
theorem sorryFull_strictly_strawsonDE :
    IsStrawsonDE (sorryFull (λ _ => [World.w1])) (λ p w => p w) ∧
    ¬IsDownwardEntailing (sorryFull (λ _ => [World.w1])) :=
  ⟨sorryFull_isStrawsonDE _, sorryFull_not_de⟩

/--
`glad` is NOT Strawson-DE — it is upward entailing (UE).

If p ⊆ q: p(w) = true → q(w) = true, and all preferred worlds satisfying
p also satisfy q. So `glad` preserves entailment direction — it does NOT
license NPIs.

This is the adversative/non-adversative asymmetry that von Fintel §3.3
identifies as the key to NPI licensing in attitude complements.
-/
theorem gladFull_isUE (bestOf : World → List World) :
    ∀ p q : Prop' World, (∀ w, p w → q w) →
      ∀ w, gladFull bestOf p w → gladFull bestOf q w := by
  intro p q hpq w h
  obtain ⟨hpw, hAll⟩ := h
  exact ⟨hpq w hpw, fun w' hw' => hpq w' (hAll w' hw')⟩

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

The world argument is unused: this presupposition is world-independent
(it's about whether the subject satisfies the restriction at any world).
-/
def superlativePresup (subject : World → Bool) (restriction : Prop' World)
    (_w : World) : Prop :=
  ∃ w', subject w' = true ∧ restriction w'

/--
Superlative assertion: subject has the highest degree among those
satisfying the restriction.

Simplified model: the "tallest who VP" at w checks that no one else
in the restriction exceeds the subject.
-/
def superlativeAssert (subject : World → Bool) (restriction : Prop' World) : Prop' World :=
  λ _w => (∃ y ∈ allWorlds, subject y = true ∧ restriction y) ∧
          (∀ y ∈ allWorlds, subject y = true ∨ ¬ restriction y ∨
             ¬ ∃ z ∈ allWorlds, subject z = false ∧ restriction z)

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
  intro p q hpq w ⟨wx, hsubj_wx, hp_wx⟩ h
  obtain ⟨_h_any_q, h_all_q⟩ := h
  refine ⟨?_, ?_⟩
  -- Part 1: ∃ y ∈ allWorlds, subject y ∧ p y — from presupposition
  · refine ⟨wx, ?_, hsubj_wx, hp_wx⟩
    cases wx <;> simp [allWorlds]
  -- Part 2: ∀ y, subject y ∨ ¬(p y) ∨ ¬C(p)
  · intro y hy
    by_cases hCp : ∃ z ∈ allWorlds, subject z = false ∧ p z
    · -- C(p) holds: some non-subject satisfies p. By p → q, C(q) holds too.
      obtain ⟨z, hz_mem, hz_subj, hz_p⟩ := hCp
      have hCq : ∃ z ∈ allWorlds, subject z = false ∧ q z :=
        ⟨z, hz_mem, hz_subj, hpq z hz_p⟩
      rcases h_all_q y hy with hsubj_y | hnq | hnCq
      · left; exact hsubj_y
      · right; left; intro hp_y; exact hnq (hpq y hp_y)
      · exact absurd hCq hnCq
    · -- C(p) is false: third disjunct holds directly
      right; right; exact hCp

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
def condNecessity (domain : World → List World) (α β : Prop' World) : Prop' World :=
  λ w => ∀ w' ∈ domain w, α w' → β w'

/--
The antecedent position of `condNecessity` is classically DE.

If α₁ ⊆ α₂, then "if α₂, must β" entails "if α₁, must β": the α₁-worlds
are a subset of the α₂-worlds, so the `.all β` check passes on the smaller
set whenever it passes on the larger.
-/
theorem conditional_antecedent_DE (domain : World → List World) (β : Prop' World) :
    IsDownwardEntailing (λ α => condNecessity domain α β) := by
  intro α₁ α₂ hle w h w' hw'_mem hw'_α₁
  exact h w' hw'_mem (hle w' hw'_α₁)

/--
Conditional antecedent is Strawson-DE (trivially, since it is classically DE).
-/
theorem conditional_antecedent_strawsonDE (domain : World → List World) (β : Prop' World)
    (defined : Prop' World → World → Prop) :
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
theorem isDE_implies_strawsonDE (f : Prop' World → Prop' World) (hDE : IsDE f)
    (defined : Prop' World → World → Prop) : IsStrawsonDE f defined :=
  de_implies_strawsonDE f hDE defined

/--
Negation is Strawson-DE (trivially, since it's anti-morphic).
-/
theorem pnot_isStrawsonDE (defined : Prop' World → World → Prop) :
    IsStrawsonDE pnot defined :=
  de_implies_strawsonDE pnot pnot_isDownwardEntailing defined

/--
"No student" is Strawson-DE (trivially, since it's anti-additive → DE).
-/
theorem no_student_isStrawsonDE (defined : Prop' World → World → Prop) :
    IsStrawsonDE no_student defined :=
  de_implies_strawsonDE no_student no_isDE_scope defined

/--
"At most 2 students" is Strawson-DE (trivially, since it's DE).
-/
theorem atMost2_isStrawsonDE (defined : Prop' World → World → Prop) :
    IsStrawsonDE atMost2_student defined :=
  de_implies_strawsonDE atMost2_student atMost_isDE_scope defined

/--
Strawson-DE is strictly weaker than DE: there exist functions that are
Strawson-DE but not DE. "Only" is the canonical example.
-/
theorem strawsonDE_strictly_weaker_than_DE :
    (∃ f defined, IsStrawsonDE f defined ∧ ¬IsDownwardEntailing f) := by
  exact ⟨onlyFull (λ w => w == .w0),
         λ scope _w => ∃ w', (w' == .w0) = true ∧ scope w',
         onlyFull_isStrawsonDE _,
         onlyFull_not_de⟩

end Semantics.Entailment.StrawsonEntailment
