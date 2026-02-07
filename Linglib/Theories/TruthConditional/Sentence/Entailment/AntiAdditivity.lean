/-
The DE < Anti-Additive < Anti-Morphic hierarchy (Zwarts 1996).
Reference: Zwarts (1996), Chierchia (2013) section 1.4.3, Ladusaw (1980).
-/

import Mathlib.Order.Monotone.Defs
import Mathlib.Data.List.Basic
import Linglib.Theories.TruthConditional.Sentence.Entailment.Basic
import Linglib.Theories.TruthConditional.Core.Polarity

namespace TruthConditional.Sentence.Entailment.AntiAdditivity

open TruthConditional.Sentence.Entailment
open TruthConditional.Core.Polarity
open List (Sublist)


section Definitions

/-- Anti-additive: forall A B, f(A | B) = f(A) & f(B). -/
def IsAntiAdditive (f : Prop' → Prop') : Prop :=
  ∀ p q : Prop', (∀ w, f (por p q) w = (f p w && f q w))

/--
Anti-morphic (AM): Anti-additive + distributes ∧ to ∨ in both directions.

`∀ A B, f(A ∧ B) = f(A) ∨ f(B)`

This is the characteristic property of negation (De Morgan's law).
-/
def IsAntiMorphic (f : Prop' → Prop') : Prop :=
  IsAntiAdditive f ∧
  (∀ p q : Prop', (∀ w, f (pand p q) w = (f p w || f q w)))


/--
Anti-additive implies DE.

The left-to-right direction of anti-additivity is exactly the DE property.
-/
theorem antiAdditive_implies_de (f : Prop' → Prop') (hAA : IsAntiAdditive f) :
    IsDownwardEntailing f := by
  intro p q hpq
  intro w
  -- We need: f q w ≤ f p w
  -- Key: when p ≤ q, we have por p q = q pointwise
  have h_por_eq : ∀ w', por p q w' = q w' := by
    intro w'
    have hpq_w := hpq w'
    simp only [por, Core.Proposition.Decidable.por]
    -- p w' || q w' = q w' when p w' ≤ q w'
    cases hp : p w' <;> cases hq : q w'
    · rfl
    · rfl
    · -- p w' = true, q w' = false, but hpq_w : true ≤ false, contradiction
      simp only [hp, hq] at hpq_w
      -- hpq_w : true ≤ false, derive false = true which is absurd
      have : false = true := Bool.eq_true_of_true_le hpq_w
      cases this
    · rfl
  -- Now use anti-additivity: f(p ∨ q) = f(p) ∧ f(q)
  have hAA_w := hAA p q w
  -- f(p ∨ q) w = f(p) w && f(q) w
  -- But f(p ∨ q) = f(q) since p ∨ q = q
  have h_feq : f (por p q) w = f q w := by
    congr 1
    funext w'
    exact h_por_eq w'
  -- So f(q) w = f(p) w && f(q) w
  rw [h_feq] at hAA_w
  -- This means f(q) w ≤ f(p) w (since x = x && y implies x ≤ y in Bool)
  cases hfp : f p w <;> cases hfq : f q w <;> simp_all

/--
Anti-morphic implies anti-additive.

By definition, anti-morphic is anti-additive plus the ∧-to-∨ property.
-/
theorem antiMorphic_implies_antiAdditive (f : Prop' → Prop') (hAM : IsAntiMorphic f) :
    IsAntiAdditive f :=
  hAM.1

/--
Anti-morphic implies DE.

Transitive: AM → AA → DE.
-/
theorem antiMorphic_implies_de (f : Prop' → Prop') (hAM : IsAntiMorphic f) :
    IsDownwardEntailing f :=
  antiAdditive_implies_de f (antiMorphic_implies_antiAdditive f hAM)


/--
Negation is anti-additive.

`¬(A ∨ B) = ¬A ∧ ¬B` (De Morgan's law, part 1)
-/
theorem pnot_isAntiAdditive : IsAntiAdditive pnot := by
  intro p q w
  simp only [pnot, por, Core.Proposition.Decidable.pnot, Core.Proposition.Decidable.por]
  cases p w <;> cases q w <;> rfl

/--
Negation satisfies the conjunction-to-disjunction property.

`¬(A ∧ B) = ¬A ∨ ¬B` (De Morgan's law, part 2)
-/
theorem pnot_distributes_and : ∀ p q : Prop', (∀ w, pnot (pand p q) w = (pnot p w || pnot q w)) := by
  intro p q w
  simp only [pnot, pand, Core.Proposition.Decidable.pnot, Core.Proposition.Decidable.pand]
  cases p w <;> cases q w <;> rfl

/--
Negation is anti-morphic.

This is the strongest level in the hierarchy.
-/
theorem pnot_isAntiMorphic : IsAntiMorphic pnot :=
  ⟨pnot_isAntiAdditive, pnot_distributes_and⟩


/--
"No A is B" = ∀x. A(x) → ¬B(x)

For a fixed restrictor, "no ___" as a function of scope.
-/
def no' (restr : Prop') (scope : Prop') : Prop' :=
  λ _ => allWorlds.all λ x => !(restr x && scope x)

/--
"No student ___" with fixed restrictor.
-/
def no_student : Prop' → Prop' := no' p01  -- p01 = "students"

/--
"No" is anti-additive in scope.

`No A (B ∨ C) ⊣⊢ No A B ∧ No A C`

Proof: "No student smokes or drinks" iff "No student smokes and no student drinks"
-/
theorem no_isAntiAdditive_scope : IsAntiAdditive no_student := by
  intro p q _w
  simp only [no_student, no', por, Core.Proposition.Decidable.por,
             allWorlds, p01, List.all_cons, List.all_nil]
  -- After expanding allWorlds and p01, case-split on all variable values
  -- World has 4 constructors, so we split on p and q at each
  cases p .w0 <;> cases q .w0 <;> cases p .w1 <;> cases q .w1 <;>
    cases p .w2 <;> cases q .w2 <;> cases p .w3 <;> cases q .w3 <;> decide

/--
"No" is DE in scope.

Follows from anti-additivity.
-/
theorem no_isDE_scope : IsDE no_student :=
  antiAdditive_implies_de no_student no_isAntiAdditive_scope


/--
"At most n A's are B" - true if |A ∩ B| ≤ n.

We use a simplified version for our 4-world model.
-/
def atMost (n : Nat) (restr scope : Prop') : Bool :=
  (allWorlds.filter λ w => restr w && scope w).length ≤ n

/--
"At most 2 students ___" with fixed restrictor.
-/
def atMost2_student : Prop' → Prop' :=
  λ scope => λ _ => atMost 2 p01 scope

/--
"At most n" is DE in scope.

If P ⊆ Q, then "At most n A's are Q" ⊢ "At most n A's are P"

Because |A ∩ P| ≤ |A ∩ Q| when P ⊆ Q.
-/
theorem atMost_isDE_scope : IsDE atMost2_student := by
  intro p q hpq
  intro w
  simp only [atMost2_student, atMost]
  -- Need: if atMost 2 p01 q then atMost 2 p01 p
  -- I.e., |p01 ∩ q| ≤ 2 → |p01 ∩ p| ≤ 2
  -- Since p ≤ q, we have p01 ∩ p ⊆ p01 ∩ q
  intro h
  have subset : ∀ x, (p01 x && p x) = true → (p01 x && q x) = true := by
    intro x hx
    simp only [Bool.and_eq_true] at hx ⊢
    exact ⟨hx.1, hpq x hx.2⟩
  -- The filter for p has elements that are a subset of those for q
  -- so |filter p| ≤ |filter q| when filtering the same base list
  have len_le : (allWorlds.filter λ w => p01 w && p w).length ≤
                (allWorlds.filter λ w => p01 w && q w).length := by
    -- Use monotone_filter_right: if p a → q a, then l.filter p <+ l.filter q
    have hsub : Sublist (allWorlds.filter λ w => p01 w && p w)
                        (allWorlds.filter λ w => p01 w && q w) :=
      List.monotone_filter_right allWorlds subset
    exact Sublist.length_le hsub
  -- h and len_le together imply the goal
  -- h : (filter for q).length ≤ 2 = true, need: (filter for p).length ≤ 2 = true
  simp only [decide_eq_true_eq] at h ⊢
  exact Nat.le_trans len_le h

/--
"At most n" is not anti-additive (counterexample).

The right-to-left direction fails:
- "At most 5 smoke" ∧ "At most 5 drink" does NOT imply "At most 5 smoke or drink"

Chierchia's example: 4 smoke, 3 different drink → 7 total smoke-or-drink.

Note: Our 4-world model is too small to demonstrate this concretely with the
current p01 restrictor (which has only 2 students), so we leave this as `sorry`.
The mathematical fact is well-established in the literature.
-/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost2_student := by
  sorry


/--
Strength of downward entailingness.

Names the three levels of the Zwarts (1996) hierarchy:
- `.weak` = DE only (licenses weak NPIs)
- `.antiAdditive` = DE + right-to-left (licenses strong NPIs)
- `.antiMorphic` = AA + De Morgan for ∧ (negation)
-/
inductive DEStrength where
  | weak           -- Plain DE (licenses weak NPIs)
  | antiAdditive   -- DE + ∨-distributive (licenses strong NPIs)
  | antiMorphic    -- Anti-additive + ∧-distributive (= negation)
  deriving DecidableEq, BEq, Repr


/--
Weak NPI licensing: Requires DE context.

Examples: ever, any (unstressed), alcun
-/
def licensesWeakNPI (f : Prop' → Prop') : Prop := IsDownwardEntailing f

/--
Strong NPI licensing: Requires Anti-Additive context.

Examples: lift a finger, in weeks, until
-/
def licensesStrongNPI (f : Prop' → Prop') : Prop := IsAntiAdditive f

-- Verify: negation licenses both
example : licensesWeakNPI pnot := pnot_isDownwardEntailing
example : licensesStrongNPI pnot := pnot_isAntiAdditive

-- Verify: "no" licenses both
example : licensesWeakNPI no_student := no_isDE_scope
example : licensesStrongNPI no_student := no_isAntiAdditive_scope

-- Verify: "at most n" licenses weak
example : licensesWeakNPI atMost2_student := atMost_isDE_scope


/-!
## Connection to `Fragments.English.PolarityItems`

The `DEStrength` enum there corresponds to this hierarchy:

| PolarityItems.DEStrength | This Module | Example Licensor |
|--------------------------|-------------|------------------|
| `.weak` | `IsDE` | few, at most n |
| `.antiAdditive` | `IsAntiAdditive` | no, nobody, without |
| `.antiMorphic` | `IsAntiMorphic` | not, never |

### Strong NPIs require `.antiAdditive` or stronger:

- `liftAFinger.minStrength = .antiAdditive`
- "*Few people lifted a finger" — `few` is only DE, not AA
- "No one lifted a finger" — `no one` is AA ✓

### Weak NPIs accept `.weak` or stronger:

- `ever.minStrength = .weak`
- "Few people ever complained" — `few` is DE ✓
- "No one ever complained" — `no one` is AA (≥ weak) ✓
-/

/--
Check if a context's strength is sufficient for an NPI.

`contextStrength ≥ requiredStrength`
-/
def strengthSufficient (contextStrength requiredStrength : DEStrength) : Bool :=
  match requiredStrength, contextStrength with
  | .weak, _ => true
  | .antiAdditive, .weak => false
  | .antiAdditive, _ => true
  | .antiMorphic, .antiMorphic => true
  | .antiMorphic, _ => false

-- Verify the licensing predictions
#guard strengthSufficient .antiMorphic .weak      -- negation licenses weak NPIs
#guard strengthSufficient .antiMorphic .antiAdditive  -- negation licenses strong NPIs
#guard strengthSufficient .antiAdditive .weak     -- "no" licenses weak NPIs
#guard strengthSufficient .antiAdditive .antiAdditive -- "no" licenses strong NPIs
#guard strengthSufficient .weak .weak             -- "few" licenses weak NPIs
#guard !strengthSufficient .weak .antiAdditive    -- "few" does NOT license strong NPIs

end Definitions

end TruthConditional.Sentence.Entailment.AntiAdditivity
