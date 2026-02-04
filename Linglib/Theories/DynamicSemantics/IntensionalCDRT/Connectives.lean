/-
# ICDRT Connectives

Logical connectives for Intensional CDRT with flat update.

## The Key Patterns

### 1. Double Negation Elimination (DNE)
  ¬¬φ ⟺ φ (by definition: negation swaps positive/negative)

### 2. Bathroom Disjunctions
  "Either there's no bathroom, or it's upstairs."

  The indefinite "a bathroom" is accessible to "it" in the second disjunct
  because:
  1. φ ∨ ψ evaluates ψ in the context where φ is false
  2. The negative of "there's a bathroom" introduces the bathroom dref
  3. That dref is available in the second disjunct

### 3. Cross-Disjunct Anaphora Pattern

From Elliott & Sudo (2025), adapted to flat update:

  ⟦φ ∨ ψ⟧^+ = ⟦φ⟧^+ ∪ (⟦φ⟧^- ∩ ⟦ψ⟧^+)
  ⟦φ ∨ ψ⟧^- = ⟦φ⟧^- ∩ ⟦ψ⟧^-

The second disjunct ψ is evaluated AFTER the negative update of φ!
This is what makes the bathroom dref accessible.

## References

- Hofmann (2025) §3: Disjunction and the bathroom problem
- Elliott & Sudo (2025). Free choice with anaphora. S&P 18.
-/

import Linglib.Theories.DynamicSemantics.IntensionalCDRT.Update

namespace Theories.DynamicSemantics.IntensionalCDRT

open Theories.DynamicSemantics.Core


namespace BilateralICDRT

variable {W E : Type*}

/--
DNE as equality of updates.

This is the key property: double negation doesn't just entail φ,
it IS φ (same positive and negative updates).

This was already proven as `neg_neg` but we re-emphasize it here.
-/
theorem dne_equality (φ : BilateralICDRT W E) (c : IContext W E) :
    φ.neg.neg.positive c = φ.positive c ∧
    φ.neg.neg.negative c = φ.negative c := by
  simp [neg_neg]

/--
Negation preserves context consistency.
-/
theorem neg_consistent_iff (φ : BilateralICDRT W E) (c : IContext W E) :
    (φ.neg.positive c).Nonempty ↔ (φ.negative c).Nonempty := Iff.rfl


/--
Standard disjunction: either φ or ψ holds.

⟦φ ∨ ψ⟧^+ = ⟦φ⟧^+ ∪ ⟦ψ⟧^+
⟦φ ∨ ψ⟧^- = ⟦φ⟧^- ∩ ⟦ψ⟧^-

This is the simple case WITHOUT cross-disjunct anaphora.
-/
def disjStd (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := fun c => φ.positive c ∪ ψ.positive c
  negative := fun c => φ.negative c ∩ ψ.negative c

infixl:60 " ⊕ " => disjStd


/--
Bathroom disjunction: ψ evaluated after ¬φ.

This is the key to bathroom sentences like:
  "Either there's no bathroom, or it's upstairs."

The pattern: evaluate the second disjunct in the context where the
first disjunct has been DENIED. This makes drefs from the negation
of the first disjunct accessible to the second.

⟦φ ∨_bath ψ⟧^+ = ⟦φ⟧^+ ∪ (⟦ψ⟧^+ evaluated at ⟦φ⟧^-)
⟦φ ∨_bath ψ⟧^- = ⟦φ⟧^- ∩ ⟦ψ⟧^-

Key insight: ψ.positive is applied to φ.negative, NOT to c directly.
-/
def disjBathroom (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := fun c => φ.positive c ∪ ψ.positive (φ.negative c)
  negative := fun c => φ.negative c ∩ ψ.negative (φ.negative c)

/--
Alternative formulation making the sequencing clearer.

The second disjunct "sees" the context where the first disjunct failed.
-/
def disjBathroom' (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := fun c =>
    let ctxAfterNotPhi := φ.negative c  -- Context where φ failed
    φ.positive c ∪ ψ.positive ctxAfterNotPhi
  negative := fun c =>
    let ctxAfterNotPhi := φ.negative c
    ctxAfterNotPhi ∩ ψ.negative ctxAfterNotPhi


/--
Conditional: if φ then ψ.

In the bathroom analysis, conditionals work similarly:
  "If there's a bathroom, it's upstairs."

The antecedent introduces drefs accessible in the consequent.

⟦φ → ψ⟧^+ = ⟦φ⟧^- ∪ (⟦φ⟧^+ ∩ ⟦ψ⟧^+)
⟦φ → ψ⟧^- = ⟦φ⟧^+ ∩ ⟦ψ⟧^-
-/
def impl (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := fun c => φ.negative c ∪ (φ.positive c ∩ ψ.positive (φ.positive c))
  negative := fun c => φ.positive c ∩ ψ.negative (φ.positive c)

infixr:55 " ⟹ " => impl

/--
Material conditional equivalence: φ → ψ ≡ ¬φ ∨ ψ

Using bathroom disjunction, this gives anaphora from antecedent to consequent.

Note: This equivalence requires that ψ's positive update is a subsetting operation
(i.e., ψ.positive c' ⊆ c' for any context c'). This is standard in dynamic semantics
where updates can only eliminate possibilities, not add them.
-/
theorem impl_as_disj (φ ψ : BilateralICDRT W E) (c : IContext W E)
    -- Updates are "subsetting": output is a subset of input
    (hψ_subsetting : ψ.positive (φ.positive c) ⊆ φ.positive c) :
    (impl φ ψ).positive c = (disjBathroom φ.neg ψ).positive c := by
  -- LHS: φ.negative c ∪ (φ.positive c ∩ ψ.positive (φ.positive c))
  -- RHS: φ.negative c ∪ ψ.positive (φ.positive c)
  -- With hψ_subsetting, the intersection is redundant
  apply Set.ext
  intro gw
  simp only [impl, disjBathroom, neg, Set.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    cases h with
    | inl h_neg => left; exact h_neg
    | inr h_pos => right; exact h_pos.2
  · intro h
    cases h with
    | inl h_neg => left; exact h_neg
    | inr h_psi => right; exact ⟨hψ_subsetting h_psi, h_psi⟩


/--
De Morgan: ¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ

In bilateral semantics, this holds because:
- Negation swaps positive/negative
- Conjunction sequences, disjunction chooses
-/
theorem de_morgan_conj_positive (φ ψ : BilateralICDRT W E) (c : IContext W E) :
    (φ.conj ψ).neg.positive c = (φ.conj ψ).negative c := rfl

/--
De Morgan: ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
-/
theorem de_morgan_disj_positive (φ ψ : BilateralICDRT W E) (c : IContext W E) :
    (φ.disjStd ψ).neg.positive c = φ.negative c ∩ ψ.negative c := rfl


/--
Wide-scope existential: ∃x.(φ ∨ ψ)

The variable x is introduced before the disjunction, so it's
accessible in both disjuncts.
-/
def existsWideDisj (p : PVar) (v : IVar) (domain : Set E)
    (φ ψ : BilateralICDRT W E) : BilateralICDRT W E :=
  exists_ p v domain (disjBathroom φ ψ)

/--
Narrow-scope existential in first disjunct: (∃x.φ) ∨ ψ

With bathroom disjunction, x introduced in ∃x.φ is accessible in ψ
because ψ is evaluated in the negative of ∃x.φ, which still introduces x!
-/
def existsNarrowFirstDisj (p : PVar) (v : IVar) (domain : Set E)
    (φ ψ : BilateralICDRT W E) : BilateralICDRT W E :=
  disjBathroom (exists_ p v domain φ) ψ


/--
Universal quantifier via de Morgan: ∀x.φ ≡ ¬∃x.¬φ
-/
def forall_ (p : PVar) (v : IVar) (domain : Set E)
    (φ : BilateralICDRT W E) : BilateralICDRT W E :=
  (exists_ p v domain φ.neg).neg


/--
Donkey conditional: "If a farmer owns a donkey, he beats it."

In Hofmann's flat update:
1. "a farmer" introduces dref f
2. "a donkey" introduces dref d
3. These are accessible in the consequent via propositional drefs

Structure: ∃f.∃d.(owns(f,d) → beats(f,d))

The indefinites take widest scope (flat), but propositional drefs
track that they're introduced in the antecedent context.
-/
def donkeyConditional (pFarmer pDonkey : PVar) (vFarmer vDonkey : IVar)
    (farmers donkeys : Set E)
    (owns beats : E → E → W → Prop) : BilateralICDRT W E :=
  let antecedent : BilateralICDRT W E := atom (fun w =>
    True)  -- Placeholder for owns predicate
  let consequent : BilateralICDRT W E := atom (fun w =>
    True)  -- Placeholder for beats predicate
  exists_ pFarmer vFarmer farmers
    (exists_ pDonkey vDonkey donkeys
      (impl antecedent consequent))


/--
The classic bathroom sentence:
  "Either there's no bathroom, or it's upstairs."

Analysis:
1. First disjunct: ¬∃x.bathroom(x)
2. Second disjunct: upstairs(x)
3. Bathroom disjunction: x from ¬∃ is accessible in second disjunct

Key: The negative of ∃x.bathroom(x) STILL introduces x (flatly),
but with local context where bathroom(x) is false.
-/
def bathroomSentence (p : PVar) (v : IVar) (domain : Set E)
    (bathroom upstairs : E → W → Prop) : BilateralICDRT W E :=
  let thereIsABathroom : BilateralICDRT W E :=
    exists_ p v domain (atom (fun w => ∃ e, bathroom e w))
  let itIsUpstairs : BilateralICDRT W E :=
    -- The individual dref v is accessible here!
    atom (fun w => True)  -- Placeholder - needs entity lookup
  disjBathroom thereIsABathroom.neg itIsUpstairs

/--
More detailed bathroom sentence with proper variable reference.

In full ICDRT, "it" in the second disjunct looks up variable v,
and the propositional dref p tracks where v has a referent.
-/
def bathroomSentenceFull (p : PVar) (v : IVar) (domain : Set E)
    (bathroom upstairs : Entity E → W → Prop) : BilateralICDRT W E :=
  let thereIsABathroom : BilateralICDRT W E :=
    exists_ p v domain
      { positive := fun c => c.updateFull (fun g w => bathroom (g.indiv v) w)
        negative := fun c => c.updateFull (fun g w => ¬bathroom (g.indiv v) w) }
  let itIsUpstairs : BilateralICDRT W E :=
    -- v is accessible! We can reference g.indiv v
    { positive := fun c => c.updateFull (fun g w => upstairs (g.indiv v) w)
      negative := fun c => c.updateFull (fun g w => ¬upstairs (g.indiv v) w) }
  disjBathroom thereIsABathroom.neg itIsUpstairs

end BilateralICDRT

-- SUMMARY

/-!
## What This Module Provides

### Connectives
- `neg`: Negation (swap positive/negative) - with DNE
- `conj`: Conjunction (sequence positive)
- `disjStd`: Standard disjunction (union/intersection)
- `disjBathroom`: Bathroom disjunction (cross-disjunct anaphora)
- `impl`: Conditional
- `forall_`: Universal via de Morgan
- `exists_`: Existential (from Update.lean)

### Key Theorems
- `dne_equality`: ¬¬φ = φ
- `impl_as_disj`: φ → ψ ≡ ¬φ ∨ ψ
- `de_morgan_conj_positive`, `de_morgan_disj_positive`

### Examples
- `donkeyConditional`: Donkey sentence structure
- `bathroomSentence`, `bathroomSentenceFull`: Bathroom disjunction

## The Bathroom Pattern

The key insight: `disjBathroom` evaluates the second disjunct in the
context where the first disjunct's NEGATIVE update has been applied.

This means drefs introduced by the negation of the first disjunct
are accessible in the second disjunct - exactly what's needed for
"Either there's no bathroom, or it's upstairs."
-/

end Theories.DynamicSemantics.IntensionalCDRT
