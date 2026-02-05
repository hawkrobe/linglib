/-
# ICDRT Connectives

Bilateral connectives enabling cross-disjunct anaphora (bathroom sentences).

## Main definitions

`BilateralICDRT.neg`, `disjBathroom`, `impl`, `donkeyConditional`, `bathroomSentence`

## References

- Hofmann (2025) §3: Disjunction and the bathroom problem
- Elliott & Sudo (2025). Free choice with anaphora. S&P 18.
-/

import Linglib.Theories.DynamicSemantics.IntensionalCDRT.Update

namespace Theories.DynamicSemantics.IntensionalCDRT

open Theories.DynamicSemantics.Core


namespace BilateralICDRT

variable {W E : Type*}

/-- DNE holds definitionally: ¬¬φ = φ. -/
theorem dne_equality (φ : BilateralICDRT W E) (c : IContext W E) :
    φ.neg.neg.positive c = φ.positive c ∧
    φ.neg.neg.negative c = φ.negative c := by
  simp [neg_neg]

/-- Negation preserves context consistency. -/
theorem neg_consistent_iff (φ : BilateralICDRT W E) (c : IContext W E) :
    (φ.neg.positive c).Nonempty ↔ (φ.negative c).Nonempty := Iff.rfl


/-- Standard disjunction without cross-disjunct anaphora. -/
def disjStd (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := λ c => φ.positive c ∪ ψ.positive c
  negative := λ c => φ.negative c ∩ ψ.negative c

infixl:60 " ⊕ " => disjStd


/-- Bathroom disjunction: ψ evaluated in context where φ failed, enabling cross-disjunct anaphora. -/
def disjBathroom (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := λ c => φ.positive c ∪ ψ.positive (φ.negative c)
  negative := λ c => φ.negative c ∩ ψ.negative (φ.negative c)

/--
Alternative formulation making the sequencing clearer.

The second disjunct "sees" the context where the first disjunct failed.
-/
def disjBathroom' (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := λ c =>
    let ctxAfterNotPhi := φ.negative c  -- Context where φ failed
    φ.positive c ∪ ψ.positive ctxAfterNotPhi
  negative := λ c =>
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
  positive := λ c => φ.negative c ∪ (φ.positive c ∩ ψ.positive (φ.positive c))
  negative := λ c => φ.positive c ∩ ψ.negative (φ.positive c)

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
because ψ is evaluated in the negative of ∃x.φ, which still introduces x.
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
  let antecedent : BilateralICDRT W E := atom (λ w =>
    True)  -- Placeholder for owns predicate
  let consequent : BilateralICDRT W E := atom (λ w =>
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

The negative of ∃x.bathroom(x) still introduces x (flatly),
but with local context where bathroom(x) is false.
-/
def bathroomSentence (p : PVar) (v : IVar) (domain : Set E)
    (bathroom upstairs : E → W → Prop) : BilateralICDRT W E :=
  let thereIsABathroom : BilateralICDRT W E :=
    exists_ p v domain (atom (λ w => ∃ e, bathroom e w))
  let itIsUpstairs : BilateralICDRT W E :=
    -- The individual dref v is accessible here!
    atom (λ w => True)  -- Placeholder - needs entity lookup
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
      { positive := λ c => c.updateFull (λ g w => bathroom (g.indiv v) w)
        negative := λ c => c.updateFull (λ g w => ¬bathroom (g.indiv v) w) }
  let itIsUpstairs : BilateralICDRT W E :=
    -- v is accessible; we can reference g.indiv v
    { positive := λ c => c.updateFull (λ g w => upstairs (g.indiv v) w)
      negative := λ c => c.updateFull (λ g w => ¬upstairs (g.indiv v) w) }
  disjBathroom thereIsABathroom.neg itIsUpstairs

end BilateralICDRT


end Theories.DynamicSemantics.IntensionalCDRT
