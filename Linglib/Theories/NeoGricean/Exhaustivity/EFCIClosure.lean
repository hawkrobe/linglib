/-
# EFCI Closure Analysis

Connection between EFCI alternatives and Spector's Theorem 9.

The EFCI contradiction arises because the alternative set is not closed
under conjunction. This directly connects to Spector's main result:
when ALT is closed under conjunction, exh_mw = exh_ie.

## Insight

For standard scalar alternatives, the set is typically closed under
conjunction. For EFCI alternatives, the pre-exhaustified domain
alternatives are mutually inconsistent -- their conjunction is ⊥.
This breaks closure and creates the need for rescue mechanisms.

## References

- Spector (2016). Comparing exhaustivity operators.
- Alonso-Ovalle & Moghiseh (2025). Existential free choice items.
- Chierchia (2013). Logic in Grammar.
-/

import Linglib.Theories.NeoGricean.Exhaustivity.Basic
import Linglib.Theories.NeoGricean.Exhaustivity.EFCI

namespace NeoGricean.Exhaustivity.EFCIClosure

open NeoGricean.Exhaustivity
open NeoGricean.Exhaustivity.EFCI

variable {World : Type*} {Entity : Type*}


/--
The prejacent and scalar alternative set is "almost closed" under conjunction.
The universal is the conjunction of all singleton assertions.
-/
theorem scalar_alts_structure (D : Domain Entity) (P : Entity → Prop' World) :
    universalAlt D P = λ w => ∀ d ∈ D, P d w := rfl

/--
Pre-exhaustified domain alternatives are pairwise inconsistent.
For distinct d₁, d₂ ∈ D:
  preExh(d₁) ∧ preExh(d₂) = ⊥

You can't have "exactly d₁ satisfies P" AND "exactly d₂ satisfies P".
-/
theorem preExh_pairwise_inconsistent
    (D : Domain Entity) (d₁ d₂ : Entity) (P : Entity → Prop' World)
    (_hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hne : d₁ ≠ d₂) :
    ∀ w, ¬(preExhaustify D d₁ P w ∧ preExhaustify D d₂ P w) := by
  intro w ⟨⟨_, hexcl₁⟩, ⟨hPd₂, _⟩⟩
  exact hexcl₁ d₂ hd₂ hne.symm hPd₂

/--
The conjunction of ALL pre-exhaustified domain alternatives is ⊥
(when |D| ≥ 2).
-/
theorem preExh_all_inconsistent
    (D : Domain Entity) (P : Entity → Prop' World)
    (d₁ d₂ : Entity) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hne : d₁ ≠ d₂) :
    ∀ w, ¬(∀ φ ∈ preExhDomainAlts D P, φ w) := by
  intro w hall
  have h₁ : preExhaustify D d₁ P ∈ preExhDomainAlts D P := ⟨d₁, hd₁, rfl⟩
  have h₂ : preExhaustify D d₂ P ∈ preExhDomainAlts D P := ⟨d₂, hd₂, rfl⟩
  exact preExh_pairwise_inconsistent D d₁ d₂ P hd₁ hd₂ hne w ⟨hall _ h₁, hall _ h₂⟩


/--
The EFCI alternative set fails closure under conjunction when |D| ≥ 2.
The witness: {preExh(d₁), preExh(d₂)} ⊆ ALT but ⋀{preExh(d₁), preExh(d₂)} = ⊥.
-/
theorem efci_not_closed_witness
    (D : Domain Entity) (P : Entity → Prop' World)
    (d₁ d₂ : Entity) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hne : d₁ ≠ d₂) :
    let X := {preExhaustify D d₁ P, preExhaustify D d₂ P}
    X ⊆ efciAlternatives D P ∧
    (∀ w, ¬(bigConj X w)) := by
  constructor
  · intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    -- efciAlternatives = ({exists} ∪ scalar) ∪ preExhDomain
    rcases hφ with rfl | rfl
    · -- preExhaustify D d₁ P ∈ efciAlternatives D P
      apply Set.mem_union_right  -- get into preExhDomainAlts
      exact ⟨d₁, hd₁, rfl⟩
    · -- preExhaustify D d₂ P ∈ efciAlternatives D P
      apply Set.mem_union_right
      exact ⟨d₂, hd₂, rfl⟩
  · intro w hconj
    have h₁ : preExhaustify D d₁ P w := hconj _ (Set.mem_insert _ _)
    have h₂ : preExhaustify D d₂ P w := hconj _ (Set.mem_insert_of_mem _ rfl)
    exact preExh_pairwise_inconsistent D d₁ d₂ P hd₁ hd₂ hne w ⟨h₁, h₂⟩


/-!
## Connection to Spector's Theorem 9

Spector's main result: When ALT is closed under conjunction, exh_mw ≡ exh_ie.

For EFCI:
1. The full alternative set is not closed (theorem above)
2. Therefore Theorem 9 doesn't directly apply
3. Rescue mechanisms (modal insertion, partial exhaustification) can be
   understood as restoring consistency by pruning the alternative set
-/

/--
Pruning to scalar-only alternatives may restore closure properties.
The universal is in the scalar alt set.
-/
theorem scalar_only_contains_universal (D : Domain Entity) (P : Entity → Prop' World) :
    universalAlt D P ∈ scalarOnlyAlts D P := by
  apply Set.mem_union_right
  rfl

/--
Domain-only alternatives (scalar pruned) still have the inconsistency.
But under innocent exclusion, not all can be negated together.
-/
theorem domain_only_still_not_closed
    (D : Domain Entity) (P : Entity → Prop' World)
    (d₁ d₂ : Entity) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hne : d₁ ≠ d₂) :
    let X := {preExhaustify D d₁ P, preExhaustify D d₂ P}
    X ⊆ domainOnlyAlts D P ∧ (∀ w, ¬(bigConj X w)) := by
  constructor
  · intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl
    · apply Set.mem_union_right
      exact ⟨d₁, hd₁, rfl⟩
    · apply Set.mem_union_right
      exact ⟨d₂, hd₂, rfl⟩
  · intro w hconj
    have h₁ : preExhaustify D d₁ P w := hconj _ (Set.mem_insert _ _)
    have h₂ : preExhaustify D d₂ P w := hconj _ (Set.mem_insert_of_mem _ rfl)
    exact preExh_pairwise_inconsistent D d₁ d₂ P hd₁ hd₂ hne w ⟨h₁, h₂⟩


/-!
## The Root of the EFCI Explanation

The deep explanation for EFCI behavior has three parts:

### 1. Why Full Exhaustification Causes Contradiction

Pre-exhaustified domain alternatives are mutually exclusive:
- preExh(d) = "d is the unique satisfier"
- Two things can't both be the unique satisfier
- So ⋀_d preExh(d) = ⊥ for |D| ≥ 2

When we add scalar negation (¬∀), we get XOR.
XOR combined with the equivalence from domain negations yields ⊥.

### 2. Why Rescue Mechanisms Work

Modal insertion (irgendein):
- Insert ◇ above the existential
- Now ◇[preExh(d₁)] and ◇[preExh(d₂)] are compatible
- "Possibly only d₁, possibly only d₂" is consistent
- Result: Modal variation (at least two possibilities)

Partial exhaustification (yek-i):
- Prune scalar alternatives → only domain alternatives remain
- Under innocent exclusion: can't negate all domain alts
- (Negating preExh(d) for ALL d makes the prejacent false)
- Result: No negations added; uniqueness via pragmatic reasoning

### 3. Why Uniqueness Emerges in Root Contexts

For yek-i in root (no modal):
- Partial exh with domain-only yields: ∃x. P(x) (no negations)
- But the ALTERNATIVE SET still includes preExh(d) for each d
- Pragmatic reasoning: "Why did the speaker use yek-i (activating
  domain alternatives) if not to convey that exactly one satisfies P?"
- This is a secondary pragmatic inference, not from exhaustification

### Summary

The root explanation is mutual exclusivity of pre-exhaustified alternatives:
1. Full exhaustification → contradiction (because preExh alts conflict)
2. Modal insertion → compatibility under possibility
3. Partial exhaustification → no negations (IE can't negate consistently)
4. Uniqueness → pragmatic reasoning about alternative activation
-/

/--
The negation of a pre-exhaustified alternative.
¬preExh(d) = "d is not the unique satisfier"
           = "either ¬P(d) or ∃y≠d. P(y)"
-/
def notPreExh (D : Domain Entity) (d : Entity) (P : Entity → Prop' World) : Prop' World :=
  λ w => ¬(preExhaustify D d P w)

/--
The conjunction of negated pre-exhaustified alternatives.
This says "NO element is the unique satisfier" = "either none or ≥2 satisfy P".
-/
def allNotPreExh (D : Domain Entity) (P : Entity → Prop' World) : Prop' World :=
  λ w => ∀ d ∈ D, notPreExh D d P w

/--
allNotPreExh is false when exactly one element satisfies P.

If exactly d₀ satisfies P, then preExh(d₀) is TRUE (d₀ is unique),
so notPreExh(d₀) is FALSE, so allNotPreExh is FALSE.

This is why innocent exclusion can't negate ALL domain alternatives
while keeping the prejacent (∃x. P(x)) true with a unique witness.
-/
theorem unique_witness_falsifies_allNotPreExh
    (D : Domain Entity) (P : Entity → Prop' World) (d₀ : Entity)
    (hd₀ : d₀ ∈ D)
    (hPd₀ : ∀ w, P d₀ w)
    (hunique : ∀ w d, d ∈ D → d ≠ d₀ → ¬P d w) :
    ∀ w, ¬(allNotPreExh D P w) := by
  intro w hall
  have hpreExh : preExhaustify D d₀ P w := ⟨hPd₀ w, λ d hd hne => hunique w d hd hne⟩
  have hnotPreExh := hall d₀ hd₀
  exact hnotPreExh hpreExh


end NeoGricean.Exhaustivity.EFCIClosure
