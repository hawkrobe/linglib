/-
# PLA Epistemic Operators

Dekker (2012) Chapter 4: Epistemic and doxastic modals.

## Key Concepts

### Epistemic Modality
- Might φ: φ is compatible with current information
- Must φ: φ follows from current information

### The Test Semantics
Unlike assertoric updates that eliminate possibilities, epistemic modals
TEST the information state:
- might φ passes if some (g, ê) satisfies φ
- must φ passes if all (g, ê) satisfy φ

### Conceptual Covers (Dekker §4.3)
For de re/de dicto distinctions:
- A peg is an extensional reference to an entity
- A concept is an intensional way of identifying entities

## References

- Dekker, P. (2012). Dynamic Semantics. Springer. Chapter 4.
- Veltman, F. (1996). Defaults in Update Semantics.
-/

import Linglib.Theories.DynamicSemantics.Systems.PLA.Update

namespace DynamicSemantics.PLA

open Classical


variable {E : Type*} [Nonempty E]

/--
Might φ: φ is consistent with the information state.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

This is a TEST: it doesn't eliminate possibilities, it checks if φ is possible.
-/
def Formula.might (M : Model E) (φ : Formula) : Update E :=
  λ s => if (φ.update M s).Nonempty then s else ∅

/--
Must φ: φ is supported by the information state.

⟦must φ⟧(s) = s if s ⊫[M] φ, else ∅

This is also a TEST: it passes only if φ is certain.
-/
def Formula.must (M : Model E) (φ : Formula) : Update E :=
  λ s => if s ⊫[M] φ then s else ∅


/--
Might as consistency test: might φ passes iff some possibility satisfies φ.
-/
theorem might_iff_consistent (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.might M s = s ↔ (φ.update M s).Nonempty ∨ s = ∅ := by
  simp only [Formula.might]
  constructor
  · intro h
    by_cases hne : (φ.update M s).Nonempty
    · left; exact hne
    · simp only [if_neg hne] at h
      right; exact h.symm
  · intro h
    cases h with
    | inl hne => simp only [if_pos hne]
    | inr hemp =>
      simp only [hemp, Formula.update, InfoState.restrict, Set.sep_empty,
                 Set.not_nonempty_empty, ↓reduceIte]

/--
Must as support test: must φ passes iff the state supports φ.
-/
theorem must_iff_supports (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.must M s = s ↔ (s ⊫[M] φ) ∨ s = ∅ := by
  simp only [Formula.must]
  constructor
  · intro h
    by_cases hsup : s ⊫[M] φ
    · left; exact hsup
    · simp only [if_neg hsup] at h
      right; exact h.symm
  · intro h
    cases h with
    | inl hsup => simp only [if_pos hsup]
    | inr hemp => simp only [hemp, InfoState.empty_supports, ↓reduceIte]


/--
Testing doesn't change information (when it passes).
-/
theorem might_preserves_info (M : Model E) (φ : Formula) (s : InfoState E)
    (h : (φ.update M s).Nonempty) :
    φ.might M s = s := by
  simp only [Formula.might, if_pos h]

theorem must_preserves_info (M : Model E) (φ : Formula) (s : InfoState E)
    (h : s ⊫[M] φ) :
    φ.must M s = s := by
  simp only [Formula.must, if_pos h]

/--
Veltman (1996): Tests never add possibilities.
-/
theorem might_subset (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.might M s ⊆ s := by
  simp only [Formula.might]
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.empty_subset s

theorem must_subset (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.must M s ⊆ s := by
  simp only [Formula.must]
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.empty_subset s


/--
Asserting then testing: φ ; might ψ passes iff φ-update leaves room for ψ.
-/
theorem update_then_might (M : Model E) (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.might M) s = ψ.might M (φ.update M s) := rfl

/--
Asserting then requiring: φ ; must ψ passes iff φ-update supports ψ.
-/
theorem update_then_must (M : Model E) (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.must M) s = ψ.must M (φ.update M s) := rfl


/--
Must idempotence: must (must φ) ≡ must φ

Once we've verified certainty, re-checking doesn't change anything.
-/
theorem must_idempotent (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.must M (φ.must M s) = φ.must M s := by
  simp only [Formula.must]
  by_cases hsup : s ⊫[M] φ
  · simp only [if_pos hsup]
  · simp only [if_neg hsup, InfoState.empty_supports, ↓reduceIte]

/--
Might idempotence: might (might φ) ≡ might φ

Testing for consistency twice is the same as testing once.
-/
theorem might_idempotent (M : Model E) (φ : Formula) (s : InfoState E) :
    φ.might M (φ.might M s) = φ.might M s := by
  simp only [Formula.might]
  by_cases hne : (φ.update M s).Nonempty
  · simp only [if_pos hne]
  · simp only [if_neg hne]
    simp only [Formula.update, InfoState.restrict, Set.sep_empty, Set.not_nonempty_empty,
               ↓reduceIte]


/--
If s supports φ, then might φ passes.
-/
theorem supports_implies_might (M : Model E) (φ : Formula) (s : InfoState E)
    (hs : s.Nonempty) (hsup : s ⊫[M] φ) :
    φ.might M s = s := by
  simp only [Formula.might]
  have hne : (φ.update M s).Nonempty := by
    obtain ⟨p, hp⟩ := hs
    use p
    simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq]
    exact ⟨hp, hsup p hp⟩
  simp only [if_pos hne]

/--
If s supports φ, then must φ passes.
-/
theorem supports_implies_must (M : Model E) (φ : Formula) (s : InfoState E)
    (hsup : s ⊫[M] φ) :
    φ.must M s = s := by
  simp only [Formula.must, if_pos hsup]


/--
might φ ≈ ¬must ¬φ

φ is possible iff ¬φ is not necessary.
-/
theorem might_not_must_neg (M : Model E) (φ : Formula) (s : InfoState E)
    (hs : s.Nonempty) :
    (φ.might M s).Nonempty ↔ ¬((∼φ).must M s = s ∧ s.Nonempty) ∨ ¬(s ⊫[M] (∼φ)) := by
  simp only [Formula.might, Formula.must]
  constructor
  · intro h
    split_ifs at h with hne
    · -- might passed
      right
      intro hsup_neg
      -- hsup_neg : s ⊫[M] (∼φ) means ∀ p ∈ s, ¬φ.sat
      simp only [InfoState.supports, Formula.sat] at hsup_neg
      -- But hne says φ.update M s is nonempty
      obtain ⟨p, hp⟩ := hne
      simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq] at hp
      exact hsup_neg p hp.1 hp.2
    · exact absurd h Set.not_nonempty_empty
  · intro h
    split_ifs with hne
    · exact hs
    · cases h with
      | inl hnot =>
        by_cases hsup_neg : s ⊫[M] (∼φ)
        · simp only [if_pos hsup_neg, hs, and_self, not_true_eq_false] at hnot
        · simp only [Set.not_nonempty_iff_eq_empty] at hne
          -- If update is empty and s is nonempty, then ∀ p ∈ s, ¬φ.sat
          have : s ⊫[M] (∼φ) := by
            intro p hp
            simp only [Formula.sat]
            intro hsat
            have : p ∈ φ.update M s := by
              simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq]
              exact ⟨hp, hsat⟩
            rw [hne] at this
            exact this
          exact absurd this hsup_neg
      | inr hnot =>
        simp only [Set.not_nonempty_iff_eq_empty] at hne
        have : s ⊫[M] (∼φ) := by
          intro p hp
          simp only [Formula.sat]
          intro hsat
          have : p ∈ φ.update M s := by
            simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq]
            exact ⟨hp, hsat⟩
          rw [hne] at this
          exact this
        exact absurd this hnot


/--
A concept is a way of identifying entities across possibilities.

In the simplest case, a concept is a function from (g, ê) pairs to entities.
-/
abbrev Concept (E : Type*) := (Assignment E × WitnessSeq E) → E

/--
A rigid concept identifies the same entity in all possibilities.
-/
def Concept.isRigid (c : Concept E) : Prop :=
  ∀ p q, c p = c q

/--
A descriptive concept may identify different entities.
-/
def Concept.isDescriptive (c : Concept E) : Prop :=
  ¬c.isRigid

/--
Constant concept: always refers to the same entity (proper names).
-/
def Concept.const (e : E) : Concept E := λ _ => e

omit [Nonempty E] in
theorem const_is_rigid (e : E) : (Concept.const e).isRigid := λ _ _ => rfl

/--
Variable concept: looks up a variable in the assignment.
-/
def Concept.fromVar (i : VarIdx) : Concept E := λ p => p.1 i

/--
Pronoun concept: looks up a pronoun in the witness sequence.
-/
def Concept.fromPron (i : PronIdx) : Concept E := λ p => p.2 i


/-!
## Relationship to Kratzer (1981) Modal Semantics

PLA's epistemic operators share deep structure with Kratzer's modal semantics
from `IntensionalSemantics.Modal.Kratzer`. Both frameworks implement:

### Common Pattern: Necessity as Universal Quantification

| Framework | Necessity | Domain |
|-----------|-----------|--------|
| Kratzer | `∀w' ∈ accessible(w). φ(w')` | Worlds |
| PLA | `∀(g,ê) ∈ s. φ.sat M g ê` | (Assignment, Witness) pairs |

### Key Structural Similarities

1. Modal base ≈ information state
   - Kratzer: Modal base `f(w)` determines accessible worlds via `∩f(w)`
   - PLA: Information state `s` is the set of live possibilities

2. Necessity as test
   - Kratzer: `□φ` tests if φ holds at all best worlds
   - PLA: `must φ` tests if state supports φ (all possibilities satisfy φ)

3. Possibility as consistency
   - Kratzer: `◇φ` tests if some accessible world satisfies φ
   - PLA: `might φ` tests if some possibility in s satisfies φ

4. Duality
   - Both satisfy: `might φ ≈ ¬must ¬φ`

### Key Difference: Dynamic Dimension

PLA adds state transformation that Kratzer's propositional semantics lacks:
- Kratzer modals are purely propositional (`World → Bool`)
- PLA operators are state transformers (`InfoState → InfoState`)

This allows PLA to model:
- Discourse referent introduction
- Cross-sentential anaphora
- Dynamic conjunction (non-commutative)

### Theoretical Unification

The relationship can be made precise: if we "freeze" the assignment and
witness sequence, PLA's support relation reduces to Kratzer-style necessity
over the remaining possibilities.

See `IntensionalSemantics.Modal.Kratzer` for the full Kratzer framework with:
- Modal base and ordering source
- Preorder on worlds (`kratzerPreorder`)
- Frame correspondence theorems (T, D, 4, B, 5 axioms)
- Galois connection (extension/intension duality)
-/

end DynamicSemantics.PLA
