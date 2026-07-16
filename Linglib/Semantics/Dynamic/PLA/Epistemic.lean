import Linglib.Semantics.Dynamic.PLA.Update
import Linglib.Semantics.Intensional.Rigidity

/-!
# PLA epistemic operators

Epistemic modals for PLA, from [dekker-2012]'s chapter on quantification and
modality. Unlike assertoric updates, `might` and `must` are tests in the sense
of [veltman-1996]: `might φ` passes an information state iff `φ` is consistent
with it, `must φ` iff the state supports `φ`; neither eliminates possibilities.
For de re vs de dicto distinctions, `PLA.Concept` instantiates
`Intensional.Intension` at PLA possibilities: a way of identifying entities
across assignment-witness pairs.

## Main definitions

- `PLA.Formula.might`, `PLA.Formula.must`: epistemic tests on information
  states
- `PLA.Concept`, `PLA.Concept.isRigid`: concepts over PLA possibilities

## Main results

- `PLA.might_iff_consistent`, `PLA.must_iff_supports`: test characterizations
- `PLA.might_idempotent`, `PLA.must_idempotent`: testing twice is testing once
- `PLA.might_iff_not_must_neg`: the dynamic version of the modal duality
  ◇φ ↔ ¬□¬φ
-/

namespace PLA

open Classical
open DynamicSemantics.CCP

variable {E : Type*} (M : Model E)

/--
Might φ: φ is consistent with the information state.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

This is a TEST: it doesn't eliminate possibilities, it checks if φ is possible.
-/
def Formula.might (φ : Formula) : Update E :=
  λ s => if (φ.update M s).Nonempty then s else ∅

/--
Must φ: φ is supported by the information state.

⟦must φ⟧(s) = s if s ⊫[M] φ, else ∅

This is also a TEST: it passes only if φ is certain.
-/
def Formula.must (φ : Formula) : Update E :=
  λ s => if s ⊫[M] φ then s else ∅


/--
Might as consistency test: might φ passes iff some possibility satisfies φ.
-/
theorem might_iff_consistent (φ : Formula) (s : InfoState E) :
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
theorem must_iff_supports (φ : Formula) (s : InfoState E) :
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
theorem might_preserves_info (φ : Formula) (s : InfoState E)
    (h : (φ.update M s).Nonempty) :
    φ.might M s = s := by
  simp only [Formula.might, if_pos h]

theorem must_preserves_info (φ : Formula) (s : InfoState E) (h : s ⊫[M] φ) :
    φ.must M s = s := by
  simp only [Formula.must, if_pos h]

/--
[veltman-1996]: Tests never add possibilities.
-/
theorem might_subset (φ : Formula) (s : InfoState E) :
    φ.might M s ⊆ s := by
  simp only [Formula.might]
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.empty_subset s

theorem must_subset (φ : Formula) (s : InfoState E) :
    φ.must M s ⊆ s := by
  simp only [Formula.must]
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.empty_subset s


/--
Asserting then testing: φ; might ψ passes iff φ-update leaves room for ψ.
-/
theorem update_then_might (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.might M) s = ψ.might M (φ.update M s) := rfl

/--
Asserting then requiring: φ; must ψ passes iff φ-update supports ψ.
-/
theorem update_then_must (φ ψ : Formula) (s : InfoState E) :
    (φ.update M ;; ψ.must M) s = ψ.must M (φ.update M s) := rfl


/--
Must idempotence: must (must φ) ≡ must φ

Once we've verified certainty, re-checking doesn't change anything.
-/
theorem must_idempotent (φ : Formula) (s : InfoState E) :
    φ.must M (φ.must M s) = φ.must M s := by
  simp only [Formula.must]
  by_cases hsup : s ⊫[M] φ
  · simp only [if_pos hsup]
  · simp only [if_neg hsup, InfoState.empty_supports, ↓reduceIte]

/--
Might idempotence: might (might φ) ≡ might φ

Testing for consistency twice is the same as testing once.
-/
theorem might_idempotent (φ : Formula) (s : InfoState E) :
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
theorem supports_implies_might (φ : Formula) (s : InfoState E)
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
Modal duality: might φ passes iff must ¬φ fails (on nonempty states).

`might φ` passes on s ↔ `must ¬φ` fails on s (i.e., s does not support ¬φ).
This is the dynamic version of the classical duality ◇φ ↔ ¬□¬φ.
-/
theorem might_iff_not_must_neg (φ : Formula) (s : InfoState E) (hs : s.Nonempty) :
    φ.might M s = s ↔ (∼φ).must M s ≠ s := by
  rw [ne_eq, might_iff_consistent, must_iff_supports]
  simp only [Set.nonempty_iff_ne_empty.mp hs, or_false]
  constructor
  · rintro ⟨⟨g, ê⟩, hp⟩ hsup
    rw [Formula.mem_update] at hp
    exact hsup _ hp.1 hp.2
  · intro h
    simp only [InfoState.supports, DynamicSemantics.supportOf, satisfiesPLA,
      Formula.sat, not_forall, Classical.not_not] at h
    obtain ⟨p, hp, hsat⟩ := h
    exact ⟨p, (Formula.mem_update M φ s p.1 p.2).mpr ⟨hp, hsat⟩⟩


/--
A concept is a way of identifying entities across possibilities.

PLA-specific instance of `Intensional.Intension`: the index is an
`(Assignment E × WitnessSeq E)` pair (a PLA possibility), and the value
is an entity. This is the entity-side counterpart of Abusch 1997's
`Intension (KContext W E P T) T` time-concept (`Semantics/Tense/DeRe.lean`).
-/
abbrev Concept (E : Type*) := Intensional.Intension (Assignment E × WitnessSeq E) E

/--
A rigid concept identifies the same entity in all possibilities.
Alias for `Intensional.Intension.IsRigid` at the PLA index.
-/
abbrev Concept.isRigid (c : Concept E) : Prop :=
  Intensional.Intension.IsRigid c

/--
A descriptive concept may identify different entities.
-/
def Concept.isDescriptive (c : Concept E) : Prop :=
  ¬c.isRigid

/--
Constant concept: always refers to the same entity (proper names).
Alias for `Intensional.Intension.rigid` at the PLA index.
-/
abbrev Concept.const (e : E) : Concept E := Intensional.Intension.rigid e

theorem const_is_rigid (e : E) : (Concept.const e).isRigid :=
  Intensional.Intension.rigid_isRigid e

/--
Variable concept: looks up a variable in the assignment.
-/
def Concept.fromVar (i : VarIdx) : Concept E := λ p => p.1 i

/--
Pronoun concept: looks up a pronoun in the witness sequence.
-/
def Concept.fromPron (i : PronIdx) : Concept E := λ p => p.2 i


/-!
## Relationship to [kratzer-1981] Modal Semantics
[kratzer-1981]

PLA's epistemic operators share deep structure with Kratzer's modal semantics
from `Semantics.Modality.Kratzer`. Both frameworks implement:

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

See `Semantics.Modality.Kratzer` for the full Kratzer framework with:
- Modal base and ordering source
- Preorder on worlds (`kratzerPreorder`)
- Frame correspondence theorems (T, D, 4, B, 5 axioms)
- Galois connection (extension/intension duality)
-/

end PLA
