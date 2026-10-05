module

public import Linglib.Semantics.Dynamic.DRS.Verification
public import Linglib.Semantics.Dynamic.DRS.Reduction
public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# The box relation: dynamic face of DRS verification

The box relation of a DRS relates an input embedding to the outputs that agree with it off the
universe and verify the DRS. It is the box `Update.box` of
`Semantics/Dynamic/RegisterStructure.lean` over the universe, at the register structure of
embeddings, so Muskens's relational semantics of DRT is the general one of boxes. A DRS is true under an input when some output is related to it.

## Main declarations

* `DRS.toRel`: the box relation; `DRS.trueRel`: truth, its domain.
* `Embedding.verifies_neg_toRel` (`_imp_`, `_dis_`): complex conditions are the connectives of
  `Update` on box relations.
* `DRS.trueRel_iff_realize_toFormula`: dynamic truth is the truth of the first-order
  translation (`DRS/Reduction.lean`).
* `DRS.trueRel_congr`: truth reads the input only at the occurring referents.
* `DRS.toRel_merge`: under freshness, `merge` denotes the composition of the box relations, as
  an instance of the semantic Merging Lemma `Update.box_comp_box`.
* `DRS.trueRel_map`: alphabetic variants have the same truth conditions.

## Implementation notes

Muskens scopes the agreement of his relational semantics with the standard one to constructs
without constants, both in total-assignment form (fn. 3–4; see `DRS/Verification.lean`).

## References

* [muskens-1996]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics (Update RegisterStructure)
open DynamicSemantics.Update (neg impl disj box box_comp_box mem_box_iff)
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M] [DecidableEq V]

/-! ### The box relation -/

/-- The box relation of a DRS (SEM3) is the box over its universe testing its conditions. -/
def DRS.toRel (K : DRS L V) : Update (V → M) :=
  box K.referents {a | Embedding.Verifies a K}

/-- The box relation relates an input to the outputs that extend it across the universe and
verify the DRS. -/
@[simp] theorem DRS.toRel_iff (K : DRS L V) (a a' : Embedding V M) :
    a ~[DRS.toRel K] a' ↔ K.Extends a a' ∧ a'.Verifies K :=
  mem_box_iff

/-- A DRS is *true* under an input embedding `a` iff some output embedding is
related to it, the domain of the box relation. -/
def DRS.trueRel (K : DRS L V) (a : V → M) : Prop := a ∈ (DRS.toRel K).dom

/-- A DRS is true under an input iff some output embedding is related to it. -/
theorem DRS.trueRel_iff (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', a ~[DRS.toRel K] a' := Iff.rfl

/-- A DRS is true under an input iff some extension of the input across the universe verifies
it. -/
theorem DRS.trueRel_iff_exists_extends (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', K.Extends a a' ∧ a'.Verifies K := by
  simp only [DRS.trueRel_iff, DRS.toRel_iff]

/-! ### The spine connectives (SEM1/2) -/

/-- A negated sub-DRS is the spine's `neg` of its box relation. -/
theorem Embedding.verifies_neg_toRel (K : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.neg K) ↔ f ∈ neg (DRS.toRel K) := by
  simp only [Embedding.verifies_neg, DynamicSemantics.Update.mem_neg, DRS.toRel_iff]

/-- A conditional is the spine's `impl` of the boxes' relations. -/
theorem Embedding.verifies_imp_toRel (a c : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.imp a c) ↔ f ∈ impl (DRS.toRel a) (DRS.toRel c) := by
  simp only [Embedding.verifies_imp, DynamicSemantics.Update.mem_impl, DRS.toRel_iff, and_imp]

/-- A disjunction is the spine's `disj` of the boxes' relations. -/
theorem Embedding.verifies_dis_toRel (l r : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.dis l r) ↔ f ∈ disj (DRS.toRel l) (DRS.toRel r) := by
  simp only [Embedding.verifies_dis, DynamicSemantics.Update.mem_disj, DRS.toRel_iff]

/-! ### Truth: the triangle, coincidence, and alphabetic variants -/

/-- The dynamic truth of a DRS equals its first-order translation's `Realize`
— the third edge of the `Verifies`/`toFormula`/`toRel` triangle. -/
theorem DRS.trueRel_iff_realize_toFormula (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ (K.toFormula).Realize a :=
  (DRS.trueRel_iff_exists_extends K a).trans (DRS.realize_toFormula K a).symm

/-- Truth reads the input embedding only at the occurring referents. -/
theorem DRS.trueRel_congr {K : DRS L V} {a₁ a₂ : V → M}
    (h : Set.EqOn a₁ a₂ ↑(DRS.varFinset K)) : DRS.trueRel K a₁ ↔ DRS.trueRel K a₂ := by
  simpa only [DRS.trueRel_iff_exists_extends] using Embedding.exists_extends_verifies_congr h

/-- Renaming along a bijection transports dynamic truth, so alphabetic variants have the same
truth conditions. -/
theorem DRS.trueRel_map {W : Type*} [DecidableEq W] (e : V ≃ W)
    (K : DRS L V) (a : Embedding W M) :
    DRS.trueRel (K.map e) a ↔ DRS.trueRel K (a ∘ e) := by
  simpa only [DRS.trueRel_iff_exists_extends] using Embedding.exists_extends_verifies_map e a K

/-! ### The merging lemma: sequencing is merge, under freshness -/

/-- When `K₂`'s universe is fresh for `K₁`'s conditions, the merge `K₁ ⊕ K₂` denotes the
composition of the two box relations (the Merging Lemma of §II.2). It is the semantic Merging
Lemma `Update.box_comp_box`, since freshness puts `K₂`'s referents outside the dimension set of
`K₁`'s conditions. -/
theorem DRS.toRel_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions)) :
    (DRS.toRel (K₁.merge K₂) : Update (V → M)) = DRS.toRel K₁ ○ DRS.toRel K₂ := by
  rw [DRS.toRel, DRS.toRel, DRS.toRel, box_comp_box fun r hr ↦ ?_]
  · congr 1
    ext a
    simp
  · rw [RegisterStructure.notMem_dimSet_iff]
    intro g e
    simp only [Set.mem_ofPred_eq, RegisterStructure.extend_eq_update, Embedding.verifies_iff]
    refine forall₂_congr fun c hc ↦ Embedding.verifiesCondition_congr c fun y hy ↦ ?_
    refine Function.update_of_ne (fun hyr ↦ Finset.disjoint_left.1 hfresh hr ?_) e g
    exact hyr ▸ Condition.varFinset_subset_varFinsetL hc (Finset.mem_coe.1 hy)

end DRT
