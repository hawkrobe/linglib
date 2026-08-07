import Linglib.Semantics.Dynamic.DRS.Verification
import Linglib.Semantics.Dynamic.DRS.Reduction
import Linglib.Semantics.Dynamic.Update

/-!
# The box relation: dynamic face of DRS verification

The relational (input–output) face of the unified verification semantics
(`DRS/Verification.lean`): the *box relation* `K.toRel a a'` holds when the
output `a'` extends the input `a` across `K` and verifies `K`, and a DRS is
*true* under an input iff some output is related to it (the spine's anaphoric
`closure`). This is [muskens-1996]'s SEM3 format (input → output, the format
of [groenendijk-stokhof-1991]), definable in one line from verification —
Muskens's remark that his relational interpretation "is in fact equivalent"
to the standard one (his fn. 3–4 scope it: constant-free constructs, and both
sides in the total-assignment rendering; see the deviation note in
`DRS/Verification.lean`). His SEM1/2 clauses — complex conditions as the
spine connectives `neg`/`impl`/`disj` on box relations — are derived
characterizations (`verifies_neg_toRel`, …), connecting DRS verification to
the connective algebra shared across the dynamic-semantics spine.

## Main declarations

* `DRS.toRel` — the box relation; `DRS.trueRel` — relational truth, its
  `closure`.
* `Embedding.verifies_neg_toRel` (`_imp_`, `_dis_`) — complex conditions are
  the spine connectives on box relations (SEM1/2).
* `DRS.trueRel_iff_realize_toFormula` — dynamic truth equals the first-order
  translation's `Realize` (`DRS/Reduction.lean`).
* `DRS.trueRel_congr` — coincidence: truth reads the input only at the
  occurring referents.
* `DRS.toRel_merge` — the Merging Lemma: under freshness, `merge` denotes the
  spine sequencing `Update.seq` of the two box relations.
* `DRS.trueRel_map` — alphabetic variants have the same truth conditions.

## Implementation notes

Naming: the relational face (`toRel`, `trueRel`) follows the spine's
lowerCamel operation names (`neg`, `seq`, `closure`); verification
(`Embedding.Verifies`, `DRS/Verification.lean`) uses the field's own verb, and
the first-order reduction (`DRS/Reduction.lean`) speaks mathlib's
`Formula.Realize`.
-/

open FirstOrder FirstOrder.Language
open DynamicSemantics (Update)
open DynamicSemantics.Update (neg impl disj closure seq)

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-! ### The box relation -/

/-- The box relation (SEM3): the output `a'` extends the input `a` across `K`
and verifies `K`. -/
def DRS.toRel (K : DRS L V) : Update (V → M) :=
  fun a a' => K.Extends a a' ∧ Embedding.Verifies a' K

@[simp] theorem DRS.toRel_iff (K : DRS L V) (a a' : Embedding V M) :
    DRS.toRel K a a' ↔ K.Extends a a' ∧ a'.Verifies K := Iff.rfl

/-- A DRS is *true* under an input embedding `a` iff some output embedding is
related to it — the spine's anaphoric `closure`. -/
def DRS.trueRel (K : DRS L V) (a : V → M) : Prop := closure (DRS.toRel K) a

/-- `trueRel` unfolded: some output embedding is related to the input. -/
theorem DRS.trueRel_iff (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ ∃ a', DRS.toRel K a a' := Iff.rfl

/-! ### The spine connectives (SEM1/2) -/

/-- A negated sub-DRS is the spine's `neg` of its box relation. -/
theorem Embedding.verifies_neg_toRel (K : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.neg K) ↔ neg (DRS.toRel K) f := by
  simp only [Embedding.verifies_neg]; rfl

/-- A conditional is the spine's `impl` of the boxes' relations. -/
theorem Embedding.verifies_imp_toRel (a c : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.imp a c) ↔ impl (DRS.toRel a) (DRS.toRel c) f := by
  simp only [Embedding.verifies_imp, impl, DRS.toRel, and_imp]

/-- A disjunction is the spine's `disj` of the boxes' relations. -/
theorem Embedding.verifies_dis_toRel (l r : DRS L V) (f : Embedding V M) :
    f.VerifiesCondition (.dis l r) ↔ disj (DRS.toRel l) (DRS.toRel r) f := by
  simp only [Embedding.verifies_dis, disj]
  exact exists_or.symm

/-! ### Truth: the triangle, coincidence, and alphabetic variants -/

/-- The dynamic truth of a DRS equals its first-order translation's `Realize`
— the third edge of the `Verifies`/`toFormula`/`toRel` triangle. -/
theorem DRS.trueRel_iff_realize_toFormula [DecidableEq V] (K : DRS L V) (a : V → M) :
    DRS.trueRel K a ↔ (K.toFormula).Realize a :=
  (DRS.realize_toFormula K a).symm

/-- **Coincidence**: truth reads the input embedding only at the occurring
referents. -/
theorem DRS.trueRel_congr [DecidableEq V] {K : DRS L V} {a₁ a₂ : V → M}
    (h : Set.EqOn a₁ a₂ ↑(DRS.occ K)) : DRS.trueRel K a₁ ↔ DRS.trueRel K a₂ :=
  Embedding.exists_extends_verifies_congr h

/-- Renaming along a bijection transports dynamic truth: alphabetic variants
have the same truth conditions. -/
theorem DRS.trueRel_map {W : Type*} [DecidableEq W] (e : V ≃ W)
    (K : DRS L V) (a : Embedding W M) :
    DRS.trueRel (K.map e) a ↔ DRS.trueRel K (a ∘ e) :=
  Embedding.exists_extends_verifies_map e a K

/-! ### The merging lemma: sequencing is merge, under freshness -/

/-- **Merging Lemma** (§II.2): when `K₂`'s universe is fresh
for `K₁`'s conditions, the merge `K₁ ⊕ K₂` denotes the spine sequencing
(relational composition) of the two box relations — `‖K₁ ⊕ K₂‖ = seq ‖K₁‖ ‖K₂‖`.
This is what gives `merge` its dynamic meaning. -/
theorem DRS.toRel_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.occL K₁.conditions)) :
    (DRS.toRel (K₁.merge K₂) : Update (V → M)) = seq (DRS.toRel K₁) (DRS.toRel K₂) := by
  obtain ⟨U₁, conds₁⟩ := K₁
  obtain ⟨U₂, conds₂⟩ := K₂
  simp only [DRS.referents_mk, DRS.conditions_mk, Finset.disjoint_left] at hfresh
  funext a a'
  apply propext
  simp only [DRS.toRel, DRS.Extends, DRS.merge, DRS.referents_mk, DRS.conditions_mk,
    Embedding.verifies_mk, List.forall_mem_append, seq, Relation.Comp]
  constructor
  · rintro ⟨hag, hh₁, hh₂⟩
    refine ⟨U₂.piecewise a a', ⟨?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      by_cases hxU2 : x ∈ U₂
      · rw [Finset.piecewise_eq_of_mem _ _ _ hxU2]
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU2]
        refine hag x ?_
        rw [Finset.mem_union, not_or]
        exact ⟨hx, hxU2⟩
    · intro c hc
      refine (Embedding.verifiesCondition_congr c fun x hx => ?_).mpr (hh₁ c hc)
      exact Finset.piecewise_eq_of_notMem _ _ _
        (fun hU => hfresh hU (Condition.occ_subset_occL hc (Finset.mem_coe.mp hx)))
    · intro x hx
      exact (Finset.piecewise_eq_of_notMem _ _ _ hx).symm
    · exact hh₂
  · rintro ⟨a'', ⟨hag1, hh1⟩, hag2, hh2⟩
    refine ⟨?_, ?_, hh2⟩
    · intro x hx
      rw [Finset.mem_union, not_or] at hx
      rw [hag2 x hx.2, hag1 x hx.1]
    · intro c hc
      refine (Embedding.verifiesCondition_congr c fun x hx => ?_).mpr (hh1 c hc)
      exact hag2 x fun hU => hfresh hU (Condition.occ_subset_occL hc (Finset.mem_coe.mp hx))

end DRT
