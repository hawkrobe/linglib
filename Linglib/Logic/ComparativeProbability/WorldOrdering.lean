import Linglib.Logic.ComparativeProbability.Defs
import Linglib.Core.Order.Domination
import Mathlib.Data.Fintype.Powerset

/-!
# World-ordering semantics: the l-lifting as a comparative-probability model

[lewis-1973]'s comparative possibility lifts an ordering of worlds to an
ordering of propositions (`dominationLift`); [holliday-icard-2013] (§5) take it
as a semantics for comparative epistemic modals with complete logic WJR
([halpern-2003] Thm. 7.5.1). This file gives the model-theoretic content of that
completeness: a monotone, transitive comparison relation is an l-lifting of some
reflexive world relation **iff** it satisfies right-union (axiom `J`) and
determination by singletons.

## Main statements

* `strict_dominationLift_iff` — over a total world relation the strict lift is
  Lewis's ∃∀ clause.
* `exists_dominationLift_repr`, `dominationLift_repr_iff` — the WJR
  representation and its round trip.
-/

namespace ComparativeProbability

section

variable {α : Type*} {r : α → α → Prop}

/-- Over a **total** relation, the strict l-lifting collapses to Lewis's
∃∀ comparative possibility: some A-point strictly dominates every B-point. -/
theorem strict_dominationLift_iff (hTotal : ∀ a b, r a b ∨ r b a)
    (A B : Set α) :
    ComparativeProbability.Strict (dominationLift r) A B ↔
    ∃ a ∈ A, ∀ b ∈ B, r a b ∧ ¬ r b a := by
  constructor
  · rintro ⟨-, hn⟩
    unfold dominationLift at hn
    push Not at hn
    obtain ⟨a, haA, ha⟩ := hn
    exact ⟨a, haA, fun b hbB =>
      ⟨(hTotal a b).resolve_right (ha b hbB), ha b hbB⟩⟩
  · rintro ⟨a, haA, ha⟩
    refine ⟨fun b hbB => ⟨a, haA, (ha b hbB).1⟩, fun h => ?_⟩
    obtain ⟨b, hbB, hba⟩ := h a haA
    exact (ha b hbB).2 hba


end

/-- Helper: if ge A {b} for every b ∈ B, then ge A B, given monotonicity (T)
    and right-union (J). Proved by Finset induction on B.toFinset. -/
private lemma ge_of_forall_singleton {W : Type*} [Fintype W]
    {ge : Set W → Set W → Prop}
    (hT : ∀ A B : Set W, A ⊆ B → ge B A)
    (hJ : RightUnion ge)
    (A B : Set W) (h : ∀ b ∈ B, ge A {b}) : ge A B := by
  classical
  suffices ∀ (s : Finset W), (∀ b, b ∈ s → ge A {b}) → ge A (↑s) by
    rw [← Set.coe_toFinset B]
    exact this B.toFinset (fun b hb => h b (Set.mem_toFinset.mp hb))
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty]
    exact hT ∅ A (Set.empty_subset A)
  | @insert b s hbs ih =>
    intro hsub
    rw [Finset.coe_insert]
    exact hJ A _ _ (hsub _ (Finset.mem_insert_self _ _))
      (ih (fun c hc => hsub c (Finset.mem_insert_of_mem hc)))

/-- **Theorem 2** ([halpern-2003], Thm. 7.5.1a; [holliday-icard-2013]):
    a monotone, transitive comparison relation satisfying J (right-union)
    and DS (determination by singletons) is representable by Lewis's l-lifting
    from a reflexive preorder on worlds.

    The paper states this as a *logic* completeness theorem for **WJR**
    (K + BT + Tran + J + Mon + R). We prove the underlying per-model
    *representation* result, which is the model-theoretic core: the semantic
    hypotheses correspond to WJR's axioms evaluated on a single model, without
    formalizing the syntax or proof system.

    Construction: `ge_w u v := ge {u} {v}`. -/
theorem exists_dominationLift_repr {W : Type*} [Fintype W]
    {ge : Set W → Set W → Prop}
    (hMono : ∀ A B : Set W, A ⊆ B → ge B A)
    (hTran : ∀ A B C : Set W, ge A B → ge B C → ge A C)
    (hJ : RightUnion ge) (hDS : DeterminedBySingletons ge) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w),
      ∀ A B, ge A B ↔ dominationLift ge_w A B := by
  refine ⟨fun u v => ge {u} {v}, fun w => hMono {w} {w} subset_rfl, fun A B => ?_⟩
  constructor
  · intro hAB b hbB
    have hBb : ge B {b} := hMono {b} B (Set.singleton_subset_iff.mpr hbB)
    exact hDS A b (hTran A B {b} hAB hBb)
  · intro hLift
    apply ge_of_forall_singleton hMono hJ A B
    intro b hbB
    obtain ⟨a, haA, hab⟩ := hLift b hbB
    have hAa : ge A {a} := hMono {a} A (Set.singleton_subset_iff.mpr haA)
    exact hTran A {a} {b} hAa hab

/-- Round trip of `exists_dominationLift_repr`: a monotone, transitive
    comparison relation is representable by Lewis's l-lifting **iff** it
    satisfies right-union and determination by singletons — the
    model-theoretic form of soundness and completeness for WJR
    ([holliday-icard-2013]; [halpern-2003] Thm. 7.5.1). Soundness transfers
    `dominationLift_rightUnion` and `dominationLift_determinedBySingletons`
    across the representation. -/
theorem dominationLift_repr_iff {W : Type*} [Fintype W]
    {ge : Set W → Set W → Prop}
    (hMono : ∀ A B : Set W, A ⊆ B → ge B A)
    (hTran : ∀ A B C : Set W, ge A B → ge B C → ge A C) :
    (∃ ge_w : W → W → Prop, (∀ w, ge_w w w) ∧
      ∀ A B, ge A B ↔ dominationLift ge_w A B) ↔
    RightUnion ge ∧ DeterminedBySingletons ge := by
  constructor
  · rintro ⟨ge_w, -, hiff⟩
    refine ⟨fun A B C hab hac => ?_, fun A b hA => ?_⟩
    · exact (hiff _ _).mpr (dominationLift_rightUnion _ _ _
        ((hiff _ _).mp hab) ((hiff _ _).mp hac))
    · obtain ⟨a, ha, hab⟩ := dominationLift_determinedBySingletons A b ((hiff _ _).mp hA)
      exact ⟨a, ha, (hiff _ _).mpr hab⟩
  · rintro ⟨hJ, hDS⟩
    obtain ⟨ge_w, hrefl, hiff⟩ := exists_dominationLift_repr hMono hTran hJ hDS
    exact ⟨ge_w, hrefl, hiff⟩


end ComparativeProbability
