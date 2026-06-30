import Linglib.Core.Order.ComparativeProbability.Patterns
import Linglib.Core.Order.ComparativeProbability.Systems
import Mathlib.Data.Set.Card

/-!
# Epistemic Entailment Patterns ([holliday-icard-2013], Figure 1)

[holliday-icard-2013] [harrison-trainor-holliday-icard-2018] [yalcin-2010] [lewis-1973]
[halpern-2003]

[holliday-icard-2013] Figure 1 lists 10 validity patterns (V1–V7, V11–V13)
and 3 invalidity patterns (I1–I3) for epistemic comparatives. (V8–V10 are from
[yalcin-2010] and omitted from H&I's condensed figure.) This file defines
each pattern as a `Prop`-valued predicate on a comparison relation `ge`, then
proves which patterns hold (or fail) in each of four semantic classes:

| Pattern | Measure (FP∞) | Qualitative (FA) | l-lifting (W) | m-lifting     |
|---------|:-------------:|:----------------:|:-------------:|:-------------:|
| V1      | ✓             | ✓                | ✓             | ✓             |
| V2      | ✓             | ✓                | ✓             | ✓             |
| V3      | ✓             | ✓                | ✓             | ✓             |
| V4      | ✓             | ✓                | ✓             | ✓             |
| V5      | ✓             | ✓                | ✓             | ✓             |
| V6      | ✓             | ✓                | ✓             | ✓             |
| V7      | ✓             | ✓                | ✓             | ✓             |
| V11     | ✓             | ✓                | ✗             | ✓             |
| V12     | ✓             | ✓                | ✓ (preorder)  | ✓             |
| V13     | ✓             | ✓                | ✗             | ✓             |
| I1      | ✗             | ✗                | ✓ (disj. bug) | ✗             |
| I2      | ✗             | ✗                | ✓ (disj. bug) | ✗             |
| I3      | ✗             | ✗                | ✓ (disj. bug) | ✗             |

The world-ordering column illustrates the "disjunction problem": the l-lifting
(due to [lewis-1973]) validates patterns (I1–I3) that are invalid under measure
semantics, showing that world-ordering semantics is strictly stronger than
intended. V11 and V13 are invalid for l-lifting (Fact 1 in the paper).
Completeness of the l-lifting logic is due to [halpern-2003].
-/

namespace ComparativeProbability


variable {W : Type*}

/-! ### Measure semantics (FP∞): I1–I3 counterexamples -/

section MeasureSemantics

/-! Counterexample infrastructure: uniform measure on `Fin 3` (`μ {i} = 1/3`). -/

attribute [local instance] Classical.propDecidable

private noncomputable def uf3 : FinAddMeasure (Fin 3) where
  mu := λ A =>
    (if (0 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (1 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (2 : Fin 3) ∈ A then (1:ℚ)/3 else 0)
  nonneg := λ A => add_nonneg (add_nonneg
    (by split <;> norm_num) (by split <;> norm_num)) (by split <;> norm_num)
  additive := λ A B hAB => by
    simp only [Set.mem_union]
    by_cases h0A : (0 : Fin 3) ∈ A <;> by_cases h0B : (0 : Fin 3) ∈ B <;>
    by_cases h1A : (1 : Fin 3) ∈ A <;> by_cases h1B : (1 : Fin 3) ∈ B <;>
    by_cases h2A : (2 : Fin 3) ∈ A <;> by_cases h2B : (2 : Fin 3) ∈ B <;>
    simp_all [Set.disjoint_left] <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; norm_num

private theorem uf3_mu_eq (A : Set (Fin 3)) :
    uf3.mu A =
    (if (0 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (1 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (2 : Fin 3) ∈ A then (1:ℚ)/3 else 0) := rfl

private theorem uf3_mu_0 : uf3.mu {(0 : Fin 3)} = 1/3 := by
  simp only [uf3_mu_eq, Set.mem_singleton_iff, Fin.reduceEq, reduceIte]; norm_num

private theorem uf3_mu_1 : uf3.mu {(1 : Fin 3)} = 1/3 := by
  simp only [uf3_mu_eq, Set.mem_singleton_iff, Fin.reduceEq, reduceIte]; norm_num

private theorem uf3_mu_2 : uf3.mu {(2 : Fin 3)} = 1/3 := by
  simp only [uf3_mu_eq, Set.mem_singleton_iff, Fin.reduceEq, reduceIte]; norm_num

private theorem uf3_mu_union_12 : uf3.mu ({(1 : Fin 3)} ∪ {2}) = 2/3 := by
  rw [uf3.additive _ _ (Set.disjoint_singleton.mpr (by omega)), uf3_mu_1, uf3_mu_2]; norm_num

private theorem uf3_mu_pair_01 : uf3.mu ({0, 1} : Set (Fin 3)) = 2/3 := by
  rw [show ({0, 1} : Set (Fin 3)) = {0} ∪ {1} from Set.insert_eq 0 {1},
    uf3.additive _ _ (Set.disjoint_singleton.mpr (by omega)), uf3_mu_0, uf3_mu_1]; norm_num

private theorem uf3_mu_compl' (A : Set (Fin 3)) : uf3.mu Aᶜ = 1 - uf3.mu A := by
  have := uf3.mu_compl A; linarith

/-- I1 is invalid for measure semantics: with uniform measure on Fin 3,
    {0} ≿ {1} and {0} ≿ {2} but ¬({0} ≿ {1,2}). -/
theorem measure_not_I1 :
    ∃ m : FinAddMeasure (Fin 3), ¬patternI1 m.inducedGe := by
  refine ⟨uf3, λ hI1 => ?_⟩
  have h01 : uf3.inducedGe {(0 : Fin 3)} {1} := by
    unfold FinAddMeasure.inducedGe; rw [uf3_mu_0, uf3_mu_1]
  have h02 : uf3.inducedGe {(0 : Fin 3)} {2} := by
    unfold FinAddMeasure.inducedGe; rw [uf3_mu_0, uf3_mu_2]
  have hconc := hI1 {(0 : Fin 3)} {1} {2} h01 h02
  simp only [FinAddMeasure.inducedGe, Set.sup_eq_union, uf3_mu_0, uf3_mu_union_12] at hconc
  linarith

/-- I2 is invalid for measure semantics: with uniform measure on Fin 3,
    {0,1} ≿ {0,1}ᶜ but ¬({0,1} ≿ univ). -/
theorem measure_not_I2 :
    ∃ m : FinAddMeasure (Fin 3), ¬patternI2 m.inducedGe := by
  refine ⟨uf3, λ hI2 => ?_⟩
  have hge : uf3.inducedGe ({0, 1} : Set (Fin 3)) ({0, 1} : Set (Fin 3))ᶜ := by
    simp only [FinAddMeasure.inducedGe, uf3_mu_pair_01, uf3_mu_compl']; linarith
  have hconc := hI2 ({0, 1} : Set (Fin 3)) Set.univ hge
  simp only [FinAddMeasure.inducedGe, uf3_mu_pair_01, uf3.total] at hconc; linarith

/-- I3 is invalid for measure semantics: with uniform measure on Fin 3,
    Probably({0,1}) but ¬({0,1} ≿ univ). -/
theorem measure_not_I3 :
    ∃ m : FinAddMeasure (Fin 3), ¬patternI3 m.inducedGe := by
  refine ⟨uf3, λ hI3 => ?_⟩
  have hprob : Probably uf3.inducedGe ({0, 1} : Set (Fin 3)) := by
    refine ⟨by simp only [FinAddMeasure.inducedGe, uf3_mu_pair_01, uf3_mu_compl']; linarith,
      fun h => ?_⟩
    simp only [FinAddMeasure.inducedGe, uf3_mu_pair_01, uf3_mu_compl'] at h; linarith
  have hconc := hI3 ({0, 1} : Set (Fin 3)) Set.univ hprob
  simp only [FinAddMeasure.inducedGe, uf3_mu_pair_01, uf3.total] at hconc; linarith

end MeasureSemantics

/-! ### Qualitative additivity (FA) -/

section QualitativeAdditivity

/-- I1 is invalid for FA: every finitely additive measure induces an FA system
    via `toSystemFA`, so the measure counterexample transfers. -/
theorem fa_not_I1 : ∃ (W : Type) (sys : EpistemicSystemFA W), ¬patternI1 sys.ge :=
  let ⟨m, hm⟩ := measure_not_I1
  ⟨Fin 3, m.toSystemFA, hm⟩

/-- I2 is invalid for FA. -/
theorem fa_not_I2 : ∃ (W : Type) (sys : EpistemicSystemFA W), ¬patternI2 sys.ge :=
  let ⟨m, hm⟩ := measure_not_I2
  ⟨Fin 3, m.toSystemFA, hm⟩

/-- I3 is invalid for FA. -/
theorem fa_not_I3 : ∃ (W : Type) (sys : EpistemicSystemFA W), ¬patternI3 sys.ge :=
  let ⟨m, hm⟩ := measure_not_I3
  ⟨Fin 3, m.toSystemFA, hm⟩

end QualitativeAdditivity

/-! ### World-ordering semantics (l-lifting) -/

/-! Recall: `dominationLift` is the l-lifting (due to [lewis-1973]):
    `dominationLift ge_w A B := ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b`,
    i.e. every element of B is dominated by some element of A. The identifier
    `dominationLift` (defined in `Defs`) reflects [halpern-2003]'s completeness
    result; the lifting operation itself is due to [lewis-1973].

    The `V2`–`V7` proofs below (and their m-lift analogues) are deliberately
    *not* routed through the abstract `patternV*_of` layer: the lifts validate
    these patterns for **arbitrary** world relations, whereas the abstract route
    would require reflexivity and transitivity of `ge_w` (the lift is monotone
    only given reflexivity, transitive only given transitivity). The abstract
    layer is consumed exactly where its hypotheses are genuinely needed
    (`V11`/`V12` for the m-lift, via `matchingLift_isTrans` and
    `matchingLift_isComplementReversing`). -/

section WorldOrdering

theorem dominationLift_V1 {W : Type*} (ge_w : W → W → Prop) :
    patternV1 (dominationLift ge_w) := patternV1_holds

theorem dominationLift_V2 {W : Type*} (ge_w : W → W → Prop) :
    patternV2 (dominationLift ge_w) := by
  intro A B ⟨hAB, hABnot⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- ge A Aᶜ: Aᶜ ⊆ (A ∩ B)ᶜ, use hAB.
    intro b hb
    obtain ⟨a, ⟨ha, _⟩, hge⟩ := hAB b (fun ⟨ha, _⟩ => hb ha)
    exact ⟨a, ha, hge⟩
  · -- ¬ge Aᶜ A: restricts to ge (A∩B)ᶜ (A∩B).
    intro hc; apply hABnot; intro b ⟨hbA, _⟩
    obtain ⟨a, ha, hge⟩ := hc b hbA
    exact ⟨a, fun ⟨haA, _⟩ => ha haA, hge⟩
  · intro b hb
    obtain ⟨a, ⟨_, ha⟩, hge⟩ := hAB b (fun ⟨_, hbB⟩ => hb hbB)
    exact ⟨a, ha, hge⟩
  · intro hc; apply hABnot; intro b ⟨_, hbB⟩
    obtain ⟨a, ha, hge⟩ := hc b hbB
    exact ⟨a, fun ⟨_, haB⟩ => ha haB, hge⟩

theorem dominationLift_V3 {W : Type*} (ge_w : W → W → Prop) :
    patternV3 (dominationLift ge_w) := by
  intro A B ⟨hA, hAnot⟩
  constructor
  · rw [compl_sup]; intro b ⟨hbAc, _⟩
    obtain ⟨a, ha, hge⟩ := hA b hbAc
    exact ⟨a, Set.mem_union_left B ha, hge⟩
  · rw [compl_sup]; intro hc; apply hAnot; intro b hbA
    obtain ⟨a, ⟨haAc, _⟩, hge⟩ := hc b (Set.mem_union_left B hbA)
    exact ⟨a, haAc, hge⟩

theorem dominationLift_V4 {W : Type*} (ge_w : W → W → Prop) :
    patternV4 (dominationLift ge_w) := by
  intro _ b hb; exact hb.elim

theorem dominationLift_V5 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternV5 (dominationLift ge_w) := by
  intro _ b hb; exact ⟨b, Set.mem_univ b, hRefl b⟩

theorem dominationLift_V6 {W : Type*} [Nonempty W] (ge_w : W → W → Prop) :
    patternV6 (dominationLift ge_w) := by
  intro A hAc
  have hAuniv : A = Set.univ := by
    ext x; simp only [Set.mem_univ, iff_true]
    by_contra hx; obtain ⟨a, ha, _⟩ := hAc x hx; exact ha.elim
  subst hAuniv
  show dominationLift ge_w Set.univ Set.univᶜ ∧ ¬dominationLift ge_w Set.univᶜ Set.univ
  rw [Set.compl_univ]
  exact ⟨fun b hb => hb.elim,
    fun h => by obtain ⟨w⟩ := ‹Nonempty W›; obtain ⟨a, ha, _⟩ := h w (Set.mem_univ w); exact ha.elim⟩

theorem dominationLift_V7 {W : Type*} (ge_w : W → W → Prop) :
    patternV7 (dominationLift ge_w) := by
  intro A ⟨_, hAnot⟩ hempty
  by_cases hne : (A : Set W).Nonempty
  · obtain ⟨x, hx⟩ := hne; exact (hempty x hx).choose_spec.1.elim
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty] at hAnot
    exact hAnot (fun b hb => hb.elim)

/-- V11 is **invalid** for world-ordering semantics (Fact 1 in
    [holliday-icard-2013]). Counterexample: W = Fin 2, ge_w total.
    A = W (Probably, since W ≿ ∅ and ¬(∅ ≿ W)). B = {0} (B ≿ A since
    ge_w is total, but Bᶜ = {1} ≿ B since ge_w is total — not strictly). -/
theorem dominationLift_not_V11 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV11 (dominationLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, fun h => ?_⟩
  have hBA : dominationLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} Set.univ :=
    fun _ _ => ⟨0, rfl, trivial⟩
  have hprobA : Probably (dominationLift (fun (_ _ : Fin 2) => True)) Set.univ :=
    ⟨fun b hb => absurd (Set.mem_univ b) hb, fun hge =>
      absurd (Set.mem_univ _) (hge (0 : Fin 2) (Set.mem_univ _)).choose_spec.1⟩
  refine (h Set.univ {(0 : Fin 2)} hBA hprobA).2 (fun b _ => ?_)
  exact ⟨1, fun h1 => absurd (Set.mem_singleton_iff.mp h1) (by omega), trivial⟩

/-- V12 is valid for world-ordering semantics with a preorder (Fact 1 in
    [holliday-icard-2013]). Requires transitivity for the case where
    y ∈ Bᶜ ∩ Aᶜ: chain through A via ge A Aᶜ, then through B via ge B A. -/
theorem dominationLift_V12 {W : Type*} (ge_w : W → W → Prop)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV12 (dominationLift ge_w) := by
  intro A B hBA hA y hyBc
  by_cases hyA : y ∈ A
  · exact hBA y hyA
  · obtain ⟨a, haA, hge_ay⟩ := hA y hyA
    obtain ⟨b, hbB, hge_ba⟩ := hBA a haA
    exact ⟨b, hbB, hTrans b a y hge_ba hge_ay⟩

/-- V13 is invalid for world-ordering semantics. Counterexample:
    W = Fin 2, ge_w = total (everything related). A = {0}, B = {1}.
    Then (A \ B) ≻ ∅ holds but (A ∪ B) ≻ B fails because ge B (A ∪ B). -/
theorem dominationLift_not_V13 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV13 (dominationLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, fun h => ?_⟩
  have hA : ({0} : Set (Fin 2)) \ {1} = {0} := by
    ext x; simp only [Set.mem_diff, Set.mem_singleton_iff]; omega
  have hstrict : Strict (dominationLift (fun (_ _ : Fin 2) => True)) ({0} \ {1}) ∅ :=
    ⟨fun b hb => hb.elim, fun hge => by
      obtain ⟨a, ha, _⟩ := hge (0 : Fin 2) (by rw [hA]; rfl); exact ha.elim⟩
  have huniv : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]; omega
  have hresult := h {0} {1} hstrict
  simp only [Set.sup_eq_union, huniv] at hresult
  exact hresult.2 (fun b _ => ⟨1, rfl, trivial⟩)

/-- I1 is valid for world-ordering semantics: the "disjunction problem". -/
theorem dominationLift_I1 {W : Type*} (ge_w : W → W → Prop) :
    patternI1 (dominationLift ge_w) := by
  intro A B C hAB hAC b hb
  exact hb.elim (hAB b) (hAC b)

/-- I2 is valid for world-ordering semantics. -/
theorem dominationLift_I2 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternI2 (dominationLift ge_w) := by
  intro A B hA b hbB
  by_cases hbA : b ∈ A
  · exact ⟨b, hbA, hRefl b⟩
  · exact hA b hbA

/-- I3 is valid for world-ordering semantics. -/
theorem dominationLift_I3 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternI3 (dominationLift ge_w) := by
  intro A B ⟨hA, _⟩; exact dominationLift_I2 ge_w hRefl A B hA

end WorldOrdering

/-! ### m-lifting ([holliday-icard-2013], Fact 5) -/

/-! The m-lifting validates all 13 validity patterns V1–V13 and invalidates
    I1–I3 (Fact 5 in [holliday-icard-2013]). This avoids the
    "disjunction problem" that plagues the l-lifting.

    V1, V3–V7 follow from the l-lifting proofs (since m-lifting implies
    l-lifting). V2, V11–V13 use the injection structure directly;
    V11–V12 rely on complement reversal (`matchingLift_complement_reversal`). -/

section MLift

/-- Every m-lift entails an l-lift: if there is an injection from B to A
    with each image dominating its preimage, then in particular every
    element of B is dominated by some element of A. -/
theorem matchingLift_implies_dominationLift {W : Type*} {ge_w : W → W → Prop}
    {A B : Set W} (h : matchingLift ge_w A B) : dominationLift ge_w A B := by
  obtain ⟨f, hf, _⟩ := h
  exact fun b hbB => ⟨f b, (hf b hbB).1, (hf b hbB).2⟩

theorem matchingLift_V1 {W : Type*} (ge_w : W → W → Prop) :
    patternV1 (matchingLift ge_w) := patternV1_holds

/-- V2 is valid for the m-lifting: △(A ∩ B) → △A ∧ △B.

    Proof: restrict the injection f : (A∩B)ᶜ ↪ A∩B to Aᶜ ⊆ (A∩B)ᶜ to get
    the ge half. For the Strict half, any reverse injection g : A ↪ Aᶜ
    restricts to A∩B ↪ (A∩B)ᶜ (since Aᶜ ⊆ (A∩B)ᶜ), contradicting the
    hypothesis ¬matchingLift (A∩B)ᶜ (A∩B). Symmetric for B. -/
theorem matchingLift_V2 {W : Type*} (ge_w : W → W → Prop) :
    patternV2 (matchingLift ge_w) := by
  intro A B ⟨⟨f, hf, hinj⟩, hABnot⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨f, fun b hb => ⟨(hf b (fun h => hb h.1)).1.1, (hf b (fun h => hb h.1)).2⟩,
      fun b₁ b₂ h1 h2 => hinj b₁ b₂ (fun h => h1 h.1) (fun h => h2 h.1)⟩
  · exact fun ⟨g, hg, ginj⟩ => hABnot ⟨g,
      fun b hb => ⟨fun h => (hg b hb.1).1 h.1, (hg b hb.1).2⟩,
      fun b₁ b₂ h1 h2 => ginj b₁ b₂ h1.1 h2.1⟩
  · exact ⟨f, fun b hb => ⟨(hf b (fun h => hb h.2)).1.2, (hf b (fun h => hb h.2)).2⟩,
      fun b₁ b₂ h1 h2 => hinj b₁ b₂ (fun h => h1 h.2) (fun h => h2 h.2)⟩
  · exact fun ⟨g, hg, ginj⟩ => hABnot ⟨g,
      fun b hb => ⟨fun h => (hg b hb.2).1 h.2, (hg b hb.2).2⟩,
      fun b₁ b₂ h1 h2 => ginj b₁ b₂ h1.2 h2.2⟩

theorem matchingLift_V3 {W : Type*} (ge_w : W → W → Prop) :
    patternV3 (matchingLift ge_w) := by
  intro A B ⟨hA, hAnot⟩
  obtain ⟨f, hf, hinj⟩ := hA
  constructor
  · rw [compl_sup]
    exact ⟨f, fun b ⟨hbAc, _⟩ => let ⟨ha, hge⟩ := hf b hbAc; ⟨Set.mem_union_left B ha, hge⟩,
      fun b₁ b₂ ⟨h1, _⟩ ⟨h2, _⟩ => hinj b₁ b₂ h1 h2⟩
  · refine fun ⟨g, hg, ginj⟩ => hAnot ⟨g, fun b hbA => ?_,
      fun b₁ b₂ h1 h2 => ginj b₁ b₂ (Set.mem_union_left B h1) (Set.mem_union_left B h2)⟩
    obtain ⟨hgc, hge⟩ := hg b (Set.mem_union_left B hbA)
    exact ⟨fun hga => hgc (Set.mem_union_left B hga), hge⟩

theorem matchingLift_V4 {W : Type*} (ge_w : W → W → Prop) :
    patternV4 (matchingLift ge_w) := by
  intro A; exact ⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩

theorem matchingLift_V5 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternV5 (matchingLift ge_w) := by
  intro A; exact ⟨id, fun b hb => ⟨Set.mem_univ b, hRefl b⟩, fun _ _ _ _ h => h⟩

theorem matchingLift_V6 {W : Type*} [Nonempty W] (ge_w : W → W → Prop) :
    patternV6 (matchingLift ge_w) := by
  intro A hAc
  have hAuniv : A = Set.univ := by
    ext x; simp only [Set.mem_univ, iff_true]
    by_contra hx; obtain ⟨f, hf, _⟩ := hAc; obtain ⟨ha, _⟩ := hf x hx; exact ha.elim
  subst hAuniv
  show matchingLift ge_w Set.univ Set.univᶜ ∧ ¬matchingLift ge_w Set.univᶜ Set.univ
  rw [Set.compl_univ]
  exact ⟨⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩,
    fun ⟨f, hf, _⟩ => by obtain ⟨w⟩ := ‹Nonempty W›; exact (hf w (Set.mem_univ w)).1.elim⟩

theorem matchingLift_V7 {W : Type*} (ge_w : W → W → Prop) :
    patternV7 (matchingLift ge_w) := by
  intro A ⟨_, hAnot⟩ hempty
  obtain ⟨f, hf, _⟩ := hempty
  by_cases hne : (A : Set W).Nonempty
  · obtain ⟨x, hx⟩ := hne; exact (hf x hx).1.elim
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty] at hAnot
    exact hAnot ⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩

/-! V11–V13 require `[Finite W]` and reflexivity (and V11/V12 additionally
need transitivity). The paper ([holliday-icard-2013]) assumes a finite poset
`(W, ≥)`. The proofs of V11 and V12 follow the companion paper
[harrison-trainor-holliday-icard-2018]: the injection extension `≥ⁱ` (= `matchingLift`)
is a GFC order, which implies V12 directly. The key lemma is *complement
reversal*: `matchingLift ge_w B A → matchingLift ge_w Aᶜ Bᶜ` (via an f-chain construction on
elements of `A ∩ Bᶜ`). V12 then follows from complement reversal plus two
applications of matchingLift transitivity. -/

/-! #### Helper: matchingLift transitivity -/

private theorem matchingLift_trans {W : Type*} {ge_w : W → W → Prop}
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {A B C : Set W} (hAB : matchingLift ge_w A B) (hBC : matchingLift ge_w B C) :
    matchingLift ge_w A C := by
  obtain ⟨f, hf, hinj_f⟩ := hAB
  obtain ⟨g, hg, hinj_g⟩ := hBC
  exact ⟨f ∘ g, fun c hc =>
    ⟨(hf (g c) (hg c hc).1).1, hTrans _ _ _ (hf (g c) (hg c hc).1).2 (hg c hc).2⟩,
    fun c₁ c₂ hc1 hc2 heq =>
    hinj_g c₁ c₂ hc1 hc2 (hinj_f (g c₁) (g c₂) (hg c₁ hc1).1 (hg c₂ hc2).1 heq)⟩

/-! #### Helper lemmas for the f-chain construction -/

/-- If iterates f^[0],...,f^[n-1] of p stay in A, then f^[n] p ∈ B for n ≥ 1. -/
private theorem matchingLift_iter_in_B {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B) {p : W}
    (n : ℕ) (hn : n ≥ 1) (hA : ∀ m, m < n → f^[m] p ∈ A) :
    f^[n] p ∈ B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Function.iterate_succ', Function.comp_apply]
  exact hfmem _ (hA m (by omega))

/-- Iterates of p ∈ A \ B are pairwise distinct while staying in A. -/
private theorem matchingLift_iter_ne_of_lt {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p : W} (hpB : p ∉ B) (hall : ∀ m, f^[m] p ∈ A) :
    ∀ i j, i < j → f^[i] p ≠ f^[j] p := by
  intro i
  induction i with
  | zero =>
    intro j hj heq
    simp only [Function.iterate_zero, id_eq] at heq
    exact hpB (heq ▸ matchingLift_iter_in_B hfmem j (by omega) (fun m _ => hall m))
  | succ i' ih =>
    intro j hj heq
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Function.iterate_succ', Function.comp_apply] at heq
    exact ih j' (by omega) (hfinj _ _ (hall i') (hall j') heq)

/-- The f-chain starting at p ∈ A \ B must eventually exit A. -/
private theorem matchingLift_chain_exits {W : Type*} [Finite W] {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p : W} (hp : p ∈ A) (hpB : p ∉ B) :
    ∃ n, f^[n] p ∉ A := by
  by_contra h; push Not at h
  have hall : ∀ m, f^[m] p ∈ A := by
    intro m; cases m with
    | zero => simpa
    | succ m => exact h (m + 1)
  have hdist := matchingLift_iter_ne_of_lt hfmem hfinj hpB hall
  have hinj : Function.Injective (fun n : ℕ => (⟨f^[n] p, hall n⟩ : ↥A)) := by
    intro i j heq; simp only [Subtype.mk.injEq] at heq
    rcases lt_trichotomy i j with h | h | h
    · exact absurd heq (hdist i j h)
    · exact h
    · exact absurd heq.symm (hdist j i h)
  haveI : Infinite ↥A := Infinite.of_injective _ hinj
  exact not_finite ↥A

/-- If both chains stay in A for n steps and f^[n] x = f^[n] y, then x = y. -/
private theorem matchingLift_iterate_inj_of_mem {W : Type*} {A : Set W} {f : W → W}
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {x y : W} {n : ℕ}
    (hx : ∀ m, m < n → f^[m] x ∈ A) (hy : ∀ m, m < n → f^[m] y ∈ A)
    (heq : f^[n] x = f^[n] y) : x = y := by
  induction n with
  | zero => simpa using heq
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply] at heq
    exact ih (fun m hm => hx m (by omega)) (fun m hm => hy m (by omega))
      (hfinj _ _ (hx n (by omega)) (hy n (by omega)) heq)

/-- Two f-chains landing at the same point must have started at the same point.
    Handles all four injectivity cases uniformly via `wlog`. -/
private theorem matchingLift_chain_origin_eq {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p₁ p₂ : W} {k₁ k₂ : ℕ}
    (hp1 : p₁ ∉ B) (hp2 : p₂ ∉ B)
    (hk1 : ∀ m, m < k₁ → f^[m] p₁ ∈ A)
    (hk2 : ∀ m, m < k₂ → f^[m] p₂ ∈ A)
    (heq : f^[k₁] p₁ = f^[k₂] p₂) : p₁ = p₂ := by
  wlog hle : k₁ ≤ k₂ with H
  · exact (H hfmem hfinj hp2 hp1 hk2 hk1 heq.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Function.iterate_add_apply] at heq
  have hpeeled := matchingLift_iterate_inj_of_mem hfinj hk1
    (fun m hm => by rw [← Function.iterate_add_apply]; exact hk2 (m + d) (by omega)) heq
  cases d with
  | zero => simpa using hpeeled
  | succ d => exact absurd (hpeeled ▸ matchingLift_iter_in_B hfmem (d + 1) (by omega)
      fun m hm => hk2 m (by omega)) hp1

/-- Dominance through a chain: ge_w (f^[n] p) p (including n = 0 by reflexivity). -/
private theorem matchingLift_chain_dominance {W : Type*} {A : Set W}
    {ge_w : W → W → Prop} {f : W → W}
    (hRefl : ∀ w, ge_w w w)
    (hfge : ∀ a, a ∈ A → ge_w (f a) a)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {p : W} (n : ℕ) (hp : ∀ m, m < n → f^[m] p ∈ A) :
    ge_w (f^[n] p) p := by
  induction n with
  | zero => simpa using hRefl p
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact hTrans _ _ _ (hfge _ (hp n (by omega))) (ih fun m hm => hp m (by omega))

/-! #### Complement reversal -/

/-- Complement reversal: matchingLift ge_w B A → matchingLift ge_w Aᶜ Bᶜ.
    Maps p ∈ A ∩ Bᶜ to f^[k](p) (first exit from A) and
    q ∈ Aᶜ ∩ Bᶜ to q (reflexivity). Injectivity of all four
    cross-cases follows from `chain_origin_eq`
    ([harrison-trainor-holliday-icard-2018], Lemma 3.7). -/
private theorem matchingLift_complement_reversal {W : Type*} [Finite W]
    {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {A B : Set W} (h : matchingLift ge_w B A) : matchingLift ge_w Aᶜ Bᶜ := by
  obtain ⟨f, hf, hinj_f⟩ := h
  have hfmem : ∀ a, a ∈ A → f a ∈ B := fun a ha => (hf a ha).1
  have hfge : ∀ a, a ∈ A → ge_w (f a) a := fun a ha => (hf a ha).2
  classical
  have hExits : ∀ p, p ∈ A → p ∉ B → ∃ n, f^[n] p ∉ A :=
    fun p hp hpB => matchingLift_chain_exits hfmem hinj_f hp hpB
  let ei (w : W) (hwA : w ∈ A) (hwB : w ∉ B) := Nat.find (hExits w hwA hwB)
  have ei_spec : ∀ w hwA hwB, f^[ei w hwA hwB] w ∉ A :=
    fun w hwA hwB => Nat.find_spec (hExits w hwA hwB)
  have ei_min : ∀ w hwA hwB m, m < ei w hwA hwB → f^[m] w ∈ A :=
    fun w hwA hwB m hm => by_contra fun h => Nat.find_min (hExits w hwA hwB) hm h
  let g : W → W := fun w =>
    if hwA : w ∈ A then if hwB : w ∈ B then w else f^[ei w hwA hwB] w else w
  have g_iter : ∀ b' (_ : b' ∉ B), ∃ k,
      g b' = f^[k] b' ∧ f^[k] b' ∉ A ∧ ∀ m, m < k → f^[m] b' ∈ A := by
    intro b' hb'
    by_cases hbA : b' ∈ A
    · exact ⟨ei b' hbA hb', by simp [g, dif_pos hbA, dif_neg hb'],
        ei_spec b' hbA hb', ei_min b' hbA hb'⟩
    · exact ⟨0, by simp [g, dif_neg hbA], hbA, fun _ hm => absurd hm (by omega)⟩
  refine ⟨g, fun b' hb' => ?_, fun b₁ b₂ hb1 hb2 heq => ?_⟩
  · obtain ⟨k, hgk, hnotA, hkA⟩ := g_iter b' hb'
    exact ⟨hgk ▸ hnotA, hgk ▸ matchingLift_chain_dominance hRefl hfge hTrans k hkA⟩
  · obtain ⟨k₁, hgk1, -, hk1A⟩ := g_iter b₁ hb1
    obtain ⟨k₂, hgk2, -, hk2A⟩ := g_iter b₂ hb2
    rw [hgk1, hgk2] at heq
    exact matchingLift_chain_origin_eq hfmem hinj_f hb1 hb2 hk1A hk2A heq

/-! #### V11/V12 from transitivity and complement reversal

The m-lifting of a reflexive, transitive world ordering on finite `W` is
transitive (`matchingLift_trans`) and complement-reversing
(`matchingLift_complement_reversal`); V11 and V12 then follow from the abstract
`patternV11_of`/`patternV12_of` with those registered as local
`IsTrans`/`IsComplementReversing` instances. The injection extension `≿ⁱ`
(= `matchingLift`) is moreover the genuine generalized-finite-cancellation order
of [harrison-trainor-holliday-icard-2018] (`ComparativeProbability.GFCOrder`). -/

/-- The m-lift's transitivity, packaged for the abstract pattern layer. -/
def matchingLift_isTrans {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    IsTrans (Set W) (matchingLift ge_w) :=
  ⟨fun _ _ _ => matchingLift_trans hTrans⟩

/-- The m-lift's complement reversal, packaged for the abstract pattern layer. -/
def matchingLift_isComplementReversing {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    IsComplementReversing (matchingLift ge_w) :=
  ⟨fun _ _ h => matchingLift_complement_reversal hRefl hTrans h⟩

/-- V12 is valid for the m-lifting on finite posets (Fact 5 in
    [holliday-icard-2013]): the m-lift is transitive and complement-reversing,
    so `patternV12_of` supplies the pattern. -/
theorem matchingLift_V12 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV12 (matchingLift ge_w) := by
  haveI := matchingLift_isTrans ge_w hTrans
  haveI := matchingLift_isComplementReversing ge_w hRefl hTrans
  exact patternV12_of

/-- V11 is valid for the m-lifting on finite posets (Fact 5 in
    [holliday-icard-2013]): immediate from `patternV11_of`. -/
theorem matchingLift_V11 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV11 (matchingLift ge_w) := by
  haveI := matchingLift_isTrans ge_w hTrans
  haveI := matchingLift_isComplementReversing ge_w hRefl hTrans
  exact patternV11_of

/-- V13 is valid for the m-lifting on finite posets (Fact 5 in
    [holliday-icard-2013]). The ge half uses id on B (reflexivity);
    the Strict half uses pigeonhole (|A∪B| > |B| since A\B nonempty,
    finiteness). -/
theorem matchingLift_V13 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    patternV13 (matchingLift ge_w) := by
  intro A B ⟨_, hNotEmpty⟩
  have hABne : (A \ B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hNotEmpty; rw [h]
    exact ⟨id, fun b hb => hb.elim, fun _ _ _ _ h => h⟩
  refine ⟨⟨id, fun b hb => ⟨Set.mem_union_right A hb, hRefl b⟩, fun _ _ _ _ h => h⟩,
    fun ⟨f, hf, hinj⟩ => ?_⟩
  have hle : (A ∪ B).ncard ≤ B.ncard :=
    Set.ncard_le_ncard_of_injOn f (fun b hb => (hf b hb).1)
      (fun b₁ hb₁ b₂ hb₂ heq => hinj b₁ b₂ hb₁ hb₂ heq) (Set.toFinite _)
  have hsub : B ⊂ A ∪ B := ⟨Set.subset_union_right, fun h =>
    hABne.elim fun x hx => hx.2 (h (Set.mem_union_left B hx.1))⟩
  have hlt := Set.ncard_lt_ncard hsub (Set.toFinite _)
  omega

/-- I1 is **invalid** for the m-lifting (Fact 5 in [holliday-icard-2013]).
    Counterexample: W = Fin 2, ge_w total. A = {0}, B = {0}, C = {1}.
    matchingLift A B and matchingLift A C both hold (singleton ↪ singleton), but
    ¬matchingLift A (B ∪ C) since |A| = 1 < 2 = |B ∪ C| (no injection). -/
theorem matchingLift_not_I1 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI1 (matchingLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, fun h => ?_⟩
  have hAB : matchingLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} {0} :=
    ⟨id, fun b hb => ⟨hb, trivial⟩, fun _ _ _ _ h => h⟩
  have hAC : matchingLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} {1} :=
    ⟨fun _ => 0, fun _ hb => ⟨rfl, trivial⟩,
     fun b₁ b₂ h1 h2 _ => by rw [Set.mem_singleton_iff] at h1 h2; rw [h1, h2]⟩
  have huniv : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]; omega
  have hresult := h {(0 : Fin 2)} {0} {1} hAB hAC
  simp only [Set.sup_eq_union, huniv] at hresult
  obtain ⟨f, hf, hinj⟩ := hresult
  have hf0 := Set.mem_singleton_iff.mp (hf 0 (Set.mem_univ _)).1
  have hf1 := Set.mem_singleton_iff.mp (hf 1 (Set.mem_univ _)).1
  exact absurd (hinj 0 1 (Set.mem_univ _) (Set.mem_univ _) (hf0.trans hf1.symm)) (by omega)

/-- Shared counterexample core for I2/I3: with the total relation on `Fin 3`,
    `{0,1}` m-lifts its complement `{2}` (injection `_ ↦ 0`) but not all of
    `univ` (no injection `Fin 3 ↪ {0,1}`, by pigeonhole). -/
private theorem matchingLift_pair01_AAc :
    matchingLift (fun (_ _ : Fin 3) => True) ({0, 1} : Set (Fin 3)) ({0, 1} : Set (Fin 3))ᶜ :=
  ⟨fun _ => 0, fun _ _ => ⟨Set.mem_insert 0 {1}, trivial⟩, fun b₁ b₂ hb1 hb2 _ => by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb1 hb2
    omega⟩

private theorem matchingLift_pair01_not_univ :
    ¬matchingLift (fun (_ _ : Fin 3) => True) ({0, 1} : Set (Fin 3)) Set.univ := by
  intro ⟨f, hf, hinj⟩
  have h0 := (hf 0 (Set.mem_univ _)).1
  have h1 := (hf 1 (Set.mem_univ _)).1
  have h2 := (hf 2 (Set.mem_univ _)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | (have := hinj 0 1 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 0 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 1 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)

/-- I2 is **invalid** for the m-lifting (Fact 5 in [holliday-icard-2013]).
    Counterexample: W = Fin 3, ge_w total. A = {0,1}, B = univ.
    matchingLift A Aᶜ holds (|Aᶜ| = 1 ≤ 2 = |A|), but ¬matchingLift A univ
    since |A| = 2 < 3 = |univ|. -/
theorem matchingLift_not_I2 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI2 (matchingLift ge_w) :=
  ⟨Fin 3, fun _ _ => True, fun _ => trivial, fun h =>
    matchingLift_pair01_not_univ (h _ Set.univ matchingLift_pair01_AAc)⟩

/-- I3 is **invalid** for the m-lifting (Fact 5 in [holliday-icard-2013]).
    Same counterexample as I2: W = Fin 3, ge_w total, A = {0,1}, B = univ.
    A ≿ Aᶜ (injection {2} → {0,1}) and ¬(Aᶜ ≿ A) (no injection {0,1} → {2}),
    so Probably A. But ¬(A ≿ univ) by cardinality. -/
theorem matchingLift_not_I3 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI3 (matchingLift ge_w) := by
  refine ⟨Fin 3, fun _ _ => True, fun _ => trivial, fun h => ?_⟩
  refine matchingLift_pair01_not_univ (h _ Set.univ ⟨matchingLift_pair01_AAc, ?_⟩)
  intro ⟨f, hf, hinj⟩
  have h0 := (hf 0 (Set.mem_insert 0 {1})).1
  have h1 := (hf 1 (Or.inr rfl : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)))).1
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h0 h1
  have := hinj 0 1 (Set.mem_insert 0 {1}) (Or.inr rfl) (by omega); omega

/-! #### Non-totality of the m-lifting -/

/-- The m-lifting is NOT total, even for total preorders on worlds.
    Counterexample: W = Fin 4, ge_w = (· ≥ ·), A = {3, 0}, B = {2, 1}.
    Neither A ≿ⁱ B (only 3 dominates 2, leaving nothing for 1) nor
    B ≿ⁱ A (nothing in B dominates 3). -/
theorem matchingLift_not_total :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧
      (∀ u v w, ge_w u v → ge_w v w → ge_w u w) ∧
      (∀ u v, ge_w u v ∨ ge_w v u) ∧
      ∃ A B : Set W, ¬matchingLift ge_w A B ∧ ¬matchingLift ge_w B A := by
  refine ⟨Fin 4, (· ≥ ·), fun w => le_refl w, fun u v w huv hvw => le_trans hvw huv,
    fun u v => le_total v u, {3, 0}, {2, 1}, ?_, ?_⟩
  · intro ⟨f, hf, hinj⟩
    have h2 := hf 2 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    have h1 := hf 1 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 h1
    exact absurd (hinj 2 1 (by simp) (by simp) (by omega)) (by omega)
  · intro ⟨f, hf, _⟩
    have h3 := hf 3 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
    omega

end MLift

end ComparativeProbability
