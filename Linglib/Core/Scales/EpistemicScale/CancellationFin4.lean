import Linglib.Core.Scales.EpistemicScale.Cancellation
import Linglib.Core.Order.Caratheodory
import Linglib.Core.Order.SignVectors
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases

/-! # Cancellation for `Fin 4`: the structural merge-reduction proof

Every finitely additive epistemic-comparison system on four worlds satisfies
Scott cancellation, hence is representable by a finitely additive measure
([holliday-icard-2013] Theorem 8).

## Main declarations

* `Core.Scale.fa_cancellation_fin4` — FA axioms imply cancellation on `Fin 4`.
* `Core.Scale.representable_fin4` — every FA system on `Fin 4` is representable.
* `Core.Scale.no_null_cancellation` — cancellation for systems with no null atoms.
* `Core.Scale.ge_union_context`, `ge_generalized_merge`, `ge_mono_dominated`,
  `ge_empty_target` — reusable consequences of the FA axioms (any arity).

## Implementation notes

The proof rests on two imported layers — conic Carathéodory
(`Caratheodory.exists_posdep_card_le_five`) and the sign-vector core
(`SignVec.exists_antidom_pair`) — and adds the merge reduction: a valid family
of comparisons whose vector sum is a single comparison vector proves that
comparison (`merge_to_single`), by a four-rule recursion whose stuck case is
discharged through the sign-vector core via `v1_tailored`.  The comparison
vector calculus (`cmpVec`, `mergeCmp`, `cvSumList`) and the merge recursion
itself are private plumbing; only the theorems above are exported.
-/

namespace Core.Scale

/-- **Add common context** (from Axiom A + the diff-cancellation): for `C` disjoint
    from both `X` and `Y`, `X ≿ Y ↔ (X ∪ C) ≿ (Y ∪ C)`. -/
lemma ge_union_context {n : ℕ} (sys : EpistemicSystemFA (Fin n)) (X Y C : Set (Fin n))
    (hCX : Disjoint C X) (hCY : Disjoint C Y) :
    sys.ge X Y ↔ sys.ge (X ∪ C) (Y ∪ C) := by
  rw [sys.additive X Y, sys.additive (X ∪ C) (Y ∪ C)]
  have hCXl : ∀ x, x ∈ C → x ∉ X := fun x hx => Set.disjoint_left.mp hCX hx
  have hCYl : ∀ x, x ∈ C → x ∉ Y := fun x hx => Set.disjoint_left.mp hCY hx
  have e1 : (X ∪ C) \ (Y ∪ C) = X \ Y := by
    ext x
    have := hCXl x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  have e2 : (Y ∪ C) \ (X ∪ C) = Y \ X := by
    ext x
    have := hCYl x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  rw [e1, e2]

/-- **Generalized merge**: two valid comparisons whose left parts are disjoint and
    whose right parts are disjoint merge into their union — even with pivot overlaps
    (X₁∩Y₂, X₂∩Y₁ ≠ ∅). The width-2 additivity in full generality.
    Derivation: add context `X₂\Y₁` to the first and `Y₁\X₂` to the second, transit
    through `X₂∪Y₁`, then restore the pivot `P = X₂∩Y₁` via Axiom A. -/
lemma ge_generalized_merge {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {X₁ Y₁ X₂ Y₂ : Set (Fin n)}
    (h1 : sys.ge X₁ Y₁) (h2 : sys.ge X₂ Y₂)
    (hX : Disjoint X₁ X₂) (hY : Disjoint Y₁ Y₂) :
    sys.ge (X₁ ∪ X₂) (Y₁ ∪ Y₂) := by
  have hXl : ∀ x, x ∈ X₁ → x ∉ X₂ := fun x hx => Set.disjoint_left.mp hX hx
  have hYl : ∀ x, x ∈ Y₂ → x ∉ Y₁ := fun x hy2 hy1 => Set.disjoint_left.mp hY hy1 hy2
  -- context C₁ = X₂ \ Y₁ added to (X₁ ≿ Y₁)
  have step1 : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₁ ∪ (X₂ \ Y₁)) :=
    (ge_union_context sys X₁ Y₁ (X₂ \ Y₁)
      (Set.disjoint_left.mpr fun x hx hx1 => hXl x hx1 hx.1)
      (Set.disjoint_left.mpr fun x hx hxY1 => hx.2 hxY1)).mp h1
  -- context C₂ = Y₁ \ X₂ added to (X₂ ≿ Y₂)
  have step2 : sys.ge (X₂ ∪ (Y₁ \ X₂)) (Y₂ ∪ (Y₁ \ X₂)) :=
    (ge_union_context sys X₂ Y₂ (Y₁ \ X₂)
      (Set.disjoint_left.mpr fun x hx hx2 => hx.2 hx2)
      (Set.disjoint_left.mpr fun x hx hxY2 => hYl x hxY2 hx.1)).mp h2
  have hmid : Y₁ ∪ (X₂ \ Y₁) = X₂ ∪ (Y₁ \ X₂) := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; tauto
  rw [hmid] at step1
  have htrans : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₂ ∪ (Y₁ \ X₂)) := sys.trans _ _ _ step1 step2
  set P : Set (Fin n) := X₂ ∩ Y₁ with hP
  have hLHS : X₁ ∪ (X₂ \ Y₁) = (X₁ ∪ X₂) \ P := by
    ext x
    have := hXl x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    tauto
  have hRHS : Y₂ ∪ (Y₁ \ X₂) = (Y₁ ∪ Y₂) \ P := by
    ext x
    have := hYl x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    tauto
  rw [hLHS, hRHS] at htrans
  have hPsubX : P ⊆ X₁ ∪ X₂ := Set.inter_subset_left.trans Set.subset_union_right
  have hPsubY : P ⊆ Y₁ ∪ Y₂ := Set.inter_subset_right.trans Set.subset_union_left
  have key := (ge_union_context sys ((X₁ ∪ X₂) \ P) ((Y₁ ∪ Y₂) \ P) P
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)).mp htrans
  rwa [Set.diff_union_of_subset hPsubX, Set.diff_union_of_subset hPsubY] at key

/-- **Mono-domination discharge**: a single valid comparison `X ≿ Y` with `X ⊆ P`
    and `Q ⊆ Y` proves `P ≿ Q` (monotonicity twice + transitivity). Used to discharge
    the merge-to-single target when one family member already dominates it. -/
lemma ge_mono_dominated {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {X Y P Q : Set (Fin n)} (h : sys.ge X Y) (hXP : X ⊆ P) (hQY : Q ⊆ Y) :
    sys.ge P Q :=
  sys.trans _ _ _ (sys.mono X P hXP) (sys.trans _ _ _ h (sys.mono Q Y hQY))

/-- **Trivial-target discharge**: `P ≿ ∅` always (monotonicity, `∅ ⊆ P`). The
    merge-to-single base case when the target's negative part is empty. -/
lemma ge_empty_target {n : ℕ} (sys : EpistemicSystemFA (Fin n)) (P : Set (Fin n)) :
    sys.ge P ∅ :=
  sys.mono ∅ P (Set.empty_subset P)

/-! ### Merge-to-single infrastructure

A comparison is a pair of disjoint finsets `(pos, neg)`; its integer vector is
`1_pos − 1_neg ∈ {−1,0,1}ⁿ`. `mergeCmp` combines two comparisons whose pos-parts and
neg-parts are disjoint into the disjoint-normal-form of their vector sum. -/

/-- Integer comparison vector of a finset pair. -/
private def cmpVec {n : ℕ} (c : Finset (Fin n) × Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ c.1 then 1 else 0) - (if i ∈ c.2 then 1 else 0)

/-- Merge two comparisons into the disjoint normal form of their vector sum. -/
private def mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  ((c.1 ∪ d.1) \ (c.2 ∪ d.2), (c.2 ∪ d.2) \ (c.1 ∪ d.1))

/-- The merged comparison's vector is the sum of the two vectors, provided pos-parts
    are disjoint and neg-parts are disjoint (so no coordinate doubles). -/
private lemma cmpVec_mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n))
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) (i : Fin n) :
    cmpVec (mergeCmp c d) i = cmpVec c i + cmpVec d i := by
  have h1 : i ∈ c.1 → i ∉ d.1 := fun h => Finset.disjoint_left.mp hpos h
  have h2 : i ∈ c.2 → i ∉ d.2 := fun h => Finset.disjoint_left.mp hneg h
  simp only [cmpVec, mergeCmp, Finset.mem_sdiff, Finset.mem_union]
  split_ifs <;> simp_all

/-- `mergeCmp` of two valid comparisons is valid, given the disjointness conditions.
    Uses `ge_generalized_merge` then Axiom A to reach disjoint normal form. -/
private lemma mergeCmp_valid {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {c d : Finset (Fin n) × Finset (Fin n)}
    (hc : sys.ge ↑c.1 ↑c.2) (hd : sys.ge ↑d.1 ↑d.2)
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) :
    sys.ge ↑(mergeCmp c d).1 ↑(mergeCmp c d).2 := by
  have hmerge : sys.ge (↑c.1 ∪ ↑d.1) (↑c.2 ∪ ↑d.2) :=
    ge_generalized_merge sys hc hd
      (by rwa [← Finset.disjoint_coe] at hpos)
      (by rwa [← Finset.disjoint_coe] at hneg)
  -- reduce to disjoint form via Axiom A
  rw [sys.additive (↑c.1 ∪ ↑d.1) (↑c.2 ∪ ↑d.2)] at hmerge
  have e1 : (↑c.1 ∪ ↑d.1 : Set (Fin n)) \ (↑c.2 ∪ ↑d.2) = ↑(mergeCmp c d).1 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  have e2 : (↑c.2 ∪ ↑d.2 : Set (Fin n)) \ (↑c.1 ∪ ↑d.1) = ↑(mergeCmp c d).2 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  rwa [e1, e2] at hmerge

/-- Pointwise integer vector-sum of a list of comparisons. -/
private def cvSumList {n : ℕ} (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) : ℤ :=
  (L.map (fun c => cmpVec c i)).sum

@[simp] private lemma cvSumList_cons {n : ℕ} (c : Finset (Fin n) × Finset (Fin n))
    (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    cvSumList (c :: L) i = cmpVec c i + cvSumList L i := by
  simp only [cvSumList, List.map_cons, List.sum_cons]

private lemma cvSumList_perm {n : ℕ} {L L' : List (Finset (Fin n) × Finset (Fin n))}
    (h : L.Perm L') (i : Fin n) : cvSumList L i = cvSumList L' i := by
  simp only [cvSumList]; exact (h.map _).sum_eq

/-- **Two-member null-forcing**: if two valid disjoint comparisons have vector-sum `≤ 0`
    everywhere with a strict negative coordinate, some atom is null (`ge ∅ {i}`).
    Disjointness forces `A ⊆ D` and `C ⊆ B`, giving `ge C A → ge C B → (Axiom A) ge ∅ (B\C)`
    and symmetrically `ge ∅ (D\A)`; the strict coordinate lies in one of them. -/
private lemma null_from_pair (sys : EpistemicSystemFA (Fin 4))
    {A B C D : Finset (Fin 4)}
    (hAB : sys.ge ↑A ↑B) (hCD : sys.ge ↑C ↑D)
    (hABd : Disjoint A B) (hCDd : Disjoint C D)
    (hle : ∀ i, cmpVec (A, B) i + cmpVec (C, D) i ≤ 0)
    (i₀ : Fin 4) (hlt : cmpVec (A, B) i₀ + cmpVec (C, D) i₀ < 0) :
    ∃ i, sys.ge (∅ : Set (Fin 4)) {i} := by
  -- A ⊆ D and C ⊆ B (membership facts from disjointness)
  have hAD : A ⊆ D := by
    intro a ha
    by_contra haD
    have := hle a
    simp only [cmpVec, if_pos ha, if_neg (Finset.disjoint_left.mp hABd ha), if_neg haD,
      sub_zero] at this
    split_ifs at this <;> omega
  have hCB : C ⊆ B := by
    intro c hc
    by_contra hcB
    have := hle c
    simp only [cmpVec, if_pos hc, if_neg (Finset.disjoint_left.mp hCDd hc), if_neg hcB,
      sub_zero] at this
    split_ifs at this <;> omega
  -- ge C A, ge C B
  have hCA : sys.ge ↑C ↑A := sys.trans _ _ _ hCD (sys.mono ↑A ↑D (Finset.coe_subset.mpr hAD))
  have hCB_ge : sys.ge ↑C ↑B := sys.trans _ _ _ hCA hAB
  -- Axiom A: ge ∅ (B \ C)
  have hBC : sys.ge (∅ : Set (Fin 4)) ↑(B \ C) := by
    have hax := (sys.additive ↑C ↑B).mp hCB_ge
    rwa [← Finset.coe_sdiff, ← Finset.coe_sdiff,
      Finset.sdiff_eq_empty_iff_subset.mpr hCB, Finset.coe_empty] at hax
  -- symmetric: ge A D, ge A C, ge A D? -> ge ∅ (D \ A)
  have hAC : sys.ge ↑A ↑C := sys.trans _ _ _ hAB (sys.mono ↑C ↑B (Finset.coe_subset.mpr hCB))
  have hAD_ge : sys.ge ↑A ↑D := sys.trans _ _ _ hAC hCD
  have hDA : sys.ge (∅ : Set (Fin 4)) ↑(D \ A) := by
    have hax := (sys.additive ↑A ↑D).mp hAD_ge
    rwa [← Finset.coe_sdiff, ← Finset.coe_sdiff,
      Finset.sdiff_eq_empty_iff_subset.mpr hAD, Finset.coe_empty] at hax
  -- strict coordinate i₀ ∈ (B \ C) ∪ (D \ A)
  have hmem : i₀ ∈ B \ C ∨ i₀ ∈ D \ A := by
    simp only [cmpVec, Finset.mem_sdiff] at hlt ⊢
    split_ifs at hlt <;> simp_all
  rcases hmem with hm | hm
  · exact ⟨i₀, sys.trans _ _ _ hBC (sys.mono {i₀} ↑(B \ C)
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm))⟩
  · exact ⟨i₀, sys.trans _ _ _ hDA (sys.mono {i₀} ↑(D \ A)
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm))⟩

/-! ### Bridging comparisons to ℚ sign vectors -/

/-- ℚ-valued sign vector of a comparison. -/
private def toQVec (c : Finset (Fin 4) × Finset (Fin 4)) : Fin 4 → ℚ :=
  fun i => (cmpVec c i : ℚ)

private lemma toQVec_apply (c : Finset (Fin 4) × Finset (Fin 4)) (k : Fin 4) :
    toQVec c k = (if k ∈ c.1 then (1 : ℚ) else 0) - (if k ∈ c.2 then 1 else 0) := by
  simp only [toQVec, cmpVec]
  split_ifs <;> norm_num

private lemma posSupport_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    SignVec.posSupport (toQVec c) = c.1 := by
  ext k
  rw [SignVec.mem_posSupport, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2 <;>
    first
      | exact absurd h2 (Finset.disjoint_left.mp hc h1)
      | norm_num [h1, h2]

private lemma negSupport_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    SignVec.negSupport (toQVec c) = c.2 := by
  ext k
  rw [SignVec.mem_negSupport, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2 <;>
    first
      | exact absurd h2 (Finset.disjoint_left.mp hc h1)
      | norm_num [h1, h2]

private lemma cmpVec_swap (A B : Finset (Fin 4)) (i : Fin 4) :
    cmpVec (B, A) i = -cmpVec (A, B) i := by
  simp only [cmpVec]
  ring

/-- Comparisons with both parts empty contribute nothing to the vector sum. -/
private lemma cvSumList_filter_ne_empty (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅) (i : Fin 4) :
    cvSumList (L.filter (fun c => c.1 ≠ ∅)) i = cvSumList L i := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    have h0' : ∀ c' ∈ rest, c'.1 = ∅ → c'.2 = ∅ :=
      fun c' hc' => h0 c' (List.mem_cons_of_mem _ hc')
    by_cases hc : c.1 = ∅
    · have hc2 := h0 c (List.mem_cons.mpr (Or.inl rfl)) hc
      rw [List.filter_cons_of_neg (by simp [hc]), cvSumList_cons, ih h0',
        show cmpVec c i = 0 from by simp [cmpVec, hc, hc2]]
      omega
    · rw [List.filter_cons_of_pos (by simp [hc]), cvSumList_cons, cvSumList_cons, ih h0']

/-- **The (V1) consequence** the recursion needs (the combinatorial crux, isolated):
    a "stuck" family — no generalized-mergeable pair, no mono-dominating member,
    summing to `(vpos, vneg)` with `vneg` nonempty — either contains a **null pair**
    (two members whose comparison vectors sum `≤ 0` with a strict negative coordinate)
    or has a member generalized-merged by the reversed target `(vneg, vpos)`.

    This is exactly (V1) applied to `L ∪ {(vneg, vpos)}` (balanced): (V1) yields a
    g-merge or anti-dom pair; an anti-dom pair inside `L` is a null pair, an anti-dom
    pair with the reversed target is mono-domination (excluded), a g-merge pair inside
    `L` is excluded by `hnogm`, leaving a g-merge with the reversed target.
    Verified true for all families (expert proof + exhaustive ≤5-circuit check). -/
private lemma v1_tailored
    (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (hdisj : ∀ c ∈ L, Disjoint c.1 c.2)
    {vpos vneg : Finset (Fin 4)}
    (hvpvn : Disjoint vpos vneg)
    (hsum : ∀ i, cvSumList L i = cmpVec (vpos, vneg) i)
    (hne : vneg.Nonempty)
    (hnotdom : ∀ c ∈ L, c.1 ⊆ vpos → ¬ vneg ⊆ c.2)
    (hnogm : ¬ ∃ c d rest, L.Perm (c :: d :: rest) ∧ Disjoint c.1 d.1 ∧ Disjoint c.2 d.2) :
    (∃ c ∈ L, ∃ d ∈ L,
        (∀ i, cmpVec (c.1, c.2) i + cmpVec (d.1, d.2) i ≤ 0) ∧
        (∃ i, cmpVec (c.1, c.2) i + cmpVec (d.1, d.2) i < 0))
      ∨ (∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2) := by
  classical
  -- Step A: a member with empty positive part and nonempty negative part is
  -- itself a null pair
  by_cases hemp : ∃ c ∈ L, c.1 = ∅ ∧ c.2.Nonempty
  · obtain ⟨c, hcL, hc1, k, hk⟩ := hemp
    refine Or.inl ⟨c, hcL, c, hcL, fun i => ?_, k, ?_⟩
    · simp only [cmpVec, hc1, if_neg (Finset.notMem_empty i)]
      split_ifs <;> omega
    · simp only [cmpVec, hc1, if_neg (Finset.notMem_empty k), if_pos hk]
      omega
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2
  · exact Or.inr hrd
  have h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅ := by
    intro c hc h1
    by_contra h2
    exact hemp ⟨c, hc, h1, Finset.nonempty_iff_ne_empty.mpr h2⟩
  -- Step C: the balanced ℚ sign-vector family on `L′ ∪ {reversed target}`
  set L' := L.filter (fun c => c.1 ≠ ∅) with hL'
  set l : List (Fin 4 → ℚ) := ((vneg, vpos) :: L').map toQVec with hl
  set S : Finset (Fin 4 → ℚ) := l.toFinset with hS
  have hfil : ∀ i, cvSumList L' i = cvSumList L i := by
    intro i
    rw [hL']
    exact cvSumList_filter_ne_empty L h0 i
  have hmem_shape : ∀ v ∈ S, ∃ c, (c = (vneg, vpos) ∨ c ∈ L') ∧ toQVec c = v := by
    intro v hv
    rw [hS, List.mem_toFinset, hl, List.mem_map] at hv
    obtain ⟨c, hc, hcv⟩ := hv
    exact ⟨c, List.mem_cons.mp hc, hcv⟩
  have hdisj' : ∀ c, (c = (vneg, vpos) ∨ c ∈ L') → Disjoint c.1 c.2 := by
    rintro c (rfl | hc)
    · exact hvpvn.symm
    · exact hdisj c (List.mem_of_mem_filter hc)
  have hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1 := by
    intro v hv i
    obtain ⟨c, _, rfl⟩ := hmem_shape v hv
    rw [toQVec_apply]
    split_ifs <;> norm_num
  have hposne : ∀ v ∈ S, ∃ i, v i = 1 := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := hmem_shape v hv
    rcases hc with rfl | hc
    · obtain ⟨k, hk⟩ := hne
      refine ⟨k, ?_⟩
      rw [toQVec_apply, if_pos hk, if_neg (Finset.disjoint_right.mp hvpvn hk)]
      norm_num
    · have hcL : c ∈ L := List.mem_of_mem_filter hc
      have hc1 : c.1 ≠ ∅ := by simpa using List.of_mem_filter hc
      obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hc1
      refine ⟨k, ?_⟩
      rw [toQVec_apply, if_pos hk, if_neg (Finset.disjoint_left.mp (hdisj c hcL) hk)]
      norm_num
  have hSne : S.Nonempty := by
    refine ⟨toQVec (vneg, vpos), ?_⟩
    rw [hS, List.mem_toFinset, hl]
    exact List.mem_map.mpr ⟨(vneg, vpos), List.mem_cons.mpr (Or.inl rfl), rfl⟩
  have hdQ : ∀ v ∈ S, 0 < ((l.count v : ℕ) : ℚ) := by
    intro v hv
    rw [hS, List.mem_toFinset] at hv
    exact_mod_cast List.count_pos_iff.mpr hv
  have hbal : ∑ v ∈ S, ((l.count v : ℕ) : ℚ) • v = 0 := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hc := Finset.sum_list_map_count l (fun v => v i)
    rw [hS, Finset.sum_congr rfl (fun v _ => (nsmul_eq_mul _ _).symm), ← hc, hl,
      List.map_map]
    simp only [Function.comp_def, List.map_cons, List.sum_cons]
    have hLs : (L'.map (fun c => toQVec c i)).sum = ((cvSumList L' i : ℤ) : ℚ) := by
      simp only [toQVec, cvSumList]
      rw [Int.cast_list_sum, List.map_map]
      rfl
    rw [hLs, hfil i, hsum i]
    simp only [toQVec]
    rw [cmpVec_swap]
    push_cast
    ring
  -- no-g-merge transfers to the vector family
  have hSnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (SignVec.posSupport v) (SignVec.posSupport w) ∧ Disjoint (SignVec.negSupport v) (SignVec.negSupport w)) := by
    rintro v hv w hw hvw ⟨hg1, hg2⟩
    obtain ⟨c, hc, rfl⟩ := hmem_shape v hv
    obtain ⟨c', hc', rfl⟩ := hmem_shape w hw
    rw [posSupport_toQVec (hdisj' c hc), posSupport_toQVec (hdisj' c' hc')] at hg1
    rw [negSupport_toQVec (hdisj' c hc), negSupport_toQVec (hdisj' c' hc')] at hg2
    rcases hc with rfl | hc <;> rcases hc' with rfl | hc'
    · exact hvw rfl
    · exact hrd ⟨c', List.mem_of_mem_filter hc', hg1, hg2⟩
    · exact hrd ⟨c, List.mem_of_mem_filter hc, hg1.symm, hg2.symm⟩
    · have hcc' : c ≠ c' := fun he => hvw (by rw [he])
      have hcL : c ∈ L := List.mem_of_mem_filter hc
      have hc'L : c' ∈ L := List.mem_of_mem_filter hc'
      have hp1 := List.perm_cons_erase hcL
      have hc'e : c' ∈ L.erase c := (List.mem_erase_of_ne (Ne.symm hcc')).mpr hc'L
      have hp2 := List.perm_cons_erase hc'e
      exact hnogm ⟨c, c', (L.erase c).erase c',
        hp1.trans (List.Perm.cons c hp2), hg1, hg2⟩
  -- Carathéodory pivot, then the finite core
  obtain ⟨S', hS'S, hS'ne, hS'card, d', hd', hsum'⟩ :=
    Caratheodory.exists_posdep_card_le_five S (fun v => ((l.count v : ℕ) : ℚ)) hdQ hSne hbal
  obtain ⟨v, hvS', w, hwS', hvw, had1, had2⟩ :=
    SignVec.exists_antidom_pair S' d' hd' (fun v hv => hsign v (hS'S hv))
      (fun v hv => hposne v (hS'S hv)) (fun v hv w hw => hSnogm v (hS'S hv) w (hS'S hw))
      hsum' hS'ne hS'card
  have hvS : v ∈ S := hS'S hvS'
  have hwS : w ∈ S := hS'S hwS'
  -- vector-level consequences of the anti-dominating pair
  have hps : ∀ i, v i = 1 → w i = -1 := fun i h => SignVec.mem_negSupport.mp (had1 (SignVec.mem_posSupport.mpr h))
  have hps' : ∀ i, w i = 1 → v i = -1 := fun i h => SignVec.mem_negSupport.mp (had2 (SignVec.mem_posSupport.mpr h))
  have hvle : ∀ i, v i + w i ≤ 0 := by
    intro i
    rcases eq_or_ne (v i) 1 with h1 | h1
    · rw [h1, hps i h1]; norm_num
    rcases eq_or_ne (w i) 1 with h2 | h2
    · rw [h2, hps' i h2]; norm_num
    rcases hsign v hvS i with h | h | h <;> rcases hsign w hwS i with h' | h' | h' <;>
      first
        | exact absurd h h1
        | exact absurd h' h2
        | (rw [h, h']; norm_num)
  have hvstrict : ∃ i, v i + w i < 0 := by
    by_contra hall
    push_neg at hall
    have heq : ∀ i, w i = -v i := fun i =>
      le_antisymm (by have := hvle i; linarith) (by have := hall i; linarith)
    refine hSnogm v hvS w hwS hvw ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk'
      rw [SignVec.mem_posSupport] at hk hk'
      rw [heq k, hk] at hk'
      norm_num at hk'
    · rw [Finset.disjoint_left]
      intro k hk hk'
      rw [SignVec.mem_negSupport] at hk hk'
      rw [heq k, hk] at hk'
      norm_num at hk'
  -- map the pair back to comparisons
  obtain ⟨c, hc, rfl⟩ := hmem_shape v hvS
  obtain ⟨c', hc', rfl⟩ := hmem_shape w hwS
  rcases hc with rfl | hc <;> rcases hc' with rfl | hc'
  · exact (hvw rfl).elim
  · -- the reversed target anti-dominated by `c'` is mono-domination, excluded
    exfalso
    refine hnotdom c' (List.mem_of_mem_filter hc') ?_ ?_
    · rwa [posSupport_toQVec (hdisj' c' (Or.inr hc')),
        negSupport_toQVec (hdisj' _ (Or.inl rfl))] at had2
    · rwa [posSupport_toQVec (hdisj' _ (Or.inl rfl)),
        negSupport_toQVec (hdisj' c' (Or.inr hc'))] at had1
  · exfalso
    refine hnotdom c (List.mem_of_mem_filter hc) ?_ ?_
    · rwa [posSupport_toQVec (hdisj' c (Or.inr hc)),
        negSupport_toQVec (hdisj' _ (Or.inl rfl))] at had1
    · rwa [posSupport_toQVec (hdisj' _ (Or.inl rfl)),
        negSupport_toQVec (hdisj' c (Or.inr hc))] at had2
  · -- both from `L`: the null pair
    refine Or.inl ⟨c, List.mem_of_mem_filter hc, c', List.mem_of_mem_filter hc',
      fun i => ?_, ?_⟩
    · have h := hvle i
      simp only [toQVec] at h
      exact_mod_cast h
    · obtain ⟨i, hi⟩ := hvstrict
      refine ⟨i, ?_⟩
      simp only [toQVec] at hi
      exact_mod_cast hi

/-- **Recombine** (case 4 of the merge recursion): if a member `c` is valid, the
    reversed target `r = (vneg, vpos)` generalized-merges `c` (`Disjoint vneg c.1`,
    `Disjoint vpos c.2`), and the residual target `t' = t − cmpVec c` — namely
    `(p, q)` with `p = (vpos \ c.1) ∪ (c.2 \ vneg)`, `q = (vneg \ c.2) ∪ (c.1 \ vpos)`
    — is provable (`ge p q`, the IH), then `ge vpos vneg`. Proved by merging `(p,q)`
    with `c` via `mergeCmp_valid`; the disjoint-normal-form is exactly `(vpos, vneg)`. -/
private lemma recombine (sys : EpistemicSystemFA (Fin 4))
    (vpos vneg : Finset (Fin 4)) (c : Finset (Fin 4) × Finset (Fin 4))
    (hcd : Disjoint c.1 c.2) (hvv : Disjoint vpos vneg)
    (hrc1 : Disjoint vneg c.1) (hrc2 : Disjoint vpos c.2)
    (hc : sys.ge ↑c.1 ↑c.2)
    (hX : sys.ge ↑((vpos \ c.1) ∪ (c.2 \ vneg)) ↑((vneg \ c.2) ∪ (c.1 \ vpos))) :
    sys.ge ↑vpos ↑vneg := by
  set p := (vpos \ c.1) ∪ (c.2 \ vneg) with hp
  set q := (vneg \ c.2) ∪ (c.1 \ vpos) with hq
  have dvv : ∀ x, x ∈ vpos → x ∉ vneg := fun x h => Finset.disjoint_left.mp hvv h
  have dvc1 : ∀ x, x ∈ vneg → x ∉ c.1 := fun x h => Finset.disjoint_left.mp hrc1 h
  have dvc2 : ∀ x, x ∈ vpos → x ∉ c.2 := fun x h => Finset.disjoint_left.mp hrc2 h
  have dc : ∀ x, x ∈ c.1 → x ∉ c.2 := fun x h => Finset.disjoint_left.mp hcd h
  have hdp : Disjoint p c.1 := by
    rw [hp, Finset.disjoint_union_left]
    exact ⟨Finset.sdiff_disjoint, Disjoint.mono_left Finset.sdiff_subset hcd.symm⟩
  have hdq : Disjoint q c.2 := by
    rw [hq, Finset.disjoint_union_left]
    exact ⟨Finset.sdiff_disjoint, Disjoint.mono_left Finset.sdiff_subset hcd⟩
  have hmerge := mergeCmp_valid sys (c := (p, q)) (d := c) hX hc hdp hdq
  have e1 : (mergeCmp (p, q) c).1 = vpos := by
    apply Finset.ext; intro x
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have e2 : (mergeCmp (p, q) c).2 = vneg := by
    apply Finset.ext; intro x
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rwa [e1, e2] at hmerge

/-- **Merge-to-single**: on a no-null Fin 4 system, any valid family of disjoint
    comparisons whose vector-sum equals a single comparison vector `(vpos, vneg)`
    proves `vpos ≿ vneg`. Four uniform rules: trivial target (`vneg = ∅`),
    mono-domination, merge a generalizable pair and recurse, or (no g-merge pair)
    `v1_tailored` gives a null pair (→ contradiction via `hnull`) or a member merged
    by the reversed target (→ peel it, recurse, `recombine`). -/
private theorem merge_to_single (sys : EpistemicSystemFA (Fin 4))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i})
    (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (hdisj : ∀ c ∈ L, Disjoint c.1 c.2)
    (hvalid : ∀ c ∈ L, sys.ge ↑c.1 ↑c.2)
    (vpos vneg : Finset (Fin 4))
    (hvpvn : Disjoint vpos vneg)
    (hsum : ∀ i, cvSumList L i = cmpVec (vpos, vneg) i) :
    sys.ge ↑vpos ↑vneg := by
  by_cases hne : vneg.Nonempty
  · by_cases hdom : ∃ c ∈ L, c.1 ⊆ vpos ∧ vneg ⊆ c.2
    · -- mono-domination discharge
      obtain ⟨c, hcL, hc1, hc2⟩ := hdom
      exact ge_mono_dominated sys (hvalid c hcL)
        (Finset.coe_subset.mpr hc1) (Finset.coe_subset.mpr hc2)
    · -- no mono-dominating member: either a gmerge pair (merge & recurse) or, failing
      -- that, a forced null atom contradicting `hnull`.
      push_neg at hdom
      by_cases hgm : ∃ c d rest, L.Perm (c :: d :: rest) ∧ Disjoint c.1 d.1 ∧ Disjoint c.2 d.2
      case neg =>
        rcases v1_tailored L hdisj hvpvn hsum hne hdom hgm with
          ⟨c, hcL, d, hdL, hle, i0, hlt⟩ | ⟨c, hcL, hrc1, hrc2⟩
        · -- null pair → null atom → contradicts hnull
          obtain ⟨i, hi⟩ := null_from_pair sys (hvalid c hcL) (hvalid d hdL)
            (hdisj c hcL) (hdisj d hdL) hle i0 hlt
          exact absurd hi (hnull i)
        · -- reversed target g-merges `c`: peel `c`, recurse on residual target, recombine
          have hperm := List.perm_cons_erase hcL
          have hsum' : ∀ i, cvSumList (L.erase c) i =
              cmpVec ((vpos \ c.1) ∪ (c.2 \ vneg), (vneg \ c.2) ∪ (c.1 \ vpos)) i := by
            intro i
            have h1 : cvSumList L i = cmpVec c i + cvSumList (L.erase c) i := by
              rw [cvSumList_perm hperm i, cvSumList_cons]
            have he : cvSumList (L.erase c) i = cmpVec (vpos, vneg) i - cmpVec c i := by
              have := hsum i; omega
            rw [he]
            have a1 : i ∈ vpos → i ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a2 : i ∈ vpos → i ∉ c.2 := fun h => Finset.disjoint_left.mp hrc2 h
            have a3 : i ∈ vneg → i ∉ c.1 := fun h => Finset.disjoint_left.mp hrc1 h
            have a4 : i ∈ c.1 → i ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [cmpVec, Finset.mem_union, Finset.mem_sdiff]
            by_cases h1v : i ∈ vpos <;> by_cases h2v : i ∈ vneg <;>
              by_cases h3v : i ∈ c.1 <;> by_cases h4v : i ∈ c.2 <;>
              simp_all
          have hpq : Disjoint ((vpos \ c.1) ∪ (c.2 \ vneg)) ((vneg \ c.2) ∪ (c.1 \ vpos)) := by
            rw [Finset.disjoint_left]; intro x hxp hxq
            have a1 : x ∈ vpos → x ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a4 : x ∈ c.1 → x ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [Finset.mem_union, Finset.mem_sdiff] at hxp hxq
            tauto
          have hdisj' : ∀ x ∈ L.erase c, Disjoint x.1 x.2 :=
            fun x hx => hdisj x (List.mem_of_mem_erase hx)
          have hvalid' : ∀ x ∈ L.erase c, sys.ge ↑x.1 ↑x.2 :=
            fun x hx => hvalid x (List.mem_of_mem_erase hx)
          have IH := merge_to_single sys hnull (L.erase c) hdisj' hvalid'
            ((vpos \ c.1) ∪ (c.2 \ vneg)) ((vneg \ c.2) ∪ (c.1 \ vpos)) hpq hsum'
          exact recombine sys vpos vneg c (hdisj c hcL) hvpvn hrc1 hrc2 (hvalid c hcL) IH
      obtain ⟨c, d, rest, hperm, hpd, hnd⟩ := hgm
      -- new list: mergeCmp c d :: rest, one shorter
      have hcmem : c ∈ L := hperm.mem_iff.mpr (by simp)
      have hdmem : d ∈ L := hperm.mem_iff.mpr (by simp)
      have hrestsub : ∀ x ∈ rest, x ∈ L := fun x hx => hperm.mem_iff.mpr (by simp [hx])
      have hdisj' : ∀ x ∈ mergeCmp c d :: rest, Disjoint x.1 x.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [mergeCmp]; exact disjoint_sdiff_sdiff
        · exact hdisj x (hrestsub x hx)
      have hvalid' : ∀ x ∈ mergeCmp c d :: rest, sys.ge ↑x.1 ↑x.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact mergeCmp_valid sys (hvalid c hcmem) (hvalid d hdmem) hpd hnd
        · exact hvalid x (hrestsub x hx)
      have hsum' : ∀ i, cvSumList (mergeCmp c d :: rest) i = cmpVec (vpos, vneg) i := by
        intro i
        rw [cvSumList_cons, cmpVec_mergeCmp c d hpd hnd i, ← hsum i,
            cvSumList_perm hperm i]
        simp only [cvSumList_cons]
        omega
      exact merge_to_single sys hnull (mergeCmp c d :: rest) hdisj' hvalid' vpos vneg hvpvn hsum'
  · -- trivial-target discharge: vneg = ∅
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simpa using ge_empty_target sys (↑vpos)
termination_by L.length
decreasing_by
  all_goals
    have h := hperm.length_eq
    simp only [List.length_cons] at h ⊢
    omega

/-! ### Denominator-clearing infrastructure

To turn a rational-weighted neutral portfolio into an integer-balanced list of unit
comparisons, multiply every weight by the common denominator `D` and replicate each
comparison `wc.weight·D` times. The helpers below compute the vector sum of such a
`flatMap`-of-`replicate` list and recover `D · weightedSum` after casting back to `ℚ`. -/

private lemma cvSumList_flatMap {n : ℕ} {α : Type*} (P : List α)
    (f : α → List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    cvSumList (P.flatMap f) i = (P.map (fun a => cvSumList (f a) i)).sum := by
  induction P with
  | nil => simp [cvSumList]
  | cons a P ih =>
    rw [List.flatMap_cons,
      show cvSumList (f a ++ List.flatMap f P) i
          = cvSumList (f a) i + cvSumList (List.flatMap f P) i by
        simp only [cvSumList, List.map_append, List.sum_append], ih,
      List.map_cons, List.sum_cons]

private lemma cvSumList_replicate {n : ℕ} (m : ℕ) (c : Finset (Fin n) × Finset (Fin n))
    (i : Fin n) : cvSumList (List.replicate m c) i = (m : ℤ) * cmpVec c i := by
  simp only [cvSumList, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

private lemma weight_mul_den (q : ℚ) : q * (q.den : ℚ) = (q.num : ℚ) := by
  have h := Rat.num_div_den q
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [div_eq_iff hd] at h
  exact h.symm

private lemma den_prod_pos (P : List (WComparison 4)) :
    0 < (P.map (fun wc => wc.weight.den)).prod := by
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos a.weight.den_pos ih

/-- Casting the integer multiplicities back to `ℚ` recovers `D · weightedSum`. -/
private lemma cleared_sum_eq (P : Portfolio 4) (i : Fin 4) (D : ℕ)
    (mult : WComparison 4 → ℕ)
    (hcast : ∀ wc, List.Mem wc P → ((mult wc : ℤ) : ℚ) = wc.weight * (D : ℚ)) :
    (((P.map (fun wc => (mult wc : ℤ) * cmpVec (wc.left, wc.right) i)).sum : ℤ) : ℚ)
      = (D : ℚ) * P.weightedSum i := by
  rw [Portfolio.weightedSum]
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [ih (fun wc h => hcast wc (List.Mem.tail a h)), mul_add]
    congr 1
    rw [hcast a (List.Mem.head P)]
    show a.weight * ↑D * ↑(comparisonVec 4 a.left a.right i)
        = ↑D * (a.weight * ↑(comparisonVec 4 a.left a.right i))
    ring

/-- **Integer-balance bridge**: from a valid neutral portfolio `P` with a member `s`,
    clearing denominators yields a unit-weight list `R` of valid disjoint comparisons
    with `cvSumList R = cmpVec (s.right, s.left)` — the denominator-cleared balanced
    multiset with one copy of `s` removed. -/
private theorem exists_balanced_list (sys : EpistemicSystemFA (Fin 4))
    (P : Portfolio 4) (hvalid : P.isValid sys.ge) (hneutral : P.isNeutral)
    (s : WComparison 4) (hsmem : List.Mem s P) :
    ∃ R : List (Finset (Fin 4) × Finset (Fin 4)),
      (∀ c ∈ R, Disjoint c.1 c.2) ∧ (∀ c ∈ R, sys.ge ↑c.1 ↑c.2) ∧
      (∀ i, cvSumList R i = cmpVec (s.right, s.left) i) := by
  set D : ℕ := (P.map (fun wc => wc.weight.den)).prod with hD
  have hDpos : 0 < D := hD ▸ den_prod_pos P
  have hdvd : ∀ wc, List.Mem wc P → wc.weight.den ∣ D := by
    intro wc hwc
    rw [hD]
    exact List.dvd_prod (by simp only [List.mem_map]; exact ⟨wc, hwc, rfl⟩)
  set mult : WComparison 4 → ℕ :=
    fun wc => (wc.weight.num * (D / wc.weight.den : ℕ)).toNat with hmult
  have hcast : ∀ wc, List.Mem wc P → ((mult wc : ℤ) : ℚ) = wc.weight * (D : ℚ) := by
    intro wc hwc
    obtain ⟨k, hk⟩ := hdvd wc hwc
    have hdk : D / wc.weight.den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k wc.weight.den_pos
    have hnumpos : 0 < wc.weight.num := Rat.num_pos.mpr wc.weight_pos
    have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hk; omega)
    have hmz : 0 ≤ wc.weight.num * (D / wc.weight.den : ℕ) := by
      rw [hdk]; positivity
    rw [hmult]
    simp only
    rw [Int.toNat_of_nonneg hmz, hdk]
    push_cast
    rw [hk]
    push_cast
    rw [← mul_assoc, weight_mul_den]
  have hmultpos : ∀ wc, List.Mem wc P → 1 ≤ mult wc := by
    intro wc hwc
    obtain ⟨k, hk⟩ := hdvd wc hwc
    have hdk : D / wc.weight.den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k wc.weight.den_pos
    have hnumpos : 0 < wc.weight.num := Rat.num_pos.mpr wc.weight_pos
    have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hk; omega)
    rw [hmult]
    simp only
    rw [hdk]
    have hp : 0 < wc.weight.num * (k : ℤ) := by positivity
    omega
  set Lfull : List (Finset (Fin 4) × Finset (Fin 4)) :=
    P.flatMap (fun wc => List.replicate (mult wc) (wc.left, wc.right)) with hLfull
  have hmemLfull : ∀ c, c ∈ Lfull → ∃ wc, List.Mem wc P ∧ c = (wc.left, wc.right) := by
    intro c hc
    rw [hLfull, List.mem_flatMap] at hc
    obtain ⟨wc, hwc, hc⟩ := hc
    exact ⟨wc, hwc, List.eq_of_mem_replicate hc⟩
  have hLdisj : ∀ c ∈ Lfull, Disjoint c.1 c.2 := by
    intro c hc
    obtain ⟨wc, _, rfl⟩ := hmemLfull c hc
    exact wc.disjoint
  have hLvalid : ∀ c ∈ Lfull, sys.ge ↑c.1 ↑c.2 := by
    intro c hc
    obtain ⟨wc, hwc, rfl⟩ := hmemLfull c hc
    exact hvalid wc hwc
  have hLsum : ∀ i, cvSumList Lfull i = 0 := by
    intro i
    have hstep : cvSumList Lfull i =
        (P.map (fun wc => (mult wc : ℤ) * cmpVec (wc.left, wc.right) i)).sum := by
      rw [hLfull, cvSumList_flatMap]
      congr 1
      apply List.map_congr_left
      intro wc _
      rw [cvSumList_replicate]
    have hzero : ((cvSumList Lfull i : ℤ) : ℚ) = 0 := by
      rw [hstep, cleared_sum_eq P i D mult hcast, hneutral i, mul_zero]
    exact_mod_cast hzero
  have hsLfull : (s.left, s.right) ∈ Lfull := by
    rw [hLfull, List.mem_flatMap]
    exact ⟨s, hsmem, List.mem_replicate.mpr ⟨by have := hmultpos s hsmem; omega, rfl⟩⟩
  refine ⟨Lfull.erase (s.left, s.right), ?_, ?_, ?_⟩
  · intro c hc
    exact hLdisj c (List.mem_of_mem_erase hc)
  · intro c hc
    exact hLvalid c (List.mem_of_mem_erase hc)
  · intro i
    have hperm := List.perm_cons_erase hsLfull
    have h1 : cvSumList Lfull i
        = cmpVec (s.left, s.right) i + cvSumList (Lfull.erase (s.left, s.right)) i := by
      rw [cvSumList_perm hperm i, cvSumList_cons]
    have h2 : cvSumList (Lfull.erase (s.left, s.right)) i = - cmpVec (s.left, s.right) i := by
      have := hLsum i; omega
    rw [h2]
    simp only [cmpVec]
    split_ifs <;> omega

/-- **No-null case** of Theorem 8a (Fin 4): when no atom is null, every valid neutral
    portfolio is non-strict, via the merge reduction `merge_to_single`. -/
theorem no_null_cancellation (sys : EpistemicSystemFA (Fin 4))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i}) :
    Cancellation 4 sys.ge := by
  intro P hvalid hneutral hstrict
  obtain ⟨s, hsmem, hsstrict⟩ := hstrict
  apply hsstrict
  obtain ⟨R, hRdisj, hRvalid, hRsum⟩ := exists_balanced_list sys P hvalid hneutral s hsmem
  exact merge_to_single sys hnull R hRdisj hRvalid s.right s.left s.disjoint.symm hRsum

/-! ### Fin 3 via lexicographic extension

A `Fin 3` system with no null atoms extends to a `Fin 4` system by adding a
*dominant* fourth world: comparisons are decided first by membership of the
new world, then by the restriction to the original three.  The extension
preserves the FA axioms and the absence of null atoms, and reflects
cancellation, so `no_null_cancellation` discharges the no-null case of
`fa_cancellation_fin3`; null atoms reduce to `representable_fin2`.  Theorem 8a
for `Fin 3` then *follows from* cancellation — replacing the former
measure-by-measure case analysis. -/

/-- Restriction of a `Fin 4` proposition to the first three worlds. -/
private def restrict3 (A : Set (Fin 4)) : Set (Fin 3) := {i | Fin.castSucc i ∈ A}

/-- Lexicographic extension: the new world `Fin.last 3` dominates; ties break
    by the restriction. -/
def extendFA (sys : EpistemicSystemFA (Fin 3)) : EpistemicSystemFA (Fin 4) where
  ge A B := (Fin.last 3 ∈ A ∧ Fin.last 3 ∉ B) ∨
    ((Fin.last 3 ∈ A ↔ Fin.last 3 ∈ B) ∧ sys.ge (restrict3 A) (restrict3 B))
  refl _ := Or.inr ⟨Iff.rfl, sys.refl _⟩
  mono A B hAB := by
    by_cases hb : Fin.last 3 ∈ B
    · by_cases ha : Fin.last 3 ∈ A
      · exact Or.inr ⟨iff_of_true hb ha, sys.mono _ _ fun i hi => hAB hi⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨iff_of_false hb (fun h => hb (hAB h)),
        sys.mono _ _ fun i hi => hAB hi⟩
  bottom := Or.inl ⟨trivial, fun h => h⟩
  nonTrivial := by
    rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr trivial
  total A B := by
    by_cases ha : Fin.last 3 ∈ A <;> by_cases hb : Fin.last 3 ∈ B
    · rcases sys.total (restrict3 A) (restrict3 B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_true ha hb, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_true hb ha, h⟩)
    · exact Or.inl (Or.inl ⟨ha, hb⟩)
    · exact Or.inr (Or.inl ⟨hb, ha⟩)
    · rcases sys.total (restrict3 A) (restrict3 B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_false ha hb, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_false hb ha, h⟩)
  trans A B C := by
    rintro (⟨ha, hnb⟩ | ⟨hab, hge1⟩) (⟨hb, hnc⟩ | ⟨hbc, hge2⟩)
    · exact absurd hb hnb
    · exact Or.inl ⟨ha, fun hc => hnb (hbc.mpr hc)⟩
    · exact Or.inl ⟨hab.mpr hb, hnc⟩
    · exact Or.inr ⟨hab.trans hbc, sys.trans _ _ _ hge1 hge2⟩
  additive A B := by
    by_cases ha : Fin.last 3 ∈ A <;> by_cases hb : Fin.last 3 ∈ B
    · -- tie on both sides; restriction additivity carries it
      have hab : Fin.last 3 ∉ A \ B := fun h => h.2 hb
      have hba : Fin.last 3 ∉ B \ A := fun h => h.2 ha
      constructor
      · rintro (⟨-, hnb⟩ | ⟨-, hge⟩)
        · exact absurd hb hnb
        · exact Or.inr ⟨iff_of_false hab hba, (sys.additive _ _).mp hge⟩
      · rintro (⟨h3, -⟩ | ⟨-, hge⟩)
        · exact absurd h3 hab
        · exact Or.inr ⟨iff_of_true ha hb, (sys.additive _ _).mpr hge⟩
    · -- the new world sits in `A \ B`: both sides true by dominance
      exact iff_of_true (Or.inl ⟨ha, hb⟩) (Or.inl ⟨⟨ha, hb⟩, fun h => hb h.1⟩)
    · -- the new world sits in `B \ A`: both sides false
      refine iff_of_false ?_ ?_
      · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
        · exact ha h3
        · exact ha (hiff.mpr hb)
      · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
        · exact ha h3.1
        · exact ha (hiff.mpr ⟨hb, ha⟩).1
    · -- the new world is absent everywhere; restriction additivity again
      have hab : Fin.last 3 ∉ A \ B := fun h => ha h.1
      have hba : Fin.last 3 ∉ B \ A := fun h => hb h.1
      constructor
      · rintro (⟨h3, -⟩ | ⟨-, hge⟩)
        · exact absurd h3 ha
        · exact Or.inr ⟨iff_of_false hab hba, (sys.additive _ _).mp hge⟩
      · rintro (⟨h3, -⟩ | ⟨-, hge⟩)
        · exact absurd h3 hab
        · exact Or.inr ⟨iff_of_false ha hb, (sys.additive _ _).mpr hge⟩

/-- The extension preserves the absence of null atoms. -/
private lemma extendFA_no_null (sys : EpistemicSystemFA (Fin 3))
    (hnull : ∀ i : Fin 3, ¬sys.ge ∅ {i}) :
    ∀ j : Fin 4, ¬(extendFA sys).ge ∅ {j} := by
  refine Fin.lastCases ?_ ?_
  · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr rfl
  · intro i
    rintro (⟨h3, -⟩ | ⟨-, hge⟩)
    · exact h3
    · refine hnull i ?_
      have he : restrict3 {Fin.castSucc i} = {i} := by
        ext k
        simp [restrict3, Fin.castSucc_inj, eq_comm]
      rwa [show restrict3 ∅ = ∅ from rfl, he] at hge

/-- The new world never lies in an embedded finset. -/
private lemma last_notMem_map (s : Finset (Fin 3)) :
    Fin.last 3 ∉ s.map Fin.castSuccEmb := by
  rw [Finset.mem_map]
  rintro ⟨i, -, hi⟩
  exact absurd hi (Fin.castSucc_lt_last i).ne

/-- Embedded finsets restrict back to themselves. -/
private lemma restrict3_coe_map (s : Finset (Fin 3)) :
    restrict3 ↑(s.map Fin.castSuccEmb) = ↑s := by
  ext i
  show Fin.castSuccEmb i ∈ ↑(s.map Fin.castSuccEmb) ↔ _
  rw [Finset.mem_coe, Finset.mem_map']

/-- Embed a `Fin 3` comparison into `Fin 4` along `Fin.castSucc`. -/
private def embedComparison (wc : WComparison 3) : WComparison 4 where
  left := wc.left.map Fin.castSuccEmb
  right := wc.right.map Fin.castSuccEmb
  weight := wc.weight
  disjoint := by
    rw [Finset.disjoint_map]
    exact wc.disjoint
  weight_pos := wc.weight_pos

private lemma comparisonVec_map_last (A B : Finset (Fin 3)) :
    comparisonVec 4 (A.map Fin.castSuccEmb) (B.map Fin.castSuccEmb) (Fin.last 3) = 0 := by
  unfold comparisonVec
  rw [if_neg (last_notMem_map A), if_neg (last_notMem_map B), sub_zero]

private lemma comparisonVec_map_castSucc (A B : Finset (Fin 3)) (i : Fin 3) :
    comparisonVec 4 (A.map Fin.castSuccEmb) (B.map Fin.castSuccEmb) i.castSucc =
      comparisonVec 3 A B i := by
  show ((if Fin.castSuccEmb i ∈ A.map Fin.castSuccEmb then 1 else 0) -
      (if Fin.castSuccEmb i ∈ B.map Fin.castSuccEmb then 1 else 0) : ℤ) =
    comparisonVec 3 A B i
  simp only [Finset.mem_map']
  rfl

/-- Cancellation transfers back along the lexicographic extension. -/
private theorem cancellation_extendFA (sys : EpistemicSystemFA (Fin 3))
    (h : Cancellation 4 (extendFA sys).ge) : Cancellation 3 sys.ge := by
  intro P hvalid hneutral hstrict
  refine h (P.map embedComparison) ?_ ?_ ?_
  · -- validity transfers through the restriction
    intro wc' hmem
    obtain ⟨wc, hwcP, rfl⟩ := List.mem_map.mp hmem
    have hL : (embedComparison wc).left = wc.left.map Fin.castSuccEmb := rfl
    have hR : (embedComparison wc).right = wc.right.map Fin.castSuccEmb := rfl
    refine Or.inr ⟨iff_of_false ?_ ?_, ?_⟩
    · rw [hL]
      exact fun h3 => last_notMem_map _ (Finset.mem_coe.mp h3)
    · rw [hR]
      exact fun h3 => last_notMem_map _ (Finset.mem_coe.mp h3)
    · rw [hL, hR, restrict3_coe_map, restrict3_coe_map]
      exact hvalid wc hwcP
  · -- neutrality: the new coordinate vanishes; the old ones are unchanged
    refine Fin.lastCases ?_ ?_
    · simp only [Portfolio.weightedSum, List.map_map]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨wc, -, rfl⟩ := List.mem_map.mp hx
      show (embedComparison wc).weight *
        ((comparisonVec 4 (embedComparison wc).left (embedComparison wc).right
          (Fin.last 3) : ℤ) : ℚ) = 0
      rw [show (embedComparison wc).left = wc.left.map Fin.castSuccEmb from rfl,
        show (embedComparison wc).right = wc.right.map Fin.castSuccEmb from rfl,
        comparisonVec_map_last]
      simp
    · intro i
      have he : Portfolio.weightedSum (P.map embedComparison) i.castSucc =
          P.weightedSum i := by
        simp only [Portfolio.weightedSum, List.map_map]
        congr 1
        refine List.map_congr_left fun wc _ => ?_
        show (embedComparison wc).weight *
            ((comparisonVec 4 (embedComparison wc).left (embedComparison wc).right
              i.castSucc : ℤ) : ℚ) =
          wc.weight * ((comparisonVec 3 wc.left wc.right i : ℤ) : ℚ)
        rw [show (embedComparison wc).left = wc.left.map Fin.castSuccEmb from rfl,
          show (embedComparison wc).right = wc.right.map Fin.castSuccEmb from rfl,
          comparisonVec_map_castSucc,
          show (embedComparison wc).weight = wc.weight from rfl]
      rw [he]
      exact hneutral i
  · -- strictness transfers
    obtain ⟨wc, hwcP, hstr⟩ := hstrict
    refine ⟨embedComparison wc, List.mem_map.mpr ⟨wc, hwcP, rfl⟩, fun hge => hstr ?_⟩
    have hL : (embedComparison wc).left = wc.left.map Fin.castSuccEmb := rfl
    have hR : (embedComparison wc).right = wc.right.map Fin.castSuccEmb := rfl
    rcases hge with ⟨h3, -⟩ | ⟨-, hge⟩
    · rw [hR] at h3
      exact absurd (Finset.mem_coe.mp h3) (last_notMem_map _)
    · rwa [hL, hR, restrict3_coe_map, restrict3_coe_map] at hge

/-- **Cancellation for Fin 3**, structurally: null atoms reduce to `Fin 2`
    representability; the no-null case extends lexicographically into `Fin 4`
    and pulls back through `no_null_cancellation`. -/
theorem fa_cancellation_fin3 (sys : EpistemicSystemFA (Fin 3)) :
    Cancellation 3 sys.ge := by
  by_cases h0 : sys.ge ∅ {(0 : Fin 3)}
  · have hnn : ∃ i : Fin 2, ¬sys.ge ∅ {Fin.succ i} := by
      by_contra hall
      push_neg at hall
      obtain ⟨i, hi⟩ := not_all_null sys
      fin_cases i
      · exact hi h0
      · exact hi (by simpa using hall 0)
      · exact hi (by simpa using hall 1)
    obtain ⟨m, hm⟩ := null_elem_reduce sys h0 hnn (fun sys' => representable_fin2 sys')
    exact representable_implies_cancellation m hm
  · by_cases h1 : sys.ge ∅ {(1 : Fin 3)}
    · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 1) sys
        (null_elem_reduce (transportFA (Equiv.swap 0 1) sys)
          ((perm_null_convert _ _ 0 1 (by decide)).mpr h1)
          ⟨0, fun h => h0 ((perm_null_convert _ _ 1 0 (by decide)).mp h)⟩
          (fun sys' => representable_fin2 sys'))
      exact representable_implies_cancellation m hm
    · by_cases h2 : sys.ge ∅ {(2 : Fin 3)}
      · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 2) sys
          (null_elem_reduce (transportFA (Equiv.swap 0 2) sys)
            ((perm_null_convert _ _ 0 2 (by decide)).mpr h2)
            ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
            (fun sys' => representable_fin2 sys'))
        exact representable_implies_cancellation m hm
      · have hnull : ∀ i : Fin 3, ¬sys.ge ∅ {i} := fun i => by fin_cases i <;> assumption
        exact cancellation_extendFA sys
          (no_null_cancellation (extendFA sys) (extendFA_no_null sys hnull))

/-- **Theorem 8a for Fin 3**: every FA system on three elements is representable —
    now *derived from* Scott cancellation, replacing the former measure-by-measure
    case analysis. -/
theorem representable_fin3 (sys : EpistemicSystemFA (Fin 3)) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin3 sys)

/-- Null element `0` on `Fin 4`: cancellation via null reduction to `Fin 3`. -/
private theorem fa_cancellation_fin4_null0' (sys : EpistemicSystemFA (Fin 4))
    (h0 : sys.ge ∅ {(0 : Fin 4)})
    (hnn : ∃ i : Fin 3, ¬sys.ge ∅ {Fin.succ i}) :
    Cancellation 4 sys.ge := by
  obtain ⟨m, hm⟩ := null_elem_reduce sys h0 hnn (fun sys' => representable_fin3 sys')
  exact representable_implies_cancellation m hm

/-- **Theorem 8a (Fin 4), structural**: every FA system on `Fin 4` satisfies
    cancellation. Null cases reduce to `Fin 3` (existing `null_elem_reduce` machinery);
    the no-null case is the merge reduction `no_null_cancellation`. Replaces the
    88-chamber `fa_cancellation_fin4`. -/
theorem fa_cancellation_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    Cancellation 4 sys.ge := by
  by_cases h0 : sys.ge ∅ {(0 : Fin 4)}
  · exact fa_cancellation_fin4_null0' sys h0 (by
      by_contra hall; push_neg at hall
      obtain ⟨i, hi⟩ := not_all_null sys
      fin_cases i
      · exact hi h0
      · exact hi (by simpa using hall 0)
      · exact hi (by simpa using hall 1)
      · exact hi (by simpa using hall 2))
  · by_cases h1 : sys.ge ∅ {(1 : Fin 4)}
    · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 1) sys
        (null_elem_reduce (transportFA (Equiv.swap 0 1) sys)
          ((perm_null_convert _ _ 0 1 (by decide)).mpr h1)
          ⟨0, fun h => h0 ((perm_null_convert _ _ 1 0 (by decide)).mp h)⟩
          (fun sys' => representable_fin3 sys'))
      exact representable_implies_cancellation m hm
    · by_cases h2 : sys.ge ∅ {(2 : Fin 4)}
      · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 2) sys
          (null_elem_reduce (transportFA (Equiv.swap 0 2) sys)
            ((perm_null_convert _ _ 0 2 (by decide)).mpr h2)
            ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
            (fun sys' => representable_fin3 sys'))
        exact representable_implies_cancellation m hm
      · by_cases h3 : sys.ge ∅ {(3 : Fin 4)}
        · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 3) sys
            (null_elem_reduce (transportFA (Equiv.swap 0 3) sys)
              ((perm_null_convert _ _ 0 3 (by decide)).mpr h3)
              ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
              (fun sys' => representable_fin3 sys'))
          exact representable_implies_cancellation m hm
        · exact no_null_cancellation sys (fun i => by fin_cases i <;> assumption)

/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem representable_fin4 (sys : EpistemicSystemFA (Fin 4)) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end Core.Scale
