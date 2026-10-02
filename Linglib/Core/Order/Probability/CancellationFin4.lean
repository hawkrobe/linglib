module

public import Linglib.Core.Analysis.Convex.Caratheodory
public import Linglib.Core.LinearAlgebra.AffineSpace.FiniteDimensional
public import Linglib.Core.Order.Probability.Scott
public import Linglib.Core.Order.SignVectors
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FinCases

/-! # Cancellation on three and four atoms

Every qualitative probability order on at most four atoms satisfies Scott cancellation, hence is
representable by a finitely additive measure, as Kraft, Pratt and Seidenberg showed.

## Main declarations

* `ComparativeProbability.no_null_cancellation`: cancellation on `Fin 4` with no null atoms.
* `ComparativeProbability.fa_cancellation_fin4`: every FA system on `Fin 4` satisfies
  cancellation.
* `ComparativeProbability.representable_fin4`: every FA system on `Fin 4` is representable.

## Implementation notes

The proof rests on two imported layers, Carathéodory's theorem at the origin
(`exists_finset_eq_pos_convex_span_of_mem_convexHull`) and the sign-vector core
(`SignVec.exists_antidom_pair`), and adds the merge reduction: a valid family
of comparisons whose integer sum is a single sign vector proves that
comparison (`merge_to_single`), by a four-rule recursion whose stuck case is
discharged through the sign-vector core via `v1_tailored`.  Comparisons are
`Scott.lean`'s sign vectors; two comparisons with no shared nonzero coordinate
*merge* into the sign of their sum (`merge`), and the merge recursion itself
is private plumbing, so only the theorems above are exported.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

/-! ### Merging comparisons

Two sign vectors are *mergeable* when no coordinate carries the same nonzero
sign in both; their merge is the sign of their sum, which is then their sum. -/

/-- The merge of two sign vectors is the sign of their pointwise sum. -/
private def merge {n : ℕ} (v w : Fin n → SignType) (i : Fin n) : SignType :=
  SignType.sign ((v i : ℤ) + w i)

/-- Two sign vectors are mergeable when no coordinate carries the same nonzero sign in both. -/
private def Mergeable {n : ℕ} (v w : Fin n → SignType) : Prop :=
  Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)

private lemma Mergeable.apply {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) (i : Fin n) :
    v i = w i → v i = 0 := by
  intro hvw
  rcases SignType.trichotomy (v i) with h0 | h0 | h0
  · exact absurd (hvw ▸ h0 : w i = -1) (Set.disjoint_left.mp h.2 h0)
  · exact h0
  · exact absurd (hvw ▸ h0 : w i = 1) (Set.disjoint_left.mp h.1 h0)

private lemma mergeable_of_apply {n : ℕ} {v w : Fin n → SignType}
    (h : ∀ i, v i = w i → v i = 0) : Mergeable v w :=
  ⟨Set.disjoint_left.mpr fun i h₁ h₂ ↦ by
      have := h i (h₁.trans h₂.symm); simp_all,
    Set.disjoint_left.mpr fun i h₁ h₂ ↦ by
      have := h i (h₁.trans h₂.symm); simp_all⟩

private lemma merge_apply_aux (a b : SignType) (h : a = b → a = 0) :
    (SignType.sign ((a : ℤ) + b) : ℤ) = a + b := by
  revert h; revert a b; decide

private lemma sign_add_eq_one_iff (a b : SignType) (h : a = b → a = 0) :
    SignType.sign ((a : ℤ) + b) = 1 ↔ (a = 1 ∨ b = 1) ∧ ¬(a = -1 ∨ b = -1) := by
  revert h; revert a b; decide

private lemma sign_add_eq_neg_one_iff (a b : SignType) (h : a = b → a = 0) :
    SignType.sign ((a : ℤ) + b) = -1 ↔ (a = -1 ∨ b = -1) ∧ ¬(a = 1 ∨ b = 1) := by
  revert h; revert a b; decide

private lemma eq_neg_one_of_add_nonpos (a b : SignType) (ha : a = 1) (h : (a : ℤ) + b ≤ 0) :
    b = -1 := by
  revert ha h; revert a b; decide

private lemma or_of_add_neg (a b : SignType) (h : (a : ℤ) + b < 0) :
    (a = -1 ∧ ¬b = 1) ∨ (b = -1 ∧ ¬a = 1) := by
  revert h; revert a b; decide

private lemma add_self_nonpos (a : SignType) (h : a ≠ 1) : (a : ℤ) + a ≤ 0 := by
  revert h; revert a; decide

private lemma eq_zero_of_ne_one_of_ne_neg_one (a : SignType) (h₁ : a ≠ 1) (h₂ : a ≠ -1) :
    a = 0 := by
  revert h₁ h₂; revert a; decide

/-- A merge of mergeable vectors is their sum. -/
private lemma coe_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) (i : Fin n) :
    (merge v w i : ℤ) = v i + w i :=
  merge_apply_aux _ _ (h.apply i)

private lemma posSupport_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) :
    posSupport (merge v w) = (posSupport v ∪ posSupport w) \ (negSupport v ∪ negSupport w) := by
  ext i
  simp only [mem_posSupport, merge, Set.mem_sdiff, Set.mem_union, mem_negSupport]
  exact sign_add_eq_one_iff _ _ (h.apply i)

private lemma negSupport_merge {n : ℕ} {v w : Fin n → SignType} (h : Mergeable v w) :
    negSupport (merge v w) = (negSupport v ∪ negSupport w) \ (posSupport v ∪ posSupport w) := by
  ext i
  simp only [mem_negSupport, merge, Set.mem_sdiff, Set.mem_union, mem_posSupport]
  exact sign_add_eq_neg_one_iff _ _ (h.apply i)

/-- The merge of two valid mergeable comparisons is valid
    (`QualitativeProbability.sup_le_sup`, then `QualitativeProbability.additive`). -/
private lemma merge_valid {n : ℕ} (sys : QualitativeProbability (Set (Fin n)))
    {v w : Fin n → SignType} (hv : sys.ge (posSupport v) (negSupport v))
    (hw : sys.ge (posSupport w) (negSupport w)) (h : Mergeable v w) :
    sys.ge (posSupport (merge v w)) (negSupport (merge v w)) := by
  have hmerge := sys.sup_le_sup hv hw h.2 h.1
  rw [sys.additive] at hmerge
  rwa [QualitativeProbability.ge, posSupport_merge h, negSupport_merge h]

/-- If two valid comparisons sum to `≤ 0` everywhere with a strict negative coordinate, some
    atom is null (`ge ∅ {i}`). The sum forces `posSupport v ⊆ negSupport w` and
    `posSupport w ⊆ negSupport v`; then `ge C A → ge C B → ge ∅ (B \ C)` by additivity, and
    symmetrically, and the strict coordinate lies in one of the two differences. -/
private lemma null_from_pair {n : ℕ} (sys : QualitativeProbability (Set (Fin n)))
    {v w : Fin n → SignType}
    (hv : sys.ge (posSupport v) (negSupport v)) (hw : sys.ge (posSupport w) (negSupport w))
    (hle : ∀ i, (v i : ℤ) + w i ≤ 0) (i₀ : Fin n) (hlt : (v i₀ : ℤ) + w i₀ < 0) :
    ∃ i, sys.ge (∅ : Set (Fin n)) {i} := by
  have hpn : ∀ i, v i = 1 → w i = -1 := fun i h ↦ eq_neg_one_of_add_nonpos _ _ h (hle i)
  have hpn' : ∀ i, w i = 1 → v i = -1 := fun i h ↦
    eq_neg_one_of_add_nonpos _ _ h (by rw [add_comm]; exact hle i)
  have hAD : posSupport v ⊆ negSupport w := fun i h ↦ hpn i h
  have hCB : posSupport w ⊆ negSupport v := fun i h ↦ hpn' i h
  -- `ge (pos w) (pos v)` and `ge (pos w) (neg v)`
  have hCA : sys.ge (posSupport w) (posSupport v) := sys.trans (sys.mono hAD) hw
  have hCB_ge : sys.ge (posSupport w) (negSupport v) := sys.trans hv hCA
  have hBC : sys.ge (∅ : Set (Fin n)) (negSupport v \ posSupport w) := by
    have hax := (sys.additive _ _).mp hCB_ge
    rwa [Set.sdiff_eq_empty.mpr hCB] at hax
  have hAC : sys.ge (posSupport v) (posSupport w) := sys.trans (sys.mono hCB) hv
  have hDA : sys.ge (∅ : Set (Fin n)) (negSupport w \ posSupport v) := by
    have hax := (sys.additive _ _).mp (sys.trans hw hAC)
    rwa [Set.sdiff_eq_empty.mpr hAD] at hax
  have hmem : i₀ ∈ negSupport v \ posSupport w ∨ i₀ ∈ negSupport w \ posSupport v := by
    simp only [Set.mem_sdiff, mem_negSupport, mem_posSupport]
    exact or_of_add_neg _ _ hlt
  rcases hmem with hm | hm
  · exact ⟨i₀, sys.trans (sys.mono (Set.singleton_subset_iff.mpr hm)) hBC⟩
  · exact ⟨i₀, sys.trans (sys.mono (Set.singleton_subset_iff.mpr hm)) hDA⟩

/-! ### Bridging comparisons to ℚ sign vectors -/

/-- `toQVec v` casts the signs of a comparison to rationals. -/
private def toQVec (v : Fin 4 → SignType) : Fin 4 → ℚ := fun i ↦ (v i : ℚ)

private lemma toQVec_eq (v : Fin 4 → SignType) (i : Fin 4) : toQVec v i = ((v i : ℤ) : ℚ) := by
  simp [toQVec]

private lemma coe_posSupport_toQVec (v : Fin 4 → SignType) :
    ↑(SignVec.posSupport (toQVec v)) = posSupport v := by
  ext i
  simp only [Finset.mem_coe, SignVec.mem_posSupport, toQVec, mem_posSupport]
  cases v i <;> decide

private lemma coe_negSupport_toQVec (v : Fin 4 → SignType) :
    ↑(SignVec.negSupport (toQVec v)) = negSupport v := by
  ext i
  simp only [Finset.mem_coe, SignVec.mem_negSupport, toQVec, mem_negSupport]
  cases v i <;> decide

/-- Zero vectors contribute nothing to the sum. -/
private lemma comparisonSum_filter_ne_zero {n : ℕ} (L : List (Fin n → SignType)) (i : Fin n) :
    comparisonSum (L.filter (· ≠ 0)) i = comparisonSum L i := by
  induction L with
  | nil => rfl
  | cons v rest ih =>
    by_cases hv : v = 0
    · rw [List.filter_cons_of_neg (by simp [hv]), comparisonSum_cons, ih, hv]; simp
    · rw [List.filter_cons_of_pos (by simp [hv]), comparisonSum_cons, comparisonSum_cons, ih]

/-- A stuck family of comparisons, with no mergeable pair and no mono-dominating member,
    summing to a target `t` with nonempty negative support either contains a *null pair* (two
    members whose sum is `≤ 0` with a strict negative coordinate) or has a member mergeable
    with the reversed target `-t`.

    The balanced family `L ∪ {-t}` thins by Carathéodory's theorem to at most five members, and
    `SignVec.exists_antidom_pair` then yields an anti-dominating pair unless some member is
    mergeable with `-t`. An anti-dominating pair inside `L` is a null pair; one involving `-t`
    is a mono-domination, which is excluded. -/
private lemma v1_tailored (L : List (Fin 4 → SignType)) {t : Fin 4 → SignType}
    (hsum : ∀ i, comparisonSum L i = t i) (hne : (negSupport t).Nonempty)
    (hnotdom : ∀ v ∈ L, posSupport v ⊆ posSupport t → ¬ negSupport t ⊆ negSupport v)
    (hnogm : ¬ ∃ v w rest, L.Perm (v :: w :: rest) ∧ Mergeable v w) :
    (∃ v ∈ L, ∃ w ∈ L, (∀ i, (v i : ℤ) + w i ≤ 0) ∧ ∃ i, (v i : ℤ) + w i < 0)
      ∨ ∃ v ∈ L, Mergeable (-t) v := by
  classical
  -- Step A: a member with empty positive support and nonempty negative support
  -- is a null pair with itself
  by_cases hemp : ∃ v ∈ L, posSupport v = ∅ ∧ (negSupport v).Nonempty
  · obtain ⟨v, hvL, hv1, k, hk⟩ := hemp
    have hv0 : ∀ i, v i ≠ 1 := fun i h ↦ Set.notMem_empty i (hv1 ▸ h)
    refine Or.inl ⟨v, hvL, v, hvL, fun i ↦ add_self_nonpos _ (hv0 i), k, ?_⟩
    rw [mem_negSupport.mp hk]; decide
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ v ∈ L, Mergeable (-t) v
  · exact Or.inr hrd
  have h0 : ∀ v ∈ L, v ≠ 0 → (posSupport v).Nonempty := by
    intro v hv hv0
    by_contra h1
    rw [Set.not_nonempty_iff_eq_empty] at h1
    have h2 : negSupport v = ∅ := by
      by_contra h2
      exact hemp ⟨v, hv, h1, Set.nonempty_iff_ne_empty.mpr h2⟩
    refine hv0 (funext fun i ↦ eq_zero_of_ne_one_of_ne_neg_one _ ?_ ?_)
    · exact fun h ↦ Set.notMem_empty i (h1 ▸ (h : i ∈ posSupport v))
    · exact fun h ↦ Set.notMem_empty i (h2 ▸ (h : i ∈ negSupport v))
  -- Step C: the balanced ℚ sign-vector family on `L′ ∪ {-t}`
  set L' := L.filter (· ≠ 0) with hL'
  set l : List (Fin 4 → ℚ) := ((-t) :: L').map toQVec with hl
  set S : Finset (Fin 4 → ℚ) := l.toFinset with hS
  have hfil : ∀ i, comparisonSum L' i = comparisonSum L i := fun i ↦ by
    rw [hL']; exact comparisonSum_filter_ne_zero L i
  have hmem_shape : ∀ x ∈ S, ∃ v, (v = -t ∨ v ∈ L') ∧ toQVec v = x := by
    intro x hx
    rw [hS, List.mem_toFinset, hl, List.mem_map] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    exact ⟨v, List.mem_cons.mp hv, hvx⟩
  have hsign : ∀ x ∈ S, ∀ i, x i = -1 ∨ x i = 0 ∨ x i = 1 := by
    intro x hx i
    obtain ⟨v, _, rfl⟩ := hmem_shape x hx
    simp only [toQVec]; cases v i <;> simp [SignType.cast]
  have hposne : ∀ x ∈ S, ∃ i, x i = 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hmem_shape x hx
    rcases hv with rfl | hv
    · obtain ⟨k, hk⟩ := hne
      exact ⟨k, by simp [toQVec, mem_negSupport.mp hk]⟩
    · obtain ⟨k, hk⟩ := h0 v (List.mem_of_mem_filter hv) (by simpa using List.of_mem_filter hv)
      exact ⟨k, by simp [toQVec, mem_posSupport.mp hk]⟩
  have hSne : S.Nonempty := by
    refine ⟨toQVec (-t), ?_⟩
    rw [hS, List.mem_toFinset, hl]
    exact List.mem_map.mpr ⟨-t, List.mem_cons.mpr (Or.inl rfl), rfl⟩
  have hdQ : ∀ x ∈ S, 0 < ((l.count x : ℕ) : ℚ) := by
    intro x hx; rw [hS, List.mem_toFinset] at hx; exact_mod_cast List.count_pos_iff.mpr hx
  have hbal : ∑ x ∈ S, ((l.count x : ℕ) : ℚ) • x = 0 := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hc := Finset.sum_list_map_count l (fun x ↦ x i)
    rw [hS, Finset.sum_congr rfl (fun x _ ↦ (nsmul_eq_mul _ _).symm), ← hc, hl,
      List.map_map]
    simp only [Function.comp_def, List.map_cons, List.sum_cons]
    have hLs : (L'.map (fun v ↦ toQVec v i)).sum = ((comparisonSum L' i : ℤ) : ℚ) := by
      simp only [toQVec_eq, comparisonSum]; rw [Int.cast_list_sum, List.map_map]; rfl
    rw [hLs, hfil i, hsum i, toQVec_eq]
    simp
  -- no mergeable pair transfers to the vector family
  have hSnogm : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ¬(Disjoint (SignVec.posSupport x) (SignVec.posSupport y) ∧
        Disjoint (SignVec.negSupport x) (SignVec.negSupport y)) := by
    rintro x hx y hy hxy ⟨hg1, hg2⟩
    obtain ⟨v, hv, rfl⟩ := hmem_shape x hx
    obtain ⟨w, hw, rfl⟩ := hmem_shape y hy
    rw [← Finset.disjoint_coe, coe_posSupport_toQVec, coe_posSupport_toQVec] at hg1
    rw [← Finset.disjoint_coe, coe_negSupport_toQVec, coe_negSupport_toQVec] at hg2
    rcases hv with rfl | hv <;> rcases hw with rfl | hw
    · exact hxy rfl
    · exact hrd ⟨w, List.mem_of_mem_filter hw, hg1, hg2⟩
    · exact hrd ⟨v, List.mem_of_mem_filter hv, hg1.symm, hg2.symm⟩
    · have hvw : v ≠ w := fun he ↦ hxy (by rw [he])
      have hvL : v ∈ L := List.mem_of_mem_filter hv
      have hp1 := List.perm_cons_erase hvL
      have hwe : w ∈ L.erase v :=
        (List.mem_erase_of_ne (Ne.symm hvw)).mpr (List.mem_of_mem_filter hw)
      have hp2 := List.perm_cons_erase hwe
      exact hnogm ⟨v, w, (L.erase v).erase w, hp1.trans (List.Perm.cons v hp2), hg1, hg2⟩
  -- Carathéodory at the origin, then the finite core
  have h0 : (0 : Fin 4 → ℚ) ∈ convexHull ℚ (S : Set (Fin 4 → ℚ)) := by
    simpa [Finset.centerMass, hbal] using
      S.centerMass_id_mem_convexHull (fun x hx ↦ (hdQ x hx).le) (Finset.sum_pos hdQ hSne)
  obtain ⟨S', hS'S, hS'ind, d', hd', hd'1, hsum'⟩ :=
    exists_finset_eq_pos_convex_span_of_mem_convexHull h0
  replace hS'S : S' ⊆ S := Finset.coe_subset.1 hS'S
  obtain ⟨x, hxS', y, hyS', hxy, had1, had2⟩ :=
    SignVec.exists_antidom_pair S' d' hd' (fun x hx ↦ hsign x (hS'S hx))
      (fun x hx ↦ hposne x (hS'S hx)) (fun x hx y hy ↦ hSnogm x (hS'S hx) y (hS'S hy))
      hsum' (Finset.nonempty_of_sum_ne_zero (hd'1.trans_ne one_ne_zero))
      (by simpa using hS'ind.finset_card_le_finrank_succ)
  have hxS : x ∈ S := hS'S hxS'
  have hyS : y ∈ S := hS'S hyS'
  -- vector-level consequences of the anti-dominating pair
  have hps : ∀ i, x i = 1 → y i = -1 := fun i h ↦
    SignVec.mem_negSupport.mp (had1 (SignVec.mem_posSupport.mpr h))
  have hps' : ∀ i, y i = 1 → x i = -1 := fun i h ↦
    SignVec.mem_negSupport.mp (had2 (SignVec.mem_posSupport.mpr h))
  have hvle : ∀ i, x i + y i ≤ 0 := by
    intro i
    rcases eq_or_ne (x i) 1 with h1 | h1
    · rw [h1, hps i h1]; norm_num
    rcases eq_or_ne (y i) 1 with h2 | h2
    · rw [h2, hps' i h2]; norm_num
    rcases hsign x hxS i with h | h | h <;> rcases hsign y hyS i with h' | h' | h' <;>
      first | exact absurd h h1 | exact absurd h' h2 | (rw [h, h']; norm_num)
  have hvstrict : ∃ i, x i + y i < 0 := by
    by_contra hall
    push Not at hall
    have heq : ∀ i, y i = -x i := fun i ↦
      le_antisymm (by have := hvle i; linarith) (by have := hall i; linarith)
    refine hSnogm x hxS y hyS hxy ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]; intro k hk hk'
      rw [SignVec.mem_posSupport] at hk hk'
      rw [heq k, hk] at hk'; norm_num at hk'
    · rw [Finset.disjoint_left]; intro k hk hk'
      rw [SignVec.mem_negSupport] at hk hk'
      rw [heq k, hk] at hk'; norm_num at hk'
  -- map the pair back to comparisons
  obtain ⟨v, hv, rfl⟩ := hmem_shape x hxS
  obtain ⟨w, hw, rfl⟩ := hmem_shape y hyS
  rw [← Finset.coe_subset, coe_posSupport_toQVec, coe_negSupport_toQVec] at had1 had2
  rcases hv with rfl | hv <;> rcases hw with rfl | hw
  · exact (hxy rfl).elim
  · -- the reversed target anti-dominated by `w` is mono-domination, excluded
    exfalso
    rw [posSupport_neg] at had1; rw [negSupport_neg] at had2
    exact hnotdom w (List.mem_of_mem_filter hw) had2 had1
  · exfalso
    rw [posSupport_neg] at had2; rw [negSupport_neg] at had1
    exact hnotdom v (List.mem_of_mem_filter hv) had1 had2
  · -- both from `L`: the null pair
    refine Or.inl ⟨v, List.mem_of_mem_filter hv, w, List.mem_of_mem_filter hw,
      fun i ↦ ?_, ?_⟩
    · have h := hvle i; simp only [toQVec_eq] at h; exact_mod_cast h
    · obtain ⟨i, hi⟩ := hvstrict
      refine ⟨i, ?_⟩; simp only [toQVec_eq] at hi; exact_mod_cast hi

/-- When `-t` and `v` are mergeable, `t` is the merge of the residual `merge t (-v)` with `v`;
    this is the coordinatewise arithmetic of the peel rule. -/
private lemma merge_residual_aux (a b : SignType) (h : -a = b → -a = 0) :
    SignType.sign ((SignType.sign ((a : ℤ) + (-b : SignType)) : ℤ) + b) = a := by
  revert h; revert a b; decide

private lemma mergeable_residual_aux (a b : SignType) (h : -a = b → -a = 0) :
    SignType.sign ((a : ℤ) + (-b : SignType)) = b →
      SignType.sign ((a : ℤ) + (-b : SignType)) = 0 := by
  revert h; revert a b; decide

/-- If `v` is valid and mergeable with the reversed target `-t`, and the residual target
    `merge t (-v)` is provable, then so is `t`, the merge of the residual with `v`. This is the
    last case of the merge recursion. -/
private lemma recombine {n : ℕ} (sys : QualitativeProbability (Set (Fin n)))
    {t v : Fin n → SignType} (hm : Mergeable (-t) v)
    (hv : sys.ge (posSupport v) (negSupport v))
    (hX : sys.ge (posSupport (merge t (-v))) (negSupport (merge t (-v)))) :
    sys.ge (posSupport t) (negSupport t) := by
  have hm' : Mergeable (merge t (-v)) v := mergeable_of_apply fun i ↦ by
    have := hm.apply i
    simp only [Pi.neg_apply] at this
    exact mergeable_residual_aux (t i) (v i) this
  have := merge_valid sys hX hv hm'
  have e : merge (merge t (-v)) v = t := funext fun i ↦ by
    have := hm.apply i
    simp only [Pi.neg_apply] at this
    exact merge_residual_aux (t i) (v i) this
  rwa [e] at this

/-- On a `Fin 4` system with no null atoms, a valid family of comparisons whose integer sum is
    a single sign vector `t` proves `posSupport t ≿ negSupport t`. The recursion has four rules:
    a trivial target (`negSupport t = ∅`), mono-domination, merging a mergeable pair, and
    otherwise `v1_tailored`, whose null pair contradicts `hnull` and whose member mergeable
    with `-t` is peeled off before recursing on the residual (`recombine`). -/
private theorem merge_to_single (sys : QualitativeProbability (Set (Fin 4)))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i})
    (L : List (Fin 4 → SignType)) (hvalid : ∀ v ∈ L, sys.ge (posSupport v) (negSupport v))
    (t : Fin 4 → SignType) (hsum : ∀ i, comparisonSum L i = t i) :
    sys.ge (posSupport t) (negSupport t) := by
  by_cases hne : (negSupport t).Nonempty
  · by_cases hdom : ∃ v ∈ L, posSupport v ⊆ posSupport t ∧ negSupport t ⊆ negSupport v
    · -- mono-domination discharge
      obtain ⟨v, hvL, hv1, hv2⟩ := hdom
      exact sys.trans (sys.mono hv2) (sys.trans (hvalid v hvL) (sys.mono hv1))
    · -- no mono-dominating member: either a mergeable pair (merge & recurse) or,
      -- failing that, a forced null atom contradicting `hnull`.
      push Not at hdom
      by_cases hgm : ∃ v w rest, L.Perm (v :: w :: rest) ∧ Mergeable v w
      case neg =>
        rcases v1_tailored L hsum hne hdom hgm with
          ⟨v, hvL, w, hwL, hle, i0, hlt⟩ | ⟨v, hvL, hm⟩
        · -- null pair → null atom → contradicts hnull
          obtain ⟨i, hi⟩ := null_from_pair sys (hvalid v hvL) (hvalid w hwL) hle i0 hlt
          exact absurd hi (hnull i)
        · -- reversed target merges `v`: peel `v`, recurse on the residual, recombine
          have hperm := List.perm_cons_erase hvL
          have hmt : Mergeable t (-v) := ⟨by simpa using hm.2, by simpa using hm.1⟩
          have hsum' : ∀ i, comparisonSum (L.erase v) i = merge t (-v) i := fun i ↦ by
            have h1 := congrFun (comparisonSum_perm hperm) i
            rw [comparisonSum_cons, hsum i] at h1
            rw [coe_merge hmt, Pi.neg_apply, SignType.coe_neg]
            omega
          have hvalid' : ∀ x ∈ L.erase v, sys.ge (posSupport x) (negSupport x) :=
            fun x hx ↦ hvalid x (List.mem_of_mem_erase hx)
          exact recombine sys hm (hvalid v hvL)
            (merge_to_single sys hnull (L.erase v) hvalid' (merge t (-v)) hsum')
      obtain ⟨v, w, rest, hperm, hm⟩ := hgm
      -- new list: merge v w :: rest, one shorter
      have hvmem : v ∈ L := hperm.mem_iff.mpr (by simp)
      have hwmem : w ∈ L := hperm.mem_iff.mpr (by simp)
      have hrestsub : ∀ x ∈ rest, x ∈ L := fun x hx ↦ hperm.mem_iff.mpr (by simp [hx])
      have hvalid' : ∀ x ∈ merge v w :: rest, sys.ge (posSupport x) (negSupport x) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact merge_valid sys (hvalid v hvmem) (hvalid w hwmem) hm
        · exact hvalid x (hrestsub x hx)
      have hsum' : ∀ i, comparisonSum (merge v w :: rest) i = t i := fun i ↦ by
        rw [comparisonSum_cons, coe_merge hm, ← hsum i, congrFun (comparisonSum_perm hperm) i]
        simp only [comparisonSum_cons]; omega
      exact merge_to_single sys hnull (merge v w :: rest) hvalid' t hsum'
  · -- trivial-target discharge: `negSupport t = ∅`
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [QualitativeProbability.ge, hne]
    exact sys.bot_le _
termination_by L.length
decreasing_by
  all_goals
    have h := hperm.length_eq
    simp only [List.length_cons] at h ⊢
    omega

/-- A qualitative probability on `Fin 4` with no null atom satisfies cancellation, by the merge
    reduction `merge_to_single`. -/
theorem no_null_cancellation (sys : QualitativeProbability (Set (Fin 4)))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i}) : Cancellation sys.ge := by
  intro L hvalid hsum v hv
  rw [← posSupport_neg v, ← negSupport_neg v]
  refine merge_to_single sys hnull (L.erase v) (fun w hw ↦ hvalid w (List.mem_of_mem_erase hw))
    (-v) fun i ↦ ?_
  have h := congrFun ((comparisonSum_perm (List.perm_cons_erase hv)).symm.trans hsum) i
  rw [comparisonSum_cons, Pi.zero_apply] at h
  rw [Pi.neg_apply, SignType.coe_neg]
  omega

/-! ### Fin 3 via lexicographic extension

A `Fin 3` system with no null atoms extends to a `Fin 4` system by adding a
*dominant* fourth world: comparisons are decided first by membership of the
new world, then by the restriction to the original three.  The extension
preserves the FA axioms and the absence of null atoms, and reflects
cancellation, so `no_null_cancellation` discharges the no-null case of
`fa_cancellation_fin3`; null atoms reduce to `representable_fin2`.  Representability
on `Fin 3` then follows from cancellation. -/

/-- `restrict3 A` restricts a `Fin 4` proposition to the first three worlds. -/
def restrict3 (A : Set (Fin 4)) : Set (Fin 3) := {i | Fin.castSucc i ∈ A}

/-- The lexicographic extension of a `Fin 3` system to `Fin 4`, in which the new world
    `Fin.last 3` dominates and ties break by the restriction. -/
def QualitativeProbability.extendLex (sys : QualitativeProbability (Set (Fin 3))) :
    QualitativeProbability (Set (Fin 4)) where
  le A B := (Fin.last 3 ∈ B ∧ Fin.last 3 ∉ A) ∨
    ((Fin.last 3 ∈ B ↔ Fin.last 3 ∈ A) ∧ sys.le (restrict3 A) (restrict3 B))
  mono' A B hAB := by
    by_cases hb : Fin.last 3 ∈ B
    · by_cases ha : Fin.last 3 ∈ A
      · exact Or.inr ⟨iff_of_true hb ha, sys.mono fun i hi ↦ hAB hi⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨iff_of_false hb fun h ↦ hb (hAB h), sys.mono fun i hi ↦ hAB hi⟩
  nonTrivial := by
    rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr trivial
  total A B := by
    by_cases ha : Fin.last 3 ∈ A <;> by_cases hb : Fin.last 3 ∈ B
    · rcases sys.total (restrict3 A) (restrict3 B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_true hb ha, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_true ha hb, h⟩)
    · exact Or.inr (Or.inl ⟨ha, hb⟩)
    · exact Or.inl (Or.inl ⟨hb, ha⟩)
    · rcases sys.total (restrict3 A) (restrict3 B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_false hb ha, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_false ha hb, h⟩)
  trans' A B C := by
    rintro (⟨hb, hna⟩ | ⟨hba, hle1⟩) (⟨hc, hnb⟩ | ⟨hcb, hle2⟩)
    · exact absurd hb hnb
    · exact Or.inl ⟨hcb.mpr hb, hna⟩
    · exact Or.inl ⟨hc, fun ha ↦ hnb (hba.mpr ha)⟩
    · exact Or.inr ⟨hcb.trans hba, sys.trans hle1 hle2⟩
  additive A B := by
    by_cases ha : Fin.last 3 ∈ A <;> by_cases hb : Fin.last 3 ∈ B
    · -- tie on both sides; restriction additivity carries it
      have hab : Fin.last 3 ∉ A \ B := fun h ↦ h.2 hb
      have hba : Fin.last 3 ∉ B \ A := fun h ↦ h.2 ha
      constructor
      · rintro (⟨-, hna⟩ | ⟨-, hle⟩)
        · exact absurd ha hna
        · exact Or.inr ⟨iff_of_false hba hab, (sys.additive _ _).mp hle⟩
      · rintro (⟨h3, -⟩ | ⟨-, hle⟩)
        · exact absurd h3 hba
        · exact Or.inr ⟨iff_of_true hb ha, (sys.additive _ _).mpr hle⟩
    · -- the new world sits in `A \ B`: both sides false
      refine iff_of_false ?_ ?_
      · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
        · exact hb h3
        · exact hb (hiff.mpr ha)
      · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
        · exact hb h3.1
        · exact hb (hiff.mpr ⟨ha, hb⟩).1
    · -- the new world sits in `B \ A`: both sides true by dominance
      exact iff_of_true (Or.inl ⟨hb, ha⟩) (Or.inl ⟨⟨hb, ha⟩, fun h ↦ ha h.1⟩)
    · -- the new world is absent everywhere; restriction additivity again
      have hab : Fin.last 3 ∉ A \ B := fun h ↦ ha h.1
      have hba : Fin.last 3 ∉ B \ A := fun h ↦ hb h.1
      constructor
      · rintro (⟨h3, -⟩ | ⟨-, hle⟩)
        · exact absurd h3 hb
        · exact Or.inr ⟨iff_of_false hba hab, (sys.additive _ _).mp hle⟩
      · rintro (⟨h3, -⟩ | ⟨-, hle⟩)
        · exact absurd h3 hba
        · exact Or.inr ⟨iff_of_false hb ha, (sys.additive _ _).mpr hle⟩

/-- The extension preserves the absence of null atoms. -/
private lemma extendLex_no_null (sys : QualitativeProbability (Set (Fin 3)))
    (hnull : ∀ i : Fin 3, ¬sys.ge ∅ {i}) :
    ∀ j : Fin 4, ¬(QualitativeProbability.extendLex sys).ge ∅ {j} := by
  refine Fin.lastCases ?_ ?_
  · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr rfl
  · intro i
    rintro (⟨h3, -⟩ | ⟨-, hge⟩)
    · exact h3
    · refine hnull i ?_
      have he : restrict3 {Fin.castSucc i} = {i} := by
        ext k; simp [restrict3, Fin.castSucc_inj, eq_comm]
      rwa [show restrict3 ∅ = ∅ from rfl, he] at hge

/-- `embed v` extends a `Fin 3` comparison to `Fin 4`, neutral at the new world. -/
private def embed (v : Fin 3 → SignType) : Fin 4 → SignType := Fin.snoc v 0

private lemma restrict3_posSupport_embed (v : Fin 3 → SignType) :
    restrict3 (posSupport (embed v)) = posSupport v := by
  ext i; simp [restrict3, embed]

private lemma restrict3_negSupport_embed (v : Fin 3 → SignType) :
    restrict3 (negSupport (embed v)) = negSupport v := by
  ext i; simp [restrict3, embed]

private lemma last_notMem_posSupport_embed (v : Fin 3 → SignType) :
    Fin.last 3 ∉ posSupport (embed v) := by
  show ¬embed v (Fin.last 3) = 1
  rw [embed, Fin.snoc_last]; decide

private lemma last_notMem_negSupport_embed (v : Fin 3 → SignType) :
    Fin.last 3 ∉ negSupport (embed v) := by
  show ¬embed v (Fin.last 3) = -1
  rw [embed, Fin.snoc_last]; decide

/-- Cancellation transfers back along the lexicographic extension. -/
private theorem cancellation_extendLex (sys : QualitativeProbability (Set (Fin 3)))
    (h : Cancellation (QualitativeProbability.extendLex sys).ge) : Cancellation sys.ge := by
  intro L hvalid hsum v hv
  have key := h (L.map embed) ?_ ?_ (embed v) (List.mem_map_of_mem hv)
  · -- strictness transfers back
    rcases key with ⟨h3, -⟩ | ⟨-, hge⟩
    · exact absurd h3 (last_notMem_negSupport_embed v)
    · rwa [restrict3_posSupport_embed, restrict3_negSupport_embed] at hge
  · intro w hw
    obtain ⟨w, hwL, rfl⟩ := List.mem_map.mp hw
    refine Or.inr ⟨iff_of_false (last_notMem_posSupport_embed w)
      (last_notMem_negSupport_embed w), ?_⟩
    rw [restrict3_posSupport_embed, restrict3_negSupport_embed]
    exact hvalid w hwL
  · -- the new coordinate vanishes; the old ones are unchanged
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [comparisonSum, List.map_map]
      refine List.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
      show ((embed w (Fin.last 3) : ℤ)) = 0
      rw [embed, Fin.snoc_last]; rfl
    · simpa [comparisonSum, List.map_map, Function.comp_def, embed] using congrFun hsum i

/-- Every FA system on `Fin 3` satisfies cancellation. A null atom reduces to `Fin 2`
    representability; the no-null case extends lexicographically into `Fin 4` and pulls back
    through `no_null_cancellation`. -/
theorem fa_cancellation_fin3 (sys : QualitativeProbability (Set (Fin 3))) :
    Cancellation sys.ge := by
  by_cases h : ∃ j, sys.ge ∅ {j}
  · obtain ⟨j, hj⟩ := h
    exact cancellation_of_null_atom sys hj representable_fin2
  · push Not at h
    exact cancellation_extendLex sys
      (no_null_cancellation (QualitativeProbability.extendLex sys) (extendLex_no_null sys h))

/-- Every FA system on `Fin 3` is representable, by Scott cancellation. -/
theorem representable_fin3 (sys : QualitativeProbability (Set (Fin 3))) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin3 sys)

/-- Every FA system on `Fin 4` satisfies cancellation. A null atom reduces to `Fin 3`; the
    no-null case is the merge reduction `no_null_cancellation`. -/
theorem fa_cancellation_fin4 (sys : QualitativeProbability (Set (Fin 4))) :
    Cancellation sys.ge := by
  by_cases h : ∃ j, sys.ge ∅ {j}
  · obtain ⟨j, hj⟩ := h
    exact cancellation_of_null_atom sys hj representable_fin3
  · push Not at h
    exact no_null_cancellation sys h

/-- Every FA system on `Fin 4` is representable, by Scott cancellation. -/
theorem representable_fin4 (sys : QualitativeProbability (Set (Fin 4))) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end ComparativeProbability
