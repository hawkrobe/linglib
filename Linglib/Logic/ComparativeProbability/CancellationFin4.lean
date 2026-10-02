module

public import Linglib.Logic.ComparativeProbability.Scott
public import Linglib.Logic.ComparativeProbability.SignVectors
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FinCases

/-! # Cancellation on at most four atoms

Every qualitative probability order on at most four atoms satisfies Scott cancellation, hence is
representable by a finitely additive measure, as Kraft, Pratt and Seidenberg showed.

## Main declarations

* `ComparativeProbability.no_null_cancellation`: cancellation on `Fin 4` with no null atoms.
* `ComparativeProbability.QualitativeProbability.extendLex`: the extension by a dominant world.
* `ComparativeProbability.cancellation_of_le_four`: every FA system on at most four atoms
  satisfies cancellation.
* `ComparativeProbability.representable_of_le_four`: every FA system on at most four atoms is
  representable.

## Implementation notes

On `Fin 4` with no null atom the proof is the merge reduction: a valid family of comparisons
whose integer sum is a single sign vector proves that comparison (`merge_to_single`), by a
four-rule recursion whose stuck case is discharged through the sign-vector core
(`Balanced.exists_antiDominating`) via `v1_tailored`. Comparisons are `Scott.lean`'s sign
vectors; two comparisons with no shared nonzero coordinate *merge* into the sign of their sum
(`merge`). Smaller sizes reach this case by the lexicographic extension, and a null atom drops
to one atom fewer, so a single induction covers every size up to four.

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

/-! ### The stuck case of the merge recursion -/

private lemma add_nonpos_of_imp (a b : SignType) (h₁ : a = 1 → b = -1) (h₂ : b = 1 → a = -1) :
    (a : ℤ) + b ≤ 0 := by
  revert h₁ h₂; revert a b; decide

private lemma eq_zero_of_add_eq_zero_of_eq (a b : SignType) (h : (a : ℤ) + b = 0) (hab : a = b) :
    a = 0 := by
  revert h hab; revert a b; decide

/-- Zero vectors contribute nothing to the sum. -/
private lemma comparisonSum_filter_ne_zero {n : ℕ} (M : Multiset (Fin n → SignType)) (i : Fin n) :
    comparisonSum (M.filter (· ≠ 0)) i = comparisonSum M i := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons v M ih =>
    by_cases hv : v = 0
    · rw [Multiset.filter_cons_of_neg _ (by simpa using hv), comparisonSum_cons, ih, hv]; simp
    · rw [Multiset.filter_cons_of_pos _ (by simpa using hv), comparisonSum_cons,
        comparisonSum_cons, ih]

/-- A stuck family of comparisons, with no mergeable pair and no mono-dominating member,
    summing to a target `t` with nonempty negative support either contains a *null pair* (two
    members whose sum is `≤ 0` with a strict negative coordinate) or has a member mergeable
    with the reversed target `-t`.

    The family `-t ::ₘ M` sums to zero, so `exists_antiDominating` yields an anti-dominating
    pair unless some member is mergeable with `-t`. An anti-dominating
    pair inside `L` is a null pair; one involving `-t` is a mono-domination, which is
    excluded. -/
private lemma v1_tailored (M : Multiset (Fin 4 → SignType)) {t : Fin 4 → SignType}
    (hsum : ∀ i, comparisonSum M i = t i) (hne : (negSupport t).Nonempty)
    (hnotdom : ∀ v ∈ M, posSupport v ⊆ posSupport t → ¬ negSupport t ⊆ negSupport v)
    (hnogm : ¬ ∃ v w rest, M = v ::ₘ w ::ₘ rest ∧ Mergeable v w) :
    (∃ v ∈ M, ∃ w ∈ M, (∀ i, (v i : ℤ) + w i ≤ 0) ∧ ∃ i, (v i : ℤ) + w i < 0)
      ∨ ∃ v ∈ M, Mergeable (-t) v := by
  classical
  -- Step A: a member with empty positive support and nonempty negative support
  -- is a null pair with itself
  by_cases hemp : ∃ v ∈ M, posSupport v = ∅ ∧ (negSupport v).Nonempty
  · obtain ⟨v, hvL, hv1, k, hk⟩ := hemp
    have hv0 : ∀ i, v i ≠ 1 := fun i h ↦ Set.notMem_empty i (hv1 ▸ h)
    refine Or.inl ⟨v, hvL, v, hvL, fun i ↦ add_self_nonpos _ (hv0 i), k, ?_⟩
    rw [mem_negSupport.mp hk]; decide
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ v ∈ M, Mergeable (-t) v
  · exact Or.inr hrd
  have h0 : ∀ v ∈ M, v ≠ 0 → (posSupport v).Nonempty := by
    intro v hv hv0
    by_contra h1
    rw [Set.not_nonempty_iff_eq_empty] at h1
    have h2 : negSupport v = ∅ := by
      by_contra h2
      exact hemp ⟨v, hv, h1, Set.nonempty_iff_ne_empty.mpr h2⟩
    refine hv0 (funext fun i ↦ eq_zero_of_ne_one_of_ne_neg_one _ ?_ ?_)
    · exact fun h ↦ Set.notMem_empty i (h1 ▸ (h : i ∈ posSupport v))
    · exact fun h ↦ Set.notMem_empty i (h2 ▸ (h : i ∈ negSupport v))
  -- Step C: the family `-t ::ₘ M'` sums to zero
  set M' := M.filter (· ≠ 0) with hM'
  have hmem : ∀ x ∈ -t ::ₘ M', x = -t ∨ x ∈ M' := fun x hx ↦ Multiset.mem_cons.1 hx
  have hbal : comparisonSum (-t ::ₘ M') = 0 := funext fun i ↦ by
    rw [comparisonSum_cons, hM', comparisonSum_filter_ne_zero, hsum, Pi.neg_apply,
      SignType.coe_neg, neg_add_cancel, Pi.zero_apply]
  have hpos : ∀ x ∈ -t ::ₘ M', (posSupport x).Nonempty := by
    intro x hx
    rcases hmem x hx with rfl | hx
    · rwa [posSupport_neg]
    · exact h0 x (Multiset.mem_of_mem_filter hx) (by simpa using Multiset.of_mem_filter hx)
  have hmerge : ∀ x ∈ -t ::ₘ M', ∀ y ∈ -t ::ₘ M', x ≠ y → ¬Mergeable x y := by
    intro x hx y hy hxy hm
    rcases hmem x hx with rfl | hx <;> rcases hmem y hy with rfl | hy
    · exact hxy rfl
    · exact hrd ⟨y, Multiset.mem_of_mem_filter hy, hm⟩
    · exact hrd ⟨x, Multiset.mem_of_mem_filter hx, hm.symm⟩
    · have hxM := Multiset.mem_of_mem_filter hx
      have hyx : y ∈ M.erase x :=
        (Multiset.mem_erase_of_ne hxy.symm).2 (Multiset.mem_of_mem_filter hy)
      exact hnogm ⟨x, y, (M.erase x).erase y,
        by rw [Multiset.cons_erase hyx, Multiset.cons_erase hxM], hm⟩
  obtain ⟨x, hxS, y, hyS, hxy, had1, had2⟩ :=
    exists_antiDominating hbal hpos hmerge (Multiset.cons_ne_zero)
  -- `-t` is excluded by `hnotdom`, so the pair comes from `M` and is a null pair
  rcases hmem x hxS with rfl | hx <;> rcases hmem y hyS with rfl | hy
  · exact (hxy rfl).elim
  · rw [posSupport_neg] at had1; rw [negSupport_neg] at had2
    exact (hnotdom y (Multiset.mem_of_mem_filter hy) had2 had1).elim
  · rw [posSupport_neg] at had2; rw [negSupport_neg] at had1
    exact (hnotdom x (Multiset.mem_of_mem_filter hx) had1 had2).elim
  · have hle (i) : (x i : ℤ) + y i ≤ 0 :=
      add_nonpos_of_imp (x i) (y i) (fun h ↦ had1 h) (fun h ↦ had2 h)
    refine Or.inl ⟨x, Multiset.mem_of_mem_filter hx, y, Multiset.mem_of_mem_filter hy, hle, ?_⟩
    by_contra! hge
    exact hmerge x hxS y hyS hxy <| mergeable_of_apply fun i hxyi ↦
      eq_zero_of_add_eq_zero_of_eq (x i) (y i) ((hle i).antisymm (hge i)) hxyi

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
    (M : Multiset (Fin 4 → SignType)) (hvalid : ∀ v ∈ M, sys.ge (posSupport v) (negSupport v))
    (t : Fin 4 → SignType) (hsum : ∀ i, comparisonSum M i = t i) :
    sys.ge (posSupport t) (negSupport t) := by
  by_cases hne : (negSupport t).Nonempty
  · by_cases hdom : ∃ v ∈ M, posSupport v ⊆ posSupport t ∧ negSupport t ⊆ negSupport v
    · -- mono-domination discharge
      obtain ⟨v, hvM, hv1, hv2⟩ := hdom
      exact sys.trans (sys.mono hv2) (sys.trans (hvalid v hvM) (sys.mono hv1))
    · -- no mono-dominating member: either a mergeable pair (merge & recurse) or,
      -- failing that, a forced null atom contradicting `hnull`.
      push Not at hdom
      by_cases hgm : ∃ v w rest, M = v ::ₘ w ::ₘ rest ∧ Mergeable v w
      case neg =>
        rcases v1_tailored M hsum hne hdom hgm with
          ⟨v, hvM, w, hwM, hle, i0, hlt⟩ | ⟨v, hvM, hm⟩
        · -- null pair → null atom → contradicts hnull
          obtain ⟨i, hi⟩ := null_from_pair sys (hvalid v hvM) (hvalid w hwM) hle i0 hlt
          exact absurd hi (hnull i)
        · -- reversed target merges `v`: peel `v`, recurse on the residual, recombine
          have hmt : Mergeable t (-v) := ⟨by simpa using hm.2, by simpa using hm.1⟩
          have hsum' : ∀ i, comparisonSum (M.erase v) i = merge t (-v) i := fun i ↦ by
            have h1 := hsum i
            rw [← Multiset.cons_erase hvM, comparisonSum_cons] at h1
            rw [coe_merge hmt, Pi.neg_apply, SignType.coe_neg]
            omega
          exact recombine sys hm (hvalid v hvM) (merge_to_single sys hnull (M.erase v)
            (fun x hx ↦ hvalid x (Multiset.mem_of_mem_erase hx)) (merge t (-v)) hsum')
      obtain ⟨v, w, rest, hM, hm⟩ := hgm
      -- new family: `merge v w ::ₘ rest`, one smaller
      have hvalid' : ∀ x ∈ merge v w ::ₘ rest, sys.ge (posSupport x) (negSupport x) := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact merge_valid sys (hvalid v (by simp [hM])) (hvalid w (by simp [hM])) hm
        · exact hvalid x (by simp [hM, hx])
      have hsum' : ∀ i, comparisonSum (merge v w ::ₘ rest) i = t i := fun i ↦ by
        rw [comparisonSum_cons, coe_merge hm, ← hsum i, hM]
        simp only [comparisonSum_cons]; omega
      exact merge_to_single sys hnull (merge v w ::ₘ rest) hvalid' t hsum'
  · -- trivial-target discharge: `negSupport t = ∅`
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [QualitativeProbability.ge, hne]
    exact sys.bot_le _
termination_by Multiset.card M
decreasing_by
  all_goals first
    | exact Multiset.card_erase_lt_of_mem ‹_›
    | (rw [‹M = _›]; simp)

/-- A qualitative probability on `Fin 4` with no null atom satisfies cancellation, by the merge
    reduction `merge_to_single`. -/
theorem no_null_cancellation (sys : QualitativeProbability (Set (Fin 4)))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i}) : Cancellation sys.ge := by
  intro M hvalid hsum v hv
  rw [← posSupport_neg v, ← negSupport_neg v]
  refine merge_to_single sys hnull (M.erase v)
    (fun w hw ↦ hvalid w (Multiset.mem_of_mem_erase hw)) (-v) fun i ↦ ?_
  have h := congrFun hsum i
  rw [← Multiset.cons_erase hv, comparisonSum_cons, Pi.zero_apply] at h
  rw [Pi.neg_apply, SignType.coe_neg]
  omega

/-! ### Fewer atoms by lexicographic extension

A system on `Fin n` with no null atom extends to `Fin (n + 1)` by adding a *dominant* world:
comparisons are decided first by membership of the new world, then by the restriction to the
original ones. The extension preserves the axioms and the absence of null atoms, and reflects
cancellation, so iterating it carries the no-null case of every size up to four to
`no_null_cancellation`; a null atom reduces to one atom fewer. -/

/-- `sys.extendLex` extends a system on `Fin n` to `Fin (n + 1)` by a new world `Fin.last n`
    that dominates, with ties broken by the restriction along `Fin.castSucc`. -/
def QualitativeProbability.extendLex {n : ℕ} (sys : QualitativeProbability (Set (Fin n))) :
    QualitativeProbability (Set (Fin (n + 1))) where
  le A B := (Fin.last n ∈ B ∧ Fin.last n ∉ A) ∨
    ((Fin.last n ∈ B ↔ Fin.last n ∈ A) ∧ sys.le (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B))
  mono' A B hAB := by
    by_cases hb : Fin.last n ∈ B
    · by_cases ha : Fin.last n ∈ A
      · exact Or.inr ⟨iff_of_true hb ha, sys.mono fun i hi ↦ hAB hi⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨iff_of_false hb fun h ↦ hb (hAB h), sys.mono fun i hi ↦ hAB hi⟩
  nonTrivial := by
    rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr trivial
  total A B := by
    by_cases ha : Fin.last n ∈ A <;> by_cases hb : Fin.last n ∈ B
    · rcases sys.total (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_true hb ha, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_true ha hb, h⟩)
    · exact Or.inr (Or.inl ⟨ha, hb⟩)
    · exact Or.inl (Or.inl ⟨hb, ha⟩)
    · rcases sys.total (Fin.castSucc ⁻¹' A) (Fin.castSucc ⁻¹' B) with h | h
      · exact Or.inl (Or.inr ⟨iff_of_false hb ha, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_false ha hb, h⟩)
  trans' A B C := by
    rintro (⟨hb, hna⟩ | ⟨hba, hle1⟩) (⟨hc, hnb⟩ | ⟨hcb, hle2⟩)
    · exact absurd hb hnb
    · exact Or.inl ⟨hcb.mpr hb, hna⟩
    · exact Or.inl ⟨hc, fun ha ↦ hnb (hba.mpr ha)⟩
    · exact Or.inr ⟨hcb.trans hba, sys.trans hle1 hle2⟩
  additive A B := by
    by_cases ha : Fin.last n ∈ A <;> by_cases hb : Fin.last n ∈ B
    · -- tie on both sides; restriction additivity carries it
      have hab : Fin.last n ∉ A \ B := fun h ↦ h.2 hb
      have hba : Fin.last n ∉ B \ A := fun h ↦ h.2 ha
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
      have hab : Fin.last n ∉ A \ B := fun h ↦ ha h.1
      have hba : Fin.last n ∉ B \ A := fun h ↦ hb h.1
      constructor
      · rintro (⟨h3, -⟩ | ⟨-, hle⟩)
        · exact absurd h3 hb
        · exact Or.inr ⟨iff_of_false hba hab, (sys.additive _ _).mp hle⟩
      · rintro (⟨h3, -⟩ | ⟨-, hle⟩)
        · exact absurd h3 hba
        · exact Or.inr ⟨iff_of_false hb ha, (sys.additive _ _).mpr hle⟩

section Extend

variable {n : ℕ}

/-- The extension preserves the absence of null atoms. -/
private lemma extendLex_no_null (sys : QualitativeProbability (Set (Fin n)))
    (hnull : ∀ i, ¬sys.ge ∅ {i}) : ∀ j, ¬sys.extendLex.ge ∅ {j} := by
  refine Fin.lastCases ?_ fun i ↦ ?_
  · rintro (⟨h3, -⟩ | ⟨hiff, -⟩)
    · exact h3
    · exact hiff.mpr rfl
  · rintro (⟨h3, -⟩ | ⟨-, hge⟩)
    · exact h3
    · refine hnull i ?_
      have he : Fin.castSucc ⁻¹' {Fin.castSucc i} = ({i} : Set (Fin n)) := by
        ext k; simp [Fin.castSucc_inj]
      rwa [Set.preimage_empty, he] at hge

/-- `embed v` extends a comparison on `Fin n` to `Fin (n + 1)`, neutral at the new world. -/
private def embed (v : Fin n → SignType) : Fin (n + 1) → SignType := Fin.snoc v 0

private lemma preimage_posSupport_embed (v : Fin n → SignType) :
    Fin.castSucc ⁻¹' posSupport (embed v) = posSupport v := by
  ext i; simp [embed]

private lemma preimage_negSupport_embed (v : Fin n → SignType) :
    Fin.castSucc ⁻¹' negSupport (embed v) = negSupport v := by
  ext i; simp [embed]

private lemma last_notMem_posSupport_embed (v : Fin n → SignType) :
    Fin.last n ∉ posSupport (embed v) := by
  show ¬embed v (Fin.last n) = 1
  rw [embed, Fin.snoc_last]; decide

private lemma last_notMem_negSupport_embed (v : Fin n → SignType) :
    Fin.last n ∉ negSupport (embed v) := by
  show ¬embed v (Fin.last n) = -1
  rw [embed, Fin.snoc_last]; decide

/-- Cancellation transfers back along the lexicographic extension. -/
private theorem cancellation_extendLex (sys : QualitativeProbability (Set (Fin n)))
    (h : Cancellation sys.extendLex.ge) : Cancellation sys.ge := by
  intro M hvalid hsum v hv
  have key := h (M.map embed) ?_ ?_ (embed v) (Multiset.mem_map_of_mem _ hv)
  · -- strictness transfers back
    rcases key with ⟨h3, -⟩ | ⟨-, hge⟩
    · exact absurd h3 (last_notMem_negSupport_embed v)
    · rwa [preimage_posSupport_embed, preimage_negSupport_embed] at hge
  · intro w hw
    obtain ⟨w, hwL, rfl⟩ := Multiset.mem_map.mp hw
    refine Or.inr ⟨iff_of_false (last_notMem_posSupport_embed w)
      (last_notMem_negSupport_embed w), ?_⟩
    rw [preimage_posSupport_embed, preimage_negSupport_embed]
    exact hvalid w hwL
  · -- the new coordinate vanishes; the old ones are unchanged
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [comparisonSum, Multiset.map_map]
      refine Multiset.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
      show ((embed w (Fin.last n) : ℤ)) = 0
      rw [embed, Fin.snoc_last]; rfl
    · simpa [comparisonSum, Multiset.map_map, Function.comp_def, embed] using congrFun hsum i

/-- A system on at most four atoms with no null atom satisfies cancellation, since its
    lexicographic extension to `Fin 4` falls to `no_null_cancellation`. -/
private theorem no_null_cancellation_of_le_four (hn : n ≤ 4)
    (sys : QualitativeProbability (Set (Fin n))) (hnull : ∀ i, ¬sys.ge ∅ {i}) :
    Cancellation sys.ge := by
  induction h : 4 - n generalizing n with
  | zero =>
    obtain rfl : n = 4 := by omega
    exact no_null_cancellation sys hnull
  | succ k ih =>
    exact cancellation_extendLex sys
      (ih (by omega) sys.extendLex (extendLex_no_null sys hnull) (by omega))

end Extend

/-- Every FA system on at most four atoms satisfies cancellation. A null atom reduces to one atom
    fewer (`cancellation_of_null_atom`); otherwise the lexicographic extension to `Fin 4`
    applies. -/
theorem cancellation_of_le_four : ∀ {n : ℕ}, n ≤ 4 →
    ∀ sys : QualitativeProbability (Set (Fin n)), Cancellation sys.ge
  | 0, _, sys => sys.elim0
  | 1, hn, sys => no_null_cancellation_of_le_four hn sys fun i hi ↦ by
      obtain ⟨j, hj⟩ := sys.exists_singleton_not_le_empty
      exact hj (Subsingleton.elim i j ▸ hi)
  | n + 2, hn, sys => by
      by_cases h : ∃ j, sys.ge ∅ {j}
      · obtain ⟨j, hj⟩ := h
        exact cancellation_of_null_atom sys hj fun sys' ↦
          cancellation_implies_representable sys' (cancellation_of_le_four (by omega) sys')
      · push Not at h
        exact no_null_cancellation_of_le_four hn sys h

/-- Every FA system on at most four atoms is representable, by Scott cancellation. -/
theorem representable_of_le_four {n : ℕ} (hn : n ≤ 4)
    (sys : QualitativeProbability (Set (Fin n))) : Representable sys :=
  cancellation_implies_representable sys (cancellation_of_le_four hn sys)

end ComparativeProbability
