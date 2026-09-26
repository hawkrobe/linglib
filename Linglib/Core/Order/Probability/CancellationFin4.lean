module

public import Linglib.Core.Order.Probability.Scott
public import Linglib.Core.Order.Caratheodory
public import Linglib.Core.Order.SignVectors
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FinCases

/-! # Cancellation for `Fin 4`: the structural merge-reduction proof

Every qualitative probability order on four atoms satisfies Scott cancellation,
hence is representable by a finitely additive measure
([kraft-pratt-seidenberg-1959]).

## Main declarations

* `ComparativeProbability.fa_cancellation_fin4` — FA axioms imply cancellation on `Fin 4`.
* `ComparativeProbability.representable_fin4` — every FA system on `Fin 4` is representable.
* `ComparativeProbability.no_null_cancellation` — cancellation for systems with no null atoms.

## Implementation notes

The proof rests on two imported layers — conic Carathéodory
(`Caratheodory.exists_posdep_card_le_five`) and the sign-vector core
(`SignVec.exists_antidom_pair`) — and adds the merge reduction: a valid family
of comparisons whose vector sum is a single comparison vector proves that
comparison (`merge_to_single`), by a four-rule recursion whose stuck case is
discharged through the sign-vector core via `v1_tailored`.  Comparison vectors
are `Scott.lean`'s `comparisonVec`/`comparisonSum`; the merge calculus
(`mergeCmp`) and the merge recursion itself are private plumbing, and only the
theorems above are exported.
-/

@[expose] public section

namespace ComparativeProbability

/-! ### Merge-to-single infrastructure

A comparison is a pair of disjoint finsets `(pos, neg)`; its integer vector is
`1_pos − 1_neg ∈ {−1,0,1}ⁿ`. `mergeCmp` combines two comparisons whose pos-parts and
neg-parts are disjoint into the disjoint-normal-form of their vector sum. -/

/-- Merge two comparisons into the disjoint normal form of their vector sum. -/
private def mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  ((c.1 ∪ d.1) \ (c.2 ∪ d.2), (c.2 ∪ d.2) \ (c.1 ∪ d.1))

/-- The merged comparison's vector is the sum of the two vectors, provided pos-parts
    are disjoint and neg-parts are disjoint (so no coordinate doubles). -/
private lemma comparisonVec_mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n))
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) (i : Fin n) :
    comparisonVec (mergeCmp c d) i = comparisonVec c i + comparisonVec d i := by
  have h1 : i ∈ c.1 → i ∉ d.1 := fun h => Finset.disjoint_left.mp hpos h
  have h2 : i ∈ c.2 → i ∉ d.2 := fun h => Finset.disjoint_left.mp hneg h
  simp only [comparisonVec, mergeCmp, Finset.mem_sdiff, Finset.mem_union]; split_ifs <;> simp_all

/-- `mergeCmp` of two valid comparisons is valid, given the disjointness conditions.
    Uses `QualitativeProbability.sup_le_sup` then Axiom A to reach disjoint normal form. -/
private lemma mergeCmp_valid {n : ℕ} (sys : QualitativeProbability (Set (Fin n)))
    {c d : Finset (Fin n) × Finset (Fin n)}
    (hc : sys.ge ↑c.1 ↑c.2) (hd : sys.ge ↑d.1 ↑d.2)
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) :
    sys.ge ↑(mergeCmp c d).1 ↑(mergeCmp c d).2 := by
  have hmerge : sys.le (↑c.2 ∪ ↑d.2) (↑c.1 ∪ ↑d.1) :=
    sys.sup_le_sup hc hd
      (by rwa [← Finset.disjoint_coe] at hneg)
      (by rwa [← Finset.disjoint_coe] at hpos)
  -- reduce to disjoint form via Axiom A
  rw [sys.additive (↑c.2 ∪ ↑d.2) (↑c.1 ∪ ↑d.1)] at hmerge
  have e1 : (↑c.1 ∪ ↑d.1 : Set (Fin n)) \ (↑c.2 ∪ ↑d.2) = ↑(mergeCmp c d).1 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  have e2 : (↑c.2 ∪ ↑d.2 : Set (Fin n)) \ (↑c.1 ∪ ↑d.1) = ↑(mergeCmp c d).2 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  rwa [e2, e1] at hmerge

/-- **Two-member null-forcing**: if two valid disjoint comparisons have vector-sum `≤ 0`
    everywhere with a strict negative coordinate, some atom is null (`ge ∅ {i}`).
    Disjointness forces `A ⊆ D` and `C ⊆ B`, giving `ge C A → ge C B → (Axiom A) ge ∅ (B\C)`
    and symmetrically `ge ∅ (D\A)`; the strict coordinate lies in one of them. -/
private lemma null_from_pair (sys : QualitativeProbability (Set (Fin 4)))
    {A B C D : Finset (Fin 4)}
    (hAB : sys.ge ↑A ↑B) (hCD : sys.ge ↑C ↑D)
    (hABd : Disjoint A B) (hCDd : Disjoint C D)
    (hle : ∀ i, comparisonVec (A, B) i + comparisonVec (C, D) i ≤ 0)
    (i₀ : Fin 4) (hlt : comparisonVec (A, B) i₀ + comparisonVec (C, D) i₀ < 0) :
    ∃ i, sys.ge (∅ : Set (Fin 4)) {i} := by
  -- A ⊆ D and C ⊆ B (membership facts from disjointness)
  have hAD : A ⊆ D := by
    intro a ha; by_contra haD
    have := hle a
    simp only [comparisonVec, ite_eq_left ha, ite_eq_right (Finset.disjoint_left.mp hABd ha),
      ite_eq_right haD,
      sub_zero] at this
    split_ifs at this <;> omega
  have hCB : C ⊆ B := by
    intro c hc; by_contra hcB
    have := hle c
    simp only [comparisonVec, ite_eq_left hc, ite_eq_right (Finset.disjoint_left.mp hCDd hc),
      ite_eq_right hcB,
      sub_zero] at this
    split_ifs at this <;> omega
  -- ge C A, ge C B
  have hCA : sys.ge ↑C ↑A := sys.trans (sys.mono (Finset.coe_subset.mpr hAD)) hCD
  have hCB_ge : sys.ge ↑C ↑B := sys.trans hAB hCA
  -- Axiom A: ge ∅ (B \ C)
  have hBC : sys.ge (∅ : Set (Fin 4)) ↑(B \ C) := by
    have hax := (sys.additive ↑B ↑C).mp hCB_ge
    rwa [← Finset.coe_sdiff, ← Finset.coe_sdiff,
      Finset.sdiff_eq_empty_iff_subset.mpr hCB, Finset.coe_empty] at hax
  -- symmetric: ge A D, ge A C, ge A D? -> ge ∅ (D \ A)
  have hAC : sys.ge ↑A ↑C := sys.trans (sys.mono (Finset.coe_subset.mpr hCB)) hAB
  have hDA : sys.ge (∅ : Set (Fin 4)) ↑(D \ A) := by
    have hax := (sys.additive ↑D ↑A).mp (sys.trans hCD hAC)
    rwa [← Finset.coe_sdiff, ← Finset.coe_sdiff,
      Finset.sdiff_eq_empty_iff_subset.mpr hAD, Finset.coe_empty] at hax
  -- strict coordinate i₀ ∈ (B \ C) ∪ (D \ A)
  have hmem : i₀ ∈ B \ C ∨ i₀ ∈ D \ A := by
    simp only [comparisonVec, Finset.mem_sdiff] at hlt ⊢; split_ifs at hlt <;> simp_all
  rcases hmem with hm | hm
  · exact ⟨i₀, sys.trans (sys.mono
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm)) hBC⟩
  · exact ⟨i₀, sys.trans (sys.mono
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm)) hDA⟩

/-! ### Bridging comparisons to ℚ sign vectors -/

/-- ℚ-valued sign vector of a comparison. -/
private def toQVec (c : Finset (Fin 4) × Finset (Fin 4)) : Fin 4 → ℚ :=
  fun i => (comparisonVec c i : ℚ)

private lemma toQVec_apply (c : Finset (Fin 4) × Finset (Fin 4)) (k : Fin 4) :
    toQVec c k = (if k ∈ c.1 then (1 : ℚ) else 0) - (if k ∈ c.2 then 1 else 0) := by
  simp only [toQVec, comparisonVec]; split_ifs <;> norm_num

private lemma posSupport_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    SignVec.posSupport (toQVec c) = c.1 := by
  ext k
  rw [SignVec.mem_posSupport, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2 <;>
    first | exact absurd h2 (Finset.disjoint_left.mp hc h1) | norm_num [h1, h2]

private lemma negSupport_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    SignVec.negSupport (toQVec c) = c.2 := by
  ext k
  rw [SignVec.mem_negSupport, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2 <;>
    first | exact absurd h2 (Finset.disjoint_left.mp hc h1) | norm_num [h1, h2]

private lemma comparisonVec_swap (A B : Finset (Fin 4)) (i : Fin 4) :
    comparisonVec (B, A) i = -comparisonVec (A, B) i := by
  simp only [comparisonVec]; ring

/-- Comparisons with both parts empty contribute nothing to the vector sum. -/
private lemma comparisonSum_filter_ne_empty (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅) (i : Fin 4) :
    comparisonSum (L.filter (fun c => c.1 ≠ ∅)) i = comparisonSum L i := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    have h0' : ∀ c' ∈ rest, c'.1 = ∅ → c'.2 = ∅ :=
      fun c' hc' => h0 c' (List.mem_cons_of_mem _ hc')
    by_cases hc : c.1 = ∅
    · have hc2 := h0 c (List.mem_cons.mpr (Or.inl rfl)) hc
      rw [List.filter_cons_of_neg (by simp [hc]), comparisonSum_cons, ih h0',
        show comparisonVec c i = 0 from by simp [comparisonVec, hc, hc2]]
      omega
    · rw [List.filter_cons_of_pos (by simp [hc]), comparisonSum_cons, comparisonSum_cons, ih h0']

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
    (hsum : ∀ i, comparisonSum L i = comparisonVec (vpos, vneg) i)
    (hne : vneg.Nonempty)
    (hnotdom : ∀ c ∈ L, c.1 ⊆ vpos → ¬ vneg ⊆ c.2)
    (hnogm : ¬ ∃ c d rest, L.Perm (c :: d :: rest) ∧ Disjoint c.1 d.1 ∧ Disjoint c.2 d.2) :
    (∃ c ∈ L, ∃ d ∈ L,
        (∀ i, comparisonVec (c.1, c.2) i + comparisonVec (d.1, d.2) i ≤ 0) ∧
        (∃ i, comparisonVec (c.1, c.2) i + comparisonVec (d.1, d.2) i < 0))
      ∨ (∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2) := by
  classical
  -- Step A: a member with empty positive part and nonempty negative part is
  -- itself a null pair
  by_cases hemp : ∃ c ∈ L, c.1 = ∅ ∧ c.2.Nonempty
  · obtain ⟨c, hcL, hc1, k, hk⟩ := hemp
    refine Or.inl ⟨c, hcL, c, hcL, fun i => ?_, k, ?_⟩
    · simp only [comparisonVec, hc1, ite_eq_right (Finset.notMem_empty i)]; split_ifs <;> omega
    · simp only [comparisonVec, hc1, ite_eq_right (Finset.notMem_empty k), ite_eq_left hk]; omega
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2
  · exact Or.inr hrd
  have h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅ := by
    intro c hc h1; by_contra h2
    exact hemp ⟨c, hc, h1, Finset.nonempty_iff_ne_empty.mpr h2⟩
  -- Step C: the balanced ℚ sign-vector family on `L′ ∪ {reversed target}`
  set L' := L.filter (fun c => c.1 ≠ ∅) with hL'
  set l : List (Fin 4 → ℚ) := ((vneg, vpos) :: L').map toQVec with hl
  set S : Finset (Fin 4 → ℚ) := l.toFinset with hS
  have hfil : ∀ i, comparisonSum L' i = comparisonSum L i := by
    intro i; rw [hL']; exact comparisonSum_filter_ne_empty L h0 i
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
    rw [toQVec_apply]; split_ifs <;> norm_num
  have hposne : ∀ v ∈ S, ∃ i, v i = 1 := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := hmem_shape v hv
    rcases hc with rfl | hc
    · obtain ⟨k, hk⟩ := hne
      refine ⟨k, ?_⟩
      rw [toQVec_apply, ite_eq_left hk, ite_eq_right (Finset.disjoint_right.mp hvpvn hk)]; norm_num
    · have hcL : c ∈ L := List.mem_of_mem_filter hc
      have hc1 : c.1 ≠ ∅ := by simpa using List.of_mem_filter hc
      obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hc1
      refine ⟨k, ?_⟩
      rw [toQVec_apply, ite_eq_left hk, ite_eq_right (Finset.disjoint_left.mp (hdisj c hcL) hk)]
      norm_num
  have hSne : S.Nonempty := by
    refine ⟨toQVec (vneg, vpos), ?_⟩
    rw [hS, List.mem_toFinset, hl]
    exact List.mem_map.mpr ⟨(vneg, vpos), List.mem_cons.mpr (Or.inl rfl), rfl⟩
  have hdQ : ∀ v ∈ S, 0 < ((l.count v : ℕ) : ℚ) := by
    intro v hv; rw [hS, List.mem_toFinset] at hv; exact_mod_cast List.count_pos_iff.mpr hv
  have hbal : ∑ v ∈ S, ((l.count v : ℕ) : ℚ) • v = 0 := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hc := Finset.sum_list_map_count l (fun v => v i)
    rw [hS, Finset.sum_congr rfl (fun v _ => (nsmul_eq_mul _ _).symm), ← hc, hl,
      List.map_map]
    simp only [Function.comp_def, List.map_cons, List.sum_cons]
    have hLs : (L'.map (fun c => toQVec c i)).sum = ((comparisonSum L' i : ℤ) : ℚ) := by
      simp only [toQVec, comparisonSum]; rw [Int.cast_list_sum, List.map_map]; rfl
    rw [hLs, hfil i, hsum i]
    simp only [toQVec]
    rw [comparisonVec_swap]; push_cast; ring
  -- no-g-merge transfers to the vector family
  have hSnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (SignVec.posSupport v) (SignVec.posSupport w) ∧
        Disjoint (SignVec.negSupport v) (SignVec.negSupport w)) := by
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
      have hp1 := List.perm_cons_erase hcL
      have hc'e : c' ∈ L.erase c :=
        (List.mem_erase_of_ne (Ne.symm hcc')).mpr (List.mem_of_mem_filter hc')
      have hp2 := List.perm_cons_erase hc'e
      exact hnogm ⟨c, c', (L.erase c).erase c', hp1.trans (List.Perm.cons c hp2), hg1, hg2⟩
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
  have hps : ∀ i, v i = 1 → w i = -1 := fun i h =>
    SignVec.mem_negSupport.mp (had1 (SignVec.mem_posSupport.mpr h))
  have hps' : ∀ i, w i = 1 → v i = -1 := fun i h =>
    SignVec.mem_negSupport.mp (had2 (SignVec.mem_posSupport.mpr h))
  have hvle : ∀ i, v i + w i ≤ 0 := by
    intro i
    rcases eq_or_ne (v i) 1 with h1 | h1
    · rw [h1, hps i h1]; norm_num
    rcases eq_or_ne (w i) 1 with h2 | h2
    · rw [h2, hps' i h2]; norm_num
    rcases hsign v hvS i with h | h | h <;> rcases hsign w hwS i with h' | h' | h' <;>
      first | exact absurd h h1 | exact absurd h' h2 | (rw [h, h']; norm_num)
  have hvstrict : ∃ i, v i + w i < 0 := by
    by_contra hall
    push Not at hall
    have heq : ∀ i, w i = -v i := fun i =>
      le_antisymm (by have := hvle i; linarith) (by have := hall i; linarith)
    refine hSnogm v hvS w hwS hvw ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]; intro k hk hk'
      rw [SignVec.mem_posSupport] at hk hk'
      rw [heq k, hk] at hk'; norm_num at hk'
    · rw [Finset.disjoint_left]; intro k hk hk'
      rw [SignVec.mem_negSupport] at hk hk'
      rw [heq k, hk] at hk'; norm_num at hk'
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
    · have h := hvle i; simp only [toQVec] at h; exact_mod_cast h
    · obtain ⟨i, hi⟩ := hvstrict
      refine ⟨i, ?_⟩; simp only [toQVec] at hi; exact_mod_cast hi

/-- **Recombine** (case 4 of the merge recursion): if a member `c` is valid, the
    reversed target `r = (vneg, vpos)` generalized-merges `c` (`Disjoint vneg c.1`,
    `Disjoint vpos c.2`), and the residual target `t' = t − comparisonVec c` — namely
    `(p, q)` with `p = (vpos \ c.1) ∪ (c.2 \ vneg)`, `q = (vneg \ c.2) ∪ (c.1 \ vpos)`
    — is provable (`ge p q`, the IH), then `ge vpos vneg`. Proved by merging `(p,q)`
    with `c` via `mergeCmp_valid`; the disjoint-normal-form is exactly `(vpos, vneg)`. -/
private lemma recombine (sys : QualitativeProbability (Set (Fin 4)))
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
    refine Finset.ext fun x => ?_
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]; tauto
  have e2 : (mergeCmp (p, q) c).2 = vneg := by
    refine Finset.ext fun x => ?_
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]; tauto
  rwa [e1, e2] at hmerge

/-- **Merge-to-single**: on a no-null Fin 4 system, any valid family of disjoint
    comparisons whose vector-sum equals a single comparison vector `(vpos, vneg)`
    proves `vpos ≿ vneg`. Four uniform rules: trivial target (`vneg = ∅`),
    mono-domination, merge a generalizable pair and recurse, or (no g-merge pair)
    `v1_tailored` gives a null pair (→ contradiction via `hnull`) or a member merged
    by the reversed target (→ peel it, recurse, `recombine`). -/
private theorem merge_to_single (sys : QualitativeProbability (Set (Fin 4)))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i})
    (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (hdisj : ∀ c ∈ L, Disjoint c.1 c.2)
    (hvalid : ∀ c ∈ L, sys.ge ↑c.1 ↑c.2)
    (vpos vneg : Finset (Fin 4))
    (hvpvn : Disjoint vpos vneg)
    (hsum : ∀ i, comparisonSum L i = comparisonVec (vpos, vneg) i) :
    sys.ge ↑vpos ↑vneg := by
  by_cases hne : vneg.Nonempty
  · by_cases hdom : ∃ c ∈ L, c.1 ⊆ vpos ∧ vneg ⊆ c.2
    · -- mono-domination discharge
      obtain ⟨c, hcL, hc1, hc2⟩ := hdom
      exact sys.trans (sys.mono (Finset.coe_subset.mpr hc2))
        (sys.trans (hvalid c hcL) (sys.mono (Finset.coe_subset.mpr hc1)))
    · -- no mono-dominating member: either a gmerge pair (merge & recurse) or, failing
      -- that, a forced null atom contradicting `hnull`.
      push Not at hdom
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
          have hsum' : ∀ i, comparisonSum (L.erase c) i =
              comparisonVec ((vpos \ c.1) ∪ (c.2 \ vneg), (vneg \ c.2) ∪ (c.1 \ vpos)) i := by
            intro i
            have h1 : comparisonSum L i = comparisonVec c i + comparisonSum (L.erase c) i := by
              rw [congrFun (comparisonSum_perm hperm) i, comparisonSum_cons]
            have he : comparisonSum (L.erase c) i =
                comparisonVec (vpos, vneg) i - comparisonVec c i := by
              have := hsum i; omega
            rw [he]
            have a1 : i ∈ vpos → i ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a2 : i ∈ vpos → i ∉ c.2 := fun h => Finset.disjoint_left.mp hrc2 h
            have a3 : i ∈ vneg → i ∉ c.1 := fun h => Finset.disjoint_left.mp hrc1 h
            have a4 : i ∈ c.1 → i ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [comparisonVec, Finset.mem_union, Finset.mem_sdiff]
            by_cases h1v : i ∈ vpos <;> by_cases h2v : i ∈ vneg <;>
              by_cases h3v : i ∈ c.1 <;> by_cases h4v : i ∈ c.2 <;> simp_all
          have hpq : Disjoint ((vpos \ c.1) ∪ (c.2 \ vneg)) ((vneg \ c.2) ∪ (c.1 \ vpos)) := by
            rw [Finset.disjoint_left]; intro x hxp hxq
            have a1 : x ∈ vpos → x ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a4 : x ∈ c.1 → x ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [Finset.mem_union, Finset.mem_sdiff] at hxp hxq; tauto
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
      have hsum' : ∀ i, comparisonSum (mergeCmp c d :: rest) i = comparisonVec (vpos, vneg) i := by
        intro i
        rw [comparisonSum_cons, comparisonVec_mergeCmp c d hpd hnd i, ← hsum i,
          congrFun (comparisonSum_perm hperm) i]
        simp only [comparisonSum_cons]; omega
      exact merge_to_single sys hnull (mergeCmp c d :: rest) hdisj' hvalid' vpos vneg hvpvn hsum'
  · -- trivial-target discharge: vneg = ∅
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simpa using sys.bot_le (↑vpos)
termination_by L.length
decreasing_by
  all_goals
    have h := hperm.length_eq
    simp only [List.length_cons] at h ⊢
    omega

/-- **No-null case** of Theorem 8a (Fin 4): when no atom is null, every
    balanced list of valid comparisons reverses, via the merge reduction
    `merge_to_single`. -/
theorem no_null_cancellation (sys : QualitativeProbability (Set (Fin 4)))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i}) : Cancellation sys.ge := by
  intro L hdisj hvalid hsum c hc
  refine merge_to_single sys hnull (L.erase c) (fun d hd ↦ hdisj d (List.mem_of_mem_erase hd))
    (fun d hd ↦ hvalid d (List.mem_of_mem_erase hd)) c.2 c.1 (hdisj c hc).symm fun i ↦ ?_
  have h := congrFun ((comparisonSum_perm (List.perm_cons_erase hc)).symm.trans hsum) i
  rw [comparisonSum_cons, Pi.zero_apply] at h
  simp only [comparisonVec] at h ⊢
  omega

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
def restrict3 (A : Set (Fin 4)) : Set (Fin 3) := {i | Fin.castSucc i ∈ A}

/-- Lexicographic extension: the new world `Fin.last 3` dominates; ties break
    by the restriction. -/
def QualitativeProbability.extendLex (sys : QualitativeProbability (Set (Fin 3))) :
    QualitativeProbability (Set (Fin 4)) where
  le A B := (Fin.last 3 ∈ B ∧ Fin.last 3 ∉ A) ∨
    ((Fin.last 3 ∈ B ↔ Fin.last 3 ∈ A) ∧ sys.le (restrict3 A) (restrict3 B))
  mono' A B hAB := by
    by_cases hb : Fin.last 3 ∈ B
    · by_cases ha : Fin.last 3 ∈ A
      · exact Or.inr ⟨iff_of_true hb ha, sys.mono fun i hi => hAB hi⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨iff_of_false hb fun h => hb (hAB h), sys.mono fun i hi => hAB hi⟩
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
    · exact Or.inl ⟨hc, fun ha => hnb (hba.mpr ha)⟩
    · exact Or.inr ⟨hcb.trans hba, sys.trans hle1 hle2⟩
  additive A B := by
    by_cases ha : Fin.last 3 ∈ A <;> by_cases hb : Fin.last 3 ∈ B
    · -- tie on both sides; restriction additivity carries it
      have hab : Fin.last 3 ∉ A \ B := fun h => h.2 hb
      have hba : Fin.last 3 ∉ B \ A := fun h => h.2 ha
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
      exact iff_of_true (Or.inl ⟨hb, ha⟩) (Or.inl ⟨⟨hb, ha⟩, fun h => ha h.1⟩)
    · -- the new world is absent everywhere; restriction additivity again
      have hab : Fin.last 3 ∉ A \ B := fun h => ha h.1
      have hba : Fin.last 3 ∉ B \ A := fun h => hb h.1
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

/-- The new world never lies in an embedded finset. -/
private lemma last_notMem_map (s : Finset (Fin 3)) :
    Fin.last 3 ∉ s.map Fin.castSuccEmb := by
  rw [Finset.mem_map]; rintro ⟨i, -, hi⟩; exact absurd hi (Fin.castSucc_lt_last i).ne

/-- Embedded finsets restrict back to themselves. -/
private lemma restrict3_coe_map (s : Finset (Fin 3)) :
    restrict3 ↑(s.map Fin.castSuccEmb) = ↑s := by
  ext i
  show Fin.castSuccEmb i ∈ ↑(s.map Fin.castSuccEmb) ↔ _
  rw [Finset.mem_coe, Finset.mem_map']

/-- Embed a `Fin 3` comparison into `Fin 4` along `Fin.castSucc`. -/
private def embed (c : Finset (Fin 3) × Finset (Fin 3)) : Finset (Fin 4) × Finset (Fin 4) :=
  (c.1.map Fin.castSuccEmb, c.2.map Fin.castSuccEmb)

private lemma comparisonVec_embed_last (c : Finset (Fin 3) × Finset (Fin 3)) :
    comparisonVec (embed c) (Fin.last 3) = 0 := by
  show ((if Fin.last 3 ∈ c.1.map Fin.castSuccEmb then 1 else 0) -
    (if Fin.last 3 ∈ c.2.map Fin.castSuccEmb then 1 else 0) : ℤ) = 0
  rw [ite_eq_right (last_notMem_map _), ite_eq_right (last_notMem_map _), sub_zero]

private lemma comparisonVec_embed_castSucc (c : Finset (Fin 3) × Finset (Fin 3)) (i : Fin 3) :
    comparisonVec (embed c) i.castSucc = comparisonVec c i := by
  simp [comparisonVec, embed]

/-- Cancellation transfers back along the lexicographic extension. -/
private theorem cancellation_extendLex (sys : QualitativeProbability (Set (Fin 3)))
    (h : Cancellation (QualitativeProbability.extendLex sys).ge) : Cancellation sys.ge := by
  intro L hdisj hvalid hsum c hc
  have key := h (L.map embed) ?_ ?_ ?_ (embed c) (List.mem_map_of_mem hc)
  · -- strictness transfers back
    rcases key with ⟨h3, -⟩ | ⟨-, hge⟩
    · exact absurd (Finset.mem_coe.mp h3) (last_notMem_map _)
    · have hge' : sys.le (restrict3 ↑(c.1.map Fin.castSuccEmb))
          (restrict3 ↑(c.2.map Fin.castSuccEmb)) := hge
      rwa [restrict3_coe_map, restrict3_coe_map] at hge'
  · intro d hd
    obtain ⟨d, hdL, rfl⟩ := List.mem_map.mp hd
    exact (Finset.disjoint_map _).mpr (hdisj d hdL)
  · intro d hd
    obtain ⟨d, hdL, rfl⟩ := List.mem_map.mp hd
    refine Or.inr ⟨iff_of_false (fun h3 ↦ last_notMem_map _ (Finset.mem_coe.mp h3))
      (fun h3 ↦ last_notMem_map _ (Finset.mem_coe.mp h3)), ?_⟩
    show sys.le (restrict3 ↑(d.2.map Fin.castSuccEmb)) (restrict3 ↑(d.1.map Fin.castSuccEmb))
    rw [restrict3_coe_map, restrict3_coe_map]
    exact hvalid d hdL
  · -- the new coordinate vanishes; the old ones are unchanged
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [comparisonSum, List.map_map]
      refine List.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx
      exact comparisonVec_embed_last d
    · simpa [comparisonSum, List.map_map, Function.comp_def, comparisonVec_embed_castSucc]
        using congrFun hsum i

/-- **Cancellation for Fin 3**, structurally: a null atom reduces to `Fin 2`
    representability; the no-null case extends lexicographically into `Fin 4`
    and pulls back through `no_null_cancellation`. -/
theorem fa_cancellation_fin3 (sys : QualitativeProbability (Set (Fin 3))) :
    Cancellation sys.ge := by
  by_cases h : ∃ j, sys.ge ∅ {j}
  · obtain ⟨j, hj⟩ := h
    exact cancellation_of_null_atom sys hj representable_fin2
  · push Not at h
    exact cancellation_extendLex sys
      (no_null_cancellation (QualitativeProbability.extendLex sys) (extendLex_no_null sys h))

/-- **Theorem 8a for Fin 3**: every FA system on three elements is representable —
    now *derived from* Scott cancellation, replacing the former measure-by-measure
    case analysis. -/
theorem representable_fin3 (sys : QualitativeProbability (Set (Fin 3))) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin3 sys)

/-- **Theorem 8a (Fin 4), structural**: every FA system on `Fin 4` satisfies
    cancellation. A null atom reduces to `Fin 3`; the no-null case is the merge
    reduction `no_null_cancellation`. -/
theorem fa_cancellation_fin4 (sys : QualitativeProbability (Set (Fin 4))) :
    Cancellation sys.ge := by
  by_cases h : ∃ j, sys.ge ∅ {j}
  · obtain ⟨j, hj⟩ := h
    exact cancellation_of_null_atom sys hj representable_fin3
  · push Not at h
    exact no_null_cancellation sys h

/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem representable_fin4 (sys : QualitativeProbability (Set (Fin 4))) : Representable sys :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end ComparativeProbability
