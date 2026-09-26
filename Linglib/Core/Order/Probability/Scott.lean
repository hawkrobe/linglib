module

public import Linglib.Core.Order.FourierMotzkin
public import Linglib.Core.Order.Probability.Cancellation
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Scott's theorem

[scott-1964]'s representation theorem for qualitative probability on a finite
set: an order on the subsets of `Fin n` is represented by a finitely additive
probability measure iff it satisfies finite cancellation. Cancellation is
stated here in Scott's disjoint-comparison form (`Cancellation`): whenever the
indicator vectors `1_{Aₖ} - 1_{Bₖ}` of a list of comparisons `Aₖ ≿ Bₖ` between
disjoint sets sum to zero, every comparison in the list also holds reversed.
This is equivalent to the balanced-sequence form `FiniteCancellation` of
`Cancellation.lean` (`cancellation_iff_finiteCancellation`).

The hard direction is linear-programming duality over `ℚ` (`Polyhedral.farkas`):
the weight vectors representing the order form a polyhedron, which is nonempty
unless a Farkas certificate exists, and a certificate is a nonnegative
weighting of valid comparisons that sums to zero yet weights a strict one.
Clearing denominators turns it into a list violating `Cancellation`.

## Main declarations

* `Cancellation` — Scott's condition in disjoint-comparison form.
* `FiniteCancellation.cancellation`, `Cancellation.finiteCancellation`,
  `cancellation_iff_finiteCancellation` — the two forms agree.
* `cancellation_implies_representable` — the Farkas direction.
* `representable_iff_cancellation`, `representable_iff_finiteCancellation` —
  Scott's theorem.
* `cancellation_of_null_atom` — a null atom reduces cancellation to
  representability one atom down.

`[UPSTREAM]` candidate (see the note in `Defs.lean`).

## References

* [scott-1964]
* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

variable {n : ℕ}

/-! ### Comparison vectors -/

/-- The comparison vector `1_{c.1} - 1_{c.2}` of a pair of finsets. -/
def comparisonVec (c : Finset (Fin n) × Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ c.1 then 1 else 0) - (if i ∈ c.2 then 1 else 0)

/-- The sum of the comparison vectors of a list of pairs. -/
def comparisonSum (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) : ℤ :=
  (L.map (comparisonVec · i)).sum

@[simp] theorem comparisonSum_nil (i : Fin n) :
    comparisonSum ([] : List (Finset (Fin n) × Finset (Fin n))) i = 0 := rfl

@[simp] theorem comparisonSum_cons (c : Finset (Fin n) × Finset (Fin n))
    (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    comparisonSum (c :: L) i = comparisonVec c i + comparisonSum L i := by
  simp [comparisonSum]

theorem comparisonSum_perm {L L' : List (Finset (Fin n) × Finset (Fin n))} (h : L.Perm L') :
    comparisonSum L = comparisonSum L' :=
  funext fun _ ↦ (h.map _).sum_eq

/-- Dot product with a comparison vector is the difference of the side sums. -/
theorem sum_comparisonVec_mul (c : Finset (Fin n) × Finset (Fin n)) (x : Fin n → ℚ) :
    ∑ j, (comparisonVec c j : ℚ) * x j = ∑ j ∈ c.1, x j - ∑ j ∈ c.2, x j := by
  simp [comparisonVec, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_mem]

/-! ### Scott's condition -/

/-- **Scott's cancellation condition**, disjoint-comparison form
    ([scott-1964]): when the comparison vectors of a list of valid comparisons
    between disjoint sets sum to zero, every comparison in the list also holds
    reversed. -/
def Cancellation (ge : Set (Fin n) → Set (Fin n) → Prop) : Prop :=
  ∀ L : List (Finset (Fin n) × Finset (Fin n)), (∀ c ∈ L, Disjoint c.1 c.2) →
    (∀ c ∈ L, ge ↑c.1 ↑c.2) → comparisonSum L = 0 → ∀ c ∈ L, ge ↑c.2 ↑c.1

section Bridge

open scoped Classical

/-- The comparison vector sum of a list of finset pairs is the difference of
    the membership counts on its two sides. -/
private theorem comparisonSum_eq_seqCount (L : List (Finset (Fin n) × Finset (Fin n)))
    (i : Fin n) :
    comparisonSum L i = seqCount i (L.map fun c ↦ (↑c.1 : Set (Fin n))) -
      seqCount i (L.map fun c ↦ (↑c.2 : Set (Fin n))) := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, seqCount_cons, comparisonSum_cons, ih, comparisonVec, Finset.mem_coe]
    push_cast
    ring

/-- The balanced-sequence form implies the disjoint-comparison form. -/
theorem FiniteCancellation.cancellation {ge : Set (Fin n) → Set (Fin n) → Prop}
    (h : FiniteCancellation ge) : Cancellation ge := by
  intro L hdisj hge hsum c hc
  refine h ((L.erase c).map fun d ↦ ((↑d.1 : Set (Fin n)), (↑d.2 : Set (Fin n)))) ↑c.1 ↑c.2
    (fun i ↦ ?_) fun p hp ↦ ?_
  · have := congrFun ((comparisonSum_perm (List.perm_cons_erase hc)).symm.trans hsum) i
    rw [comparisonSum_eq_seqCount] at this
    simp only [List.map_map, List.map_cons, Function.comp_def, Pi.zero_apply] at this ⊢
    omega
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact hge d (List.mem_of_mem_erase hd)

/-- Membership counts on the two sides of a list of set pairs differ by the
    comparison vector sum. -/
private theorem seqCount_sub_seqCount (P : List (Set (Fin n) × Set (Fin n))) (i : Fin n) :
    (seqCount i (P.map Prod.fst) : ℤ) - seqCount i (P.map Prod.snd) =
      (P.map fun p ↦ ((if i ∈ p.1 then 1 else 0) - (if i ∈ p.2 then 1 else 0) : ℤ)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, seqCount_cons, List.sum_cons]
    push_cast
    rw [← ih]
    ring

/-- The disjoint normal form `(A \ B, B \ A)` of a comparison of sets. -/
private noncomputable def normalize (p : Set (Fin n) × Set (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  ((p.1 \ p.2).toFinset, (p.2 \ p.1).toFinset)

private theorem comparisonVec_normalize (p : Set (Fin n) × Set (Fin n)) (i : Fin n) :
    comparisonVec (normalize p) i = (if i ∈ p.1 then 1 else 0) - (if i ∈ p.2 then 1 else 0) := by
  simp only [comparisonVec, normalize, Set.mem_toFinset, Set.mem_sdiff]
  by_cases h1 : i ∈ p.1 <;> by_cases h2 : i ∈ p.2 <;> simp [h1, h2]

/-- For a qualitative probability order the disjoint-comparison form implies
    the balanced-sequence form: normalize every comparison by additivity. -/
theorem Cancellation.finiteCancellation (sys : QualitativeProbability (Set (Fin n)))
    (h : Cancellation sys.ge) : FiniteCancellation sys.ge := by
  intro prem X Y hbal hprem
  by_contra hYX
  have hXY : sys.le Y X := (sys.total X Y).resolve_left hYX
  have key := h (((X, Y) :: prem).map normalize) ?_ ?_ ?_ (normalize (X, Y))
    (List.mem_cons_self ..)
  · exact hYX ((sys.additive X Y).mpr (by simpa [normalize] using key))
  · intro c hc
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
    exact Set.disjoint_toFinset.mpr disjoint_sdiff_sdiff
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    simp only [QualitativeProbability.ge, normalize, Set.coe_toFinset]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (sys.additive Y X).mp hXY
    · exact (sys.additive p.2 p.1).mp (hprem p hp)
  · funext i
    have key := seqCount_sub_seqCount ((X, Y) :: prem) i
    simp only [List.map_cons, hbal i, sub_self, List.sum_cons] at key
    simp only [comparisonSum, List.map_map, List.map_cons, Function.comp_def,
      comparisonVec_normalize, Pi.zero_apply, List.sum_cons]
    omega

/-- The two forms of Scott's condition agree on a qualitative probability order. -/
theorem cancellation_iff_finiteCancellation (sys : QualitativeProbability (Set (Fin n))) :
    Cancellation sys.ge ↔ FiniteCancellation sys.ge :=
  ⟨Cancellation.finiteCancellation sys, FiniteCancellation.cancellation⟩

end Bridge

/-! ### Weighted cancellation

The Farkas certificate is a rational weighting of comparisons; `Cancellation`
handles it once the weights are cleared to natural multiplicities. -/

/-- Nonnegative rationals over a finite index have a common positive
    denominator `D`, with `D • w` natural-valued. -/
private theorem exists_nat_mul {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    ∃ (D : ℕ) (m : ι → ℕ), 0 < D ∧ ∀ i, (m i : ℚ) = D * w i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ w
  choose z hz using fun i ↦ hb i (Finset.mem_univ i)
  refine ⟨(b : ℤ).natAbs, fun i ↦ (z i).natAbs,
    Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero b), fun i ↦ ?_⟩
  have : ((z i : ℤ) : ℚ) = (b : ℤ) * w i := by simpa [zsmul_eq_mul] using hz i
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, this, abs_mul,
    abs_of_nonneg (hw i)]

private theorem comparisonSum_flatMap {α : Type*} (l : List α)
    (f : α → List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    comparisonSum (l.flatMap f) i = (l.map fun a ↦ comparisonSum (f a) i).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, comparisonSum, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem comparisonSum_replicate (m : ℕ) (c : Finset (Fin n) × Finset (Fin n))
    (i : Fin n) : comparisonSum (List.replicate m c) i = m * comparisonVec c i := by
  simp [comparisonSum, List.sum_replicate]

/-- Cancellation for rational weightings: a nonnegative weighting of valid
    comparisons whose comparison vectors sum to zero reverses every comparison
    it weights. -/
private theorem Cancellation.weighted {ge : Set (Fin n) → Set (Fin n) → Prop}
    (h : Cancellation ge) (w : Finset (Fin n) × Finset (Fin n) → ℚ) (hw : ∀ c, 0 ≤ w c)
    (hvalid : ∀ c, 0 < w c → Disjoint c.1 c.2 ∧ ge ↑c.1 ↑c.2)
    (hsum : ∀ i, ∑ c, w c * comparisonVec c i = 0) {c : Finset (Fin n) × Finset (Fin n)}
    (hc : 0 < w c) : ge ↑c.2 ↑c.1 := by
  obtain ⟨D, m, hD, hm⟩ := exists_nat_mul w hw
  have hpos : ∀ d, 0 < w d ↔ 0 < m d := fun d ↦ by
    rw [← Nat.cast_pos (α := ℚ), hm]
    exact ⟨fun h ↦ by positivity, fun h ↦ pos_of_mul_pos_right h (Nat.cast_nonneg D)⟩
  have hmem : ∀ d, d ∈ Finset.univ.toList.flatMap (fun d ↦ List.replicate (m d) d) ↔ 0 < w d :=
    fun d ↦ by simp [List.mem_flatMap, List.mem_replicate, hpos, Nat.pos_iff_ne_zero]
  refine h _ (fun d hd ↦ (hvalid d ((hmem d).mp hd)).1) (fun d hd ↦ (hvalid d ((hmem d).mp hd)).2)
    (funext fun i ↦ ?_) c ((hmem c).mpr hc)
  have : ((comparisonSum (Finset.univ.toList.flatMap fun d ↦ List.replicate (m d) d) i : ℤ) : ℚ)
      = D * ∑ d, w d * comparisonVec d i := by
    rw [comparisonSum_flatMap, Finset.sum_map_toList, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun d _ ↦ by rw [comparisonSum_replicate]; push_cast; rw [hm]; ring
  rw [hsum, mul_zero] at this
  exact_mod_cast this

/-! ### The Farkas direction -/

section Farkas

open scoped Classical

variable (sys : QualitativeProbability (Set (Fin n)))

/-- The comparisons between disjoint finsets that hold in `sys`. -/
private noncomputable def validPairs : List (Finset (Fin n) × Finset (Fin n)) :=
  (Finset.univ.filter fun c ↦ Disjoint c.1 c.2 ∧ sys.ge ↑c.1 ↑c.2).toList

private theorem mem_validPairs {c : Finset (Fin n) × Finset (Fin n)} :
    c ∈ validPairs sys ↔ Disjoint c.1 c.2 ∧ sys.ge ↑c.1 ↑c.2 := by
  simp [validPairs]

/-- The linear constraint of a comparison: `x(c.1) - x(c.2) ≥ 1` if `c` is
    strict and `≥ 0` otherwise, written `lhs · x ≤ rhs`. -/
private noncomputable def row (c : Finset (Fin n) × Finset (Fin n)) : Polyhedral.Ineq n :=
  ⟨fun j ↦ -(comparisonVec c j : ℚ), if sys.ge ↑c.2 ↑c.1 then 0 else -1⟩

private theorem row_sat {c : Finset (Fin n) × Finset (Fin n)} {x : Fin n → ℚ} :
    (row sys c).sat x ↔
      (if sys.ge ↑c.2 ↑c.1 then 0 else 1) ≤ ∑ j ∈ c.1, x j - ∑ j ∈ c.2, x j := by
  simp only [row, Polyhedral.Ineq.sat, Polyhedral.dot, neg_mul, Finset.sum_neg_distrib,
    sum_comparisonVec_mul]
  split_ifs <;> constructor <;> intro h <;> linarith

/-- The linear system of all valid comparisons. -/
private noncomputable def system : Polyhedral.System n := (validPairs sys).map (row sys)

/-- A solution of the system, normalized, is a representing measure. -/
private theorem representable_of_feasible {x : Fin n → ℚ} (hx : ∀ r ∈ system sys, r.sat x) :
    Representable sys := by
  have hvalid : ∀ c : Finset (Fin n) × Finset (Fin n), Disjoint c.1 c.2 → sys.ge ↑c.1 ↑c.2 →
      (if sys.ge ↑c.2 ↑c.1 then 0 else 1) ≤ ∑ j ∈ c.1, x j - ∑ j ∈ c.2, x j :=
    fun c hd hg ↦ (row_sat sys).mp (hx _ (List.mem_map_of_mem ((mem_validPairs sys).mpr ⟨hd, hg⟩)))
  have hnn : ∀ j, 0 ≤ x j := fun j ↦ by
    have := hvalid ({j}, ∅) (Finset.disjoint_empty_right _) (by simpa using sys.bot_le _)
    simp only [Finset.sum_singleton, Finset.sum_empty, sub_zero] at this
    split_ifs at this <;> linarith
  have hσ : 0 < ∑ j, x j := by
    have := hvalid (Finset.univ, ∅) (Finset.disjoint_empty_right _) (by simpa using sys.bot_le _)
    have hstrict : ¬sys.ge ↑(∅ : Finset (Fin n)) ↑(Finset.univ : Finset (Fin n)) := by
      simpa [← Set.top_eq_univ, ← Set.bot_eq_empty] using sys.nonTrivial
    simp only [hstrict, ite_false, Finset.sum_empty, sub_zero] at this
    linarith
  let m := FinAddMeasure.ofFintype (fun j ↦ x j / ∑ j, x j)
    (fun j ↦ div_nonneg (hnn j) hσ.le) (by rw [← Finset.sum_div, div_self hσ.ne'])
  have hm : ∀ A : Set (Fin n), m A = (∑ j ∈ A.toFinset, x j) / ∑ j, x j := fun A ↦ by
    simp only [m, FinAddMeasure.ofFintype, FinAddMeasure.coe_mk]
    rw [Finset.sum_div, ← Fintype.sum_ite_mem A.toFinset]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [Set.mem_toFinset]
  refine ⟨m, reduce_to_disjoint sys m fun C D hCD ↦ ?_⟩
  rw [hm, hm, div_le_div_iff_of_pos_right hσ]
  constructor
  · intro h
    have := hvalid (D.toFinset, C.toFinset) (Set.disjoint_toFinset.mpr hCD.symm) (by simpa using h)
    split_ifs at this <;> linarith
  · intro h
    by_contra hCD'
    have := hvalid (C.toFinset, D.toFinset) (Set.disjoint_toFinset.mpr hCD)
      (by simpa using (sys.total C D).resolve_left hCD')
    rw [ite_eq_right (by simpa using hCD')] at this
    linarith

/-- A Farkas certificate for the system, regrouped by comparison, is a
    nonnegative neutral weighting with positive weight on a strict comparison. -/
private theorem not_cancellation_of_infeasCert (cert : Polyhedral.InfeasCert (system sys)) :
    ¬Cancellation sys.ge := by
  intro hcancel
  have hlen : (system sys).length = (validPairs sys).length := List.length_map ..
  -- the comparison behind each row
  let pair : Fin (system sys).length → Finset (Fin n) × Finset (Fin n) := fun i ↦
    (validPairs sys).get (i.cast hlen)
  have hget : ∀ i, (system sys).get i = row sys (pair i) := fun i ↦ by
    simp [system, List.get_eq_getElem, pair]
  -- the weight of a comparison: the certificate weights of its rows
  let w : Finset (Fin n) × Finset (Fin n) → ℚ := fun c ↦ ∑ i, if pair i = c then cert.ws i else 0
  have hw : ∀ c, 0 ≤ w c := fun c ↦ Finset.sum_nonneg fun i _ ↦ by
    split_ifs <;> simp [cert.nonneg]
  have hregroup : ∀ g : Finset (Fin n) × Finset (Fin n) → ℚ,
      ∑ c, w c * g c = ∑ i, cert.ws i * g (pair i) := fun g ↦ by
    simp only [w, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_ite_eq]; simp
  have hpos : ∀ c, 0 < w c → ∃ i, pair i = c ∧ 0 < cert.ws i := fun c hc ↦ by
    by_contra hall
    push Not at hall
    refine hc.not_ge (Finset.sum_nonpos fun i _ ↦ ?_)
    split_ifs with hi
    · exact hall i hi
    · exact le_rfl
  have hvalid : ∀ c, 0 < w c → Disjoint c.1 c.2 ∧ sys.ge ↑c.1 ↑c.2 := fun c hc ↦ by
    obtain ⟨i, rfl, -⟩ := hpos c hc
    exact (mem_validPairs sys).mp (List.get_mem _ _)
  have hsum : ∀ j, ∑ c, w c * comparisonVec c j = 0 := fun j ↦ by
    have h := cert.coeffsZero j
    simp only [hget, row, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h
    rw [hregroup]; exact h
  have hstrict : ∃ i, 0 < cert.ws i ∧ ¬sys.ge ↑(pair i).2 ↑(pair i).1 := by
    by_contra hall
    push Not at hall
    have h := cert.boundNeg
    simp only [hget, row] at h
    refine h.not_ge (le_of_eq (Finset.sum_eq_zero fun i _ ↦ ?_).symm)
    split_ifs with hi
    · exact mul_zero _
    · rw [le_antisymm (not_lt.mp fun hlt ↦ hi (hall i hlt)) (cert.nonneg i), zero_mul]
  obtain ⟨i, hi, hstr⟩ := hstrict
  refine hstr (hcancel.weighted w hw hvalid hsum (c := pair i) (lt_of_lt_of_le hi ?_))
  have := Finset.single_le_sum (f := fun k ↦ if pair k = pair i then cert.ws k else 0)
    (fun k _ ↦ by split_ifs <;> simp [cert.nonneg]) (Finset.mem_univ i)
  simpa using this

/-- **Scott's theorem**, hard direction: a qualitative probability order
    satisfying cancellation is represented by a finitely additive measure. -/
theorem cancellation_implies_representable (h : Cancellation sys.ge) : Representable sys :=
  (Polyhedral.farkas (system sys)).elim (fun ⟨_, hx⟩ ↦ representable_of_feasible sys hx)
    fun ⟨cert⟩ ↦ absurd h (not_cancellation_of_infeasCert sys cert)

end Farkas

/-! ### Scott's theorem -/

/-- **Scott's theorem** ([scott-1964]), disjoint-comparison form. -/
theorem representable_iff_cancellation (sys : QualitativeProbability (Set (Fin n))) :
    Representable sys ↔ Cancellation sys.ge :=
  ⟨fun h ↦ h.finiteCancellation.cancellation, cancellation_implies_representable sys⟩

/-- **Scott's theorem** ([scott-1964]), balanced-sequence form. -/
theorem representable_iff_finiteCancellation (sys : QualitativeProbability (Set (Fin n))) :
    Representable sys ↔ FiniteCancellation sys.ge :=
  (representable_iff_cancellation sys).trans (cancellation_iff_finiteCancellation sys)

/-- A null atom plus representability one cardinality down yields cancellation:
    swap the null atom to position 0 and apply `null_elem_reduce`. -/
theorem cancellation_of_null_atom (sys : QualitativeProbability (Set (Fin (n + 2))))
    {j : Fin (n + 2)} (hj : sys.ge ∅ {j})
    (sub : ∀ sys' : QualitativeProbability (Set (Fin (n + 1))), Representable sys') :
    Cancellation sys.ge := by
  set σ := Equiv.swap (0 : Fin (n + 2)) j with hσ
  have h0 : (sys.transport σ).le {0} ∅ := by
    rw [perm_null_iff, show σ.symm 0 = j by simp [hσ]]; exact hj
  have hnn : ∃ i : Fin (n + 1), ¬(sys.transport σ).le {Fin.succ i} ∅ := by
    obtain ⟨k, hk⟩ := (sys.transport σ).exists_singleton_not_le_empty
    obtain ⟨i, rfl⟩ : ∃ i, Fin.succ i = k := Fin.exists_succ_eq.mpr fun h ↦ hk (h ▸ h0)
    exact ⟨i, hk⟩
  exact (representable_iff_cancellation sys).mp
    (perm_repr σ sys (null_elem_reduce _ h0 hnn sub))

end ComparativeProbability
