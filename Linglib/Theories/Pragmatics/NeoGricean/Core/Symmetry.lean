import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Fox2007

/-!
# Symmetric Alternatives

The **symmetry problem** is the central challenge for any theory of scalar
implicatures based on alternatives. The problem: for any stronger
alternative A of an assertion S, the sentence S ∧ ¬A is also stronger
than S and yields the *opposite* implicature. A theory of alternatives
must explain why A enters the alternative set but S ∧ ¬A does not.

The problem emerged in the early 1970s: @cite{horn-1972} established
the Gricean derivation of scalar implicatures, and @cite{kroch-1972}
discussed the same reasoning for quantifiers, creating the conditions
for recognizing that symmetric alternatives pose a fundamental obstacle.
Every subsequent theory of alternatives is shaped by this problem:

- @cite{katzir-2007} addresses it via **structural complexity**: S ∧ ¬A
  is structurally more complex than S, so it is excluded from F(S)
- @cite{fox-2007}'s **innocent exclusion** correctly handles symmetric
  alternatives (they land in different MCEs, so neither is in I-E),
  but the problem of which alternatives *enter the set* remains
- @cite{fox-katzir-2011} show that **contextual restriction cannot
  break symmetry** — only the formal alternative set F can
- @cite{breheny-et-al-2018} show that none of these fully solve
  the problem (indirect SIs, gradable adjectives, too many/few
  lexical alternatives remain problematic)

This file defines the core concepts — `isSymmetric`, complement
equivalence, and inconsistency of joint exclusion — as theory-neutral
infrastructure that any approach can import. The definition follows
@cite{fox-katzir-2011} definition 12, but the concept is not specific
to that paper.

## Key Definitions and Theorems

- `isSymmetric`: S₁, S₂ partition S's denotation (def 12)
- `symmetric_complement`: S ∧ ¬S₁ = S₂ when symmetric
- `both_excluded_inconsistent`: excluding both contradicts S
- `symmetric_not_ie`: symmetric alternatives are never in I-E
- `exhB_vacuous_of_ie_empty`: exhB = identity when I-E is empty
- `symmetric_exhB_vacuous`: exhB is vacuous when only symmetric alts
- `RelevanceClosure`: closure under ¬ and ∧ (condition 50)
- `context_cannot_break_symmetry`: C preserves symmetry (constraint 28)
-/

namespace NeoGricean.Symmetry

open NeoGricean.Exhaustivity.Fox2007


-- ============================================================
-- SECTION 1: The Symmetry Predicate
-- ============================================================

/-- Two propositions are **symmetric alternatives** of S if they
    partition S's denotation: their union equals S and they are
    mutually exclusive.

    Formalized from @cite{fox-katzir-2011} definition 12. The
    underlying problem was recognized in the early 1970s
    (@cite{horn-1972}, @cite{kroch-1972}).

    Note: this is stricter than mere non-innocent-excludability.
    Disjuncts p, q of p∨q are often mutually compatible (p ∩ q ≠ ∅)
    and hence NOT symmetric, though they still resist innocent
    exclusion for related reasons (@cite{fox-katzir-2011} fn. 18). -/
def isSymmetric {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) : Bool :=
  -- (a) ⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧
  domain.all (fun w => (s₁ w || s₂ w) == s w) &&
  -- (b) ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅
  domain.all (fun w => !(s₁ w && s₂ w))


-- ============================================================
-- SECTION 2: Core Properties
-- ============================================================

/-- When S₁, S₂ are symmetric alternatives of S, S ∧ ¬S₁ is
    extensionally equal to S₂. This is the key fact underlying
    the relevance argument: showing S ∧ ¬S₁ is relevant suffices
    to show S₂ is relevant. -/
theorem symmetric_complement {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool)
    (hsym : isSymmetric domain s s₁ s₂ = true) :
    domain.all (fun w => (s w && !s₁ w) == s₂ w) = true := by
  unfold isSymmetric at hsym
  have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsym
  rw [List.all_eq_true] at ha hb ⊢
  intro w hw
  specialize ha w hw
  specialize hb w hw
  simp [BEq.beq] at ha hb ⊢
  cases h1 : s₁ w <;> cases h2 : s₂ w <;> simp_all


-- ============================================================
-- SECTION 3: Bridge to Innocent Exclusion (Fox 2007)
-- ============================================================

/-- Excluding both symmetric alternatives is inconsistent with S.
    If S₁, S₂ partition S, then S ∧ ¬S₁ ∧ ¬S₂ is unsatisfiable:
    every S-world is an S₁-world or S₂-world (by the union
    condition) but the exclusion requires it to be neither. -/
theorem both_excluded_inconsistent {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₁ i₂ : Nat) (excl : List Nat)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₁ : alts[i₁]? = some s₁) (hi₂ : alts[i₂]? = some s₂)
    (hm₁ : i₁ ∈ excl) (hm₂ : i₂ ∈ excl) :
    exclusionConsistent domain s alts excl = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold exclusionConsistent at h
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, hwand⟩ := h
  rw [Bool.and_eq_true_iff] at hwand
  obtain ⟨_, hall⟩ := hwand
  rw [List.all_eq_true] at hall
  have hs1 := hall s₁ (List.mem_filterMap.mpr ⟨i₁, hm₁, hi₁⟩)
  have hs2 := hall s₂ (List.mem_filterMap.mpr ⟨i₂, hm₂, hi₂⟩)
  unfold isSymmetric at hsym
  have ⟨ha, _⟩ := Bool.and_eq_true_iff.mp hsym
  rw [List.all_eq_true] at ha
  specialize ha w hw
  simp [BEq.beq] at ha
  cases s₁ w <;> cases s₂ w <;> simp_all

-- ── Private helpers for symmetric_not_ie ──────────────────

private theorem list_self_contains (l : List Nat) :
    l.all (fun i => l.contains i) = true := by
  rw [List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr hx

private theorem list_contains_trans (a b c : List Nat)
    (hab : a.all (fun i => b.contains i) = true)
    (hbc : b.all (fun i => c.contains i) = true) :
    a.all (fun i => c.contains i) = true := by
  rw [List.all_eq_true] at hab hbc ⊢
  intro x hx
  exact hbc x (List.contains_iff_mem.mp (hab x hx))

private theorem exists_max_length (l : List (List Nat)) (hl : l ≠ []) :
    ∃ m ∈ l, ∀ t ∈ l, t.length ≤ m.length := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst hxs
      exact ⟨x, List.mem_cons_self, fun t ht => by
        simp [List.mem_cons] at ht; subst ht; exact Nat.le_refl _⟩
    · obtain ⟨m, hm, hmax⟩ := ih hxs
      by_cases h : x.length ≥ m.length
      · exact ⟨x, List.mem_cons_self, fun t ht => by
          cases List.mem_cons.mp ht with
          | inl h' => subst h'; exact Nat.le_refl _
          | inr h' => exact Nat.le_trans (hmax t h') h⟩
      · exact ⟨m, List.mem_cons_of_mem x hm, fun t ht => by
          cases List.mem_cons.mp ht with
          | inl h' => subst h'; omega
          | inr h' => exact hmax t h'⟩

private theorem mce_consistent {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (M : List Nat) (hM : M ∈ maxConsistentExclusions domain p alts) :
    exclusionConsistent domain p alts M = true := by
  unfold maxConsistentExclusions at hM
  exact (List.mem_filter.mp (List.mem_filter.mp hM).1).2

private theorem exists_maximal_extension
    (consistent : List (List Nat))
    (E : List Nat) (hE : E ∈ consistent) :
    ∃ M ∈ consistent.filter (fun s =>
      !consistent.any fun t =>
        decide (t.length > s.length) && s.all fun i => t.contains i),
    E.all (fun i => M.contains i) = true := by
  have hE_ext : E ∈ consistent.filter (fun T => E.all (fun i => T.contains i)) :=
    List.mem_filter.mpr ⟨hE, list_self_contains E⟩
  obtain ⟨M, hM_ext, hM_max⟩ := exists_max_length _
    (List.ne_nil_of_mem hE_ext)
  have ⟨hM_con, hM_sup⟩ := List.mem_filter.mp hM_ext
  have hM_not_dominated : consistent.any (fun t =>
      decide (t.length > M.length) && M.all (fun i => t.contains i)) = false := by
    rw [Bool.eq_false_iff]
    intro habs
    rw [List.any_eq_true] at habs
    obtain ⟨T, hT_con, hT_prop⟩ := habs
    rw [Bool.and_eq_true_iff] at hT_prop
    obtain ⟨hT_len, hT_sub⟩ := hT_prop
    have hT_ext : T ∈ consistent.filter (fun T' => E.all (fun i => T'.contains i)) :=
      List.mem_filter.mpr ⟨hT_con, list_contains_trans E M T hM_sup hT_sub⟩
    have := hM_max T hT_ext
    simp [decide_eq_true_eq] at hT_len
    omega
  exact ⟨M, List.mem_filter.mpr ⟨hM_con, by
    simp only [Bool.not_eq_true']; exact hM_not_dominated⟩, hM_sup⟩

private theorem ie_imp_in_all_mce {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) (i : Nat)
    (h : (ieIndices domain p alts).contains i = true) :
    ∀ M ∈ maxConsistentExclusions domain p alts, M.contains i = true := by
  unfold ieIndices at h
  intro M hM
  match hmces : maxConsistentExclusions domain p alts with
  | [] =>
    rw [hmces] at hM
    exact absurd hM List.not_mem_nil
  | first :: rest =>
    rw [hmces] at hM
    simp only [hmces] at h
    have hi_filtered := List.contains_iff_mem.mp h
    have ⟨hi_first, hi_pred⟩ := List.mem_filter.mp hi_filtered
    cases List.mem_cons.mp hM with
    | inl heq => subst heq; exact List.contains_iff_mem.mpr hi_first
    | inr hrest =>
      rw [List.all_eq_true] at hi_pred
      exact hi_pred M hrest

private theorem nil_mem_sublists (xs : List Nat) :
    [] ∈ sublists xs := by
  induction xs with
  | nil => unfold sublists; exact List.mem_cons_self
  | cons x xs ih =>
    unfold sublists
    rw [List.mem_append]
    exact Or.inl ih

private theorem singleton_mem_sublists
    (i : Nat) (xs : List Nat) (h : i ∈ xs) :
    [i] ∈ sublists xs := by
  induction xs with
  | nil => exact absurd h List.not_mem_nil
  | cons x xs ih =>
    unfold sublists
    rw [List.mem_append]
    cases List.mem_cons.mp h with
    | inl heq =>
      right
      subst heq
      exact List.mem_map_of_mem (nil_mem_sublists xs)
    | inr hmem =>
      left
      exact ih hmem

private theorem sym_witness {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (h_sat₁ : domain.any s₁ = true) :
    ∃ w ∈ domain, s w = true ∧ s₂ w = false := by
  unfold isSymmetric at hsym
  have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsym
  rw [List.all_eq_true] at ha hb
  rw [List.any_eq_true] at h_sat₁
  obtain ⟨w, hw, hs₁w⟩ := h_sat₁
  specialize ha w hw
  specialize hb w hw
  simp [BEq.beq] at ha hb
  refine ⟨w, hw, ?_, ?_⟩
  · rw [← ha, hs₁w]; simp
  · cases hs₂ : s₂ w with
    | false => rfl
    | true => exfalso; simp [hs₁w, hs₂] at hb

private theorem sym_nonweaker {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₂ : Nat) (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true)
    (h_bound : i₂ < alts.length) :
    i₂ ∈ nonWeakerIndices domain s alts := by
  unfold nonWeakerIndices
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr h_bound, ?_⟩
  simp only [hi₂]
  rw [List.any_eq_true]
  obtain ⟨w, hw, hsw, hs₂w⟩ := sym_witness domain s s₁ s₂ hsym h_sat₁
  exact ⟨w, hw, by rw [Bool.and_eq_true_iff]; exact ⟨hsw, by simp [hs₂w]⟩⟩

private theorem singleton_consistent {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₂ : Nat) (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true) :
    exclusionConsistent domain s alts [i₂] = true := by
  unfold exclusionConsistent
  rw [List.any_eq_true]
  obtain ⟨w, hw, hsw, hs₂w⟩ := sym_witness domain s s₁ s₂ hsym h_sat₁
  refine ⟨w, hw, ?_⟩
  rw [Bool.and_eq_true_iff]
  constructor
  · exact hsw
  · rw [List.all_eq_true]
    intro q hq
    simp [List.filterMap, hi₂] at hq
    rw [hq, hs₂w]; rfl

private theorem exists_mce_containing {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₂ : Nat) (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true)
    (h_bound : i₂ < alts.length) :
    ∃ M ∈ maxConsistentExclusions domain s alts, M.contains i₂ = true := by
  have h_nw := sym_nonweaker domain s s₁ s₂ alts i₂ hsym hi₂ h_sat₁ h_bound
  have h_in_consistent : [i₂] ∈ (sublists (nonWeakerIndices domain s alts)).filter
      (exclusionConsistent domain s alts) :=
    List.mem_filter.mpr ⟨singleton_mem_sublists i₂ _ h_nw,
      singleton_consistent domain s s₁ s₂ alts i₂ hsym hi₂ h_sat₁⟩
  obtain ⟨M, hM_max, hM_sup⟩ := exists_maximal_extension _ [i₂] h_in_consistent
  exact ⟨M, hM_max, by
    rw [List.all_eq_true] at hM_sup
    exact hM_sup i₂ List.mem_cons_self⟩

private theorem isSymmetric_comm {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool)
    (hsym : isSymmetric domain s s₁ s₂ = true) :
    isSymmetric domain s s₂ s₁ = true := by
  unfold isSymmetric at hsym ⊢
  have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsym
  rw [Bool.and_eq_true_iff]
  constructor
  · rw [List.all_eq_true] at ha ⊢
    intro w hw; specialize ha w hw
    simp [BEq.beq] at ha ⊢
    rw [Bool.or_comm]; exact ha
  · rw [List.all_eq_true] at hb ⊢
    intro w hw; specialize hb w hw
    simp at hb ⊢
    exact Or.comm.mp hb

-- ── Main theorem ──────────────────────────────────────────

/-- **General principle**: symmetric alternatives are never innocently
    excludable. If S₁, S₂ partition S's denotation and both appear in
    the alternative set, then neither is in I-E.

    The argument: since ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅ and ⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧,
    excluding both is unsatisfiable (proved by
    `both_excluded_inconsistent`). So each MCE contains at most
    one of {S₁, S₂}. Since each can be consistently excluded
    individually (witnessed by an S₂-world or S₁-world respectively),
    each appears in some MCE but not all. Hence neither is in
    I-E = ⋂MCEs.

    The proof establishes that `{i₂}` is a consistent exclusion set
    (using `sym_witness`), extends it to a maximal consistent exclusion
    (via `exists_maximal_extension`), and observes that this MCE
    cannot contain `i₁` (by `both_excluded_inconsistent`). The
    symmetric argument shows an MCE containing `i₁` but not `i₂`. -/
theorem symmetric_not_ie {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₁ i₂ : Nat) (_h_ne : i₁ ≠ i₂)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₁ : alts[i₁]? = some s₁) (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true)
    (h_sat₂ : domain.any s₂ = true) :
    let ie := ieIndices domain s alts
    ie.contains i₁ = false ∧ ie.contains i₂ = false := by
  intro ie
  have hsym' := isSymmetric_comm domain s s₁ s₂ hsym
  have h_bound₁ := (List.getElem?_eq_some_iff.mp hi₁).1
  have h_bound₂ := (List.getElem?_eq_some_iff.mp hi₂).1
  constructor
  · -- ie.contains i₁ = false: the MCE containing i₂ witnesses absence
    rw [Bool.eq_false_iff]
    intro h_in_ie
    have h_all := ie_imp_in_all_mce domain s alts i₁ h_in_ie
    obtain ⟨M, hM_mce, hM_i₂⟩ := exists_mce_containing domain s s₁ s₂ alts i₂
      hsym hi₂ h_sat₁ h_bound₂
    have hM_i₁ := h_all M hM_mce
    exact absurd (mce_consistent domain s alts M hM_mce)
      (Bool.eq_false_iff.mp (both_excluded_inconsistent domain s s₁ s₂ alts i₁ i₂ M
        hsym hi₁ hi₂
        (List.contains_iff_mem.mp hM_i₁) (List.contains_iff_mem.mp hM_i₂)))
  · -- ie.contains i₂ = false: the MCE containing i₁ witnesses absence
    rw [Bool.eq_false_iff]
    intro h_in_ie
    have h_all := ie_imp_in_all_mce domain s alts i₂ h_in_ie
    obtain ⟨M, hM_mce, hM_i₁⟩ := exists_mce_containing domain s s₂ s₁ alts i₁
      hsym' hi₁ h_sat₂ h_bound₁
    have hM_i₂ := h_all M hM_mce
    exact absurd (mce_consistent domain s alts M hM_mce)
      (Bool.eq_false_iff.mp (both_excluded_inconsistent domain s s₁ s₂ alts i₁ i₂ M
        hsym hi₁ hi₂
        (List.contains_iff_mem.mp hM_i₁) (List.contains_iff_mem.mp hM_i₂)))


-- ============================================================
-- SECTION 4: Vacuity Corollary
-- ============================================================

/-- When `ieIndices` returns the empty list, `exhB` reduces to the
    prejacent — no alternatives are excluded. -/
theorem exhB_vacuous_of_ie_empty {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool)
    (h : ieIndices domain p alts = []) :
    ∀ w, exhB domain alts p w = p w := by
  intro w
  simp [exhB, h, Bool.and_true]

-- ── Helpers for symmetric_exhB_vacuous ───────────────────────

private theorem mem_of_mem_sublists
    (x : Nat) (xs : List Nat) (l : List Nat)
    (hl : l ∈ sublists xs) (hx : x ∈ l) : x ∈ xs := by
  induction xs generalizing l with
  | nil =>
    simp [sublists] at hl
    subst hl
    exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    simp only [sublists] at hl
    rw [List.mem_append] at hl
    cases hl with
    | inl h_left => exact List.mem_cons_of_mem y (ih l h_left hx)
    | inr h_right =>
      rw [List.mem_map] at h_right
      obtain ⟨l', hl', heq⟩ := h_right
      subst heq
      cases List.mem_cons.mp hx with
      | inl heq => subst heq; exact List.mem_cons_self
      | inr hmem => exact List.mem_cons_of_mem y (ih l' hl' hmem)

private theorem mce_elem_in_nw {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (M : List Nat) (i : Nat)
    (hM : M ∈ maxConsistentExclusions domain p alts)
    (hi : i ∈ M) :
    i ∈ nonWeakerIndices domain p alts := by
  unfold maxConsistentExclusions at hM
  have hM_con := (List.mem_filter.mp hM).1
  have hM_sub := (List.mem_filter.mp hM_con).1
  exact mem_of_mem_sublists i (nonWeakerIndices domain p alts) M hM_sub hi

private theorem ie_elem_in_nw {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (i : Nat)
    (h : i ∈ ieIndices domain p alts) :
    i ∈ nonWeakerIndices domain p alts := by
  unfold ieIndices at h
  match hmces : maxConsistentExclusions domain p alts with
  | [] => rw [hmces] at h; exact absurd h List.not_mem_nil
  | first :: rest =>
    rw [hmces] at h
    have hi_first := (List.mem_filter.mp h).1
    have hfirst_mce : first ∈ maxConsistentExclusions domain p alts := by
      rw [hmces]; exact List.mem_cons_self
    exact mce_elem_in_nw domain p alts first i hfirst_mce hi_first

-- ── Main corollary ──────────────────────────────────────────

/-- **Vacuity corollary**: when the symmetric pair are the *only*
    non-weaker alternatives, `exhB` is the identity —
    exhaustification is vacuous.

    This is the general principle underlying the concrete
    `FoxKatzir2011.symmetry_problem`: with both symmetric
    alternatives present and no other non-weaker alternatives,
    I-E is empty, so `exh` does nothing. -/
theorem symmetric_exhB_vacuous {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₁ i₂ : Nat) (h_ne : i₁ ≠ i₂)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₁ : alts[i₁]? = some s₁) (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true) (h_sat₂ : domain.any s₂ = true)
    (h_only : ∀ j, j ∈ nonWeakerIndices domain s alts →
      j = i₁ ∨ j = i₂) :
    ∀ w, exhB domain alts s w = s w := by
  have ⟨h_not₁, h_not₂⟩ := symmetric_not_ie domain s s₁ s₂ alts i₁ i₂
    h_ne hsym hi₁ hi₂ h_sat₁ h_sat₂
  have h_ie_empty : ieIndices domain s alts = [] := by
    match h_eq : ieIndices domain s alts with
    | [] => rfl
    | j :: _ =>
      exfalso
      have hj : j ∈ ieIndices domain s alts := by
        rw [h_eq]; exact List.mem_cons_self
      have h_nw := ie_elem_in_nw domain s alts j hj
      cases h_only j h_nw with
      | inl heq =>
        subst heq
        exact absurd (List.contains_iff_mem.mpr hj)
          (Bool.eq_false_iff.mp h_not₁)
      | inr heq =>
        subst heq
        exact absurd (List.contains_iff_mem.mpr hj)
          (Bool.eq_false_iff.mp h_not₂)
  exact exhB_vacuous_of_ie_empty domain alts s h_ie_empty


-- ============================================================
-- SECTION 5: Relevance Closure and Constraint 28
-- ============================================================

/-!
## Context Cannot Break Symmetry

The set of contextually relevant sentences C must satisfy closure
conditions (@cite{fox-katzir-2011} condition 50):

(50a) If S is relevant, so is ¬S.
(50b) If S₁, S₂ are relevant, so is S₁ ∧ S₂.

From these conditions, constraint (28) follows: **symmetry cannot be
broken in C**. If S₁ is relevant and S is relevant, then S ∧ ¬S₁ is
relevant (by 50a + 50b). But when S₁, S₂ are symmetric, S ∧ ¬S₁ ≡ S₂
(by `symmetric_complement`). So S₂ is also relevant, and contextual
restriction cannot selectively eliminate one symmetric alternative
while keeping the other.
-/

/-- Closure conditions on relevance (condition 50). -/
structure RelevanceClosure (W : Type) where
  relevant : (W → Bool) → Bool
  negClosed : ∀ (p : W → Bool), relevant p = true →
    relevant (fun w => !p w) = true
  conjClosed : ∀ (p q : W → Bool), relevant p = true →
    relevant q = true → relevant (fun w => p w && q w) = true

/-- **C cannot break symmetry (constraint 28)**: if S₁ is relevant
    and S is relevant, then the symmetric partner S ∧ ¬S₁ (which
    equals S₂ when S₁, S₂ are symmetric by `symmetric_complement`)
    is also relevant.

    Therefore any contextual restriction that keeps S₁ must also
    keep S₂. Symmetry breaking must happen in F, not in C. -/
theorem context_cannot_break_symmetry {W : Type}
    (rc : RelevanceClosure W)
    (s s₁ : W → Bool)
    (hs : rc.relevant s = true)
    (h₁ : rc.relevant s₁ = true) :
    rc.relevant (fun w => s w && !s₁ w) = true :=
  rc.conjClosed s (fun w => !s₁ w) hs (rc.negClosed s₁ h₁)


end NeoGricean.Symmetry
