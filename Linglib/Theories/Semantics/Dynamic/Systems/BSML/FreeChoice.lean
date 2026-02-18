import Linglib.Theories.Semantics.Dynamic.Systems.BSML.Basic

/-!
# BSML Free Choice Theorems

Pragmatic enrichment and free choice derivations in BSML (Aloni 2022).

## Key Results

| Result | Statement |
|--------|-----------|
| Narrow Scope FC | [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β |
| Wide Scope FC | [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (if R indisputable) |
| Dual Prohibition | [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β |

## Proof Architecture

Free choice is DERIVED from three independent principles:
1. **Split disjunction**: team is partitioned for ∨
2. **NE enrichment**: [·]⁺ adds non-emptiness constraints recursively
3. **NE non-flatness**: empty teams fail NE, so both parts must be non-empty

## References

- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
  @cite{aloni-2022}
-/

namespace Semantics.Dynamic.BSML

open Semantics.Dynamic.TeamSemantics

-- ============================================================================
-- Section 1: Flatness
-- ============================================================================

/-- A team proposition is flat if support is downward closed under subset -/
def isFlat {W : Type*} (prop : Team W → Bool) (worlds : List W) : Prop :=
  ∀ t t' : Team W, t'.subset t worlds = true → prop t = true → prop t' = true

/-- Atoms are flat: if all worlds in t satisfy p, then all worlds in t' ⊆ t satisfy p -/
theorem atom_is_flat {W : Type*} [DecidableEq W] (M : BSMLModel W) (p : String) :
    isFlat (λ t => support M (.atom p) t) M.worlds := by
  intro t t' hSub hSupp
  simp only [support, Team.all] at *
  simp only [Team.subset, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
              Bool.eq_false_iff] at *
  intro w hw
  cases ht' : t' w
  · simp
  · have h1 := hSub w hw
    simp [ht'] at h1
    have h2 := hSupp w hw
    simp [h1] at h2
    simp [h2]

/-- NE is NOT flat: the empty team doesn't support NE, but is a subset of any team that does -/
theorem ne_not_flat {W : Type*} [DecidableEq W] [Inhabited W] (worlds : List W) (hWorlds : worlds ≠ []) :
    ¬isFlat (λ t => support (BSMLModel.universal worlds : BSMLModel W) .ne t) worlds := by
  intro hFlat
  simp only [isFlat] at hFlat
  have hEmpty : Team.empty.subset Team.full worlds = true := by
    simp [Team.subset, Team.empty, Team.full, List.all_eq_true]
  have hFullNE : support (BSMLModel.universal worlds) .ne Team.full = true := by
    simp only [support, Team.isNonEmpty, BSMLModel.universal]
    cases worlds with
    | nil => contradiction
    | cons w ws =>
        simp only [List.any_cons, Team.full]
        rfl
  have hEmptyNotNE : support (BSMLModel.universal worlds) .ne Team.empty = false := by
    simp only [support, Team.isNonEmpty, BSMLModel.universal]
    have hAnyEmpty : ∀ ws : List W, ws.any Team.empty = false := λ ws => by
      induction ws with
      | nil => rfl
      | cons w ws ih => simp only [List.any_cons, Team.empty, Bool.false_or, ih]
    exact hAnyEmpty worlds
  have := hFlat Team.full Team.empty hEmpty hFullNE
  rw [hEmptyNotNE] at this
  exact Bool.false_ne_true this

-- ============================================================================
-- Section 2: Pragmatic Enrichment + Structure Lemmas
-- ============================================================================

/--
Pragmatic enrichment [·]⁺ (Definition 6 from Aloni 2022).

The key insight: add non-emptiness constraints recursively.
This captures the "neglect-zero" tendency in human cognition.

[p]⁺ = p ∧ NE
[NE]⁺ = NE
[¬φ]⁺ = ¬[φ]⁺ ∧ NE
[φ ∧ ψ]⁺ = [φ]⁺ ∧ [ψ]⁺
[φ ∨ ψ]⁺ = [φ]⁺ ∨ [ψ]⁺
[◇φ]⁺ = ◇[φ]⁺ ∧ NE
[□φ]⁺ = □[φ]⁺ ∧ NE
-/
def enrich : BSMLFormula → BSMLFormula
  | .atom p => .conj (.atom p) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg (enrich φ)) .ne
  | .conj φ ψ => .conj (enrich φ) (enrich ψ)
  | .disj φ ψ => .disj (enrich φ) (enrich ψ)
  | .poss φ => .conj (.poss (enrich φ)) .ne
  | .nec φ => .conj (.nec (enrich φ)) .ne

/-- Enrichment of negation is negation of enrichment, conjoined with NE -/
theorem enrich_neg_structure (φ : BSMLFormula) :
    enrich (.neg φ) = .conj (.neg (enrich φ)) .ne := rfl

/-- Enrichment of conjunction is conjunction of enrichments (no extra NE) -/
theorem enrich_conj_structure (φ ψ : BSMLFormula) :
    enrich (.conj φ ψ) = .conj (enrich φ) (enrich ψ) := rfl

/-- Enrichment of disjunction is disjunction of enrichments (no extra NE) -/
theorem enrich_disj_structure (φ ψ : BSMLFormula) :
    enrich (.disj φ ψ) = .disj (enrich φ) (enrich ψ) := rfl

/-- Enrichment of possibility is possibility of enrichment, conjoined with NE -/
theorem enrich_poss_structure (φ : BSMLFormula) :
    enrich (.poss φ) = .conj (.poss (enrich φ)) .ne := rfl

-- ============================================================================
-- Section 3: Enriched Support Implies Non-emptiness
-- ============================================================================

/-- Elements of an allSubsets sublist are in the original list -/
private lemma mem_of_mem_allSubsets {α : Type*} (l sub : List α)
    (hsub : sub ∈ allSubsets l) : ∀ x ∈ sub, x ∈ l := by
  induction l generalizing sub with
  | nil => simp [allSubsets] at hsub; subst hsub; simp
  | cons a as ih =>
    simp only [allSubsets, List.mem_append] at hsub
    intro x hx
    cases hsub with
    | inl h => exact List.mem_cons.mpr (Or.inr (ih _ h x hx))
    | inr h =>
      obtain ⟨sub', hmem, rfl⟩ := List.mem_map.mp h
      cases hx with
      | head => exact List.mem_cons.mpr (Or.inl rfl)
      | tail _ hx => exact List.mem_cons.mpr (Or.inr (ih _ hmem x hx))

/-- Members of a split's left part are in the original team -/
private lemma split_left_mem {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (v : W) (ht1v : t1 v = true) : t v = true := by
  simp only [generateSplits, List.mem_map] at hmem
  obtain ⟨left, hleft, heq⟩ := hmem
  have ht1_eq : t1 = Team.ofList left := (Prod.ext_iff.mp heq).1.symm
  rw [ht1_eq] at ht1v
  simp only [Team.ofList] at ht1v
  have hv_in_left : v ∈ left := List.mem_of_elem_eq_true ht1v
  have hv_in_toList := mem_of_mem_allSubsets _ _ hleft v hv_in_left
  simp only [Team.toList, List.mem_filter] at hv_in_toList
  exact hv_in_toList.2

/-- Members of a split's right part are in the original team -/
private lemma split_right_mem {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (v : W) (ht2v : t2 v = true) : t v = true := by
  simp only [generateSplits, List.mem_map] at hmem
  obtain ⟨left, _, heq⟩ := hmem
  have ht2_eq : t2 = (λ w => t w && !(Team.ofList left w)) := (Prod.ext_iff.mp heq).2.symm
  rw [ht2_eq] at ht2v
  simp only [Bool.and_eq_true] at ht2v; exact ht2v.1

/-- If a split part is non-empty, the original team is non-empty -/
private lemma split_nonempty {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (hne : t1.isNonEmpty worlds = true) : t.isNonEmpty worlds = true := by
  simp only [Team.isNonEmpty, List.any_eq_true] at hne ⊢
  obtain ⟨v, hv, ht1v⟩ := hne
  exact ⟨v, hv, split_left_mem t t1 t2 worlds hmem v ht1v⟩

/-- If an enriched formula (other than NE) is supported, the team is non-empty.

    For atoms, negation, and modals this follows from the top-level NE conjunct.
    For conjunction and disjunction (which lack top-level NE in Definition 6),
    non-emptiness is inherited from the enriched sub-formulas. -/
theorem enriched_support_implies_nonempty {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W)
    (h : support M (enrich φ) t = true) :
    t.isNonEmpty M.worlds = true := by
  induction φ generalizing t with
  | ne => exact h
  | atom p =>
      simp only [enrich, support] at h
      cases hA : (t.all (M.valuation p) M.worlds) <;> cases hB : t.isNonEmpty M.worlds <;> simp_all
  | neg ψ _ =>
      simp only [enrich, support] at h
      cases hA : (antiSupport M (enrich ψ) t) <;> cases hB : t.isNonEmpty M.worlds <;> simp_all
  | conj ψ₁ ψ₂ ih₁ _ =>
      unfold enrich at h
      unfold support at h
      apply ih₁
      revert h; cases support M (enrich ψ₁) t <;> simp
  | disj ψ₁ ψ₂ ih₁ _ =>
      unfold enrich at h; unfold support at h
      obtain ⟨⟨t1, t2⟩, hmem, hsupp⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true] at hsupp
      exact split_nonempty t t1 t2 M.worlds hmem (ih₁ t1 hsupp.1)
  | poss ψ _ =>
      simp only [enrich, support] at h
      cases hB : t.isNonEmpty M.worlds <;> simp_all
  | nec ψ _ =>
      simp only [enrich, support] at h
      cases hB : t.isNonEmpty M.worlds <;> simp_all

-- ============================================================================
-- Section 4: Core Split Lemma
-- ============================================================================

/-- If disjunction is supported, there exists a split where both parts support their disjuncts -/
theorem split_exists {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W)
    (h : support M (.disj φ ψ) t = true) :
    ∃ t₁ t₂ : Team W, support M φ t₁ = true ∧ support M ψ t₂ = true := by
  simp only [support] at h
  have := List.any_eq_true.mp h
  obtain ⟨⟨t1, t2⟩, _, hSupp⟩ := this
  have h1 : support M φ t1 = true := by
    cases hA : support M φ t1 <;> simp_all
  have h2 : support M ψ t2 = true := by
    cases hA : support M ψ t2 <;> simp_all
  exact ⟨t1, t2, h1, h2⟩

/-- THE CORE LEMMA: Enriched disjunction forces both parts of split to be non-empty.

This is the derivation of free choice from first principles:
- Split disjunction partitions the team
- Enrichment adds NE to each disjunct
- NE being non-flat means each part must be genuinely non-empty
- Therefore both alternatives are "live" (FC!)
-/
theorem enriched_split_forces_both_nonempty {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W)
    (h : support M (enrich (.disj φ ψ)) t = true) :
    ∃ t₁ t₂ : Team W,
      t₁.isNonEmpty M.worlds = true ∧
      t₂.isNonEmpty M.worlds = true ∧
      support M (enrich φ) t₁ = true ∧
      support M (enrich ψ) t₂ = true := by
  simp only [enrich, support] at h
  have hSplit := List.any_eq_true.mp h
  obtain ⟨⟨t1, t2⟩, _, hBoth⟩ := hSplit
  have hPhi : support M (enrich φ) t1 = true := by
    cases hA : support M (enrich φ) t1 <;> simp_all
  have hPsi : support M (enrich ψ) t2 = true := by
    cases hA : support M (enrich ψ) t2 <;> simp_all
  have hT1NE := enriched_support_implies_nonempty M φ t1 hPhi
  have hT2NE := enriched_support_implies_nonempty M ψ t2 hPsi
  exact ⟨t1, t2, hT1NE, hT2NE, hPhi, hPsi⟩

-- ============================================================================
-- Section 5: Structural Asymmetry (Support vs Anti-Support)
-- ============================================================================

/-- Anti-support of disjunction is conjunction of anti-supports (no split!) -/
theorem antiSupport_disj_is_conj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W) :
    antiSupport M (.disj φ ψ) t =
    (antiSupport M φ t && antiSupport M ψ t) := by
  simp only [antiSupport]

/-- The asymmetry: disjunction support uses existential (split), anti-support uses universal (conj) -/
theorem support_antiSupport_asymmetry {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W) :
    -- Support: existential over splits
    (support M (.disj φ ψ) t = true ↔
      (generateSplits t M.worlds).any (λ (t1, t2) =>
        support M φ t1 && support M ψ t2) = true) ∧
    -- Anti-support: universal (conjunction)
    (antiSupport M (.disj φ ψ) t = true ↔
      antiSupport M φ t = true ∧ antiSupport M ψ t = true) := by
  constructor
  · simp only [support]
  · simp only [antiSupport, Bool.and_eq_true]

-- ============================================================================
-- Section 6: Infrastructure Lemmas
-- ============================================================================

/-- Monotonicity for List.all: if f implies g pointwise, then all f implies all g -/
private lemma list_all_mono {α : Type*} (l : List α) (f g : α → Bool)
    (hfg : ∀ x, f x = true → g x = true) (hf : l.all f = true) : l.all g = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at *
    exact ⟨hfg x hf.1, ih hf.2⟩

/-- Monotonicity for Team.all -/
private lemma team_all_mono {W : Type*} (t : Team W) (f g : W → Bool) (worlds : List W)
    (hfg : ∀ w, f w = true → g w = true)
    (hf : t.all f worlds = true) : t.all g worlds = true := by
  unfold Team.all at *
  exact list_all_mono worlds _ _ (fun w hw => by
    cases ht : t w <;> simp_all) hf

/-- Empty team satisfies Team.all for any predicate (vacuous truth) -/
private lemma team_all_of_isEmpty {W : Type*} (t : Team W) (p : W → Bool) (worlds : List W)
    (he : t.isEmpty worlds = true) : t.all p worlds = true := by
  unfold Team.all Team.isEmpty at *
  simp only [Bool.not_eq_true'] at he
  induction worlds with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.any_cons, List.all_cons, Bool.or_eq_false_iff, Bool.and_eq_true] at *
    exact ⟨by simp [he.1], ih he.2⟩

/-- Anti-support of enriched atom disjunction implies anti-support of left atom -/
private lemma antiSupport_enriched_disj_implies_left {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (t' : Team W)
    (h : antiSupport M (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) t' = true) :
    antiSupport M (.atom a) t' = true := by
  unfold antiSupport at h
  have h1 : antiSupport M (.conj (.atom a) .ne) t' = true := by
    revert h; cases antiSupport M (.conj (.atom a) .ne) t' <;> simp
  unfold antiSupport at h1
  cases hA : antiSupport M (.atom a) t'
  · exfalso
    rw [hA, Bool.false_or] at h1
    unfold antiSupport at h1 hA
    have := team_all_of_isEmpty t' (fun w => !M.valuation a w) M.worlds h1
    rw [this] at hA
    simp at hA
  · rfl

/-- Anti-support of enriched atom disjunction implies anti-support of right atom -/
private lemma antiSupport_enriched_disj_implies_right {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (t' : Team W)
    (h : antiSupport M (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) t' = true) :
    antiSupport M (.atom b) t' = true := by
  unfold antiSupport at h
  have h1 : antiSupport M (.conj (.atom b) .ne) t' = true := by
    revert h; cases antiSupport M (.conj (.atom b) .ne) t' <;> simp_all
  unfold antiSupport at h1
  cases hB : antiSupport M (.atom b) t'
  · exfalso
    rw [hB, Bool.false_or] at h1
    unfold antiSupport at h1 hB
    have := team_all_of_isEmpty t' (fun w => !M.valuation b w) M.worlds h1
    rw [this] at hB
    simp at hB
  · rfl

/-- Anti-support monotonicity for ◇ -/
private lemma antiSupport_poss_weaken {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (φ ψ : BSMLFormula) (t : Team W)
    (hmono : ∀ t' : Team W, antiSupport M φ t' = true → antiSupport M ψ t' = true)
    (h : antiSupport M (.poss φ) t = true) :
    antiSupport M (.poss ψ) t = true := by
  unfold antiSupport at h ⊢
  exact team_all_mono t _ _ M.worlds (fun w hw => by
    exact list_all_mono (generateSubteams (M.access w) M.worlds) _ _ (fun t' ht' => by
      cases he : t'.isEmpty M.worlds
      · simp only [he, Bool.false_or] at ht' ⊢
        exact hmono t' ht'
      · simp
    ) hw
  ) h

/-- The empty list is always in allSubsets -/
private lemma nil_mem_allSubsets {α : Type*} (l : List α) : [] ∈ allSubsets l := by
  induction l with
  | nil => simp [allSubsets]
  | cons _ as ih => simp only [allSubsets, List.mem_append]; left; exact ih

/-- A singleton is in allSubsets when the element is in the list -/
private lemma singleton_mem_allSubsets {α : Type*} [DecidableEq α] (l : List α) (x : α)
    (hx : x ∈ l) : [x] ∈ allSubsets l := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [allSubsets, List.mem_append]
    cases hx with
    | head => right; exact List.mem_map.mpr ⟨[], nil_mem_allSubsets as, rfl⟩
    | tail _ hx => left; exact ih hx

/-- Members of a subteam are in the original team -/
private lemma subteam_mem {W : Type*} [DecidableEq W]
    (t s : Team W) (worlds : List W)
    (hs : s ∈ generateSubteams t worlds)
    (v : W) (hsv : s v = true) : t v = true := by
  simp only [generateSubteams, List.mem_map] at hs
  obtain ⟨sub, hsub, rfl⟩ := hs
  simp only [Team.ofList] at hsv
  have hv_in_sub : v ∈ sub := List.mem_of_elem_eq_true hsv
  have hv_in_toList := mem_of_mem_allSubsets _ _ hsub v hv_in_sub
  simp only [Team.toList, List.mem_filter] at hv_in_toList
  exact hv_in_toList.2

/-- A singleton team for v is in generateSubteams when v is in the team -/
private lemma singleton_in_generateSubteams {W : Type*} [DecidableEq W]
    (t : Team W) (worlds : List W) (v : W)
    (hv : v ∈ worlds) (htv : t v = true) :
    Team.ofList [v] ∈ generateSubteams t worlds := by
  simp only [generateSubteams, List.mem_map]
  exact ⟨[v], singleton_mem_allSubsets _ v
    (by simp [Team.toList, List.mem_filter, hv, htv]), rfl⟩

/-- Singleton team is non-empty -/
private lemma singleton_isNonEmpty {W : Type*} [DecidableEq W]
    (v : W) (worlds : List W) (hv : v ∈ worlds) :
    (Team.ofList [v]).isNonEmpty worlds = true := by
  simp only [Team.isNonEmpty, List.any_eq_true]
  exact ⟨v, hv, by simp [Team.ofList]⟩

/-- Singleton team supports an atom when the valuation holds at that world -/
private lemma singleton_support_atom {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (v : W)
    (hv : v ∈ M.worlds) (hval : M.valuation p v = true) :
    support M (.atom p) (Team.ofList [v]) = true := by
  unfold support Team.all
  apply List.all_eq_true.mpr
  intro w hw
  cases hm : Team.ofList [v] w
  · simp
  · simp only [Bool.not_true, Bool.false_or]
    simp only [Team.ofList] at hm
    have hv_eq := List.mem_of_elem_eq_true hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_eq
    subst hv_eq; exact hval

/-- If v is accessible from w and satisfies atom p, the ◇p subteams.any condition holds -/
private lemma poss_atom_witness {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (w v : W)
    (hv : v ∈ M.worlds) (hacc : M.access w v = true) (hval : M.valuation p v = true) :
    (generateSubteams (M.access w) M.worlds).any
      (λ t' => t'.isNonEmpty M.worlds && support M (.atom p) t') = true := by
  apply List.any_eq_true.mpr
  refine ⟨Team.ofList [v],
    singleton_in_generateSubteams (M.access w) M.worlds v hv hacc, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨singleton_isNonEmpty v M.worlds hv, singleton_support_atom M p v hv hval⟩

/-- From s ⊨ (atom p) ∧ NE, extract a world witness with membership and valuation -/
private lemma atom_witness_of_enriched_conj {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (s : Team W)
    (h : support M (.conj (.atom p) .ne) s = true) :
    ∃ v ∈ M.worlds, s v = true ∧ M.valuation p v = true := by
  unfold support at h
  simp only [Bool.and_eq_true] at h
  have hs := h.1; have hne_raw := h.2
  unfold support at hne_raw
  simp only [Team.isNonEmpty, List.any_eq_true] at hne_raw
  obtain ⟨v, hv, hsv⟩ := hne_raw
  refine ⟨v, hv, hsv, ?_⟩
  unfold support Team.all at hs
  simp only [List.all_eq_true] at hs
  have := hs v hv
  simp only [hsv, Bool.not_true, Bool.false_or] at this
  exact this

/-- From s ⊨ (a ∧ NE) ∨ (b ∧ NE), extract witnesses for both atoms in s -/
private lemma both_witnesses_of_enriched_disj {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (s : Team W)
    (h : support M (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true) :
    (∃ va ∈ M.worlds, s va = true ∧ M.valuation a va = true) ∧
    (∃ vb ∈ M.worlds, s vb = true ∧ M.valuation b vb = true) := by
  unfold support at h
  obtain ⟨⟨s1, s2⟩, hsplit, hboth⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hboth
  obtain ⟨va, hva_w, hva_s1, hva_val⟩ := atom_witness_of_enriched_conj M a s1 hboth.1
  obtain ⟨vb, hvb_w, hvb_s2, hvb_val⟩ := atom_witness_of_enriched_conj M b s2 hboth.2
  exact ⟨⟨va, hva_w, split_left_mem s s1 s2 M.worlds hsplit va hva_s1, hva_val⟩,
         ⟨vb, hvb_w, split_right_mem s s1 s2 M.worlds hsplit vb hvb_s2, hvb_val⟩⟩

/-- Team.beq gives pointwise equality -/
private lemma team_beq_apply {W : Type*} (t1 t2 : Team W) (worlds : List W) (w : W)
    (hbeq : t1.beq t2 worlds = true) (hw : w ∈ worlds) : t1 w = t2 w := by
  unfold Team.beq at hbeq
  simp only [List.all_eq_true] at hbeq
  exact beq_iff_eq.mp (hbeq w hw)

/-- Indisputability transfers accessibility -/
private lemma indisputable_access_transfer {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (t : Team W) (w₁ w₂ v : W)
    (hInd : M.isIndisputable t = true)
    (hw₁ : w₁ ∈ M.worlds) (htw₁ : t w₁ = true)
    (hw₂ : w₂ ∈ M.worlds) (htw₂ : t w₂ = true)
    (hv : v ∈ M.worlds)
    (hacc : M.access w₁ v = true) :
    M.access w₂ v = true := by
  unfold BSMLModel.isIndisputable at hInd
  have hw₁_mem : w₁ ∈ t.toList M.worlds := by
    simp [Team.toList, List.mem_filter, hw₁, htw₁]
  have hw₂_mem : w₂ ∈ t.toList M.worlds := by
    simp [Team.toList, List.mem_filter, hw₂, htw₂]
  cases hmem : t.toList M.worlds with
  | nil => rw [hmem] at hw₁_mem; simp at hw₁_mem
  | cons w rest =>
    rw [hmem] at hw₁_mem hw₂_mem hInd
    simp only [List.all_eq_true] at hInd
    have hbeq₁ : (M.access w).beq (M.access w₁) M.worlds = true := by
      cases hw₁_mem with
      | head =>
        unfold Team.beq; simp only [List.all_eq_true]; intro w' _; exact beq_self_eq_true _
      | tail _ h => exact hInd w₁ h
    have hbeq₂ : (M.access w).beq (M.access w₂) M.worlds = true := by
      cases hw₂_mem with
      | head =>
        unfold Team.beq; simp only [List.all_eq_true]; intro w' _; exact beq_self_eq_true _
      | tail _ h => exact hInd w₂ h
    rw [← team_beq_apply _ _ M.worlds v hbeq₂ hv,
        team_beq_apply _ _ M.worlds v hbeq₁ hv]
    exact hacc

-- ============================================================================
-- Section 7: Free Choice Theorems
-- ============================================================================

/-!
## Why FC Requires Atomic Formulas

The FC theorems below are restricted to atomic α and β. The general version
(for arbitrary BSMLFormula) is FALSE: enrichment [φ]⁺ does not entail φ
for formulas containing □ under negation, because the NE added by enrichment
creates "escape hatches" via empty accessibility sets.
-/

/-- Counterexample worlds -/
private inductive CexWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr

/-- Counterexample model: w0 accesses {w1, w2}; w1, w2, w3 have empty accessibility -/
private def cexModel : BSMLModel CexWorld where
  worlds := [.w0, .w1, .w2, .w3]
  access := λ w => match w with
    | .w0 => λ w' => w' == .w1 || w' == .w2
    | _ => λ _ => false
  valuation := λ p w => match p with
    | "p" => w == .w1 || w == .w2
    | _ => false

/-- The general narrowScopeFC is false for formulas with □ under negation -/
theorem narrowScopeFC_false_for_general_formulas :
    support cexModel
      (enrich (.poss (.disj (.neg (.nec (.nec (.atom "q")))) (.atom "p"))))
      (λ w => w == .w0) = true ∧
    support cexModel
      (.poss (.neg (.nec (.nec (.atom "q")))))
      (λ w => w == .w0) = false := by native_decide

/--
Narrow-scope Free Choice: [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (for atomic α, β)

Restricted to atoms because [φ]⁺ |= φ fails for general formulas.
-/
theorem narrowScopeFC {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W)
    (h : support M (enrich (.poss (.disj (.atom a) (.atom b)))) t = true) :
    support M (.poss (.atom a)) t = true ∧
    support M (.poss (.atom b)) t = true := by
  simp only [enrich] at h
  unfold support at h
  have hPoss : support M
    (.poss (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne))) t = true := by
    revert h; cases support M _ t <;> simp
  unfold support at hPoss ⊢
  unfold Team.all at hPoss ⊢
  constructor
  · apply List.all_eq_true.mpr
    intro w hw
    have hfw := (List.all_eq_true.mp hPoss) w hw
    cases ht : t w
    · simp
    · simp only [ht, Bool.not_true, Bool.false_or] at hfw ⊢
      obtain ⟨s, hs_mem, hs_supp⟩ := List.any_eq_true.mp hfw
      have hsupp : support M
          (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true := by
        revert hs_supp; cases support M _ s <;> simp_all
      obtain ⟨⟨va, hva_w, hva_s, hva_val⟩, _⟩ :=
        both_witnesses_of_enriched_disj M a b s hsupp
      have hva_acc := subteam_mem (M.access w) s M.worlds hs_mem va hva_s
      exact poss_atom_witness M a w va hva_w hva_acc hva_val
  · apply List.all_eq_true.mpr
    intro w hw
    have hfw := (List.all_eq_true.mp hPoss) w hw
    cases ht : t w
    · simp
    · simp only [ht, Bool.not_true, Bool.false_or] at hfw ⊢
      obtain ⟨s, hs_mem, hs_supp⟩ := List.any_eq_true.mp hfw
      have hsupp : support M
          (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true := by
        revert hs_supp; cases support M _ s <;> simp_all
      obtain ⟨_, ⟨vb, hvb_w, hvb_s, hvb_val⟩⟩ :=
        both_witnesses_of_enriched_disj M a b s hsupp
      have hvb_acc := subteam_mem (M.access w) s M.worlds hs_mem vb hvb_s
      exact poss_atom_witness M b w vb hvb_w hvb_acc hvb_val

/--
Wide-scope Free Choice: [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (for atomic α, β with indisputable R)

Indisputability (R[w] = R[v] for all w, v ∈ t) allows extending
the ◇ witness from one part of the split to all of t.
-/
theorem wideScopeFC {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W)
    (hInd : M.isIndisputable t = true)
    (h : support M (enrich (.disj (.poss (.atom a)) (.poss (.atom b)))) t = true) :
    support M (.poss (.atom a)) t = true ∧
    support M (.poss (.atom b)) t = true := by
  simp only [enrich] at h
  -- Extract the split: t₁ ⊨ ◇(a ∧ NE) ∧ NE, t₂ ⊨ ◇(b ∧ NE) ∧ NE
  unfold support at h
  obtain ⟨⟨t1, t2⟩, hsplit, hboth⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hboth
  obtain ⟨ht1_full, ht2_full⟩ := hboth
  unfold support at ht1_full ht2_full
  simp only [Bool.and_eq_true] at ht1_full ht2_full
  obtain ⟨ht1_poss, ht1_ne_raw⟩ := ht1_full
  obtain ⟨ht2_poss, ht2_ne_raw⟩ := ht2_full
  unfold support at ht1_ne_raw ht2_ne_raw
  -- Pick w₁ ∈ t₁, w₂ ∈ t₂ (from non-emptiness)
  simp only [Team.isNonEmpty, List.any_eq_true] at ht1_ne_raw ht2_ne_raw
  obtain ⟨w₁, hw₁_w, htw₁⟩ := ht1_ne_raw
  obtain ⟨w₂, hw₂_w, htw₂⟩ := ht2_ne_raw
  have htw₁_t : t w₁ = true := split_left_mem t t1 t2 M.worlds hsplit w₁ htw₁
  have htw₂_t : t w₂ = true := split_right_mem t t1 t2 M.worlds hsplit w₂ htw₂
  -- From ◇(a ∧ NE) at w₁: extract accessible va with M.valuation a va
  unfold support Team.all at ht1_poss
  have hw₁_entry := (List.all_eq_true.mp ht1_poss) w₁ hw₁_w
  simp only [htw₁, Bool.not_true, Bool.false_or] at hw₁_entry
  obtain ⟨s_a, hs_a_mem, hs_a_supp⟩ := List.any_eq_true.mp hw₁_entry
  have hs_a_support : support M (.conj (.atom a) .ne) s_a = true := by
    revert hs_a_supp; cases support M _ s_a <;> simp_all
  obtain ⟨va, hva_w, hva_sa, hva_val⟩ := atom_witness_of_enriched_conj M a s_a hs_a_support
  have hva_acc_w₁ : M.access w₁ va = true :=
    subteam_mem (M.access w₁) s_a M.worlds hs_a_mem va hva_sa
  -- From ◇(b ∧ NE) at w₂: extract accessible vb with M.valuation b vb
  unfold support Team.all at ht2_poss
  have hw₂_entry := (List.all_eq_true.mp ht2_poss) w₂ hw₂_w
  simp only [htw₂, Bool.not_true, Bool.false_or] at hw₂_entry
  obtain ⟨s_b, hs_b_mem, hs_b_supp⟩ := List.any_eq_true.mp hw₂_entry
  have hs_b_support : support M (.conj (.atom b) .ne) s_b = true := by
    revert hs_b_supp; cases support M _ s_b <;> simp_all
  obtain ⟨vb, hvb_w, hvb_sb, hvb_val⟩ := atom_witness_of_enriched_conj M b s_b hs_b_support
  have hvb_acc_w₂ : M.access w₂ vb = true :=
    subteam_mem (M.access w₂) s_b M.worlds hs_b_mem vb hvb_sb
  -- Prove both ◇a and ◇b for all of t using indisputability
  unfold support
  unfold Team.all
  constructor
  · apply List.all_eq_true.mpr
    intro w hw
    cases htw : t w
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      exact poss_atom_witness M a w va hva_w
        (indisputable_access_transfer M t w₁ w va hInd hw₁_w htw₁_t hw htw hva_w hva_acc_w₁)
        hva_val
  · apply List.all_eq_true.mpr
    intro w hw
    cases htw : t w
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      exact poss_atom_witness M b w vb hvb_w
        (indisputable_access_transfer M t w₂ w vb hInd hw₂_w htw₂_t hw htw hvb_w hvb_acc_w₂)
        hvb_val

/--
Dual Prohibition: [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β (for atomic α, β)

This uses anti-support, which is conjunction for disjunction (no split!).
-/
theorem dualProhibition {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W)
    (h : support M (enrich (.neg (.poss (.disj (.atom a) (.atom b))))) t = true) :
    support M (.neg (.poss (.atom a))) t = true ∧
    support M (.neg (.poss (.atom b))) t = true := by
  simp only [enrich] at h
  unfold support at h
  have hNeg : support M
    ((((BSMLFormula.atom a).conj BSMLFormula.ne).disj
      ((BSMLFormula.atom b).conj BSMLFormula.ne)).poss.conj BSMLFormula.ne).neg t = true := by
    revert h; cases support M _ t <;> simp
  have hNE : support M BSMLFormula.ne t = true := by
    revert h; cases support M BSMLFormula.ne t <;> simp_all
  unfold support at hNeg
  unfold antiSupport at hNeg
  unfold support at hNE
  have hNotEmpty : antiSupport M BSMLFormula.ne t = false := by
    unfold antiSupport
    simp only [Team.isEmpty, Team.isNonEmpty] at *
    simp [hNE]
  rw [hNotEmpty, Bool.or_false] at hNeg
  unfold support
  constructor
  · exact antiSupport_poss_weaken M _ _ t
      (fun t' => antiSupport_enriched_disj_implies_left M a b t') hNeg
  · exact antiSupport_poss_weaken M _ _ t
      (fun t' => antiSupport_enriched_disj_implies_right M a b t') hNeg

-- ============================================================================
-- Section 8: Unfolding Lemmas
-- ============================================================================

/-- Support of negation is anti-support of formula -/
lemma support_neg {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) :
    support M (.neg φ) t = antiSupport M φ t := by
  simp only [support]

/-- Anti-support of negation is support of formula -/
lemma antiSupport_neg {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Team W) :
    antiSupport M (.neg φ) t = support M φ t := by
  simp only [antiSupport]

/-- Anti-support of disjunction is conjunction of anti-supports -/
lemma antiSupport_disj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W) :
    antiSupport M (.disj φ ψ) t =
    (antiSupport M φ t && antiSupport M ψ t) := by
  simp only [antiSupport]

/-- Support of conjunction requires both conjuncts supported -/
lemma support_conj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Team W) :
    support M (.conj φ ψ) t =
    (support M φ t && support M ψ t) := by
  simp only [support]

/-- Empty team supports all atoms (ex falso / vacuous truth) -/
lemma empty_supports_atom {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (p : String) :
    support M (.atom p) Team.empty = true := by
  simp only [support, Team.all, Team.empty]
  induction M.worlds with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.all_cons, Bool.not_false, Bool.true_or, Bool.true_and]
      exact ih

end Semantics.Dynamic.BSML
