import Linglib.Core.Logic.Quantification.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

/-!
# Counting generalized quantifiers
[barwise-cooper-1981] [keenan-stavi-1986] [peters-westerstahl-2006]
[mostowski-1957]

`[Fintype α]`-gated specializations: counting quantifiers (`most_sem`,
`few_sem`, `half_sem`, the `at_*_n_sem` family, the exceptive
`all_but_n_sem`, `between_n_m_sem`, and the non-conservative counterexample
`m_sem`), plus the cardinality-based `Quantity` and `Proportional` predicates
and the bridge to model-agnostic `QuantityInvariant`.

## Main declarations

* `count` — `(Finset.univ.filter P).card` over a `Fintype` carrier.
* Counting GQs (`most_sem`, `few_sem`, `half_sem`, `both_sem`, `neither_sem`,
  `at_least_n_sem`, `at_most_n_sem`, `exactly_n_sem`, `all_but_n_sem`,
  `between_n_m_sem`, `m_sem`).
* `Quantity` — cardinality-based isomorphism closure.
* `Proportional` — truth-value depends only on the ratio |A∩B|/|A\B|.
-/

namespace Core.Quantification

/-- Count of elements satisfying a predicate, via `Finset.univ.filter`. -/
def count {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] : Nat :=
  (Finset.univ.filter P).card

open Classical

variable {α : Type*} [Fintype α]

/-! ### Counting denotations -/

open Classical in
/-- ⟦most⟧(R)(S) = |R ∩ S| > |R \ S|. -/
noncomputable def most_sem : GQ α := fun R S =>
  count (fun x : α => R x ∧ S x) > count (fun x : α => R x ∧ ¬ S x)

open Classical in
/-- ⟦few⟧(R)(S) = |R ∩ S| < |R \ S|. Dual of `most_sem`. -/
noncomputable def few_sem : GQ α := fun R S =>
  count (fun x : α => R x ∧ S x) < count (fun x : α => R x ∧ ¬ S x)

open Classical in
/-- ⟦half⟧(R)(S) = 2 * |R ∩ S| = |R|. -/
noncomputable def half_sem : GQ α := fun R S =>
  2 * count (fun x : α => R x ∧ S x) = count (fun x : α => R x)

open Classical in
/-- ⟦both⟧(R)(S) = ⟦every⟧(R)(S) ∧ |R| ≥ 2. K&S §2.3. -/
noncomputable def both_sem : GQ α := fun R S =>
  every_sem R S ∧ (Finset.univ.filter (fun x : α => R x)).card ≥ 2

open Classical in
/-- ⟦neither⟧ = gqMeet ⟦no⟧ (|R| ≥ 2). K&S (83b). -/
noncomputable def neither_sem : GQ α :=
  gqMeet no_sem
    (fun (R : α → Prop) _ => (Finset.univ.filter (fun x : α => R x)).card ≥ 2)

open Classical in
/-- ⟦at least n⟧(R)(S) = |R ∩ S| ≥ n. -/
noncomputable def at_least_n_sem (n : Nat) : GQ α := fun R S =>
  count (fun x : α => R x ∧ S x) ≥ n

open Classical in
/-- ⟦at most n⟧(R)(S) = |R ∩ S| ≤ n. -/
noncomputable def at_most_n_sem (n : Nat) : GQ α := fun R S =>
  count (fun x : α => R x ∧ S x) ≤ n

open Classical in
/-- ⟦exactly n⟧(R)(S) = |R ∩ S| = n. -/
noncomputable def exactly_n_sem (n : Nat) : GQ α := fun R S =>
  count (fun x : α => R x ∧ S x) = n

open Classical in
/-- ⟦all but n⟧(R)(S) = |R \ S| = n. The exceptive counterpart of
    `exactly_n_sem`; generalizes "every" (= all but 0). -/
noncomputable def all_but_n_sem (n : Nat) : GQ α := fun R S =>
  count (fun x : α => R x ∧ ¬ S x) = n

/-- ⟦between n and k⟧(R)(S) = n ≤ |R ∩ S| ≤ k. -/
noncomputable def between_n_m_sem (n k : Nat) : GQ α :=
  gqMeet (at_least_n_sem n) (at_most_n_sem k)

open Classical in
/-- A non-conservative quantifier for contrast: ⟦M⟧(A,B) = |A| > |B|
    (van de Pol et al.'s hypothetical counterpart to "most"). -/
noncomputable def m_sem : GQ α := fun R S =>
  count (fun x : α => R x) > count (fun x : α => S x)

/-! ### `count` helpers -/

open Classical in
/-- `count P = count (P ∘ f)` when `f` is a bijection. -/
theorem count_bij_inv (f : α → α) (hBij : Function.Bijective f)
    {P : α → Prop} [DecidablePred P] :
    count P = @count _ _ (P ∘ f) (fun x => ‹DecidablePred P› (f x)) := by
  simp only [count, Function.comp]
  symm; apply Finset.card_bij (fun x _ => f x)
  · intro x hx; simp [Finset.mem_filter] at hx ⊢; exact hx
  · intro x₁ _ x₂ _ h; exact hBij.injective h
  · intro y hy
    simp [Finset.mem_filter] at hy
    obtain ⟨x, rfl⟩ := hBij.surjective y
    exact ⟨x, by simp [Finset.mem_filter, hy], rfl⟩

/-- Equivalent predicates produce equal counts. -/
private theorem count_congr_iff {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : count P = count Q := by
  unfold count; congr 1; ext x
  constructor
  · intro hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, (h x).mp hx.2⟩
  · intro hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, (h x).mpr hx.2⟩

/-- Instance-polymorphic: `count(R∧S) = count(R∧(R∧S))` for any
    `DecidablePred` instances. -/
private theorem count_and_idem_any (R S : α → Prop)
    (inst1 : DecidablePred (fun x : α => R x ∧ S x))
    (inst2 : DecidablePred (fun x : α => R x ∧ (R x ∧ S x))) :
    @count _ _ _ inst1 = @count _ _ _ inst2 := by
  unfold count; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hR, hS⟩ => ⟨hR, hR, hS⟩, fun ⟨hR, _, hS⟩ => ⟨hR, hS⟩⟩

/-- Instance-polymorphic: `count(R∧¬S) = count(R∧¬(R∧S))` for any
    `DecidablePred` instances. -/
private theorem count_neg_idem_any (R S : α → Prop)
    (inst1 : DecidablePred (fun x : α => R x ∧ ¬ S x))
    (inst2 : DecidablePred (fun x : α => R x ∧ ¬ (R x ∧ S x))) :
    @count _ _ _ inst1 = @count _ _ _ inst2 := by
  unfold count; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hR, hNS⟩ => ⟨hR, fun ⟨_, hS⟩ => hNS hS⟩,
         fun ⟨hR, hN⟩ => ⟨hR, fun hS => hN ⟨hR, hS⟩⟩⟩

/-- If `P` implies `Q` pointwise, then `|filter P| ≤ |filter Q|`. -/
private theorem count_le_of_imp {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) : count P ≤ count Q := by
  apply Finset.card_le_card
  intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h x

/-- |R| = |R∩S| + |R\S|. -/
private theorem count_decompose (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] :
    count (fun x : α => R x) =
      count (fun x : α => R x ∧ S x) +
      count (fun x : α => R x ∧ ¬ S x) := by
  simp only [count]
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact ⟨fun hR => by by_cases hS : S x <;> simp [hR, hS],
           fun h => h.elim And.left And.left⟩
  · simp only [Finset.disjoint_filter]
    intro x _ ⟨_, h1⟩ ⟨_, h2⟩; exact h2 h1

/-! ### Conservativity of counting GQs -/

theorem most_conservative : Conservative (most_sem (α := α)) := by
  intro R S; simp only [most_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _, ← count_neg_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _, count_neg_idem_any R S _ _]; exact h

theorem few_conservative : Conservative (few_sem (α := α)) := by
  intro R S; simp only [few_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _, ← count_neg_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _, count_neg_idem_any R S _ _]; exact h

theorem half_conservative : Conservative (half_sem (α := α)) := by
  intro R S; simp only [half_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

theorem both_conservative : Conservative (both_sem (α := α)) := by
  intro R S; simp only [both_sem]; rw [every_conservative R S]

theorem neither_conservative : Conservative (neither_sem (α := α)) := by
  intro R S; simp only [neither_sem, gqMeet]; rw [no_conservative R S]

theorem at_least_n_conservative (n : Nat) :
    Conservative (at_least_n_sem (α := α) n) := by
  intro R S; simp only [at_least_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

theorem at_most_n_conservative (n : Nat) :
    Conservative (at_most_n_sem (α := α) n) := by
  intro R S; simp only [at_most_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

theorem exactly_n_conservative (n : Nat) :
    Conservative (exactly_n_sem (α := α) n) := by
  intro R S; simp only [exactly_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

theorem all_but_n_conservative (n : Nat) :
    Conservative (all_but_n_sem (α := α) n) := by
  intro R S; simp only [all_but_n_sem]
  constructor <;> intro h
  · rw [← count_neg_idem_any R S _ _]; exact h
  · rw [count_neg_idem_any R S _ _]; exact h

theorem between_n_m_conservative (n k : Nat) :
    Conservative (between_n_m_sem (α := α) n k) := by
  intro R S; simp only [between_n_m_sem, gqMeet]
  exact Iff.and (at_least_n_conservative n R S) (at_most_n_conservative k R S)

/-! ### Counting quantifier identities ([peters-westerstahl-2006] §4.3) -/

/-- `⟦some⟧ = ⟦at least 1⟧`. -/
theorem some_eq_at_least_1 :
    (some_sem (α := α) : GQ α) = (at_least_n_sem (α := α) 1 : GQ α) := by
  funext R S
  simp only [some_sem, at_least_n_sem]
  refine propext ⟨fun ⟨x, hR, hS⟩ => ?_, fun h => ?_⟩
  · simp only [count]
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hR, hS⟩⟩).ne'
  · simp only [count] at h
    have hpos : 0 < (Finset.univ.filter (fun x : α => R x ∧ S x)).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2⟩

/-- `⟦at most n⟧ = outerNeg ⟦at least n+1⟧`. -/
theorem at_most_eq_outerNeg_at_least_succ (n : Nat) :
    (at_most_n_sem (α := α) n : GQ α) =
    (outerNeg (at_least_n_sem (α := α) (n + 1)) : GQ α) := by
  funext R S; simp only [at_most_n_sem, at_least_n_sem, outerNeg]
  exact propext ⟨fun h hGe => by omega, fun h => by omega⟩

/-- `⟦no⟧ = ⟦at most 0⟧`. -/
theorem no_eq_at_most_0 :
    (no_sem (α := α) : GQ α) = (at_most_n_sem (α := α) 0 : GQ α) := by
  rw [← outerNeg_some_eq_no, some_eq_at_least_1, at_most_eq_outerNeg_at_least_succ]

/-- `⟦exactly n⟧ = ⟦at least n⟧ ⊓ ⟦at most n⟧`. -/
theorem exactly_eq_meet_at_least_at_most (n : Nat) :
    (exactly_n_sem (α := α) n : GQ α) =
    (gqMeet (at_least_n_sem (α := α) n) (at_most_n_sem (α := α) n) : GQ α) := by
  funext R S; simp only [exactly_n_sem, at_least_n_sem, at_most_n_sem, gqMeet]
  exact propext ⟨fun h => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => by omega⟩

/-- `⟦all but 0⟧ = ⟦every⟧`. -/
theorem all_but_0_eq_every :
    (all_but_n_sem (α := α) 0 : GQ α) = (every_sem (α := α) : GQ α) := by
  funext R S; simp only [all_but_n_sem, every_sem]
  refine propext ⟨fun h x hR => ?_, fun h => ?_⟩
  · by_contra hS
    have : 0 < count (fun x : α => R x ∧ ¬ S x) :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hR, hS⟩⟩
    omega
  · simp only [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ ⟨hR, hNS⟩; exact hNS (h x hR)

/-! ### Scope monotonicity of counting GQs -/

theorem few_scope_down : ScopeDownwardMono (few_sem (α := α)) := by
  intro R S S' hSS' h
  simp only [few_sem] at *
  have h1 : count (fun x : α => R x ∧ S x) ≤
      count (fun x : α => R x ∧ S' x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : α => R x ∧ ¬ S' x) ≤
      count (fun x : α => R x ∧ ¬ S x) :=
    count_le_of_imp fun x ⟨hR, hNS'⟩ => ⟨hR, fun hS => hNS' (hSS' x hS)⟩
  omega

theorem most_scope_up : ScopeUpwardMono (most_sem (α := α)) := by
  intro R S S' hSS' h
  simp only [most_sem] at *
  have h1 : count (fun x : α => R x ∧ S x) ≤
      count (fun x : α => R x ∧ S' x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : α => R x ∧ ¬ S' x) ≤
      count (fun x : α => R x ∧ ¬ S x) :=
    count_le_of_imp fun x ⟨hR, hNS'⟩ => ⟨hR, fun hS => hNS' (hSS' x hS)⟩
  omega

theorem at_least_n_scope_up (n : Nat) :
    ScopeUpwardMono (at_least_n_sem (α := α) n) := by
  intro R S S' hSS' h
  simp only [at_least_n_sem] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩)

theorem at_most_n_scope_down (n : Nat) :
    ScopeDownwardMono (at_most_n_sem (α := α) n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact outerNeg_up_to_down _ (at_least_n_scope_up _)

/-! ### Smoothness -/

theorem most_downNE : DownNEMon (most_sem (α := α)) := by
  intro R S R' hSub hKeep hQ
  simp only [most_sem] at *
  have hEq : count (fun x : α => R' x ∧ S x) =
      count (fun x : α => R x ∧ S x) := by
    simp only [count]; congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩,
           fun ⟨hR, hS⟩ => ⟨hKeep x hR hS, hS⟩⟩
  have hLe : count (fun x : α => R' x ∧ ¬ S x) ≤
      count (fun x : α => R x ∧ ¬ S x) :=
    count_le_of_imp fun x ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩
  omega

theorem most_upSE : UpSEMon (most_sem (α := α)) := by
  intro R S R' hSub hDiff hQ
  simp only [most_sem] at *
  have hEq : count (fun x : α => R' x ∧ ¬ S x) =
      count (fun x : α => R x ∧ ¬ S x) := by
    simp only [count]; congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hDiff x hR' hS, hS⟩,
           fun ⟨hR, hS⟩ => ⟨hSub x hR, hS⟩⟩
  have hLe : count (fun x : α => R x ∧ S x) ≤
      count (fun x : α => R' x ∧ S x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hSub x hR, hS⟩
  omega

theorem most_smooth : Smooth (most_sem (α := α)) :=
  ⟨most_downNE, most_upSE⟩

theorem at_least_n_restrictor_up (n : Nat) :
    RestrictorUpwardMono (at_least_n_sem (α := α) n) := by
  intro R R' S hRR' h
  simp only [at_least_n_sem] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hRR' x hR, hS⟩)

theorem at_least_n_downNE (n : Nat) :
    DownNEMon (at_least_n_sem (α := α) n) := by
  intro R S R' hSub hKeep hQ
  simp only [at_least_n_sem] at *
  have hEq : count (fun x : α => R' x ∧ S x) =
      count (fun x : α => R x ∧ S x) := by
    simp only [count]; congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩,
           fun ⟨hR, hS⟩ => ⟨hKeep x hR hS, hS⟩⟩
  omega

theorem at_least_n_smooth (n : Nat) :
    Smooth (at_least_n_sem (α := α) n) :=
  ⟨at_least_n_downNE n,
   restrictorUpMono_to_upSE _ (at_least_n_restrictor_up n)⟩

theorem at_most_n_restrictor_down (n : Nat) :
    RestrictorDownwardMono (at_most_n_sem (α := α) n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact outerNeg_restrictorUp_to_down _ (at_least_n_restrictor_up _)

theorem at_most_n_coSmooth (n : Nat) :
    CoSmooth (at_most_n_sem (α := α) n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact (smooth_iff_outerNeg_coSmooth _).mp (at_least_n_smooth _)

/-! ### Quantity / isomorphism closure ([mostowski-1957])

Cardinality-based, `Fintype`-gated. Bridges to the model-agnostic
`QuantityInvariant` (in `Defs.lean`) are sorry'd pending a Prop-predicate
adaptation of the cell-bijection machinery. -/

/-- Quantity / isomorphism closure: `Q(A, B)` depends only on the four
    cardinalities `|A ∩ B|`, `|A \ B|`, `|B \ A|`, `|M \ (A ∪ B)|`.
    Type-⟨1,1⟩ generalization of [mostowski-1957]'s permutation
    invariance for type-⟨1⟩ quantifiers, due to [van-benthem-1984]. -/
def Quantity (q : GQ α) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : α → Prop),
    count (fun x => R₁ x ∧ S₁ x) =
      count (fun x => R₂ x ∧ S₂ x) →
    count (fun x => R₁ x ∧ ¬ S₁ x) =
      count (fun x => R₂ x ∧ ¬ S₂ x) →
    count (fun x => ¬ R₁ x ∧ S₁ x) =
      count (fun x => ¬ R₂ x ∧ S₂ x) →
    count (fun x => ¬ R₁ x ∧ ¬ S₁ x) =
      count (fun x => ¬ R₂ x ∧ ¬ S₂ x) →
    (q R₁ S₁ ↔ q R₂ S₂)

/-- `Quantity → QuantityInvariant`: cardinality-dependence implies
    bijection-invariance.
    TODO: proof requires adapting cell-bijection machinery to Prop predicates. -/
theorem quantityInvariant_of_quantity (q : GQ α) (hQ : Quantity q) :
    QuantityInvariant q := by
  sorry

variable [DecidableEq α]

/-- `QuantityInvariant → Quantity`: bijection-invariance implies
    cardinality-dependence.
    TODO: proof requires adapting cell-bijection machinery to Prop predicates. -/
theorem quantity_of_quantityInvariant (q : GQ α)
    (hQ : QuantityInvariant q) :
    Quantity q := by
  sorry

/-! ### Quantity closure -/

theorem quantity_outerNeg (q : GQ α) (h : Quantity q) :
    Quantity (outerNeg q) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [outerNeg]; exact Iff.not (h R₁ S₁ R₂ S₂ hTT hTF hFT hFF)

theorem quantity_gqMeet (q₁ q₂ : GQ α)
    (h₁ : Quantity q₁) (h₂ : Quantity q₂) :
    Quantity (gqMeet q₁ q₂) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [gqMeet]
  exact Iff.and (h₁ R₁ S₁ R₂ S₂ hTT hTF hFT hFF)
                (h₂ R₁ S₁ R₂ S₂ hTT hTF hFT hFF)

/-! ### Quantity of concrete GQs -/

theorem at_least_n_quantity (n : Nat) :
    Quantity (at_least_n_sem (α := α) n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  simp only [at_least_n_sem]; omega

theorem at_most_n_quantity (n : Nat) :
    Quantity (at_most_n_sem (α := α) n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  simp only [at_most_n_sem]; omega

theorem exactly_n_quantity (n : Nat) :
    Quantity (exactly_n_sem (α := α) n) := by
  rw [exactly_eq_meet_at_least_at_most]
  exact quantity_gqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity n)

theorem some_quantity : Quantity (some_sem (α := α)) := by
  rw [some_eq_at_least_1]; exact at_least_n_quantity 1

theorem no_quantity : Quantity (no_sem (α := α)) := by
  rw [no_eq_at_most_0]; exact at_most_n_quantity 0

/-- `⟦every⟧` satisfies `QuantityInvariant` (proved directly via bijection
    invariance of `∀`). -/
private theorem every_quantityInvariant :
    QuantityInvariant (every_sem (α := α)) := by
  intro A B A' B' f hBij hA hB
  simp only [every_sem]
  rw [forall_bij_inv f hBij]
  exact forall_congr' fun x => by
    rw [show A (f x) ↔ A' x from hA x, show B (f x) ↔ B' x from hB x]

theorem every_quantity : Quantity (every_sem (α := α)) := by
  sorry -- Requires quantity_of_quantityInvariant which itself is sorry'd

theorem most_quantity : Quantity (most_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  simp only [most_sem]; omega

theorem few_quantity : Quantity (few_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  simp only [few_sem]; omega

theorem half_quantity : Quantity (half_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  simp only [half_sem]
  constructor <;> intro h
  · have h₁ := count_decompose R₁ S₁
    have h₂ := count_decompose R₂ S₂
    omega
  · have h₁ := count_decompose R₁ S₁
    have h₂ := count_decompose R₂ S₂
    omega

theorem all_but_n_quantity (n : Nat) :
    Quantity (all_but_n_sem (α := α) n) := by
  intro R₁ S₁ R₂ S₂ _ hTF _ _
  simp only [all_but_n_sem]; omega

theorem between_n_m_quantity (n k : Nat) :
    Quantity (between_n_m_sem (α := α) n k) :=
  quantity_gqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity k)

/-! ### Satisfies universals (counting) -/

theorem most_satisfiesUniversals : SatisfiesUniversals (most_sem (α := α)) :=
  ⟨most_conservative, Or.inl most_scope_up⟩

theorem few_satisfiesUniversals : SatisfiesUniversals (few_sem (α := α)) :=
  ⟨few_conservative, Or.inr few_scope_down⟩

theorem at_least_n_satisfiesUniversals (n : Nat) :
    SatisfiesUniversals (at_least_n_sem (α := α) n) :=
  ⟨at_least_n_conservative n, Or.inl (at_least_n_scope_up n)⟩

theorem at_most_n_satisfiesUniversals (n : Nat) :
    SatisfiesUniversals (at_most_n_sem (α := α) n) :=
  ⟨at_most_n_conservative n, Or.inr (at_most_n_scope_down n)⟩

/-! ### Proportional quantifiers ([peters-westerstahl-2006] §4.3) -/

/-- Proportional: `q`'s truth value depends only on the ratio `|A∩B|/|A\B|`. -/
def Proportional (q : GQ α) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : α → Prop),
    let tt₁ := count (fun x : α => R₁ x ∧ S₁ x)
    let tf₁ := count (fun x : α => R₁ x ∧ ¬ S₁ x)
    let tt₂ := count (fun x : α => R₂ x ∧ S₂ x)
    let tf₂ := count (fun x : α => R₂ x ∧ ¬ S₂ x)
    0 < tt₁ + tf₁ → 0 < tt₂ + tf₂ →
    tt₁ * tf₂ = tt₂ * tf₁ →
    (q R₁ S₁ ↔ q R₂ S₂)

private theorem cross_ratio_preserves_gt (a₁ b₁ a₂ b₂ : Nat)
    (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁)
    (hgt : a₁ > b₁) :
    a₂ > b₂ := by
  by_contra hle
  push Not at hle
  rcases Nat.eq_zero_or_pos b₂ with rfl | hb₂pos
  · omega
  · have h1 : (b₁ + 1) * b₂ ≤ a₁ * b₂ := Nat.mul_le_mul_right b₂ hgt
    have h3 : a₂ * b₁ ≤ b₂ * b₁ := Nat.mul_le_mul_right b₁ hle
    rw [Nat.add_mul] at h1; rw [Nat.mul_comm b₂ b₁] at h3; omega

private theorem cross_ratio_gt_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ > b₁ ↔ a₂ > b₂ :=
  ⟨cross_ratio_preserves_gt a₁ b₁ a₂ b₂ hne₂ hcross,
   cross_ratio_preserves_gt a₂ b₂ a₁ b₁ hne₁ hcross.symm⟩

private theorem cross_ratio_lt_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ < b₁ ↔ a₂ < b₂ := by
  have hcross' : b₁ * a₂ = b₂ * a₁ := by
    rw [Nat.mul_comm b₁ a₂, Nat.mul_comm b₂ a₁]; exact hcross.symm
  exact cross_ratio_gt_iff b₁ a₁ b₂ a₂ (by omega) (by omega) hcross'

private theorem cross_ratio_eq_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ = b₁ ↔ a₂ = b₂ := by
  refine ⟨fun heq => ?_, fun heq => ?_⟩
  · rw [heq] at hcross hne₁
    rw [Nat.mul_comm a₂ b₁] at hcross
    exact (Nat.mul_left_cancel (by omega) hcross).symm
  · rw [heq] at hcross hne₂
    rw [Nat.mul_comm a₁ b₂] at hcross
    exact Nat.mul_left_cancel (by omega) hcross

theorem most_proportional : Proportional (most_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [most_sem]
  exact cross_ratio_gt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

theorem few_proportional : Proportional (few_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [few_sem]
  exact cross_ratio_lt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

private theorem half_prop_core (a₁ b₁ a₂ b₂ : Nat)
    (hNE₁ : 0 < a₁ + b₁) (hNE₂ : 0 < a₂ + b₂)
    (hCross : a₁ * b₂ = a₂ * b₁) :
    (2 * a₁ = a₁ + b₁) ↔ (2 * a₂ = a₂ + b₂) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (cross_ratio_eq_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross).mp (by omega)
    omega
  · have := (cross_ratio_eq_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross).mpr (by omega)
    omega

theorem half_proportional : Proportional (half_sem (α := α)) := by
  intro R₁ S₁ R₂ S₂
  dsimp only []
  intro hNE₁ hNE₂ hCross
  simp only [half_sem]
  rw [count_decompose R₁ S₁, count_decompose R₂ S₂]
  exact half_prop_core _ _ _ _ hNE₁ hNE₂ hCross

end Core.Quantification
