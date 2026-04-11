import Linglib.Theories.Semantics.Comparison.Metalinguistic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

/-!
# Metalinguistic Degrees
@cite{rudolph-kocurek-2024}

Degree-theoretic formulation of metalinguistic gradability (Supplement §C).
The revised semantics (`evalRevised`) induces a degree structure on
sentences: the **metalinguistic degree** of a sentence A (relative to
an index ⟨≤, i, w⟩) is the equivalence class of its denotation set
⟦A⟧_i = {j ≤ i | ⟦A⟧^{j,w} = 1} under a matching relation ∼.

## Key Results

- **∼ is an equivalence relation** (Fact 8): reflexive ✓, symmetric ✓, transitive ✓ (⊆ field)
- **⊐ properties** (Facts 11–12): irreflexive ✓, transitive ✓, total ✓, respects ∼ ✓ (⊆ field)
- **A ≈ B iff deg(A) = deg(B)** (Fact 9) ✓: ME = same metalinguistic degree
- **A ≻ B iff deg(A) ⊐ deg(B)** (Fact 10) ✓: revised MC = degree ordering

This connects the expressivist framework to a proper algebraic structure
backed by Mathlib's `Setoid`, `Quotient`, and order theory. The metalinguistic
degree construction parallels @cite{klein-1980}'s emergent degrees
(see `Hierarchy.lean:nondistinct_iff_equal_measure`), but operates on
*interpretations* rather than *entities*.
-/

namespace Semantics.Comparison.MetalinguisticDegree

open Semantics.Comparison.Metalinguistic


-- ════════════════════════════════════════════════════════════════
-- § 0. Bridge: SemanticOrdering → Mathlib Preorder
-- ════════════════════════════════════════════════════════════════

/-- Convert a `SemanticOrdering` to a Mathlib `Preorder`.

Wraps the Bool-valued `le` as a Prop-valued `≤`, following the
`QUD.toSetoid` pattern. A `def` (not an instance) to avoid global
instance pollution — use `letI := ord.toPreorder` locally. -/
def SemanticOrdering.toPreorder {I : Type} (ord : SemanticOrdering I) :
    Preorder I where
  le i j := ord.le i j = true
  le_refl i := ord.le_refl i
  le_trans i j k hij hjk := ord.le_trans i j k hij hjk

/-- The semantic ordering is total. -/
theorem SemanticOrdering.isTotal {I : Type} (ord : SemanticOrdering I) :
    ∀ (i j : I), ord.le i j = true ∨ ord.le j i = true :=
  ord.le_total


-- ════════════════════════════════════════════════════════════════
-- § 1. Field and Denotation Sets
-- ════════════════════════════════════════════════════════════════

/-- The field I_i: the set of interpretations ranked at or below i. -/
def field {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) : Finset I :=
  Finset.univ.filter (λ j => ord.le j i)

/-- The denotation of a formula: the set of interpretations in I_i
where the formula is true (under the revised semantics). -/
def denotation {I W Pred Entity : Type} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Finset I :=
  (field ord i).filter (λ j => evalRevised interpFn φ ord j w)

/-- The complement of a set relative to the field I_i. -/
def fieldComplement {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) : Finset I :=
  field ord i \ X


-- ════════════════════════════════════════════════════════════════
-- § 2. The ∼ Equivalence Relation (Supplement §C, p. 9)
-- ════════════════════════════════════════════════════════════════

/-- Condition (i) of the ∼ equivalence: every element of X\Y is
matched by an element of Y\X at least as high, and vice versa.

This is the same as the basic ME matching condition applied to
interpretation sets rather than formulas. -/
def equivCond1 {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'' = true) ∧
  (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'' = true)

/-- Condition (ii) of the ∼ equivalence: every element of the
symmetric difference (X ∪ Y) \ (X ∩ Y) is dominated by both
an element of X ∩ Y and an element of X̄ ∩ Ȳ (relative to I_i).

This handles the "Figure 1" situation where A ↔ ¬B always holds
at top-ranked interpretations: if every A-or-B-but-not-both
interpretation is matched by both an A∧B and a ¬A∧¬B interpretation. -/
def equivCond2 {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'' = true) ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'' = true)

/-- Metalinguistic degree equivalence: X ∼_i Y.

Two interpretation sets have the same metalinguistic degree iff
either (i) their symmetric difference elements are pairwise matched
in rank, or (ii) every unmatched element is dominated by both an
element in the overlap and an element outside both sets.

This mirrors the revised ME truth conditions (Supplement §B) applied
to sets rather than formulas. -/
def degreeEquiv {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  equivCond1 ord i X Y ∨ equivCond2 ord i X Y

/-- Bool-valued decidable version of equivCond1. -/
def equivCond1B {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'' = true) &&
  decide (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'' = true)

/-- Bool-valued decidable version of equivCond2. -/
def equivCond2B {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'' = true) ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'' = true))

/-- Bool-valued decidable version of degreeEquiv. -/
def degreeEquivB {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  equivCond1B ord i X Y || equivCond2B ord i X Y


-- ════════════════════════════════════════════════════════════════
-- § 3. Fact 8: ∼ is an Equivalence Relation
-- ════════════════════════════════════════════════════════════════

/-- Fact 8a: ∼ is reflexive.
X \ X = ∅, so all conditions are vacuously satisfied. -/
theorem degreeEquiv_refl {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    degreeEquiv ord i X X := by
  left
  constructor <;> intro i' h <;> simp at h

/-- Fact 8b: ∼ is symmetric.
Both conditions are symmetric in X and Y: condition (i) swaps the
two conjuncts, and condition (ii) is invariant under X ↔ Y since
X ∩ Y = Y ∩ X and X ∪ Y = Y ∪ X. -/
theorem degreeEquiv_symm {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y X := by
  intro h
  rcases h with h1 | h2
  · left; exact ⟨h1.2, h1.1⟩
  · right
    intro i' hi'
    have hi'swap : i' ∈ (X ∪ Y) \ (X ∩ Y) := by
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hi' ⊢
      exact ⟨Or.symm hi'.1, λ ⟨h1, h2⟩ => hi'.2 ⟨h2, h1⟩⟩
    obtain ⟨h2a, h2b⟩ := h2 i' hi'swap
    constructor
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2a
      exact ⟨i'', by rwa [Finset.inter_comm] at hi''mem, hi''le⟩
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2b
      exact ⟨i'', by rwa [Finset.union_comm] at hi''mem, hi''le⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. The ⊐ Ordering on Sets (Supplement §C, p. 10)
-- ════════════════════════════════════════════════════════════════

/-- X ⊐ Y: interpretation set X is strictly better than Y.

Mirrors the revised MC truth conditions (Supplement §B):
∃ i' ∈ I_i such that i' ∈ X \ Y and either
(a) all elements of X ∩ Y are strictly below i', or
(b) all elements of I_i \ (X ∪ Y) are strictly below i',
and in both cases all elements of Y \ X are strictly below i'. -/
def strictlyBetter {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i' = true) ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i' = true) ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i' = true))

/-- Bool-valued decidable version of strictlyBetter. -/
def strictlyBetterB {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i' = true) ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i' = true) ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i' = true)))


-- ════════════════════════════════════════════════════════════════
-- § 5b. Order-Theoretic Helpers
-- ════════════════════════════════════════════════════════════════

/-- Every nonempty Finset has a maximal element under a total preorder. -/
private lemma exists_le_max {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (S : Finset I) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, ord.le s m = true := by
  induction S using Finset.cons_induction with
  | empty => exact absurd hS (by simp)
  | cons x S' hx ih =>
    by_cases hS' : S'.Nonempty
    · obtain ⟨m, hm, hle⟩ := ih hS'
      rcases ord.le_total x m with h | h
      · exact ⟨m, Finset.mem_cons.mpr (Or.inr hm), fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact h
          · exact hle s hs'⟩
      · exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
          rcases Finset.mem_cons.mp hs with rfl | hs'
          · exact ord.le_refl _
          · exact ord.le_trans s m x (hle s hs') h⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'
      exact ⟨x, Finset.mem_cons_self x S', fun s hs => by
        simp [hS'] at hs; exact hs ▸ ord.le_refl _⟩

/-- ¬(a < b) ↔ b ≤ a (by totality). -/
private lemma not_lt_iff_ge {I : Type} (ord : SemanticOrdering I) (a b : I) :
    ord.lt a b = false ↔ ord.le b a = true := by
  constructor
  · intro h
    rcases ord.le_total a b with hab | hba
    · simp [SemanticOrdering.lt, hab] at h; exact h
    · exact hba
  · intro h; simp [SemanticOrdering.lt, h]

/-- a < b → a ≤ b. -/
private lemma le_of_lt' {I : Type} (ord : SemanticOrdering I) (a b : I) :
    ord.lt a b = true → ord.le a b = true := by
  simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true']
  exact fun ⟨h, _⟩ => h

/-- a ≤ b ∧ b < c → a < c. -/
private lemma le_lt_trans' {I : Type} (ord : SemanticOrdering I) (a b c : I) :
    ord.le a b = true → ord.lt b c = true → ord.lt a c = true := by
  simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true']
  intro hab ⟨hbc, hncb⟩
  refine ⟨ord.le_trans a b c hab hbc, ?_⟩
  cases hca : ord.le c a
  · rfl
  · exact absurd (ord.le_trans c a b hca hab) (by simp [hncb])

/-- a < b ∧ b ≤ c → a < c. -/
private lemma lt_le_trans' {I : Type} (ord : SemanticOrdering I) (a b c : I) :
    ord.lt a b = true → ord.le b c = true → ord.lt a c = true := by
  simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true']
  intro ⟨hab, hnba⟩ hbc
  refine ⟨ord.le_trans a b c hab hbc, ?_⟩
  cases hca : ord.le c a
  · rfl
  · exact absurd (ord.le_trans b c a hbc hca) (by simp [hnba])

/-- Bool helper: b ≠ true → b = false. -/
private theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ (b = true)) :
    b = false := by
  cases b <;> simp_all

/-- (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X). -/
private lemma mem_symdiff_iff {I : Type} [DecidableEq I]
    (X Y : Finset I) (s : I) :
    s ∈ (X ∪ Y) \ (X ∩ Y) ↔ s ∈ (X \ Y) ∪ (Y \ X) := by
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hx | hy, hni⟩
    · exact Or.inl ⟨hx, fun hy => hni ⟨hx, hy⟩⟩
    · exact Or.inr ⟨hy, fun hx => hni ⟨hx, hy⟩⟩
  · rintro (⟨hx, hny⟩ | ⟨hy, hnx⟩)
    · exact ⟨Or.inl hx, fun ⟨_, hy⟩ => hny hy⟩
    · exact ⟨Or.inr hy, fun ⟨hx, _⟩ => hnx hx⟩

/-- X ≠ Y → (X \ Y) ∪ (Y \ X) is nonempty. -/
private lemma symdiff_nonempty {I : Type} [DecidableEq I]
    (X Y : Finset I) (h : X ≠ Y) : ((X \ Y) ∪ (Y \ X)).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  apply h; ext x
  constructor
  · intro hx
    by_contra hy
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hy⟩))
    rw [h_empty] at this; simp at this
  · intro hy
    by_contra hx
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hy, hx⟩))
    rw [h_empty] at this; simp at this


-- ════════════════════════════════════════════════════════════════
-- § 6. Facts 11–12: ⊐ on Degrees
-- ════════════════════════════════════════════════════════════════

/-- Fact 12a: ⊐ is irreflexive on sets.
i' ∈ X \ X is impossible, so no witness exists. -/
theorem strictlyBetter_irrefl {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    ¬ strictlyBetter ord i X X := by
  intro ⟨i', hi', _, _, _⟩
  simp at hi'

/-- If X ∼ Y, then ¬(X ⊐ Y).
Under equivCond1, any witness i' ∈ X\Y is matched by i'' ∈ Y\X with
i' ≤ i'', contradicting i'' < i'. Under equivCond2, the witness is
dominated by an X∩Y or field\(X∪Y) element, contradicting the inner
disjunct of ⊐. -/
theorem degreeEquiv_not_strictlyBetter {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I) :
    degreeEquiv ord i X Y → ¬ strictlyBetter ord i X Y := by
  intro h_eq ⟨i', h_sdiff, _, h_ymx, h_inner⟩
  rcases h_eq with ⟨h_match, _⟩ | h2
  · -- equivCond1: i' ∈ X\Y is matched by i'' ∈ Y\X with i' ≤ i''
    obtain ⟨i'', h_i''_sdiff, h_le⟩ := h_match i' h_sdiff
    have h_lt := h_ymx i'' h_i''_sdiff
    simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at h_lt
    simp [h_lt.2] at h_le
  · -- equivCond2: i' ∈ (X ∪ Y) \ (X ∩ Y), dominated by X∩Y and field\(X∪Y)
    have h_symdiff : i' ∈ (X ∪ Y) \ (X ∩ Y) :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp h_sdiff).1),
         fun h => (Finset.mem_sdiff.mp h_sdiff).2 (Finset.mem_inter.mp h).2⟩
    obtain ⟨⟨i₁, h_i₁_mem, h_le₁⟩, ⟨i₂, h_i₂_mem, h_le₂⟩⟩ := h2 i' h_symdiff
    rcases h_inner with h_cap | h_comp
    · have h_lt := h_cap i₁ h_i₁_mem
      simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at h_lt
      simp [h_lt.2] at h_le₁
    · have h_lt := h_comp i₂ h_i₂_mem
      simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at h_lt
      simp [h_lt.2] at h_le₂

/-- Fact 11: ⊐ respects ∼ on the right.
If X ⊐ Y and Y ∼ Z (with all sets in the field), then X ⊐ Z.
Under left inner: m dominates all of Y, m ∉ Z is forced, and
matching through Y∼Z extends domination to Z\Y.
Under right inner: m dominates field\X; if m ∉ Z, Z\X ⊆ field\X;
if m ∈ Z, use Y∼Z to find alternative witness in X\Z. -/
theorem strictlyBetter_respects_right {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (_hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hyz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y : ∀ y ∈ Y, ord.lt y m = true := by
      intro y hy
      by_cases hyx : y ∈ X
      · exact h_left y (Finset.mem_inter.mpr ⟨hyx, hy⟩)
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨hy, hyx⟩)
    -- z ∈ Z, z ∉ Y → lt z m (via Y∼Z matching + m_dom_Y)
    have z_ny_lt : ∀ z, z ∈ Z → z ∉ Y → ord.lt z m = true := by
      intro z hz hny
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · obtain ⟨y', hy', hle⟩ := hyz_b z (Finset.mem_sdiff.mpr ⟨hz, hny⟩)
        exact le_lt_trans' ord z y' m hle (m_dom_Y y' (Finset.mem_sdiff.mp hy').1)
      · obtain ⟨⟨c, hc, hle⟩, _⟩ := hyz2 z
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hz),
            fun h => hny (Finset.mem_inter.mp h).1⟩)
        exact le_lt_trans' ord z c m hle (m_dom_Y c (Finset.mem_inter.mp hc).1)
    -- m ∉ Z forced: z_ny_lt m would give lt m m
    have hm_nz : m ∉ Z := by
      intro hm_z; have := z_ny_lt m hm_z hm_ny
      simp [SemanticOrdering.lt, ord.le_refl] at this
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_nz⟩, hm_f, ?_, Or.inl ?_⟩
    · intro z hz
      by_cases hz_y : z ∈ Y
      · exact hm_yx z (Finset.mem_sdiff.mpr ⟨hz_y, (Finset.mem_sdiff.mp hz).2⟩)
      · exact z_ny_lt z (Finset.mem_sdiff.mp hz).1 hz_y
    · intro c hc
      by_cases hc_y : c ∈ Y
      · exact m_dom_Y c hc_y
      · exact z_ny_lt c (Finset.mem_inter.mp hc).2 hc_y
  · -- RIGHT INNER: m dominates field \ X
    have m_dom_fX : ∀ c ∈ field ord i \ X, ord.lt c m = true := by
      intro c hc
      by_cases hc_y : c ∈ Y
      · exact hm_yx c (Finset.mem_sdiff.mpr ⟨hc_y, (Finset.mem_sdiff.mp hc).2⟩)
      · exact h_right c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
          fun h => Finset.mem_union.mp h |>.elim (Finset.mem_sdiff.mp hc).2 hc_y⟩)
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z ∩ X: find alternative witness via Y∼Z
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · -- cond1: m ∈ Z\Y → ∃ y₀ ∈ Y\Z, le m y₀; y₀ ∈ X forced
        obtain ⟨y₀, hy₀, hle⟩ := hyz_b m (Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩)
        have hy₀_x : y₀ ∈ X := by
          by_contra h
          have := m_dom_fX y₀ (Finset.mem_sdiff.mpr ⟨hYf (Finset.mem_sdiff.mp hy₀).1, h⟩)
          simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
          simp [this.2] at hle
        refine ⟨y₀, Finset.mem_sdiff.mpr ⟨hy₀_x, (Finset.mem_sdiff.mp hy₀).2⟩,
                hYf (Finset.mem_sdiff.mp hy₀).1, ?_, Or.inr ?_⟩
        · intro z hz; exact lt_le_trans' ord z m y₀
            (m_dom_fX z (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz).1,
              (Finset.mem_sdiff.mp hz).2⟩)) hle
        · intro c hc; exact lt_le_trans' ord c m y₀
            (m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
              fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)) hle
      · -- cond2: ∃ c₂ ∈ field\(Y∪Z), le m c₂; c₂ ∈ X forced
        obtain ⟨_, ⟨c₂, hc₂, hle⟩⟩ := hyz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hm_z),
            fun h => hm_ny (Finset.mem_inter.mp h).1⟩)
        have hc₂_x : c₂ ∈ X := by
          by_contra h
          have := m_dom_fX c₂ (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc₂).1, h⟩)
          simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
          simp [this.2] at hle
        have hc₂_nz : c₂ ∉ Z :=
          fun h => (Finset.mem_sdiff.mp hc₂).2 (Finset.mem_union.mpr (Or.inr h))
        refine ⟨c₂, Finset.mem_sdiff.mpr ⟨hc₂_x, hc₂_nz⟩,
                (Finset.mem_sdiff.mp hc₂).1, ?_, Or.inr ?_⟩
        · intro z hz; exact lt_le_trans' ord z m c₂
            (m_dom_fX z (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz).1,
              (Finset.mem_sdiff.mp hz).2⟩)) hle
        · intro c hc; exact lt_le_trans' ord c m c₂
            (m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
              fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)) hle
    · -- m ∉ Z: witness = m ∈ X\Z
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩, hm_f, ?_, Or.inr ?_⟩
      · intro z hz; exact m_dom_fX z (Finset.mem_sdiff.mpr
          ⟨hZf (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩)
      · intro c hc; exact m_dom_fX c (Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hc).1,
           fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)

/-- Fact 11: ⊐ respects ∼ on the left.
If X ⊐ Y and X ∼ Z (with all sets in the field), then Z ⊐ Y.
Under left inner: m dominates all of Y; use X∼Z to find
a witness in Z\Y (either m itself or a matched element).
Under right inner: m dominates field\X; m ∈ Z is forced
(matching m ∈ X\Z through X∼Z yields z ∈ field\X < m,
contradicting le m z); elements of Y\Z ∩ X use X∼Z
matching to field\X for domination. -/
theorem strictlyBetter_respects_left {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (_hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i X Z →
    strictlyBetter ord i Z Y := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hxz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y : ∀ y ∈ Y, ord.lt y m = true := by
      intro y hy
      by_cases hyx : y ∈ X
      · exact h_left y (Finset.mem_inter.mpr ⟨hyx, hy⟩)
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨hy, hyx⟩)
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z: witness m ∈ Z\Y
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inl ?_⟩
      · intro y hy; exact m_dom_Y y (Finset.mem_sdiff.mp hy).1
      · intro c hc; exact m_dom_Y c (Finset.mem_inter.mp hc).2
    · -- m ∉ Z: use X∼Z to find witness in Z with le m witness
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · -- cond1: m ∈ X\Z → ∃ z₀ ∈ Z\X, le m z₀; z₀ ∉ Y forced
        obtain ⟨z₀, hz₀, hle⟩ := hxz_a m (Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩)
        have hz₀_ny : z₀ ∉ Y := by
          intro h; have := m_dom_Y z₀ h
          simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
          simp [this.2] at hle
        refine ⟨z₀, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz₀).1, hz₀_ny⟩,
                hZf (Finset.mem_sdiff.mp hz₀).1, ?_, Or.inl ?_⟩
        · intro y hy; exact lt_le_trans' ord y m z₀
            (m_dom_Y y (Finset.mem_sdiff.mp hy).1) hle
        · intro c hc; exact lt_le_trans' ord c m z₀
            (m_dom_Y c (Finset.mem_inter.mp hc).2) hle
      · -- cond2: m ∈ (X∪Z)\(X∩Z) → ∃ z₁ ∈ X∩Z, le m z₁; z₁ ∉ Y forced
        obtain ⟨⟨z₁, hz₁, hle⟩, _⟩ := hxz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hm_x),
            fun h => hm_z (Finset.mem_inter.mp h).2⟩)
        have hz₁_ny : z₁ ∉ Y := by
          intro h; have := m_dom_Y z₁ h
          simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
          simp [this.2] at hle
        refine ⟨z₁, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz₁).2, hz₁_ny⟩,
                hXf (Finset.mem_inter.mp hz₁).1, ?_, Or.inl ?_⟩
        · intro y hy; exact lt_le_trans' ord y m z₁
            (m_dom_Y y (Finset.mem_sdiff.mp hy).1) hle
        · intro c hc; exact lt_le_trans' ord c m z₁
            (m_dom_Y c (Finset.mem_inter.mp hc).2) hle
  · -- RIGHT INNER: m dominates field \ X
    have m_dom_fX : ∀ c ∈ field ord i \ X, ord.lt c m = true := by
      intro c hc
      by_cases hc_y : c ∈ Y
      · exact hm_yx c (Finset.mem_sdiff.mpr ⟨hc_y, (Finset.mem_sdiff.mp hc).2⟩)
      · exact h_right c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
          fun h => Finset.mem_union.mp h |>.elim (Finset.mem_sdiff.mp hc).2 hc_y⟩)
    -- c ∈ X\Z → lt c m (via X∼Z matching to field\X, then m_dom_fX)
    have lt_via_xz : ∀ c, c ∈ X → c ∉ Z → ord.lt c m = true := by
      intro c hc_x hc_nz
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z', hz', hle⟩ := hxz_a c (Finset.mem_sdiff.mpr ⟨hc_x, hc_nz⟩)
        exact le_lt_trans' ord c z' m hle (m_dom_fX z'
          (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz').1,
            (Finset.mem_sdiff.mp hz').2⟩))
      · obtain ⟨_, ⟨c', hc', hle⟩⟩ := hxz2 c
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hc_x),
            fun h => hc_nz (Finset.mem_inter.mp h).2⟩)
        exact le_lt_trans' ord c c' m hle (m_dom_fX c'
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc').1,
            fun h => (Finset.mem_sdiff.mp hc').2 (Finset.mem_union.mpr (Or.inl h))⟩))
    -- m ∈ Z forced: if m ∉ Z, lt_via_xz gives lt m m
    have hm_z : m ∈ Z := by
      by_contra hm_nz; have := lt_via_xz m hm_x hm_nz
      simp [SemanticOrdering.lt, ord.le_refl] at this
    -- Witness m ∈ Z\Y
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inr ?_⟩
    · -- ∀ y ∈ Y\Z, lt y m
      intro y hy
      by_cases hy_x : y ∈ X
      · exact lt_via_xz y hy_x (Finset.mem_sdiff.mp hy).2
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hy_x⟩)
    · -- ∀ c ∈ field\(Z∪Y), lt c m
      intro c hc
      by_cases hc_x : c ∈ X
      · exact lt_via_xz c hc_x
          (fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h)))
      · exact m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1, hc_x⟩)

/-- Fact 12b: ⊐ is transitive on sets.
Given witnesses m₁ (X⊐Y) and m₂ (Y⊐Z), split on which is higher.
If m₂ ≤ m₁: m₁ cannot be in Z (else m₁ ∈ Z\Y with ¬(m₁ < m₂)),
so m₁ ∈ X\Z is the witness for X⊐Z.
If m₁ ≤ m₂: m₂ must be in X (else m₂ ∈ Y\X with ¬(m₂ < m₁)),
so m₂ ∈ X\Z is the witness for X⊐Z. -/
theorem strictlyBetter_trans {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    strictlyBetter ord i X Y → strictlyBetter ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m₁, hm₁_sd, hm₁_f, hm₁_yx, hm₁_inner⟩
         ⟨m₂, hm₂_sd, hm₂_f, hm₂_zy, hm₂_inner⟩
  have hm₁_x := (Finset.mem_sdiff.mp hm₁_sd).1
  have hm₁_ny := (Finset.mem_sdiff.mp hm₁_sd).2
  have hm₂_y := (Finset.mem_sdiff.mp hm₂_sd).1
  have hm₂_nz := (Finset.mem_sdiff.mp hm₂_sd).2
  -- Key helper: z ∈ Z\X → lt z m₁ (when m₂ ≤ m₁)
  have zx_lt_m1 (hle : ord.le m₂ m₁ = true) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₁ = true := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)
    · exact lt_le_trans' ord z m₂ m₁ (hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)) hle
  -- Key helper: z ∈ Z\X → lt z m₂ (when m₁ ≤ m₂)
  have zx_lt_m2 (hle : ord.le m₁ m₂ = true) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₂ = true := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · -- z ∈ Y\X → lt z m₁; then le z m₂ by trans; ¬(le m₂ z) by contradiction
      have h_lt := hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)
      simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at h_lt ⊢
      refine ⟨ord.le_trans z m₁ m₂ h_lt.1 hle, ?_⟩
      cases h : ord.le m₂ z
      · rfl
      · exact absurd (ord.le_trans m₁ m₂ z hle h) (by simp [h_lt.2])
    · exact hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)
  rcases ord.le_total m₂ m₁ with hle | hle
  · -- Case: m₂ ≤ m₁. Witness = m₁.
    -- m₁ ∉ Z: if m₁ ∈ Z, then m₁ ∈ Z\Y, so lt m₁ m₂. But m₂ ≤ m₁, so lt m₁ m₂ = false.
    have hm₁_nz : m₁ ∉ Z := fun h => by
      have := hm₂_zy m₁ (Finset.mem_sdiff.mpr ⟨h, hm₁_ny⟩)
      simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
      simp [hle] at this
    refine ⟨m₁, Finset.mem_sdiff.mpr ⟨hm₁_x, hm₁_nz⟩, hm₁_f, zx_lt_m1 hle, ?_⟩
    -- Inner disjunct: follows from X⊐Y's inner
    rcases hm₁_inner with h_cap | h_comp
    · -- Left: ∀ X∩Y < m₁ → ∀ X∩Z < m₁
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_x, hc_y⟩)
      · exact lt_le_trans' ord c m₂ m₁
          (hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)) hle
    · -- Right: ∀ field\(X∪Y) < m₁ → ∀ field\(X∪Z) < m₁
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_nx hc_y⟩)
  · -- Case: m₁ ≤ m₂. Witness = m₂.
    -- m₂ ∈ X: if m₂ ∉ X, then m₂ ∈ Y\X, so lt m₂ m₁. But m₁ ≤ m₂, contradiction.
    have hm₂_x : m₂ ∈ X := by
      by_contra h
      have := hm₁_yx m₂ (Finset.mem_sdiff.mpr ⟨hm₂_y, h⟩)
      simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at this
      simp [hle] at this
    refine ⟨m₂, Finset.mem_sdiff.mpr ⟨hm₂_x, hm₂_nz⟩, hm₂_f, zx_lt_m2 hle, ?_⟩
    -- Inner disjunct: follows from Y⊐Z's inner
    rcases hm₂_inner with h_cap | h_comp
    · -- Left: ∀ Y∩Z < m₂ → ∀ X∩Z < m₂
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_y, hc_z⟩)
      · exact hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)
    · -- Right: ∀ field\(Y∪Z) < m₂ → ∀ field\(X∪Z) < m₂
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := fun h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := fun h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · -- c ∈ Y\X → lt c m₁; then lt c m₂ by same argument as zx_lt_m2
        have h_lt := hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)
        simp only [SemanticOrdering.lt, Bool.and_eq_true, Bool.not_eq_true'] at h_lt ⊢
        refine ⟨ord.le_trans c m₁ m₂ h_lt.1 hle, ?_⟩
        cases h : ord.le m₂ c
        · rfl
        · exact absurd (ord.le_trans m₁ m₂ c hle h) (by simp [h_lt.2])
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, fun h => Finset.mem_union.mp h |>.elim hc_y hc_nz⟩)

/-- Fact 12c: ⊐ is total on nonequivalent sets.
For any X, Y ⊆ I_i, either X ∼ Y or X ⊐ Y or Y ⊐ X.

The proof finds the maximum element m of the symmetric difference
(X\Y)∪(Y\X), then case-splits on whether all elements on the
other side are strictly below m. If yes, we get ⊐; if no, we
get ∼ via one of the two equivalence conditions. -/
theorem strictlyBetter_total {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I)
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    degreeEquiv ord i X Y ∨ strictlyBetter ord i X Y ∨
    strictlyBetter ord i Y X := by
  by_cases h_eq : X = Y
  · exact Or.inl (h_eq ▸ degreeEquiv_refl ord i X)
  · obtain ⟨m, hm, hm_max⟩ := exists_le_max ord _ (symdiff_nonempty X Y h_eq)
    -- Helper: any element of the symdiff ≤ m
    have hm_max' : ∀ s ∈ (X \ Y) ∪ (Y \ X), ord.le s m = true := hm_max
    rcases Finset.mem_union.mp hm with hm_xy | hm_yx
    · -- m ∈ X\Y: either equivCond1, or strictlyBetter X Y
      have hm_field : m ∈ field ord i := hX (Finset.mem_sdiff.mp hm_xy).1
      by_cases h_all_yx : ∀ y ∈ Y \ X, ord.lt y m = true
      · -- All Y\X < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ X ∩ Y, ord.lt c m = true
        · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m = true
          · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge : ord.le m c₁ = true :=
              (not_lt_iff_ge ord c₁ m).mp (bool_eq_false_of_ne_true hc₁_nlt)
            have hc₂_ge : ord.le m c₂ = true :=
              (not_lt_iff_ge ord c₂ m).mp (bool_eq_false_of_ne_true hc₂_nlt)
            exact Or.inl (Or.inr (fun s hs => by
              have hs_sd := (mem_symdiff_iff X Y s).mp hs
              have h_le_sm := hm_max' s hs_sd
              exact ⟨⟨c₁, hc₁_mem, ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, hc₂_mem, ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ y₀ ∈ Y\X with ¬(lt y₀ m): equivCond1
        push Not at h_all_yx
        obtain ⟨y₀, hy₀_mem, hy₀_nlt⟩ := h_all_yx
        have hy₀_ge : ord.le m y₀ = true :=
          (not_lt_iff_ge ord y₀ m).mp (bool_eq_false_of_ne_true hy₀_nlt)
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨y₀, hy₀_mem,
              ord.le_trans x m y₀
                (hm_max' x (Finset.mem_union.mpr (Or.inl hx))) hy₀_ge⟩,
           fun y hy => ⟨m, hm_xy,
              hm_max' y (Finset.mem_union.mpr (Or.inr hy))⟩⟩)
    · -- m ∈ Y\X: symmetric case — either equivCond1, or strictlyBetter Y X
      have hm_field : m ∈ field ord i := hY (Finset.mem_sdiff.mp hm_yx).1
      by_cases h_all_xy : ∀ x ∈ X \ Y, ord.lt x m = true
      · -- All X\Y < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ Y ∩ X, ord.lt c m = true
        · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (Y ∪ X), ord.lt c m = true
          · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge : ord.le m c₁ = true :=
              (not_lt_iff_ge ord c₁ m).mp (bool_eq_false_of_ne_true hc₁_nlt)
            have hc₂_ge : ord.le m c₂ = true :=
              (not_lt_iff_ge ord c₂ m).mp (bool_eq_false_of_ne_true hc₂_nlt)
            exact Or.inl (Or.inr (fun s hs => by
              have hs_sd := (mem_symdiff_iff X Y s).mp hs
              have h_le_sm : ord.le s m = true :=
                hm_max' s hs_sd
              constructor
              · -- c₁ ∈ Y ∩ X = X ∩ Y
                exact ⟨c₁, by rw [Finset.inter_comm]; exact hc₁_mem,
                       ord.le_trans s m c₁ h_le_sm hc₁_ge⟩
              · exact ⟨c₂, by rw [Finset.union_comm]; exact hc₂_mem,
                       ord.le_trans s m c₂ h_le_sm hc₂_ge⟩))
      · -- ∃ x₀ ∈ X\Y with ¬(lt x₀ m): equivCond1
        push Not at h_all_xy
        obtain ⟨x₀, hx₀_mem, hx₀_nlt⟩ := h_all_xy
        have hx₀_ge : ord.le m x₀ = true :=
          (not_lt_iff_ge ord x₀ m).mp (bool_eq_false_of_ne_true hx₀_nlt)
        exact Or.inl (Or.inl
          ⟨fun x hx => ⟨m, hm_yx,
              hm_max' x (Finset.mem_union.mpr (Or.inl hx))⟩,
           fun y hy => ⟨x₀, hx₀_mem,
              ord.le_trans y m x₀
                (hm_max' y (Finset.mem_union.mpr (Or.inr hy))) hx₀_ge⟩⟩)


-- ════════════════════════════════════════════════════════════════
-- § 7. Fact 8c: ∼ Transitivity (via Totality + Respects)
-- ════════════════════════════════════════════════════════════════

/-- Fact 8c: ∼ is transitive (for sets in the field).
Indirect proof: if ¬(X∼Z), totality gives X⊐Z or Z⊐X.
- X⊐Z: respects_right(X,Z,Y) with Z∼Y gives X⊐Y, contradicting X∼Y.
- Z⊐X: respects_right(Z,X,Y) with X∼Y gives Z⊐Y, contradicting Y∼Z.
This avoids the direct Schröder-Bernstein bouncing chain argument. -/
theorem degreeEquiv_trans {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y Z →
    degreeEquiv ord i X Z := by
  intro hxy hyz
  by_contra h_neq
  rcases strictlyBetter_total ord i X Z hXf hZf with h | h | h
  · exact h_neq h
  · -- X ⊐ Z, Z ∼ Y → X ⊐ Y, contradicts X ∼ Y
    exact degreeEquiv_not_strictlyBetter ord i X Y hxy
      (strictlyBetter_respects_right ord i X Z Y hXf hZf hYf h
        (degreeEquiv_symm ord i Y Z hyz))
  · -- Z ⊐ X, X ∼ Y → Z ⊐ Y, contradicts Y ∼ Z
    exact degreeEquiv_not_strictlyBetter ord i Z Y
      (degreeEquiv_symm ord i Y Z hyz)
      (strictlyBetter_respects_right ord i Z X Y hZf hXf hYf h hxy)

/-- The metalinguistic setoid: ∼ as a Mathlib `Setoid` on field-subsets.
The carrier is `{X : Finset I // X ⊆ field ord i}` because
transitivity requires the ⊆ field hypothesis (via totality). -/
def metalinguisticSetoid {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :
    Setoid {X : Finset I // X ⊆ field ord i} where
  r X Y := degreeEquiv ord i X.1 Y.1
  iseqv := {
    refl := fun X => degreeEquiv_refl ord i X.1
    symm := fun {X Y} h => degreeEquiv_symm ord i X.1 Y.1 h
    trans := fun {X Y Z} hxy hyz =>
      degreeEquiv_trans ord i X.1 Y.1 Z.1 X.2 Y.2 Z.2 hxy hyz
  }


-- ════════════════════════════════════════════════════════════════
-- § 8. Metalinguistic Degree Type
-- ════════════════════════════════════════════════════════════════

/-- The type of metalinguistic degrees: equivalence classes of
interpretation sets under ∼.

A metalinguistic degree is a *set of sets of interpretations* —
all the interpretation sets that are "ranked as high" as each other.
The degree of a sentence A is `deg(⟦A⟧_i)`. -/
def MetaDegree (I : Type) [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :=
  Quotient (metalinguisticSetoid ord i)

/-- Compute the metalinguistic degree of an interpretation set. -/
def deg {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X : Finset I) (hX : X ⊆ field ord i) :
    MetaDegree I ord i :=
  Quotient.mk (metalinguisticSetoid ord i) ⟨X, hX⟩

/-- The metalinguistic degree of a formula's denotation. -/
def formulaDeg {I W Pred Entity : Type} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    MetaDegree I ord i :=
  deg ord i (denotation interpFn φ ord i w) (Finset.filter_subset _ _)


-- ════════════════════════════════════════════════════════════════
-- § 9. Facts 9–10: Correspondence with Revised Semantics
-- ════════════════════════════════════════════════════════════════

/-- Membership in `field`: j ∈ I_i iff j ≤ i. -/
private theorem mem_field_iff {I : Type} [Fintype I] [DecidableEq I]
    {ord : SemanticOrdering I} {i j : I} :
    j ∈ field ord i ↔ ord.le j i = true := by
  simp [field]

/-- Membership in `denotation`: j ∈ ⟦φ⟧_i iff j ≤ i and ⟦φ⟧^j = 1. -/
private theorem mem_denotation_iff {I W Pred Entity : Type}
    [Fintype I] [DecidableEq I]
    {interpFn : I → Interpretation W Pred Entity}
    {φ : MFormula Pred Entity}
    {ord : SemanticOrdering I} {i j : I} {w : W} :
    j ∈ denotation interpFn φ ord i w ↔
    ord.le j i = true ∧ evalRevised interpFn φ ord j w = true := by
  simp [denotation, field]

/-- Fact 10: revised MC holds iff denotation of A ⊐ denotation of B.
⟦A ≻ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ⊐ ⟦B⟧_i. -/
theorem mc_iff_degree_gt {I W Pred Entity : Type}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (.mc A B) ord i w = true ↔
    strictlyBetter ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  rw [evalRevised_mc_iff]
  constructor
  · -- Forward: ∃ i' with le, A true, B false, domination → strictlyBetter
    rintro ⟨i', h_le, h_A, h_B, h_dom⟩
    refine ⟨i', ?_, ?_, ?_, ?_⟩
    · -- i' ∈ denotation A \ denotation B
      exact Finset.mem_sdiff.mpr
        ⟨mem_denotation_iff.mpr ⟨h_le, h_A⟩,
         fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_B])⟩
    · -- i' ∈ field
      exact mem_field_iff.mpr h_le
    · -- ∀ i'' ∈ Y \ X, lt i'' i'
      intro i'' h_mem
      obtain ⟨h_inY, h_ninX⟩ := Finset.mem_sdiff.mp h_mem
      obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp h_inY
      rcases h_dom with h1 | h2
      · exact h1 i'' h_le'' h_B''
      · exact h2 i'' h_le'' (bool_eq_false_of_ne_true fun h =>
          h_ninX (mem_denotation_iff.mpr ⟨h_le'', h⟩))
    · -- inner disjunct
      rcases h_dom with h1 | h2
      · left; intro i'' h_mem
        obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2
        exact h1 i'' h_le'' h_B''
      · right; intro i'' h_mem
        have h_sd := Finset.mem_sdiff.mp h_mem
        have h_le'' := mem_field_iff.mp h_sd.1
        exact h2 i'' h_le'' (bool_eq_false_of_ne_true fun h =>
          h_sd.2 (Finset.mem_union.mpr (Or.inl (mem_denotation_iff.mpr ⟨h_le'', h⟩))))
  · -- Backward: strictlyBetter → evalRevised_mc conditions
    rintro ⟨i', h_sdiff, h_field, h_ymx, h_inner⟩
    obtain ⟨h_inX, h_ninY⟩ := Finset.mem_sdiff.mp h_sdiff
    obtain ⟨h_le, h_A⟩ := mem_denotation_iff.mp h_inX
    have h_B : evalRevised interpFn B ord i' w = false :=
      bool_eq_false_of_ne_true fun h =>
        h_ninY (mem_denotation_iff.mpr ⟨h_le, h⟩)
    refine ⟨i', h_le, h_A, h_B, ?_⟩
    rcases h_inner with h1 | h2
    · -- X ∩ Y all below → all B-true in field below
      left; intro i'' h_le'' h_B''
      by_cases h_A'' : evalRevised interpFn A ord i'' w = true
      · exact h1 i'' (Finset.mem_inter.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_A''⟩,
           mem_denotation_iff.mpr ⟨h_le'', h_B''⟩⟩)
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => h_A'' (mem_denotation_iff.mp h).2⟩)
    · -- field \ (X ∪ Y) all below → all A-false in field below
      right; intro i'' h_le'' h_A''
      by_cases h_B'' : evalRevised interpFn B ord i'' w = true
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_A''])⟩)
      · exact h2 i'' (Finset.mem_sdiff.mpr
          ⟨mem_field_iff.mpr h_le'',
           fun h => Finset.mem_union.mp h |>.elim
             (fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_A'']))
             (fun h => absurd (mem_denotation_iff.mp h).2 (by simp [h_B'']))⟩)


/-- Fact 9: ME holds iff denotations have the same degree.
⟦A ≈ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ∼ ⟦B⟧_i.
This connects the Boolean evaluation function `evalRevised` to the
algebraic degree structure. Forward direction uses `strictlyBetter_total`. -/
theorem me_iff_same_degree {I W Pred Entity : Type}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (A.me B) ord i w = true ↔
    degreeEquiv ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  set X := denotation interpFn A ord i w
  set Y := denotation interpFn B ord i w
  -- ME = ¬MC(A,B) ∧ ¬MC(B,A)
  have h_unfold : evalRevised interpFn (A.me B) ord i w =
    (!(evalRevised interpFn (.mc A B) ord i w) &&
     !(evalRevised interpFn (.mc B A) ord i w)) := rfl
  have hX : X ⊆ field ord i := by
    intro j hj; exact Finset.mem_of_subset (Finset.filter_subset _ _) hj
  have hY : Y ⊆ field ord i := by
    intro j hj; exact Finset.mem_of_subset (Finset.filter_subset _ _) hj
  constructor
  · -- Forward: ME → degreeEquiv via totality.
    -- If ¬MC(A,B) and ¬MC(B,A), then by mc_iff_degree_gt,
    -- ¬(X ⊐ Y) and ¬(Y ⊐ X). By totality, X ∼ Y.
    intro h_me
    rw [h_unfold] at h_me
    have h_nmc1 : evalRevised interpFn (.mc A B) ord i w ≠ true := by
      intro h; simp [h] at h_me
    have h_nmc2 : evalRevised interpFn (.mc B A) ord i w ≠ true := by
      intro h; simp [h] at h_me
    have h_nsb1 : ¬ strictlyBetter ord i X Y :=
      fun h => h_nmc1 ((mc_iff_degree_gt interpFn A B ord i w).mpr h)
    have h_nsb2 : ¬ strictlyBetter ord i Y X :=
      fun h => h_nmc2 ((mc_iff_degree_gt interpFn B A ord i w).mpr h)
    rcases strictlyBetter_total ord i X Y hX hY with h | h | h
    · exact h
    · exact absurd h h_nsb1
    · exact absurd h h_nsb2
  · -- Backward: degreeEquiv → ME
    intro h_eq
    rw [h_unfold]
    have h1 : evalRevised interpFn (.mc A B) ord i w ≠ true :=
      fun h => degreeEquiv_not_strictlyBetter ord i X Y h_eq
        ((mc_iff_degree_gt interpFn A B ord i w).mp h)
    have h2 : evalRevised interpFn (.mc B A) ord i w ≠ true :=
      fun h => degreeEquiv_not_strictlyBetter ord i Y X
        (degreeEquiv_symm ord i X Y h_eq)
        ((mc_iff_degree_gt interpFn B A ord i w).mp h)
    cases heq1 : evalRevised interpFn (.mc A B) ord i w <;>
    cases heq2 : evalRevised interpFn (.mc B A) ord i w <;> simp_all


-- ════════════════════════════════════════════════════════════════
-- § 8. Fact 13: Extremal Degrees
-- ════════════════════════════════════════════════════════════════

/-- Fact 13a: the full field I_i is the maximum degree.
deg(⊤) = {I_i}: the tautology's denotation is the whole field,
and nothing is strictly better than I_i. -/
theorem field_is_max {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I)
    (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i X (field ord i) ∨
    degreeEquiv ord i X (field ord i) := by
  left
  rintro ⟨i', hi', _⟩
  exact (Finset.mem_sdiff.mp hi').2 (hX (Finset.mem_sdiff.mp hi').1)

/-- Fact 13b: the empty set is the minimum degree.
deg(⊥) = {∅}: the contradiction's denotation is empty,
and nothing is strictly worse than ∅. -/
theorem empty_is_min {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I)
    (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i (∅ : Finset I) X ∨
    degreeEquiv ord i X ∅ := by
  left
  rintro ⟨i', hi', _⟩
  simp at hi'


end Semantics.Comparison.MetalinguisticDegree
