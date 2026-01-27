/-
# Exhaustivity Operators: exh_mw and exh_ie

Formalization of Spector (2016) "Comparing exhaustivity operators"
Semantics & Pragmatics Volume 9, Article 11: 1–33.

## Paper Structure

**Section 1**: Introduction

**Section 2**: Background and definitions
- 2.1: Definitions 1-4 (≤_ALT, exh_mw, compatible sets, MC-sets, IE, exh_ie)
- 2.2: Illustrations

**Section 3**: Results to be proven
- 3.2: Proposition 1, Corollary 2 (relationship of three operators)
- 3.3: Proposition 3, Corollaries 4, 5 (facts about exh_mw)
- 3.4: Propositions 6, 7, Corollary 8 (relationship exh_mw ↔ exh_ie)
- 3.5: **Theorem 9** (main result: closed under ∧ → equivalence)
- 3.6: Theorem 10, Corollary 11 (consequences)

**Section 5**: Proofs
- 5.3: Lemmas 1, 2, 3 (core lemmas connecting minimality to MC-sets)
- 5.4: Proof of Theorem 9

## Main Result

**Theorem 9**: When ALT is closed under conjunction, exh_mw = exh_ie

## References

- Spector (2016). Comparing exhaustivity operators. S&P 9(11):1-33.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Groenendijk & Stokhof (1984). Studies on the semantics of questions.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset

namespace NeoGricean.Exhaustivity

-- ============================================================================
-- SECTION 2.1: Definitions (Spector p.6-8)
-- ============================================================================

/-
"In the context of this paper, the notion of world is identical to that of model."

"The proposition expressed by a sentence is the set of worlds in which this
sentence is true."

"To mean that a proposition φ is true (resp. false) in a world u ... I write
φ(u) = 1 (resp. φ(u) = 0), rather than u ∈ φ (resp. u ∉ φ)."
-/

variable {World : Type*}

/--
A proposition as a characteristic function on worlds.
φ(w) holds iff the proposition is true at world w.
-/
abbrev Prop' (World : Type*) := World → Prop

/--
Entailment: φ ⊆ ψ (Spector uses set-theoretic notation)
"I also adopt the set-theoretic notation φ ⊆ ψ to mean that φ entails ψ."
-/
def entails (φ ψ : Prop' World) : Prop := ∀ w, φ w → ψ w

notation:50 φ " ⊆ₚ " ψ => entails φ ψ

/--
Equivalence of propositions
-/
def pequiv (φ ψ : Prop' World) : Prop := (φ ⊆ₚ ψ) ∧ (ψ ⊆ₚ φ)

notation:50 φ " ≡ₚ " ψ => pequiv φ ψ

/--
Negation of a proposition
-/
def pneg (φ : Prop' World) : Prop' World := fun w => ¬(φ w)

prefix:75 "∼" => pneg

/--
Conjunction of two propositions
-/
def pand (φ ψ : Prop' World) : Prop' World := fun w => φ w ∧ ψ w

infixl:65 " ∧ₚ " => pand

/--
Conjunction of a set of propositions (grand conjunction ⋀X)
"⋀X refers to the grand conjunction of its members, i.e., the proposition
that is true in a world u if and only if every member of X is true in u"
-/
def bigConj (X : Set (Prop' World)) : Prop' World :=
  fun w => ∀ φ ∈ X, φ w

notation "⋀" => bigConj

/--
Disjunction of a set of propositions (grand disjunction ⋁X)
"⋁X refers to the grand disjunction of the members of X, i.e., the proposition
that is true in a world u if and only if at least one member of X is true in u"
-/
def bigDisj (X : Set (Prop' World)) : Prop' World :=
  fun w => ∃ φ ∈ X, φ w

notation "⋁" => bigDisj

-- ============================================================================
-- DEFINITION 1: The preorder ≤_ALT (Spector p.7)
-- ============================================================================

variable (ALT : Set (Prop' World))

/--
**Definition 1.1**: Given a set of alternatives ALT, ≤_ALT is the preorder
over possible worlds defined as follows:

  u ≤_ALT v iff {a ∈ ALT : a(u) = 1} ⊆ {a ∈ ALT : a(v) = 1}

"u makes true a subset of the alternatives that v makes true"
-/
def leALT (u v : World) : Prop :=
  ∀ a ∈ ALT, a u → a v

/--
**Definition 1.2**: <_ALT is the strict preorder corresponding to ≤_ALT:

  u <_ALT v iff u ≤_ALT v ∧ ¬(v ≤_ALT u)

"The alternatives that u makes true are a PROPER subset of those that v makes true."
-/
def ltALT (u v : World) : Prop :=
  leALT ALT u v ∧ ¬(leALT ALT v u)

-- Notation (Spector omits the subscript ALT, we make it explicit)
notation:50 u " ≤[" ALT "] " v => leALT ALT u v
notation:50 u " <[" ALT "] " v => ltALT ALT u v

-- Basic properties of the preorder

theorem leALT_refl (u : World) : u ≤[ALT] u := by
  intro a _ h
  exact h

theorem leALT_trans (u v w : World) (huv : u ≤[ALT] v) (hvw : v ≤[ALT] w) : u ≤[ALT] w := by
  intro a ha hau
  exact hvw a ha (huv a ha hau)

-- ============================================================================
-- DEFINITION 2: exh_mw (Spector p.7)
-- ============================================================================

variable (φ : Prop' World)

/--
**Definition 2**: Exhaustivity operator based on minimal worlds (exh_mw)

Given a set of propositions ALT and a proposition φ,

  exh_mw(ALT, φ) = {u : φ(u) = 1 ∧ ¬∃v(φ(v) = 1 ∧ v <_ALT u)}

Equivalently: exh_mw(ALT, φ) = φ ∩ {u : ¬∃v(φ(v) = 1 ∧ v <_ALT u)}

"The set of φ-worlds that are minimal relative to <_ALT"
-/
def exhMW : Prop' World :=
  fun u => φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)

/--
A world u is minimal among φ-worlds relative to <_ALT.
-/
def isMinimal (u : World) : Prop :=
  φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)

-- Basic property
theorem exhMW_entails : exhMW ALT φ ⊆ₚ φ :=
  fun _ ⟨h, _⟩ => h

-- ============================================================================
-- DEFINITIONS 3: Compatible sets and MC-sets (Spector p.7)
-- ============================================================================

/--
**Definition 3.1**: A set of propositions X is consistent if there exists
a world u in which every member of X is true.
-/
def SetConsistent (X : Set (Prop' World)) : Prop :=
  ∃ u, ∀ ψ ∈ X, ψ u

/--
**Definition 3.2**: Given a proposition φ and a set of alternatives ALT,
a set of propositions E is (ALT, φ)-compatible if and only if:
a) φ ∈ E
b) every member of E distinct from φ is the negation of a member of ALT
c) E is consistent
-/
def isCompatible (E : Set (Prop' World)) : Prop :=
  φ ∈ E ∧
  (∀ ψ ∈ E, ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a) ∧
  SetConsistent E

/--
**Definition 3.3**: MC_(ALT,φ)-sets

A set is maximal (ALT, φ)-compatible (MC_(ALT,φ)-set for short) if it is
(ALT, φ)-compatible and is not properly included in any other
(ALT, φ)-compatible set.
-/
def isMCSet (E : Set (Prop' World)) : Prop :=
  isCompatible ALT φ E ∧
  ∀ E', isCompatible ALT φ E' → E ⊆ E' → E' ⊆ E

/--
**Definition 3.4**: IE_(ALT,φ) = {ψ : ψ belongs to every MC_(ALT,φ)-set}

"Note that, somewhat counter-intuitively, the set IE_(ALT,φ) is not the set of
innocently excludable alternatives, but rather the set that contains φ and all
the negations of innocently excludable alternatives."
-/
def IE : Set (Prop' World) :=
  {ψ | ∀ E, isMCSet ALT φ E → ψ ∈ E}

/--
**Definition 3.5**: An alternative a is innocently excludable given ALT and φ
if and only if ¬a ∈ IE_(ALT,φ).
-/
def isInnocentlyExcludable (a : Prop' World) : Prop :=
  a ∈ ALT ∧ (∼a) ∈ IE ALT φ

-- ============================================================================
-- DEFINITION 4: exh_ie (Spector p.8)
-- ============================================================================

/--
**Definition 4**: Exhaustivity operator based on innocent exclusion (exh_ie)

  exh_ie(ALT, φ) = {u : ∀ψ(ψ ∈ IE_(ALT,φ) → ψ(u) = 1)}

Equivalently: exh_ie(ALT, φ) = ⋀ IE_(ALT,φ)

Equivalently: exh_ie(ALT, φ) = φ ∧ ⋀{¬a : a is a member of ALT that is
                                       innocently excludable given ALT and φ}
-/
def exhIE : Prop' World :=
  fun u => ∀ ψ ∈ IE ALT φ, ψ u

-- ============================================================================
-- DEFINITION 5: Closure under conjunction/disjunction (Spector p.11)
-- ============================================================================

/--
A set ALT is closed under conjunction if for any subset X of ALT,
⋀X ∈ ALT.

(Definition 5 in Spector)
-/
def closedUnderConj : Prop :=
  ∀ X : Set (Prop' World), X ⊆ ALT → (⋀ X) ∈ ALT

/--
A set ALT is closed under disjunction if for any subset X of ALT,
⋁X ∈ ALT.
-/
def closedUnderDisj : Prop :=
  ∀ X : Set (Prop' World), X ⊆ ALT → (⋁ X) ∈ ALT

-- ============================================================================
-- MC-SET EXISTENCE (via Minimal Worlds - Spector's approach)
-- ============================================================================

/-
## Spector's Approach to MC-set Existence

Following Spector (2016) Section 5.3, we do NOT use Zorn's lemma.
Instead, MC-set existence follows from minimal world existence via Lemma 1:

  u is minimal ⟺ X(u) is an MC-set

So: minimal world exists → MC-set exists (just take X(u)).

For finite ALT, minimal worlds exist because:
- The preorder ≤_ALT has finite "height" (bounded by |ALT|)
- Any non-empty set has minimal elements under <_ALT

This is cleaner than Zorn and avoids chain-union consistency issues.
-/

/--
**Well-foundedness for finite ALT**: The strict ordering <_ALT is well-founded
when ALT is finite.

Proof idea: For any infinite descending chain w₁ >_ALT w₂ >_ALT ...,
the set of true alternatives strictly increases at each step.
Since ALT is finite, this cannot continue indefinitely.
-/
theorem ltALT_wf_of_finite (hfin : Set.Finite ALT) : WellFounded (ltALT ALT) := by
  -- Key observation: w₁ <_ALT w₂ iff {a ∈ ALT | a w₁} ⊂ {a ∈ ALT | a w₂}
  -- Since ALT is finite, these are finite sets, and ⊂ on finite sets is well-founded.
  classical
  -- Define f(w) = {a ∈ ALT | a w} as a Finset
  let trueAt : World → Set (Prop' World) := fun w => {a ∈ ALT | a w}
  have hfin_trueAt : ∀ w, (trueAt w).Finite := fun w => hfin.subset fun a h => h.1
  let f : World → Finset (Prop' World) := fun w => (hfin_trueAt w).toFinset
  -- Membership characterization
  have hmem : ∀ w a, a ∈ f w ↔ a ∈ ALT ∧ a w := fun w a =>
    Set.Finite.mem_toFinset (hfin_trueAt w)
  -- Show: leALT u v ↔ f u ⊆ f v
  have hf_le : ∀ u v, leALT ALT u v ↔ f u ⊆ f v := by
    intro u v
    simp only [leALT, Finset.subset_iff]
    constructor
    · intro hle a ha
      rw [hmem] at ha ⊢
      exact ⟨ha.1, hle a ha.1 ha.2⟩
    · intro hsub a ha hau
      have h1 : a ∈ f u := (hmem u a).mpr ⟨ha, hau⟩
      have h2 : a ∈ f v := hsub h1
      exact ((hmem v a).mp h2).2
  -- Show: ltALT u v ↔ f u ⊂ f v
  have hf_lt : ∀ u v, ltALT ALT u v ↔ f u ⊂ f v := by
    intro u v
    simp only [ltALT, Finset.ssubset_iff_subset_ne]
    rw [hf_le, hf_le]
    constructor
    · intro ⟨hsub, hnsub⟩
      refine ⟨hsub, ?_⟩
      intro heq
      apply hnsub
      rw [heq]
    · intro ⟨hsub, hne⟩
      refine ⟨hsub, ?_⟩
      intro hsub'
      apply hne
      exact Finset.Subset.antisymm hsub hsub'
  -- Use well-foundedness of ⊂ on Finset via InvImage
  have hwf : WellFounded (fun (s t : Finset (Prop' World)) => s ⊂ t) := IsWellFounded.wf
  have : ltALT ALT = InvImage (fun s t => s ⊂ t) f := by
    ext u v
    exact hf_lt u v
  rw [this]
  exact InvImage.wf f hwf

/--
**Existence of minimal worlds for finite ALT**: When ALT is finite and φ is
satisfiable, there exists a minimal φ-world.
-/
theorem exists_minimal_of_finite (hfin : Set.Finite ALT) (hsat : ∃ w, φ w) :
    ∃ u, isMinimal ALT φ u := by
  obtain ⟨w₀, hw₀⟩ := hsat
  -- Use well-foundedness to find a minimal element in {w | φ w}
  have hwf := ltALT_wf_of_finite ALT hfin
  -- The set of φ-worlds is non-empty
  have hne : {w | φ w}.Nonempty := ⟨w₀, hw₀⟩
  -- By well-foundedness, there's a minimal element
  have ⟨u, hu_φ, hu_min⟩ := hwf.has_min {w | φ w} hne
  use u
  constructor
  · exact hu_φ
  · intro ⟨v, hv_φ, hv_lt⟩
    exact hu_min v hv_φ hv_lt

/-
Note: MC-set existence theorems (`exists_MCset_of_minimal`, `exists_MCset`)
and `IE_structure` are defined after Lemma 1 below, since they depend on it.
-/

-- ============================================================================
-- SECTION 5.3: KEY LEMMAS (Spector p.21-23)
-- These lemmas are essential for proving Propositions 6 and 7
-- ============================================================================

/--
**Definition from Section 5.3**: X(u) = {φ} ∪ {¬a : a ∈ ALT ∧ a(u) = 0}

For any world u, X(u) is the set containing φ and the negations of all
alternatives that are FALSE at u.

"XALT,φ(u) = {φ} ∪ {¬a: a ∈ ALT ∧ a(u) = 0}"
-/
def X_of_world (u : World) : Set (Prop' World) :=
  {φ} ∪ {ψ | ∃ a ∈ ALT, ψ = ∼a ∧ ¬(a u)}

/--
Helper lemma: If ∼a = ∼a' then a = a' (negation is injective on propositions).
-/
theorem pneg_injective {a a' : Prop' World} (h : ∼a = ∼a') : a = a' := by
  funext w; apply eq_iff_iff.mpr; exact not_iff_not.mp (eq_iff_iff.mp (congrFun h w))

/--
**Key Equivalence** (from proof of Lemma 1):
For any two φ-worlds u and v: u <_ALT v ⟺ X(v) ⊊ X(u)

"The alternatives that u makes true are a proper subset of those v makes true"
is equivalent to "X(v) is a proper subset of X(u)".
-/
theorem ltALT_iff_X_ssubset (u v : World) (hu : φ u) (hv : φ v) :
    (u <[ALT] v) ↔ (X_of_world ALT φ v ⊂ X_of_world ALT φ u) := by
  -- Use Mathlib's ssubset_def: s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s
  rw [Set.ssubset_def]
  constructor
  · -- Forward: u <_ALT v → X(v) ⊆ X(u) ∧ ¬X(u) ⊆ X(v)
    intro ⟨hle, hne⟩
    constructor
    · -- X(v) ⊆ X(u)
      intro ψ hψv
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hψv ⊢
      rcases hψv with rfl | ⟨a, ha, rfl, hav⟩
      · left; rfl
      · right; exact ⟨a, ha, rfl, fun hau => hav (hle a ha hau)⟩
    · -- ¬X(u) ⊆ X(v)
      intro hsub
      apply hne
      intro a ha hav
      by_contra hau
      have hna_in_Xu : (∼a) ∈ X_of_world ALT φ u := by
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hau⟩
      have hna_in_Xv := hsub hna_in_Xu
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hna_in_Xv
      rcases hna_in_Xv with heq | ⟨a', ha', heq', hav'⟩
      · -- ∼a = φ: contradiction since φ v but (∼a) v means ¬(a v)
        have : (∼a) v := by rw [heq]; exact hv
        exact this hav
      · -- ∼a = ∼a' with ¬(a' v): need a = a'
        rw [pneg_injective heq'] at hav; exact hav' hav
  · -- Backward: X(v) ⊆ X(u) ∧ ¬X(u) ⊆ X(v) → u <_ALT v
    intro ⟨hsub, hnsub⟩
    constructor
    · -- u ≤_ALT v
      intro a ha hau
      by_contra hav
      have hna_in_Xv : (∼a) ∈ X_of_world ALT φ v := by
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hav⟩
      have hna_in_Xu := hsub hna_in_Xv
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hna_in_Xu
      rcases hna_in_Xu with heq | ⟨a', ha', heq', hau'⟩
      · have : (∼a) u := by rw [heq]; exact hu
        exact this hau
      · rw [pneg_injective heq'] at hau; exact hau' hau
    · -- ¬(v ≤_ALT u)
      intro hvu
      apply hnsub
      intro ψ hψu
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hψu ⊢
      rcases hψu with rfl | ⟨a, ha, rfl, hau'⟩
      · left; rfl
      · right; exact ⟨a, ha, rfl, fun hav => hau' (hvu a ha hav)⟩

/--
X(u) contains φ.
-/
theorem X_contains_phi (u : World) : φ ∈ X_of_world ALT φ u := by
  simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff]
  left; trivial

/--
Every element of X(u) is either φ or the negation of some alternative.
-/
theorem X_elements (u : World) (ψ : Prop' World) (hψ : ψ ∈ X_of_world ALT φ u) :
    ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a := by
  simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hψ
  rcases hψ with rfl | ⟨a, ha, rfl, _⟩
  · left; rfl
  · right; exact ⟨a, ha, rfl⟩

/--
u satisfies everything in X(u).
-/
theorem u_satisfies_X (u : World) (hu : φ u) : ∀ ψ ∈ X_of_world ALT φ u, ψ u := by
  intro ψ hψ
  simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hψ
  rcases hψ with rfl | ⟨a, ha, rfl, hau⟩
  · exact hu
  · simp only [pneg]; exact hau

/--
X(u) is (ALT, φ)-compatible when φ u holds.
-/
theorem X_is_compatible (u : World) (hu : φ u) : isCompatible ALT φ (X_of_world ALT φ u) := by
  constructor
  · exact X_contains_phi ALT φ u
  constructor
  · intro ψ hψ
    exact X_elements ALT φ u ψ hψ
  · exact ⟨u, u_satisfies_X ALT φ u hu⟩

/--
**Lemma 1** (Spector p.22):
For any φ-world u:
  u is a minimal φ-world relative to <_ALT ⟺ X(u) is an MC_(ALT,φ)-set.

This is the key connection between the two definitions of exhaustivity.

Note: We add the explicit hypothesis (hu : φ u) since both directions require it.
-/
theorem lemma1_minimal_iff_MCset (u : World) (hu : φ u) :
    isMinimal ALT φ u ↔ isMCSet ALT φ (X_of_world ALT φ u) := by
  constructor
  · -- Forward: u minimal → X(u) is MC-set
    intro ⟨_, hmin⟩
    constructor
    · -- X(u) is compatible
      exact X_is_compatible ALT φ u hu
    · -- X(u) is maximal: if E is compatible and X(u) ⊆ E then E ⊆ X(u)
      intro E hE_compat hXu_sub_E
      -- Suppose for contradiction that E ⊄ X(u), i.e., ∃ψ ∈ E, ψ ∉ X(u)
      by_contra hE_not_sub
      rw [Set.not_subset] at hE_not_sub
      obtain ⟨ψ, hψE, hψ_not_Xu⟩ := hE_not_sub
      -- ψ ∈ E, so ψ = φ or ψ = ∼a for some a ∈ ALT
      obtain ⟨hφE, hE_form, hE_cons⟩ := hE_compat
      have hψ_form := hE_form ψ hψE
      rcases hψ_form with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
      · -- ψ = φ: But φ ∈ X(u), contradiction
        rw [hψ_eq_φ] at hψ_not_Xu
        exact hψ_not_Xu (X_contains_phi ALT φ u)
      · -- ψ = ∼a for some a ∈ ALT
        rw [hψ_eq_na] at hψ_not_Xu hψE
        -- Since ∼a ∉ X(u), we have a(u) = 1 (otherwise ∼a would be in X(u))
        have hau : a u := by
          by_contra hau_not
          apply hψ_not_Xu
          simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          right; exact ⟨a, ha, rfl, hau_not⟩
        -- E is consistent, so there exists v satisfying everything in E
        obtain ⟨v, hv_sat⟩ := hE_cons
        -- v satisfies φ (since φ ∈ E)
        have hφv : φ v := hv_sat φ hφE
        -- v satisfies ∼a (since ∼a ∈ E)
        have hna_v : (∼a) v := hv_sat (∼a) hψE
        simp only [pneg] at hna_v
        -- So v <_ALT u
        have hv_lt_u : v <[ALT] u := by
          constructor
          · -- v ≤_ALT u: for any b ∈ ALT, if b(v) = 1 then b(u) = 1
            intro b hb hbv
            by_contra hbu
            have hnb_in_Xu : (∼b) ∈ X_of_world ALT φ u := by
              simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
              right; exact ⟨b, hb, rfl, hbu⟩
            have hnb_in_E := hXu_sub_E hnb_in_Xu
            have hnb_v : (∼b) v := hv_sat (∼b) hnb_in_E
            simp only [pneg] at hnb_v
            exact hnb_v hbv
          · -- ¬(u ≤_ALT v): a(u) = 1 but a(v) = 0
            intro huv
            exact hna_v (huv a ha hau)
        -- But this contradicts minimality of u
        exact hmin ⟨v, hφv, hv_lt_u⟩
  · -- Backward: X(u) is MC-set → u is minimal
    intro ⟨hX_compat, hX_max⟩
    constructor
    · exact hu
    · -- Show ¬∃v, φ v ∧ v <_ALT u
      intro ⟨v, hφv, hv_lt_u⟩
      -- By ltALT_iff_X_ssubset: v <_ALT u ↔ X(u) ⊂ X(v)
      -- (The theorem is stated as u <_ALT v ↔ X(v) ⊂ X(u), so we swap arguments)
      have hX_ssubset : X_of_world ALT φ u ⊂ X_of_world ALT φ v :=
        (ltALT_iff_X_ssubset ALT φ v u hφv hu).mp hv_lt_u
      -- X(v) is compatible
      have hXv_compat : isCompatible ALT φ (X_of_world ALT φ v) := X_is_compatible ALT φ v hφv
      -- X(u) ⊂ X(v) means X(u) ⊆ X(v) and ¬(X(v) ⊆ X(u))
      rw [Set.ssubset_def] at hX_ssubset
      obtain ⟨hXu_sub_Xv, hXv_not_sub_Xu⟩ := hX_ssubset
      -- By maximality of X(u): since X(v) is compatible and X(u) ⊆ X(v), we get X(v) ⊆ X(u)
      have hXv_sub_Xu := hX_max (X_of_world ALT φ v) hXv_compat hXu_sub_Xv
      -- But we have ¬(X(v) ⊆ X(u)) - contradiction!
      exact hXv_not_sub_Xu hXv_sub_Xu

-- ============================================================================
-- MC-SET EXISTENCE (consequences of Lemma 1)
-- ============================================================================

/--
**MC-set existence from minimal world existence** (Spector's approach):
When a minimal φ-world exists, an MC-set exists.

This follows directly from Lemma 1: if u is minimal, then X(u) is an MC-set.
-/
theorem exists_MCset_of_minimal (hmin : ∃ u, isMinimal ALT φ u) : ∃ E, isMCSet ALT φ E := by
  obtain ⟨u, hu_min⟩ := hmin
  exact ⟨X_of_world ALT φ u, (lemma1_minimal_iff_MCset ALT φ u hu_min.1).mp hu_min⟩

/--
**MC-set existence for finite ALT**: When ALT is finite and φ is satisfiable,
an MC-set exists.

This combines:
1. exists_minimal_of_finite: finite ALT + satisfiable φ → minimal world exists
2. exists_MCset_of_minimal: minimal world exists → MC-set exists
-/
theorem exists_MCset (hfin : Set.Finite ALT) (hsat : ∃ w, φ w) : ∃ E, isMCSet ALT φ E :=
  exists_MCset_of_minimal ALT φ (exists_minimal_of_finite ALT φ hfin hsat)

/--
Every element of IE is either φ or ∼a for some a ∈ ALT.
This follows from the structure of compatible sets.

Note: Requires finite ALT to ensure MC-sets exist.
-/
theorem IE_structure (hfin : Set.Finite ALT) (ψ : Prop' World) (hψ : ψ ∈ IE ALT φ)
    (hsat : ∃ w, φ w) : ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a := by
  -- Since an MC-set exists (by exists_MCset), ψ is in some MC-set
  obtain ⟨E, hE_mc⟩ := exists_MCset ALT φ hfin hsat
  have hψ_in_E := hψ E hE_mc
  -- By compatibility, elements of E are φ or ∼a
  exact hE_mc.1.2.1 ψ hψ_in_E

-- ============================================================================

/--
**Lemma 2** (Spector p.23, Core Lemma):
For every proposition φ, every set of alternatives ALT, and every world u,
  exh_mw(ALT, φ)(u) = 1 ⟺ there is an MC_(ALT,φ)-set X that u satisfies.

Equivalently: u is a minimal φ-world relative to <_ALT ⟺
              there is an MC_(ALT,φ)-set X that u satisfies.
-/
theorem lemma2_exhMW_iff_satisfies_MCset (u : World) :
    exhMW ALT φ u ↔ ∃ E, isMCSet ALT φ E ∧ (∀ ψ ∈ E, ψ u) := by
  constructor
  · -- Forward: exhMW u → ∃MC-set satisfied by u
    intro ⟨hu, hmin⟩
    -- By Lemma 1, X(u) is an MC-set
    have hXu_mc : isMCSet ALT φ (X_of_world ALT φ u) :=
      (lemma1_minimal_iff_MCset ALT φ u hu).mp ⟨hu, hmin⟩
    -- u satisfies X(u)
    have hu_sat_Xu := u_satisfies_X ALT φ u hu
    exact ⟨X_of_world ALT φ u, hXu_mc, hu_sat_Xu⟩
  · -- Backward: (∃MC-set satisfied by u) → exhMW u
    intro ⟨E, hE_mc, hu_sat_E⟩
    -- Extract components of MC-set (keeping hE_mc available)
    have hE_compat : isCompatible ALT φ E := hE_mc.1
    have hE_max : ∀ E', isCompatible ALT φ E' → E ⊆ E' → E' ⊆ E := hE_mc.2
    -- u satisfies E, so φ u (since φ ∈ E)
    have hφE : φ ∈ E := hE_compat.1
    have hE_form : ∀ ψ ∈ E, ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a := hE_compat.2.1
    have hu : φ u := hu_sat_E φ hφE
    -- We show u is minimal by showing X(u) = E
    -- First, E ⊆ X(u): every ψ ∈ E is in X(u)
    have hE_sub_Xu : E ⊆ X_of_world ALT φ u := by
      intro ψ hψE
      rcases hE_form ψ hψE with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
      · -- ψ = φ: φ ∈ X(u)
        rw [hψ_eq_φ]; exact X_contains_phi ALT φ u
      · -- ψ = ∼a: since u satisfies ψ, we have ¬(a u), so ∼a ∈ X(u)
        rw [hψ_eq_na]
        have hna_u : (∼a) u := hu_sat_E (∼a) (hψ_eq_na ▸ hψE)
        simp only [pneg] at hna_u
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hna_u⟩
    -- X(u) is compatible
    have hXu_compat : isCompatible ALT φ (X_of_world ALT φ u) := X_is_compatible ALT φ u hu
    -- By maximality of E: E ⊆ X(u) and X(u) compatible → X(u) ⊆ E
    have hXu_sub_E : X_of_world ALT φ u ⊆ E := hE_max (X_of_world ALT φ u) hXu_compat hE_sub_Xu
    -- So E = X(u)
    have hE_eq_Xu : E = X_of_world ALT φ u := Set.Subset.antisymm hE_sub_Xu hXu_sub_E
    -- X(u) is an MC-set (since E is and E = X(u))
    have hXu_mc : isMCSet ALT φ (X_of_world ALT φ u) := hE_eq_Xu ▸ hE_mc
    -- By Lemma 1, u is minimal
    exact (lemma1_minimal_iff_MCset ALT φ u hu).mpr hXu_mc

/--
**Lemma 3** (reformulation of Lemma 2):
  exh_mw(ALT, φ) = ⋁{⋀X : X is an MC_(ALT,φ)-set}

The minimal-worlds exhaustification is the disjunction of the conjunctions
of all MC-sets.
-/
theorem lemma3_exhMW_eq_disj_MCsets :
    exhMW ALT φ ≡ₚ (fun u => ∃ E, isMCSet ALT φ E ∧ (∀ ψ ∈ E, ψ u)) := by
  constructor
  · intro u hmw
    exact (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mp hmw
  · intro u hex
    exact (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mpr hex

-- ============================================================================
-- SECTION 3.4: Relationship between exh_mw and exh_ie (Spector p.12)
-- ============================================================================

/--
**Proposition 6** (Spector p.12): For any proposition φ with alternatives ALT,
exh_mw(ALT, φ) entails exh_ie(ALT, φ).

Proof idea: Any world satisfying exh_mw satisfies some MC-set, hence satisfies
the intersection of all MC-sets, hence satisfies IE.
-/
theorem prop6_exhMW_entails_exhIE : exhMW ALT φ ⊆ₚ exhIE ALT φ := by
  intro u hmw
  -- By Lemma 2, u satisfies some MC-set E
  obtain ⟨E, hmc, hsat⟩ := (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mp hmw
  -- Any ψ in IE is in every MC-set, including E
  intro ψ hψ_in_IE
  -- ψ ∈ IE means ψ is in every MC-set
  have hψ_in_E : ψ ∈ E := hψ_in_IE E hmc
  -- u satisfies E, so ψ u
  exact hsat ψ hψ_in_E

/--
**Proposition 7** (Spector p.12): For any ALT, any a ∈ ALT, and any proposition φ,
a is innocently excludable given ALT and φ if and only if exh_mw(ALT, φ) entails ¬a.

This characterizes innocent exclusion in terms of the minimal-worlds operator.
-/
theorem prop7_IE_iff_exhMW_entails_neg (a : Prop' World) (ha : a ∈ ALT) :
    isInnocentlyExcludable ALT φ a ↔ (exhMW ALT φ ⊆ₚ ∼a) := by
  constructor
  · -- Forward: a is IE → exh_mw ⊆ ∼a
    intro ⟨_, hna_in_IE⟩ u hmw
    -- By Lemma 2, u satisfies some MC-set E
    obtain ⟨E, hE_mc, hu_sat_E⟩ := (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mp hmw
    -- ∼a ∈ IE means ∼a is in every MC-set, including E
    have hna_in_E : (∼a) ∈ E := hna_in_IE E hE_mc
    -- u satisfies E, so u satisfies ∼a
    exact hu_sat_E (∼a) hna_in_E
  · -- Backward: exh_mw ⊆ ∼a → a is IE
    intro hmw_entails_na
    constructor
    · exact ha
    · -- Show ∼a ∈ IE, i.e., ∼a is in every MC-set
      intro E hE_mc
      -- E is consistent, so there exists v satisfying E
      have hE_compat := hE_mc.1
      obtain ⟨v, hv_sat_E⟩ := hE_compat.2.2
      -- v satisfies φ (since φ ∈ E)
      have hφv : φ v := hv_sat_E φ hE_compat.1
      -- v satisfies E (an MC-set), so by Lemma 2, exh_mw(v) holds
      have hmw_v : exhMW ALT φ v :=
        (lemma2_exhMW_iff_satisfies_MCset ALT φ v).mpr ⟨E, hE_mc, hv_sat_E⟩
      -- By hypothesis, exh_mw ⊆ ∼a, so (∼a) v
      have hna_v : (∼a) v := hmw_entails_na v hmw_v
      -- E ∪ {∼a} is consistent (witnessed by v)
      have hE_union_consistent : SetConsistent (E ∪ {∼a}) := by
        use v
        intro ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
        rcases hψ with hψE | rfl
        · exact hv_sat_E ψ hψE
        · exact hna_v
      -- E ∪ {∼a} is compatible (φ ∈ E ⊆ E ∪ {∼a}, and elements are φ or negations)
      have hE_union_compat : isCompatible ALT φ (E ∪ {∼a}) := by
        constructor
        · exact Set.mem_union_left {∼a} hE_compat.1
        constructor
        · intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hψE | rfl
          · exact hE_compat.2.1 ψ hψE
          · right; exact ⟨a, ha, rfl⟩
        · exact hE_union_consistent
      -- By maximality of E: E ⊆ E ∪ {∼a} and E ∪ {∼a} compatible → E ∪ {∼a} ⊆ E
      have hE_max := hE_mc.2
      have hsub : E ⊆ E ∪ {∼a} := Set.subset_union_left
      have hE_union_sub_E := hE_max (E ∪ {∼a}) hE_union_compat hsub
      -- So ∼a ∈ E
      have hna_in_union : (∼a) ∈ E ∪ {∼a} := Set.mem_union_right E rfl
      exact hE_union_sub_E hna_in_union

/--
**Corollary 8** (Spector p.12):
exh_ie(ALT, φ) = φ ∧ ⋀{¬a : a ∈ ALT ∧ exh_mw(ALT, φ) ⊆ ¬a}

This gives an alternative characterization of exh_ie in terms of exh_mw.

Note: The backward direction requires finite ALT for IE_structure.
-/
theorem corollary8 (hfin : Set.Finite ALT) :
    exhIE ALT φ ≡ₚ fun u => φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ₚ ∼a) → ¬(a u) := by
  constructor
  · -- exh_ie ⊆ (φ ∧ ⋀{¬a : exh_mw ⊆ ¬a})
    intro u hie
    constructor
    · -- φ u: φ ∈ IE (since φ is in every MC-set by compatibility)
      have hφ_in_IE : φ ∈ IE ALT φ := fun E hE_mc => hE_mc.1.1
      exact hie φ hφ_in_IE
    · -- For all a ∈ ALT, if exh_mw ⊆ ¬a then ¬(a u)
      intro a ha hmw_na
      have hIE_a : isInnocentlyExcludable ALT φ a :=
        (prop7_IE_iff_exhMW_entails_neg ALT φ a ha).mpr hmw_na
      have hna_u := hie (∼a) hIE_a.2
      simp only [pneg] at hna_u
      exact hna_u
  · -- (φ ∧ ⋀{¬a : exh_mw ⊆ ¬a}) ⊆ exh_ie
    -- We need to show: ∀ ψ ∈ IE, ψ u
    intro u ⟨hu, hall⟩ ψ hψ_IE
    -- Use IE_structure to determine ψ's form
    have hsat : ∃ w, φ w := ⟨u, hu⟩
    rcases IE_structure ALT φ hfin ψ hψ_IE hsat with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
    · -- Case: ψ = φ
      rw [hψ_eq_φ]; exact hu
    · -- Case: ψ = ∼a for some a ∈ ALT
      rw [hψ_eq_na]
      -- ∼a ∈ IE means a is innocently excludable
      have hna_IE : (∼a) ∈ IE ALT φ := hψ_eq_na ▸ hψ_IE
      have hIE_a : isInnocentlyExcludable ALT φ a := ⟨ha, hna_IE⟩
      -- By Prop 7, exh_mw ⊆ ∼a
      have hmw_na : exhMW ALT φ ⊆ₚ ∼a :=
        (prop7_IE_iff_exhMW_entails_neg ALT φ a ha).mp hIE_a
      -- By hypothesis hall, ¬(a u)
      have hna_u : ¬(a u) := hall a ha hmw_na
      -- So (∼a) u holds
      exact hna_u

-- ============================================================================
-- SECTION 3.5: THEOREM 9 - Main Result (Spector p.12-13)
-- ============================================================================

/--
**THEOREM 9** (Main Result, Spector p.12-13): For any φ and any ALT,
if ALT is closed under conjunction, then

  exh_mw(ALT, φ) = exh_ie(ALT, φ)

**Proof outline** (from Section 5.4):
Since exh_mw always entails exh_ie (Prop 6), we need to show exh_ie ⊆ exh_mw
when ALT is closed under conjunction.

Suppose exh_mw(φ)(u) = 0 but φ(u) = 1. We must show exh_ie(φ)(u) = 0.

Let A = {a ∈ ALT : a(u) = 1}. Since u is not minimal, every MC-set contains
a negation of some member of A. Consider ⋀A. Since every MC-set has a member
whose negation is in A, ⋀A is false in every world satisfying an MC-set.
Therefore ¬(⋀A) is consistent with every MC-set.

Since ALT is closed under conjunction, ⋀A ∈ ALT. Since ¬(⋀A) is consistent
with every MC-set and MC-sets are maximal, ¬(⋀A) ∈ IE. But (⋀A)(u) = 1,
so u fails to satisfy IE, hence exh_ie(φ)(u) = 0.
-/
theorem theorem9_main (hclosed : closedUnderConj ALT) :
    exhMW ALT φ ≡ₚ exhIE ALT φ := by
  constructor
  · -- exh_mw ⊆ exh_ie: This is Proposition 6
    exact prop6_exhMW_entails_exhIE ALT φ
  · -- exh_ie ⊆ exh_mw: Requires closure under conjunction
    intro u hie
    -- First, φ u holds (since φ ∈ IE by compatibility)
    have hφ_in_IE : φ ∈ IE ALT φ := fun E hE_mc => hE_mc.1.1
    have hu : φ u := hie φ hφ_in_IE
    -- We show u is minimal by contradiction
    -- Suppose u is not minimal: ∃v, φ v ∧ v <_ALT u
    by_contra hmw_not
    simp only [exhMW] at hmw_not
    push_neg at hmw_not
    obtain ⟨v, hφv, hv_lt_u⟩ := hmw_not hu
    -- Define A = {a ∈ ALT : a(u) = 1} (alternatives true at u)
    let A : Set (Prop' World) := {a ∈ ALT | a u}
    -- Since v <_ALT u, there exists a ∈ A with ¬(a v)
    -- (i.e., alternatives true at u but not all true at v)
    have hA_sub_ALT : A ⊆ ALT := fun a ha => ha.1
    -- ⋀A ∈ ALT by closure under conjunction
    have hconjA_in_ALT : (⋀ A) ∈ ALT := hclosed A hA_sub_ALT
    -- (⋀A)(u) = 1 since all a ∈ A are true at u
    have hconjA_u : (⋀ A) u := by
      intro a ha
      exact ha.2
    -- v <_ALT u means: alternatives true at v ⊂ alternatives true at u
    -- So there exists a ∈ ALT with a u but ¬(a v)
    -- Extract v ≤_ALT u and ¬(u ≤_ALT v) from v <_ALT u
    have hv_le_u : v ≤[ALT] u := hv_lt_u.1
    have hnot_u_le_v : ¬(u ≤[ALT] v) := hv_lt_u.2
    -- Need to unfold leALT before push_neg can work
    simp only [leALT] at hnot_u_le_v
    push_neg at hnot_u_le_v
    obtain ⟨a₀, ha₀_ALT, ha₀_u, hna₀_v⟩ := hnot_u_le_v
    -- a₀ ∈ A (since a₀ ∈ ALT and a₀ u)
    have ha₀_A : a₀ ∈ A := ⟨ha₀_ALT, ha₀_u⟩
    -- Since a₀ ∈ A and ¬(a₀ v), we have ¬((⋀A) v)
    have hconjA_not_v : ¬((⋀ A) v) := by
      intro hconj_v
      exact hna₀_v (hconj_v a₀ ha₀_A)
    -- ¬(⋀A) is true at v
    have hneg_conjA_v : (∼(⋀ A)) v := hconjA_not_v
    -- Now we need to show ¬(⋀A) ∈ IE
    -- For this, we show ¬(⋀A) is in every MC-set E
    have hneg_conjA_in_IE : (∼(⋀ A)) ∈ IE ALT φ := by
      intro E hE_mc
      -- E is an MC-set. By consistency, there exists w satisfying E.
      obtain ⟨w, hw_sat_E⟩ := hE_mc.1.2.2
      have hφw : φ w := hw_sat_E φ hE_mc.1.1
      have hmw_w : exhMW ALT φ w :=
        (lemma2_exhMW_iff_satisfies_MCset ALT φ w).mpr ⟨E, hE_mc, hw_sat_E⟩
      -- w is minimal, so ¬∃w', φ w' ∧ w' <_ALT w
      obtain ⟨_, hmin_w⟩ := hmw_w
      -- Key claim: ¬((⋀A) w)
      -- We prove this by contradiction.
      have hconjA_not_w : ¬((⋀ A) w) := by
        intro hconjA_w
        -- hconjA_w : (⋀A) w, i.e., ∀ a ∈ A, a w
        -- This means every alternative true at u is also true at w
        -- So u ≤_ALT w
        have hu_le_w : u ≤[ALT] w := by
          intro a ha hau
          -- a ∈ ALT and a u, so a ∈ A
          have ha_A : a ∈ A := ⟨ha, hau⟩
          exact hconjA_w a ha_A
        -- We have a₀ ∈ A (where a₀ u but ¬(a₀ v)), so a₀ w (by hconjA_w).
        have ha₀_w : a₀ w := hconjA_w a₀ ha₀_A
        -- So a₀ w but ¬(a₀ v), meaning ¬(w ≤_ALT v)
        have hnot_w_le_v : ¬(w ≤[ALT] v) := fun h => hna₀_v (h a₀ ha₀_ALT ha₀_w)
        -- v ≤_ALT u ≤_ALT w, so v ≤_ALT w (by transitivity)
        have hv_le_w : v ≤[ALT] w := leALT_trans ALT v u w hv_le_u hu_le_w
        -- v <_ALT w (since v ≤_ALT w and ¬(w ≤_ALT v))
        have hv_lt_w : v <[ALT] w := ⟨hv_le_w, hnot_w_le_v⟩
        -- But w is minimal, so no v' <_ALT w with φ v'
        exact hmin_w ⟨v, hφv, hv_lt_w⟩
      -- So (∼(⋀A)) w holds
      have hneg_conjA_w : (∼(⋀ A)) w := hconjA_not_w
      -- E ∪ {∼(⋀A)} is consistent (witnessed by w)
      have hE_union_consistent : SetConsistent (E ∪ {∼(⋀ A)}) := by
        use w
        intro ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
        rcases hψ with hψE | rfl
        · exact hw_sat_E ψ hψE
        · exact hneg_conjA_w
      -- E ∪ {∼(⋀A)} is compatible
      have hE_union_compat : isCompatible ALT φ (E ∪ {∼(⋀ A)}) := by
        constructor
        · exact Set.mem_union_left _ hE_mc.1.1
        constructor
        · intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hψE | rfl
          · exact hE_mc.1.2.1 ψ hψE
          · right; exact ⟨⋀ A, hconjA_in_ALT, rfl⟩
        · exact hE_union_consistent
      -- By maximality of E: E ⊆ E ∪ {∼(⋀A)} and E ∪ {∼(⋀A)} compatible → E ∪ {∼(⋀A)} ⊆ E
      have hE_max := hE_mc.2
      have hsub : E ⊆ E ∪ {∼(⋀ A)} := Set.subset_union_left
      have hE_union_sub_E := hE_max (E ∪ {∼(⋀ A)}) hE_union_compat hsub
      -- So ∼(⋀A) ∈ E
      have hneg_in_union : (∼(⋀ A)) ∈ E ∪ {∼(⋀ A)} := Set.mem_union_right E rfl
      exact hE_union_sub_E hneg_in_union
    -- So ¬(⋀A) ∈ IE. u satisfies IE, so u satisfies ¬(⋀A).
    have hneg_conjA_u : (∼(⋀ A)) u := hie (∼(⋀ A)) hneg_conjA_in_IE
    -- But (⋀A) u is true, contradiction
    simp only [pneg] at hneg_conjA_u
    exact hneg_conjA_u hconjA_u

-- ============================================================================
-- SECTION 3.6: Consequences (Spector p.13)
-- ============================================================================

-- Helper lemmas for Theorem 10

/--
De Morgan for big disjunction: ¬(⋁X) at w iff ∀ a ∈ X, ¬a at w
-/
lemma neg_bigDisj_iff (X : Set (Prop' World)) (w : World) :
    (∼(⋁ X)) w ↔ ∀ a ∈ X, (∼a) w := by
  simp only [pneg, bigDisj]
  push_neg
  rfl

/--
The disjunction closure contains the original set (via singleton disjunctions).
-/
lemma subset_disjClosure (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) :
    ALT ⊆ ALT' := by
  intro a ha
  rw [h]
  use {a}
  constructor
  · exact Set.singleton_subset_iff.mpr ha
  · ext w
    simp only [bigDisj, Set.mem_singleton_iff, exists_eq_left]

/--
Every element of the disjunction closure is a disjunction of ALT elements.
-/
lemma mem_disjClosure_iff (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) (p : Prop' World) :
    p ∈ ALT' ↔ ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X := by
  rw [h]; rfl

/--
**Key Lemma**: The preorder ≤_ALT is unchanged by disjunction closure.

If ALT' is the disjunction closure of ALT, then u ≤_{ALT} v ↔ u ≤_{ALT'} v.

Proof: If a disjunction (⋁X) is true at u where X ⊆ ALT, then some b ∈ X is true at u.
If u ≤_{ALT} v, then b is true at v, so (⋁X) is true at v.
-/
lemma leALT_disjClosure_eq (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) (u v : World) :
    leALT ALT u v ↔ leALT ALT' u v := by
  constructor
  · -- ALT ≤ implies ALT' ≤
    intro hle a ha_ALT' hau
    rw [h] at ha_ALT'
    obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
    -- a = ⋁X, a u means ∃ b ∈ X, b u
    rw [ha_eq] at hau ⊢
    simp only [bigDisj] at hau ⊢
    obtain ⟨b, hb_X, hbu⟩ := hau
    -- b ∈ ALT (since X ⊆ ALT)
    have hb_ALT : b ∈ ALT := hX_sub hb_X
    -- b v by hle
    have hbv : b v := hle b hb_ALT hbu
    exact ⟨b, hb_X, hbv⟩
  · -- ALT' ≤ implies ALT ≤
    intro hle a ha_ALT hau
    -- a ∈ ALT ⊆ ALT'
    have ha_ALT' : a ∈ ALT' := subset_disjClosure ALT ALT' h ha_ALT
    exact hle a ha_ALT' hau

/--
Corollary: The strict ordering <_ALT is unchanged by disjunction closure.
-/
lemma ltALT_disjClosure_eq (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) (u v : World) :
    ltALT ALT u v ↔ ltALT ALT' u v := by
  simp only [ltALT, leALT_disjClosure_eq ALT ALT' h]

/--
Corollary: exh_mw is unchanged by disjunction closure.
-/
lemma exhMW_disjClosure_eq (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) :
    exhMW ALT φ ≡ₚ exhMW ALT' φ := by
  constructor
  · intro u hmw
    simp only [exhMW] at hmw ⊢
    constructor
    · exact hmw.1
    · intro ⟨v, hφv, hlt_ALT'⟩
      apply hmw.2
      use v, hφv
      exact (ltALT_disjClosure_eq ALT ALT' h v u).mpr hlt_ALT'
  · intro u hmw'
    simp only [exhMW] at hmw' ⊢
    constructor
    · exact hmw'.1
    · intro ⟨v, hφv, hlt_ALT⟩
      apply hmw'.2
      use v, hφv
      exact (ltALT_disjClosure_eq ALT ALT' h v u).mp hlt_ALT

/--
**Theorem 10** (Spector p.13): For any proposition φ and any alternative set ALT,
exh_ie(ALT, φ) = exh_ie(ALT∨, φ)

where ALT∨ is the closure of ALT under disjunction.

"Closing the alternatives under disjunction (but crucially not conjunction)
is vacuous for exh_ie."

Proof strategy: Use Corollary 8's characterization:
  exhIE ALT φ ≡ₚ fun u => φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ₚ ∼a) → ¬(a u)

Since exhMW is unchanged by disjunction closure, we just need to check that
the extra conditions for ALT' (disjunctions) are implied by the ALT conditions.
-/
theorem theorem10_disj_closure_vacuous (hfin : Set.Finite ALT) (ALT' : Set (Prop' World))
    (h : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}) :
    exhIE ALT φ ≡ₚ exhIE ALT' φ := by
  -- First, note that exhMW ALT φ = exhMW ALT' φ
  have hmw_eq := exhMW_disjClosure_eq ALT φ ALT' h
  -- ALT' is also finite (it's a quotient of the finite powerset of ALT)
  -- For now, we use the fact that ALT' has same finiteness properties via ALT
  have hfin' : Set.Finite ALT' := by
    rw [h]
    -- The disjunction closure is the image of {X | X ⊆ ALT} under bigDisj
    -- {X | X ⊆ ALT} is finite by Finite.finite_subsets
    -- The image of a finite set is finite by Finite.image
    have hsubsets_fin : {X : Set (Prop' World) | X ⊆ ALT}.Finite := hfin.finite_subsets
    -- The disjunction closure is the image of subsets under bigDisj
    have heq : {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X} = bigDisj '' {X | X ⊆ ALT} := by
      ext p
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨X, hX_sub, rfl⟩
        exact ⟨X, hX_sub, rfl⟩
      · rintro ⟨X, hX_sub, rfl⟩
        exact ⟨X, hX_sub, rfl⟩
    rw [heq]
    exact hsubsets_fin.image bigDisj
  -- Use the Corollary 8 characterization
  have hc8_ALT := corollary8 ALT φ hfin
  have hc8_ALT' := corollary8 ALT' φ hfin'
  -- We need to show the two characterizations are equivalent
  constructor
  · -- exhIE ALT φ ⊆ exhIE ALT' φ
    intro u hie
    -- By Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ ∼a) → ¬(a u)
    have ⟨hφu, hALT_cond⟩ := hc8_ALT.1 u hie
    -- Need to show Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ ∼a) → ¬(a u)
    apply hc8_ALT'.2 u
    constructor
    · exact hφu
    · intro a ha_ALT' hexhMW'_sub_neg_a
      -- a ∈ ALT', so a = ⋁X for some X ⊆ ALT
      rw [h] at ha_ALT'
      obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
      -- exhMW ALT' φ ⊆ₚ ∼a means ∀ w, exhMW ALT' φ w → (∼a) w
      -- Since a = ⋁X, (∼a) = ∼(⋁X), and (∼(⋁X)) w ↔ ∀ b ∈ X, (∼b) w
      -- So exhMW ALT' φ ⊆ₚ ∼a means ∀ w, exhMW ALT' φ w → ∀ b ∈ X, ¬(b w)
      -- Since exhMW ALT φ = exhMW ALT' φ (by hmw_eq), this means:
      -- ∀ b ∈ X, exhMW ALT φ ⊆ₚ ∼b
      have hb_conds : ∀ b ∈ X, exhMW ALT φ ⊆ₚ ∼b := by
        intro b hb_X w hmw
        -- hmw : exhMW ALT φ w
        -- Need: (∼b) w, i.e., ¬(b w)
        have hmw' : exhMW ALT' φ w := hmw_eq.1 w hmw
        have : (∼a) w := hexhMW'_sub_neg_a w hmw'
        rw [ha_eq] at this
        exact (neg_bigDisj_iff X w).mp this b hb_X
      -- By hALT_cond, for each b ∈ X: ¬(b u)
      have hb_not_u : ∀ b ∈ X, ¬(b u) := fun b hb => hALT_cond b (hX_sub hb) (hb_conds b hb)
      -- Therefore ¬(a u) = ¬((⋁X) u)
      rw [ha_eq]
      simp only [bigDisj]
      push_neg
      exact hb_not_u
  · -- exhIE ALT' φ ⊆ exhIE ALT φ
    intro u hie'
    -- By Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ ∼a) → ¬(a u)
    have ⟨hφu, hALT'_cond⟩ := hc8_ALT'.1 u hie'
    -- Need to show Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ ∼a) → ¬(a u)
    apply hc8_ALT.2 u
    constructor
    · exact hφu
    · intro a ha_ALT hexhMW_sub_neg_a
      -- a ∈ ALT ⊆ ALT'
      have ha_ALT' : a ∈ ALT' := subset_disjClosure ALT ALT' h ha_ALT
      -- exhMW ALT φ ⊆ₚ ∼a, and exhMW ALT' φ = exhMW ALT φ
      have hexhMW'_sub : exhMW ALT' φ ⊆ₚ ∼a := by
        intro w hmw'
        have hmw : exhMW ALT φ w := hmw_eq.2 w hmw'
        exact hexhMW_sub_neg_a w hmw
      exact hALT'_cond a ha_ALT' hexhMW'_sub

/--
**Corollary 11** (Spector p.13): For any proposition φ and any alternative set ALT,
if ALT∨ = ALT∨∧, then exh_mw(ALT, φ) = exh_ie(ALT, φ).

"If the closure of ALT under disjunction is closed under conjunction,
applying exh_mw and exh_ie give rise to equivalent results."
-/
theorem corollary11 (hfin : Set.Finite ALT)
    (hcond : closedUnderConj {p | ∃ Y : Set (Prop' World), Y ⊆ ALT ∧ p = ⋁ Y}) :
    exhMW ALT φ ≡ₚ exhIE ALT φ := by
  -- Let ALT∨ be the disjunction closure of ALT
  let ALT' : Set (Prop' World) := {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X}
  have hALT' : ALT' = {p | ∃ X : Set (Prop' World), X ⊆ ALT ∧ p = ⋁ X} := rfl
  -- Step 1: exh_mw(ALT) = exh_mw(ALT∨) (disjunction closure is vacuous for exh_mw)
  have hmw_eq : exhMW ALT φ ≡ₚ exhMW ALT' φ := exhMW_disjClosure_eq ALT φ ALT' hALT'
  -- Step 2: exh_ie(ALT) = exh_ie(ALT∨) (Theorem 10)
  have hie_eq : exhIE ALT φ ≡ₚ exhIE ALT' φ := theorem10_disj_closure_vacuous ALT φ hfin ALT' hALT'
  -- Step 3: ALT∨ is closed under conjunction (by hypothesis)
  -- Therefore exh_mw(ALT∨) = exh_ie(ALT∨) (by Theorem 9)
  have h9 : exhMW ALT' φ ≡ₚ exhIE ALT' φ := theorem9_main ALT' φ hcond
  -- Combine: exh_mw(ALT) = exh_mw(ALT∨) = exh_ie(ALT∨) = exh_ie(ALT)
  constructor
  · -- exhMW ALT ⊆ exhIE ALT
    intro u hmw
    have hmw' := hmw_eq.1 u hmw
    have hie' := h9.1 u hmw'
    exact hie_eq.2 u hie'
  · -- exhIE ALT ⊆ exhMW ALT
    intro u hie
    have hie' := hie_eq.1 u hie
    have hmw' := h9.2 u hie'
    exact hmw_eq.2 u hmw'

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Core Definitions (Section 2.1)
- `Prop' World`: Propositions as predicates on worlds
- `leALT ALT u v`: u ≤_ALT v (u makes true ⊆ what v makes true)
- `ltALT ALT u v`: u <_ALT v (strict version)
- `exhMW ALT φ`: Minimal worlds exhaustivity operator
- `SetConsistent X`: X is satisfiable
- `isCompatible ALT φ E`: E is (ALT,φ)-compatible
- `isMCSet ALT φ E`: E is a maximal compatible set
- `IE ALT φ`: The set of propositions in every MC-set
- `isInnocentlyExcludable ALT φ a`: a is innocently excludable
- `exhIE ALT φ`: Innocent exclusion exhaustivity operator

### Key Lemmas (Section 5.3)
- `X_of_world ALT φ u`: The set {φ} ∪ {¬a : a ∈ ALT ∧ ¬(a u)}
- `lemma1_minimal_iff_MCset`: u minimal ⟺ X(u) is MC-set
- `lemma2_exhMW_iff_satisfies_MCset`: exh_mw(u) ⟺ ∃MC-set satisfied by u
- `lemma3_exhMW_eq_disj_MCsets`: exh_mw = ⋁{⋀X : X is MC-set}

### Main Results (Section 3)
- `prop6_exhMW_entails_exhIE`: exh_mw ⊆ₚ exh_ie (always)
- `prop7_IE_iff_exhMW_entails_neg`: Characterizes IE via exh_mw
- `corollary8`: exh_ie = φ ∧ ⋀{¬a : exh_mw ⊆ ¬a}
- `theorem9_main`: **Main theorem** - closed under ∧ → exh_mw ≡ₚ exh_ie
- `theorem10_disj_closure_vacuous`: Closure under ∨ is vacuous for exh_ie
- `corollary11`: If ALT∨ is closed under ∧, then exh_mw ≡ₚ exh_ie
- `exhMW_disjClosure_eq`: Closure under ∨ is vacuous for exh_mw

### Closure Properties
- `closedUnderConj ALT`: ALT is closed under conjunction
- `closedUnderDisj ALT`: ALT is closed under disjunction

## Proof Dependencies

```
lemma1_minimal_iff_MCset ←─┬─→ lemma2_exhMW_iff_satisfies_MCset
                          │
                          ↓
                    lemma3_exhMW_eq_disj_MCsets
                          │
              ┌───────────┼───────────┐
              ↓           ↓           ↓
     prop6_exhMW_entails  prop7_IE   corollary8
              │                       │
              └───────────┬───────────┘
                          ↓
                     theorem9_main (+ closedUnderConj)
                          │
              ┌───────────┼───────────┐
              ↓                       ↓
     theorem10_disj_closure    corollary11
```
-/

end NeoGricean.Exhaustivity
