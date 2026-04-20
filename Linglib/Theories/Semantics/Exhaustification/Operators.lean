/-
# Exhaustivity Operators: exh_mw and exh_ie
@cite{groenendijk-stokhof-1984} @cite{spector-2016} @cite{wang-2025} @cite{chierchia-2013}

Formalization of @cite{spector-2016} "Comparing exhaustivity operators"
Semantics & Pragmatics Volume 9, Article 11: 1–33.

## Paper Structure

Section 1: Introduction

Section 2: Background and definitions
- 2.1: Definitions 1-4 (≤_ALT, exh_mw, compatible sets, MC-sets, IE, exh_ie)
- 2.2: Illustrations

Section 3: Results to be proven
- 3.2: Proposition 1, Corollary 2 (relationship of three operators)
- 3.3: Proposition 3, Corollaries 4, 5 (facts about exh_mw)
- 3.4: Propositions 6, 7, Corollary 8 (relationship exh_mw ↔ exh_ie)
- 3.5: Theorem 9 (main result: closed under ∧ → equivalence)
- 3.6: Theorem 10, Corollary 11 (consequences)

Section 5: Proofs
- 5.3: Lemmas 1, 2, 3 (core lemmas connecting minimality to MC-sets)
- 5.4: Proof of Theorem 9

## Main Result

Theorem 9: When ALT is closed under conjunction, exh_mw = exh_ie

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset
import Linglib.Theories.Semantics.Entailment.Polarity

namespace Exhaustification

-- Re-export ContextPolarity from the consolidated polarity module
open Semantics.Entailment.Polarity (ContextPolarity)

-- SECTION 2.1: Definitions (Spector p.6-8)

/-
"In the context of this paper, the notion of world is identical to that of model."

"The proposition expressed by a sentence is the set of worlds in which this
sentence is true."

"To mean that a proposition φ is true (resp. false) in a world u... I write
φ(u) = 1 (resp. φ(u) = 0), rather than u ∈ φ (resp. u ∉ φ)."
-/

variable {World : Type*}

/-!
## Paper-mirroring notation

Spector writes `⊆`/`≡`/`¬`/`∧`/`⋀`/`⋁` for entailment, equivalence,
negation, conjunction, grand conjunction, and grand disjunction of
propositions (= sets of worlds). We bind subscripted/Spector-flavored
notations directly to mathlib primitives so paper-mirror code reads
naturally and the underlying API is just `Set` operations.
-/

@[inherit_doc Set.Subset]
notation:50 φ " ⊆ₚ " ψ => @Set.Subset _ φ ψ

/-- Mutual subset of two propositions; equivalent to `φ = ψ` for `Set`. -/
abbrev pequiv (φ ψ : Set World) : Prop := (φ ⊆ₚ ψ) ∧ (ψ ⊆ₚ φ)

@[inherit_doc pequiv]
notation:50 φ " ≡ₚ " ψ => pequiv φ ψ

@[inherit_doc Compl.compl]
prefix:75 "∼" => Compl.compl

@[inherit_doc Inter.inter]
infixl:65 " ∧ₚ " => Inter.inter

@[inherit_doc Set.sInter]
prefix:110 "⋀" => Set.sInter

@[inherit_doc Set.sUnion]
prefix:110 "⋁" => Set.sUnion

-- DEFINITION 1: The preorder ≤_ALT (Spector p.7)

variable (ALT : Set (Set World))

/--
Definition 1.1: Given a set of alternatives ALT, ≤_ALT is the preorder
over possible worlds defined as follows:

  u ≤_ALT v iff {a ∈ ALT : a(u) = 1} ⊆ {a ∈ ALT : a(v) = 1}

"u makes true a subset of the alternatives that v makes true"
-/
def leALT (u v : World) : Prop :=
  ∀ a ∈ ALT, a u → a v

/--
Definition 1.2: <_ALT is the strict preorder corresponding to ≤_ALT:

  u <_ALT v iff u ≤_ALT v ∧ ¬(v ≤_ALT u)

"The alternatives that u makes true are a proper subset of those that v makes true."
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

-- DEFINITION 2: exh_mw (Spector p.7)

variable (φ : Set World)

/--
Definition 2: Exhaustivity operator based on minimal worlds (exh_mw)

Given a set of propositions ALT and a proposition φ,

  exh_mw(ALT, φ) = {u : φ(u) = 1 ∧ ¬∃v(φ(v) = 1 ∧ v <_ALT u)}

Equivalently: exh_mw(ALT, φ) = φ ∩ {u : ¬∃v(φ(v) = 1 ∧ v <_ALT u)}

"The set of φ-worlds that are minimal relative to <_ALT"
-/
def exhMW : Set World :=
  λ u => φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)

/--
A world u is minimal among φ-worlds relative to <_ALT.
-/
def isMinimal (u : World) : Prop :=
  φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)

-- Basic property
theorem exhMW_entails : exhMW ALT φ ⊆ₚ φ :=
  λ _ ⟨h, _⟩ => h

-- DEFINITIONS 3: Compatible sets and MC-sets (Spector p.7)

/--
Definition 3.1: A set of propositions X is consistent if there exists
a world u in which every member of X is true.
-/
def SetConsistent (X : Set (Set World)) : Prop :=
  ∃ u, ∀ ψ ∈ X, ψ u

/--
Definition 3.2: Given a proposition φ and a set of alternatives ALT,
a set of propositions E is (ALT, φ)-compatible if and only if:
a) φ ∈ E
b) every member of E distinct from φ is the negation of a member of ALT
c) E is consistent
-/
def isCompatible (E : Set (Set World)) : Prop :=
  φ ∈ E ∧
  (∀ ψ ∈ E, ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a) ∧
  SetConsistent E

/--
Definition 3.3: MC_(ALT,φ)-sets

A set is maximal (ALT, φ)-compatible (MC_(ALT,φ)-set for short) if it is
(ALT, φ)-compatible and is not properly included in any other
(ALT, φ)-compatible set.
-/
def isMCSet (E : Set (Set World)) : Prop :=
  isCompatible ALT φ E ∧
  ∀ E', isCompatible ALT φ E' → E ⊆ E' → E' ⊆ E

/--
Definition 3.4: IE_(ALT,φ) = {ψ : ψ belongs to every MC_(ALT,φ)-set}

"Note that, somewhat counter-intuitively, the set IE_(ALT,φ) is not the set of
innocently excludable alternatives, but rather the set that contains φ and all
the negations of innocently excludable alternatives."
-/
def IE : Set (Set World) :=
  {ψ | ∀ E, isMCSet ALT φ E → ψ ∈ E}

/--
Definition 3.5: An alternative a is innocently excludable given ALT and φ
if and only if ¬a ∈ IE_(ALT,φ).
-/
def isInnocentlyExcludable (a : Set World) : Prop :=
  a ∈ ALT ∧ (∼a) ∈ IE ALT φ

-- DEFINITION 4: exh_ie (Spector p.8)

/--
Definition 4: Exhaustivity operator based on innocent exclusion (exh_ie)

  exh_ie(ALT, φ) = {u : ∀ψ(ψ ∈ IE_(ALT,φ) → ψ(u) = 1)}

Equivalently: exh_ie(ALT, φ) = ⋀ IE_(ALT,φ)

Equivalently: exh_ie(ALT, φ) = φ ∧ ⋀{¬a : a is a member of ALT that is
                                       innocently excludable given ALT and φ}
-/
def exhIE : Set World :=
  λ u => ∀ ψ ∈ IE ALT φ, ψ u

-- DEFINITION 5: Closure under conjunction/disjunction (Spector p.11)

/--
A set ALT is closed under conjunction if for any subset X of ALT,
⋀X ∈ ALT.

(Definition 5 in Spector)
-/
def closedUnderConj : Prop :=
  ∀ X : Set (Set World), X ⊆ ALT → (⋀ X) ∈ ALT

/--
A set ALT is closed under disjunction if for any subset X of ALT,
⋁X ∈ ALT.
-/
def closedUnderDisj : Prop :=
  ∀ X : Set (Set World), X ⊆ ALT → (⋁ X) ∈ ALT

-- MC-SET EXISTENCE (via Minimal Worlds - Spector's approach)

/-
## Spector's Approach to MC-set Existence

Following @cite{spector-2016} Section 5.3, we do not use Zorn's lemma.
Instead, MC-set existence follows from minimal world existence via Lemma 1:

  u is minimal ⟺ X(u) is an MC-set

So: minimal world exists → MC-set exists (just take X(u)).

For finite ALT, minimal worlds exist because:
- The preorder ≤_ALT has finite "height" (bounded by |ALT|)
- Any non-empty set has minimal elements under <_ALT

This is cleaner than Zorn and avoids chain-union consistency issues.
-/

/--
Well-foundedness for finite ALT: The strict ordering <_ALT is well-founded
when ALT is finite.

Proof idea: For any infinite descending chain w₁ >_ALT w₂ >_ALT...,
the set of true alternatives strictly increases at each step.
Since ALT is finite, this cannot continue indefinitely.
-/
theorem ltALT_wf_of_finite (hfin : Set.Finite ALT) : WellFounded (ltALT ALT) := by
  -- Key observation: w₁ <_ALT w₂ iff {a ∈ ALT | a w₁} ⊂ {a ∈ ALT | a w₂}
  -- Since ALT is finite, these are finite sets, and ⊂ on finite sets is well-founded.
  classical
  -- Define f(w) = {a ∈ ALT | a w} as a Finset
  let trueAt : World → Set (Set World) := λ w => {a ∈ ALT | a w}
  have hfin_trueAt : ∀ w, (trueAt w).Finite := λ w => hfin.subset λ a h => h.1
  let f : World → Finset (Set World) := λ w => (hfin_trueAt w).toFinset
  -- Membership characterization
  have hmem : ∀ w a, a ∈ f w ↔ a ∈ ALT ∧ a w := λ w a =>
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
  have hwf : WellFounded (λ (s t : Finset (Set World)) => s ⊂ t) := IsWellFounded.wf
  have : ltALT ALT = InvImage (λ s t => s ⊂ t) f := by
    ext u v
    exact hf_lt u v
  rw [this]
  exact InvImage.wf f hwf

/--
Existence of minimal worlds for finite ALT: When ALT is finite and φ is
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

-- SECTION 5.3: Key lemmas (Spector p.21-23)
-- These lemmas are essential for proving Propositions 6 and 7

/--
Definition from Section 5.3: X(u) = {φ} ∪ {¬a : a ∈ ALT ∧ a(u) = 0}

For any world u, X(u) is the set containing φ and the negations of all
alternatives that are false at u.

"XALT,φ(u) = {φ} ∪ {¬a: a ∈ ALT ∧ a(u) = 0}"
-/
def X_of_world (u : World) : Set (Set World) :=
  {φ} ∪ {ψ | ∃ a ∈ ALT, ψ = ∼a ∧ ¬(a u)}

/--
Helper lemma: if `∼a = ∼a'` then `a = a'` (negation is injective on
propositions). Direct use of mathlib's `compl_injective` for `Set`.
-/
theorem pneg_injective {a a' : Set World} (h : ∼a = ∼a') : a = a' :=
  compl_injective h

/--
Key equivalence (from proof of Lemma 1):
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
      · right; exact ⟨a, ha, rfl, λ hau => hav (hle a ha hau)⟩
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
      · right; exact ⟨a, ha, rfl, λ hav => hau' (hvu a ha hav)⟩

/--
X(u) contains φ.
-/
theorem X_contains_phi (u : World) : φ ∈ X_of_world ALT φ u := by
  simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff]
  left; trivial

/--
Every element of X(u) is either φ or the negation of some alternative.
-/
theorem X_elements (u : World) (ψ : Set World) (hψ : ψ ∈ X_of_world ALT φ u) :
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
  · exact hau

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
Lemma 1 (Spector p.22):
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
        rw [Set.mem_compl_iff] at hna_v
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
            rw [Set.mem_compl_iff] at hnb_v
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
      -- But we have ¬(X(v) ⊆ X(u)) - contradiction.
      exact hXv_not_sub_Xu hXv_sub_Xu

-- MC-SET EXISTENCE (consequences of Lemma 1)

/--
MC-set existence from minimal world existence (Spector's approach):
When a minimal φ-world exists, an MC-set exists.

This follows directly from Lemma 1: if u is minimal, then X(u) is an MC-set.
-/
theorem exists_MCset_of_minimal (hmin : ∃ u, isMinimal ALT φ u) : ∃ E, isMCSet ALT φ E := by
  obtain ⟨u, hu_min⟩ := hmin
  exact ⟨X_of_world ALT φ u, (lemma1_minimal_iff_MCset ALT φ u hu_min.1).mp hu_min⟩

/--
MC-set existence for finite ALT: When ALT is finite and φ is satisfiable,
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
theorem IE_structure (hfin : Set.Finite ALT) (ψ : Set World) (hψ : ψ ∈ IE ALT φ)
    (hsat : ∃ w, φ w) : ψ = φ ∨ ∃ a ∈ ALT, ψ = ∼a := by
  -- Since an MC-set exists (by exists_MCset), ψ is in some MC-set
  obtain ⟨E, hE_mc⟩ := exists_MCset ALT φ hfin hsat
  have hψ_in_E := hψ E hE_mc
  -- By compatibility, elements of E are φ or ∼a
  exact hE_mc.1.2.1 ψ hψ_in_E


/--
Lemma 2 (Spector p.23, Core Lemma):
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
        rw [Set.mem_compl_iff] at hna_u
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
Lemma 3 (reformulation of Lemma 2):
  exh_mw(ALT, φ) = ⋁{⋀X : X is an MC_(ALT,φ)-set}

The minimal-worlds exhaustification is the disjunction of the conjunctions
of all MC-sets.
-/
theorem lemma3_exhMW_eq_disj_MCsets :
    exhMW ALT φ ≡ₚ (λ u => ∃ E, isMCSet ALT φ E ∧ (∀ ψ ∈ E, ψ u)) := by
  constructor
  · intro u hmw
    exact (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mp hmw
  · intro u hex
    exact (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mpr hex

-- SECTION 3.4: Relationship between exh_mw and exh_ie (Spector p.12)

/--
Proposition 6 (Spector p.12): For any proposition φ with alternatives ALT,
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
Proposition 7 (Spector p.12): For any ALT, any a ∈ ALT, and any proposition φ,
a is innocently excludable given ALT and φ if and only if exh_mw(ALT, φ) entails ¬a.

This characterizes innocent exclusion in terms of the minimal-worlds operator.
-/
theorem prop7_IE_iff_exhMW_entails_neg (a : Set World) (ha : a ∈ ALT) :
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
      have hna_v : (∼a) v := hmw_entails_na hmw_v
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
Corollary 8 (Spector p.12):
exh_ie(ALT, φ) = φ ∧ ⋀{¬a : a ∈ ALT ∧ exh_mw(ALT, φ) ⊆ ¬a}

This gives an alternative characterization of exh_ie in terms of exh_mw.

Note: The backward direction requires finite ALT for IE_structure.
-/
theorem corollary8 (hfin : Set.Finite ALT) :
    exhIE ALT φ ≡ₚ λ u => φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ₚ ∼a) → ¬(a u) := by
  constructor
  · -- exh_ie ⊆ (φ ∧ ⋀{¬a : exh_mw ⊆ ¬a})
    intro u hie
    constructor
    · -- φ u: φ ∈ IE (since φ is in every MC-set by compatibility)
      have hφ_in_IE : φ ∈ IE ALT φ := λ E hE_mc => hE_mc.1.1
      exact hie φ hφ_in_IE
    · -- For all a ∈ ALT, if exh_mw ⊆ ¬a then ¬(a u)
      intro a ha hmw_na
      have hIE_a : isInnocentlyExcludable ALT φ a :=
        (prop7_IE_iff_exhMW_entails_neg ALT φ a ha).mpr hmw_na
      have hna_u := hie (∼a) hIE_a.2
      rw [Set.mem_compl_iff] at hna_u
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

-- SECTION 3.5: THEOREM 9 - Main Result (Spector p.12-13)

/--
Theorem 9 (Main Result, Spector p.12-13): For any φ and any ALT,
if ALT is closed under conjunction, then

  exh_mw(ALT, φ) = exh_ie(ALT, φ)

Proof outline (from Section 5.4):
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
    have hφ_in_IE : φ ∈ IE ALT φ := λ E hE_mc => hE_mc.1.1
    have hu : φ u := hie φ hφ_in_IE
    -- We show u is minimal by contradiction
    -- Suppose u is not minimal: ∃v, φ v ∧ v <_ALT u
    by_contra hmw_not
    change ¬ (φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)) at hmw_not
    push_neg at hmw_not
    obtain ⟨v, hφv, hv_lt_u⟩ := hmw_not hu
    -- Define A = {a ∈ ALT : a(u) = 1} (alternatives true at u)
    let A : Set (Set World) := {a ∈ ALT | a u}
    -- Since v <_ALT u, there exists a ∈ A with ¬(a v)
    -- (i.e., alternatives true at u but not all true at v)
    have hA_sub_ALT : A ⊆ ALT := λ a ha => ha.1
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
        have hnot_w_le_v : ¬(w ≤[ALT] v) := λ h => hna₀_v (h a₀ ha₀_ALT ha₀_w)
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
    rw [Set.mem_compl_iff] at hneg_conjA_u
    exact hneg_conjA_u hconjA_u

-- SECTION 3.6: Consequences (Spector p.13)

-- Helper lemmas for Theorem 10

/--
De Morgan for big disjunction: ¬(⋁X) at w iff ∀ a ∈ X, ¬a at w
-/
lemma neg_bigDisj_iff (X : Set (Set World)) (w : World) :
    (∼(⋁ X)) w ↔ ∀ a ∈ X, (∼a) w := by
  show ¬ (∃ a ∈ X, w ∈ a) ↔ ∀ a ∈ X, w ∉ a
  push Not
  rfl

/--
The disjunction closure contains the original set (via singleton disjunctions).
-/
lemma subset_disjClosure (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) :
    ALT ⊆ ALT' := by
  intro a ha
  rw [h]
  use {a}
  constructor
  · exact Set.singleton_subset_iff.mpr ha
  · ext w
    simp only [Set.mem_sUnion, Set.mem_singleton_iff, exists_eq_left]

/--
Every element of the disjunction closure is a disjunction of ALT elements.
-/
lemma mem_disjClosure_iff (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) (p : Set World) :
    p ∈ ALT' ↔ ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X := by
  rw [h]; rfl

/--
Key lemma: The preorder ≤_ALT is unchanged by disjunction closure.

If ALT' is the disjunction closure of ALT, then u ≤_{ALT} v ↔ u ≤_{ALT'} v.

Proof: If a disjunction (⋁X) is true at u where X ⊆ ALT, then some b ∈ X is true at u.
If u ≤_{ALT} v, then b is true at v, so (⋁X) is true at v.
-/
lemma leALT_disjClosure_eq (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) (u v : World) :
    leALT ALT u v ↔ leALT ALT' u v := by
  constructor
  · -- ALT ≤ implies ALT' ≤
    intro hle a ha_ALT' hau
    rw [h] at ha_ALT'
    obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
    -- a = ⋁X, a u means ∃ b ∈ X, b u
    rw [ha_eq] at hau ⊢
    simp only [Set.mem_sUnion] at hau ⊢
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
lemma ltALT_disjClosure_eq (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) (u v : World) :
    ltALT ALT u v ↔ ltALT ALT' u v := by
  simp only [ltALT, leALT_disjClosure_eq ALT ALT' h]

/--
Corollary: exh_mw is unchanged by disjunction closure.
-/
lemma exhMW_disjClosure_eq (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) :
    exhMW ALT φ ≡ₚ exhMW ALT' φ := by
  constructor
  · intro u hmw
    refine ⟨hmw.1, ?_⟩
    intro ⟨v, hφv, hlt_ALT'⟩
    apply hmw.2
    exact ⟨v, hφv, (ltALT_disjClosure_eq ALT ALT' h v u).mpr hlt_ALT'⟩
  · intro u hmw'
    refine ⟨hmw'.1, ?_⟩
    intro ⟨v, hφv, hlt_ALT⟩
    apply hmw'.2
    exact ⟨v, hφv, (ltALT_disjClosure_eq ALT ALT' h v u).mp hlt_ALT⟩

/--
Theorem 10 (Spector p.13): For any proposition φ and any alternative set ALT,
exh_ie(ALT, φ) = exh_ie(ALT∨, φ)

where ALT∨ is the closure of ALT under disjunction.

"Closing the alternatives under disjunction (but crucially not conjunction)
is vacuous for exh_ie."

Proof strategy: Use Corollary 8's characterization:
  exhIE ALT φ ≡ₚ λ u => φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ₚ ∼a) → ¬(a u)

Since exhMW is unchanged by disjunction closure, we just need to check that
the extra conditions for ALT' (disjunctions) are implied by the ALT conditions.
-/
theorem theorem10_disj_closure_vacuous (hfin : Set.Finite ALT) (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}) :
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
    have hsubsets_fin : {X : Set (Set World) | X ⊆ ALT}.Finite := hfin.finite_subsets
    -- The disjunction closure is the image of subsets under bigDisj
    have heq : {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}
        = Set.sUnion '' {X | X ⊆ ALT} := by
      ext p
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨X, hX_sub, rfl⟩
        exact ⟨X, hX_sub, rfl⟩
      · rintro ⟨X, hX_sub, rfl⟩
        exact ⟨X, hX_sub, rfl⟩
    rw [heq]
    exact hsubsets_fin.image Set.sUnion
  -- Use the Corollary 8 characterization
  have hc8_ALT := corollary8 ALT φ hfin
  have hc8_ALT' := corollary8 ALT' φ hfin'
  -- We need to show the two characterizations are equivalent
  constructor
  · -- exhIE ALT φ ⊆ exhIE ALT' φ
    intro u hie
    -- By Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ ∼a) → ¬(a u)
    have ⟨hφu, hALT_cond⟩ := hc8_ALT.1 hie
    -- Need to show Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ ∼a) → ¬(a u)
    refine hc8_ALT'.2 ⟨hφu, ?_⟩
    intro a ha_ALT' hexhMW'_sub_neg_a
    -- a ∈ ALT', so a = ⋁X for some X ⊆ ALT
    rw [h] at ha_ALT'
    obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
    have hb_conds : ∀ b ∈ X, exhMW ALT φ ⊆ₚ ∼b := by
      intro b hb_X w hmw
      have hmw' : exhMW ALT' φ w := hmw_eq.1 hmw
      have : (∼a) w := hexhMW'_sub_neg_a hmw'
      rw [ha_eq] at this
      exact (neg_bigDisj_iff X w).mp this b hb_X
    have hb_not_u : ∀ b ∈ X, ¬(b u) := λ b hb => hALT_cond b (hX_sub hb) (hb_conds b hb)
    rw [ha_eq]
    show ¬ ∃ b ∈ X, u ∈ b
    push Not
    exact hb_not_u
  · -- exhIE ALT' φ ⊆ exhIE ALT φ
    intro u hie'
    -- By Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ ∼a) → ¬(a u)
    have ⟨hφu, hALT'_cond⟩ := hc8_ALT'.1 hie'
    -- Need to show Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ ∼a) → ¬(a u)
    refine hc8_ALT.2 ⟨hφu, ?_⟩
    intro a ha_ALT hexhMW_sub_neg_a
    -- a ∈ ALT ⊆ ALT'
    have ha_ALT' : a ∈ ALT' := subset_disjClosure ALT ALT' h ha_ALT
    -- exhMW ALT φ ⊆ₚ ∼a, and exhMW ALT' φ = exhMW ALT φ
    have hexhMW'_sub : exhMW ALT' φ ⊆ₚ ∼a := by
      intro w hmw'
      have hmw : exhMW ALT φ w := hmw_eq.2 hmw'
      exact hexhMW_sub_neg_a hmw
    exact hALT'_cond a ha_ALT' hexhMW'_sub

/--
Corollary 11 (Spector p.13): For any proposition φ and any alternative set ALT,
if ALT∨ = ALT∨∧, then exh_mw(ALT, φ) = exh_ie(ALT, φ).

"If the closure of ALT under disjunction is closed under conjunction,
applying exh_mw and exh_ie give rise to equivalent results."
-/
theorem corollary11 (hfin : Set.Finite ALT)
    (hcond : closedUnderConj {p | ∃ Y : Set (Set World), Y ⊆ ALT ∧ p = ⋁ Y}) :
    exhMW ALT φ ≡ₚ exhIE ALT φ := by
  -- Let ALT∨ be the disjunction closure of ALT
  let ALT' : Set (Set World) := {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X}
  have hALT' : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋁ X} := rfl
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
    have hmw' := hmw_eq.1 hmw
    have hie' := h9.1 hmw'
    exact hie_eq.2 hie'
  · -- exhIE ALT ⊆ exhMW ALT
    intro u hie
    have hie' := hie_eq.1 hie
    have hmw' := h9.2 hie'
    exact hmw_eq.2 hmw'



-- SECTION 7: MAXIMIZE STRENGTH PRINCIPLE (@cite{chierchia-2013})

/-!
## Maximize Strength

@cite{chierchia-2013} "Logic in Grammar" proposes that scalar implicature computation
follows the Maximize Strength principle:

> "Don't add an implicature if it leads to weakening, unless you have to"

This explains the distribution of scalar implicatures across contexts:

| Context | Polarity | Effect of SI | SI computed? |
|---------|----------|--------------|--------------|
| Upward Entailing | UE | Strengthens | ✓ Yes |
| Downward Entailing | DE | Weakens | ✗ No |

### Examples

UE context (positive sentence):
- "John saw some students" → "John saw some but not all students"
- SI strengthens: original entails exhaustified

DE context (antecedent of conditional):
- "If John saw some students, he's happy" → No SI
- SI would weaken: exhaustified entails original
- Adding "not all" to antecedent makes the conditional weaker

### Connection to Exhaustification

Maximize Strength captures when `exh` is applied:
- In UE contexts: `exh(φ) ⊆ₚ φ` (strengthening) → apply exh
- In DE contexts: `φ ⊆ₚ exh(φ)` (weakening in overall sentence) → don't apply exh

### Theoretical Significance

This principle unifies several phenomena:
1. Why SIs are optional in positive contexts (strengthening available)
2. Why SIs disappear in DE contexts (would weaken)
3. Why NPIs need DE contexts (exhaustification contradicts in UE)
4. Why FCIs have complex distribution (modal rescue)
-/

-- ----------------------------------------------------------------------------
-- 7.1: Context Polarity
-- ----------------------------------------------------------------------------

-- ContextPolarity is imported from Semantics.Entailment.Polarity
-- with constructors: .upward, .downward, .nonMonotonic

/--
A context is a function that embeds a proposition into a larger structure.
-/
def Context (World : Type*) := Set World → Set World

/--
A context is upward entailing (monotone) if φ ⊆ ψ implies C(φ) ⊆ C(ψ).
-/
def IsUpwardEntailing (C : Context World) : Prop :=
  ∀ φ ψ : Set World, (φ ⊆ₚ ψ) → (C φ ⊆ₚ C ψ)

/--
A context is downward entailing (antitone) if φ ⊆ ψ implies C(ψ) ⊆ C(φ).
-/
def IsDownwardEntailing (C : Context World) : Prop :=
  ∀ φ ψ : Set World, (φ ⊆ₚ ψ) → (C ψ ⊆ₚ C φ)

-- ----------------------------------------------------------------------------
-- 7.2: Maximize Strength Theorems
-- ----------------------------------------------------------------------------

/--
In a UE context, exhaustification strengthens the embedded proposition.
That is: C(exh(φ)) ⊆ C(φ) when C is UE and exh(φ) ⊆ φ.
-/
theorem exh_in_ue_strengthens (C : Context World) (hUE : IsUpwardEntailing C)
    (φ : Set World) (exhφ : Set World) (hExhStronger : exhφ ⊆ₚ φ) :
    C exhφ ⊆ₚ C φ :=
  hUE exhφ φ hExhStronger

/--
In a DE context, exhaustification weakens the overall sentence.
That is: C(φ) ⊆ C(exh(φ)) when C is DE and exh(φ) ⊆ φ.
-/
theorem exh_in_de_weakens (C : Context World) (hDE : IsDownwardEntailing C)
    (φ : Set World) (exhφ : Set World) (hExhStronger : exhφ ⊆ₚ φ) :
    C φ ⊆ₚ C exhφ :=
  hDE exhφ φ hExhStronger

/--
The identity context is upward entailing.
-/
theorem id_context_is_UE : IsUpwardEntailing (id : Context World) := by
  intro φ ψ h
  exact h

/--
Negation context is downward entailing.
-/
theorem neg_context_is_DE :
    IsDownwardEntailing ((Compl.compl : Set World → Set World) : Context World) := by
  intro φ ψ h w hNotψ hφ
  exact hNotψ (h hφ)

-- ----------------------------------------------------------------------------
-- 7.3: Maximize Strength Decision Procedure
-- ----------------------------------------------------------------------------

/--
Maximize Strength: compute SI iff context is UE (strengthening).

This is the core principle: only apply exhaustification when it results
in strengthening of the overall assertion.
-/
def maximizeStrength (φ : Set World) (exhφ : Set World)
    (polarity : ContextPolarity) : Set World :=
  match polarity with
  | .upward => exhφ        -- Exhaustify: strengthens
  | .downward => φ         -- Don't exhaustify: would weaken
  | .nonMonotonic => φ     -- Conservative: don't exhaustify

/--
Maximize Strength with explicit context.
-/
def maximizeStrengthCtx (C : Context World) (φ : Set World) (exhφ : Set World)
    (hUE : Bool) : Set World :=
  if hUE then C exhφ else C φ

-- ----------------------------------------------------------------------------
-- 7.4: Connection to exh_mw
-- ----------------------------------------------------------------------------

/--
exh_mw strengthens the proposition by conjoining negations of excludable alternatives.
-/
theorem exhMW_strengthens (ALT : Set (Set World)) (φ : Set World) :
    exhMW ALT φ ⊆ₚ φ := by
  intro w ⟨hφ, _⟩
  exact hφ

/--
In a UE context, exh_mw results in a stronger overall sentence.
-/
theorem exhMW_strengthens_in_UE (C : Context World) (hUE : IsUpwardEntailing C)
    (ALT : Set (Set World)) (φ : Set World) :
    C (exhMW ALT φ) ⊆ₚ C φ :=
  exh_in_ue_strengthens C hUE φ (exhMW ALT φ) (exhMW_strengthens ALT φ)

/--
In a DE context, applying exh_mw weakens the overall sentence.
Hence, Maximize Strength predicts no scalar implicature in DE contexts.
-/
theorem exhMW_weakens_in_DE (C : Context World) (hDE : IsDownwardEntailing C)
    (ALT : Set (Set World)) (φ : Set World) :
    C φ ⊆ₚ C (exhMW ALT φ) :=
  exh_in_de_weakens C hDE φ (exhMW ALT φ) (exhMW_strengthens ALT φ)

-- ----------------------------------------------------------------------------
-- 7.5: Examples
-- ----------------------------------------------------------------------------

/-!
### Example: "Some students passed" in UE context

Positive sentence: C = id (identity context)
- φ = "some students passed"
- exh(φ) = "some but not all students passed"
- C(exh(φ)) ⊆ C(φ) ✓ Strengthens
- Prediction: SI computed → "not all"

### Example: "If some students passed,..." (antecedent)

Conditional antecedent: C = (λp. p → q) is DE
- φ = "some students passed"
- exh(φ) = "some but not all students passed"
- C(φ) ⊆ C(exh(φ)) - SI would weaken the conditional
- Prediction: no SI in antecedent

This matches empirical observations:
- "If some students passed, the teacher is happy" does not implicate
  "If some but not all students passed..."
-/


-- ============================================================================
-- SECTION 7: exh_mx — Per-MC-Set Exhaustification (@cite{wang-2025})
-- ============================================================================

/-!
## exh_mx: The Third Exhaustification Operator

@cite{wang-2025} "Presupposition, Competition, and Coherence" introduces `exh_mx`,
which yields one exhaustified proposition per maximal consistent subset (MC-set),
rather than intersecting all MC-sets (as `exh_ie` does).

When all MC-sets agree (i.e., ALT is closed under ∧), `exh_mx` = `exh_ie` = `exh_mw`
(by Theorem 9). When MC-sets diverge, `exh_mx` produces *multiple readings*—one
per MC-set—capturing ambiguity in presuppositional alternatives.

### Key relationships:
- `exh_mw` = ⋁{⋀E : E is MC-set} (Lemma 3 above)
- `exh_ie` = ⋀(⋂ all MC-sets) (Definition 4 above)
- `exh_mx` = one reading per MC-set: for each E, ⋀E

-/

section ExhMX

variable {World : Type*} (ALT : Set (Set World)) (φ : Set World)

/--
An `exh_mx` reading for a specific MC-set E: the conjunction of E.

Unlike `exh_ie` (which is the conjunction of the *intersection* of all MC-sets),
`exh_mx` gives one reading per MC-set. When MC-sets disagree about which
alternatives to exclude, `exh_mx` captures the resulting ambiguity.

@cite{wang-2025} Ch4: "exh_mx(ALT, φ, w) = φ(w) ∧ ∀q ∈ Max(φ, ALT)[¬q(w)]"
where Max is a specific maximal consistent subset.
-/
def exhMXReading (E : Set (Set World)) : Set World :=
  λ u => ∀ ψ ∈ E, ψ u

/--
The set of all `exh_mx` readings: one per MC-set.

This is the *set of propositions*, not a single proposition.
Each reading corresponds to a different way of consistently excluding alternatives.
-/
def exhMXReadings : Set (Set World) :=
  {p | ∃ E, isMCSet ALT φ E ∧ p = exhMXReading E}

/--
The conjunction of all `exh_mx` readings entails `exh_ie`.

Together with `exhMXReading_entails_exhIE` (each reading entails `exh_ie`),
this gives the full picture of how `exh_ie` relates to `exh_mx` readings:

    ⋀(readings) ⊆ₚ each reading ⊆ₚ exh_ie

Note: the REVERSE direction (exhIE ⊆ₚ ⋀ readings) does NOT hold in general.
When MC-sets diverge, an MC-set E may contain alternatives ψ ∉ IE.
Satisfying all of IE (exhIE) does not guarantee satisfying all of E
(a specific reading), because E may require excluding alternatives
that other MC-sets include.
-/
theorem bigConj_exhMX_entails_exhIE (hne : ∃ E, isMCSet ALT φ E) :
    (λ u => ∀ p ∈ exhMXReadings ALT φ, p u) ⊆ₚ exhIE ALT φ := by
  intro u hall ψ hψIE
  obtain ⟨E, hmc⟩ := hne
  have hψE : ψ ∈ E := hψIE E hmc
  have hreading : exhMXReading E ∈ exhMXReadings ALT φ := ⟨E, hmc, rfl⟩
  exact hall (exhMXReading E) hreading ψ hψE

/--
Every `exh_mx` reading entails `exh_ie`.

Since `exh_ie` is the intersection of all MC-sets and each `exh_mx` reading
is a single MC-set, each reading is at least as strong as `exh_ie`.
-/
theorem exhMXReading_entails_exhIE (E : Set (Set World)) (hmc : isMCSet ALT φ E) :
    exhMXReading E ⊆ₚ exhIE ALT φ := by
  intro u hread ψ hψIE
  exact hread ψ (hψIE E hmc)

/--
`exh_mw` is the disjunction of all `exh_mx` readings (Lemma 3 restated).

This connects all three operators:
- `exh_mw` = ⋁(exh_mx readings) (disjunction — some MC-set is satisfied)
- `exh_ie` = ⋀(exh_mx readings) (conjunction — all MC-sets are satisfied)
- When there is exactly one MC-set: `exh_mw` = `exh_ie` = `exh_mx`
-/
theorem exhMW_eq_bigDisj_exhMX :
    exhMW ALT φ ≡ₚ (λ u => ∃ p ∈ exhMXReadings ALT φ, p u) := by
  constructor
  · intro u hmw
    obtain ⟨E, hmc, hsat⟩ := (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mp hmw
    exact ⟨exhMXReading E, ⟨E, hmc, rfl⟩, hsat⟩
  · intro u hex
    obtain ⟨p, hp, hpu⟩ := hex
    obtain ⟨E, hmc, rfl⟩ := hp
    exact (lemma2_exhMW_iff_satisfies_MCset ALT φ u).mpr ⟨E, hmc, hpu⟩

/--
Under conjunction closure, all three exhaustification operators coincide:
`exh_ie` = `exh_mw` = ⋁(`exh_mx` readings).

This does NOT mean there is only one reading. When MC-sets diverge,
individual readings remain distinct — but their disjunction equals `exh_ie`.

Combines Theorem 9 (`exhMW ≡ₚ exhIE`) with Lemma 3 (`exhMW ≡ₚ ⋁ readings`).
-/
theorem exhOperators_coincide_under_closure (hclosed : closedUnderConj ALT) :
    exhIE ALT φ ≡ₚ (λ u => ∃ p ∈ exhMXReadings ALT φ, p u) := by
  have h9 := theorem9_main ALT φ hclosed
  have hbig := exhMW_eq_bigDisj_exhMX ALT φ
  exact ⟨λ _u hie => hbig.1 (h9.2 hie), λ _u hex => h9.1 (hbig.2 hex)⟩

/--
When there is a unique MC-set, all `exh_mx` readings are equivalent.

MC-set uniqueness is a stronger condition than conjunction closure alone.
It holds when ALT has additional structural properties (e.g., symmetric
closure under both conjunction and disjunction, per @cite{spector-2016}).
-/
theorem exhMX_unique_when_unique_MCset
    {p q : Set World}
    (hp : p ∈ exhMXReadings ALT φ) (hq : q ∈ exhMXReadings ALT φ)
    (huniq : ∀ E₁ E₂, isMCSet ALT φ E₁ → isMCSet ALT φ E₂ → E₁ = E₂) :
    p ≡ₚ q := by
  obtain ⟨E₁, hmc₁, rfl⟩ := hp
  obtain ⟨E₂, hmc₂, rfl⟩ := hq
  rw [huniq E₁ E₂ hmc₁ hmc₂]
  exact ⟨λ _ h => h, λ _ h => h⟩

end ExhMX


-- ============================================================================
-- SECTION 8: FLAT Operator (@cite{wang-2025}, @cite{groenendijk-stokhof-1984})
-- ============================================================================

/-!
## FLAT: Collapsing Nested Alternative Sets

@cite{wang-2025} Ch4 defines the FLAT operator for collapsing nested alternative sets
(sets of sets of propositions) into a flat set via cross-product conjunction.

Given S = {A₁, A₂,...} where each Aᵢ is a set of propositions,
FLAT(S) = {⋀{f(Aᵢ) | i} | f is a choice function picking one from each Aᵢ}

This is proved equivalent to @cite{groenendijk-stokhof-1984} pointwise
answerhood (Ans_PW).

-/

section FlatOperator

variable {World : Type*}

/--
FLAT: Collapse a family of alternative sets into a flat set via cross-product
conjunction. Each element of FLAT(S) is the conjunction of one choice from
each alternative set in S.

@cite{wang-2025} Ch4: FLAT({A₁,...,Aₙ}) = {a₁ ∧... ∧ aₙ | aᵢ ∈ Aᵢ}

Uses a total choice function restricted to S to avoid dependent types.
-/
def flat (S : Set (Set (Set World))) : Set (Set World) :=
  {p | ∃ (f : Set (Set World) → Set World),
    (∀ A ∈ S, f A ∈ A) ∧
    p = λ u => ∀ A ∈ S, f A u}

/--
FLAT of a singleton is the set itself.
-/
theorem flat_singleton (A : Set (Set World)) :
    flat {A} = A := by
  ext p; constructor
  · rintro ⟨f, hf, heq⟩
    have key : p = f A := by
      rw [heq]; funext u; apply propext; constructor
      · intro h; exact h A rfl
      · intro h B hB; rw [Set.mem_singleton_iff.mp hB]; exact h
    rw [key]; exact hf A rfl
  · intro hp
    refine ⟨λ _ => p, λ B hB => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.mp hB]; exact hp
    · funext u; apply propext; constructor
      · intro h B _; exact h
      · intro h; exact h A rfl

/--
FLAT of the empty family is the tautology set.
-/
theorem flat_empty : flat (∅ : Set (Set (Set World))) = {λ _ => True} := by
  ext p; constructor
  · rintro ⟨_, -, rfl⟩
    show _ = λ _ => True
    funext u; apply propext; constructor
    · intro _ ; trivial
    · intro _ B hB; exact absurd hB (by simp)
  · intro (hp : p = λ _ => True)
    refine ⟨λ _ _ => True, λ B hB => ?_, ?_⟩
    · simp at hB
    · rw [hp]; funext u; apply propext; constructor
      · intro _ B hB; simp at hB
      · intro _; trivial

end FlatOperator

-- ============================================================================
-- Innocent Inclusion (II)
-- ============================================================================

/-!
## Innocent Inclusion

From @cite{bar-lev-fox-2020}, Definition (51):

> II(p, C) = ∩{C'' ⊆ C : C'' is maximal s.t.
> {r : r ∈ C''} ∪ {p} ∪ {¬q : q ∈ IE(p,C)} is consistent}

After computing IE, find all maximal subsets of alternatives that
can consistently be assigned TRUE (given that IE alternatives are false).
An alternative is innocently includable iff it appears in ALL such maximal sets.
-/

variable {World : Type*}
variable (ALT : Set (Set World))
variable (φ : Set World)

/--
**Definition (II-compatible set)**: A set of propositions R is (ALT, φ, IE)-compatible
for inclusion if:
a) R ⊆ ALT
b) {r : r ∈ R} ∪ {φ} ∪ {¬q : q ∈ IE(ALT, φ)} is consistent
-/
def isIICompatible (R : Set (Set World)) : Prop :=
  R ⊆ ALT ∧
  SetConsistent ({φ} ∪ {ψ | ∃ q, isInnocentlyExcludable ALT φ q ∧ ψ = ∼q} ∪ R)

/--
**Definition (MI-set)**: Maximal II-compatible set.
A set R is maximally (ALT, φ, IE)-compatible if it is II-compatible
and not properly included in any other II-compatible set.
-/
def isMISet (R : Set (Set World)) : Prop :=
  isIICompatible ALT φ R ∧
  ∀ R', isIICompatible ALT φ R' → R ⊆ R' → R' ⊆ R

/--
**Definition (II)**: II(ALT, φ) = {r ∈ ALT : r belongs to every MI-set}

An alternative r is innocently includable iff it belongs to every MI-set.
-/
def II : Set (Set World) :=
  {r ∈ ALT | ∀ R, isMISet ALT φ R → r ∈ R}

/--
An alternative a is innocently includable given ALT and φ
if and only if a ∈ II(ALT, φ).
-/
def isInnocentlyIncludable (a : Set World) : Prop :=
  a ∈ II ALT φ

/--
**Definition (Exh^{IE+II})**: The exhaustivity operator with both IE and II.

  ⟦Exh^{IE+II}⟧(ALT)(φ)(w) ⇔
    φ(w) ∧
    ∀q ∈ IE(ALT,φ)[¬q(w)] ∧ -- exclude IE alternatives
    ∀r ∈ II(ALT,φ)[r(w)] -- include II alternatives

This is Bar-Lev & Fox's key operator that derives free choice.
-/
def exhIEII : Set World := λ w =>
  φ w ∧
  (∀ q, isInnocentlyExcludable ALT φ q → ¬q w) ∧
  (∀ r, isInnocentlyIncludable ALT φ r → r w)

/-!
## Cell identification

@cite{bar-lev-fox-2020} eq. (20) + (27) + footnote 21. The *cell* of
`Partition(ALT)` containing prejacent `φ` is the strongest proposition that
assigns a definite truth value to every alternative in `ALT`: the prejacent,
the negation of every IE-excludable alternative, and the truth of every
non-excludable alternative. When the cell is consistent (= satisfiable at
some world), `exhIEII` collapses onto it — exhaustification produces a
complete answer to the question induced by `ALT`. When inconsistent (the
simple-disjunction case `{a∨b, a, b, a∧b}`), `exhIEII` does no enrichment
beyond `exhIE`.
-/

/-- The non-IE alternatives: members of `ALT` that are not innocently excludable.
@cite{bar-lev-fox-2020} (the `C \ IE(p,C)` of paper eq. 20). -/
def nonExcludable : Set (Set World) :=
  {r ∈ ALT | ¬ isInnocentlyExcludable ALT φ r}

/-- The cell of `Partition(ALT)` containing prejacent `φ`.
@cite{bar-lev-fox-2020} eq. (20):
`Cell(p, C) = p ∧ ⋀{¬q : q ∈ IE(p, C)} ∧ ⋀(C \ IE(p, C))`.
-/
def cell : Set World := λ w =>
  φ w ∧
  (∀ q, isInnocentlyExcludable ALT φ q → ¬ q w) ∧
  (∀ r ∈ nonExcludable ALT φ, r w)

/-- Membership in `nonExcludable` unfolds to `r ∈ ALT` plus non-excludability. -/
@[simp] lemma mem_nonExcludable {r : Set World} :
    r ∈ nonExcludable ALT φ ↔ r ∈ ALT ∧ ¬ isInnocentlyExcludable ALT φ r := Iff.rfl

/-- Every II-compatible set consists of non-excludable alternatives: an IE
alternative cannot be in any II-compatible set, since the consistency set
would contain both the alternative and its negation. -/
lemma isIICompatible_subset_nonExcludable
    {R : Set (Set World)} (hR : isIICompatible ALT φ R) :
    R ⊆ nonExcludable ALT φ := by
  intro r hr
  refine ⟨hR.1 hr, fun hexc => ?_⟩
  obtain ⟨u, hu⟩ := hR.2
  exact hu (∼r) (Set.mem_union_left _ (Set.mem_union_right _ ⟨r, hexc, rfl⟩))
    (hu r (Set.mem_union_right _ hr))

/-- When the cell is consistent (nonempty as a set of worlds), `nonExcludable`
is itself II-compatible: a witnessing world for the cell witnesses the
consistency set `{φ} ∪ {¬q | q excludable} ∪ nonExcludable`. -/
lemma isIICompatible_nonExcludable_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    isIICompatible ALT φ (nonExcludable ALT φ) := by
  obtain ⟨u, hφ, hexcl, hne⟩ := h
  refine ⟨fun _ hr => hr.1, u, ?_⟩
  rintro ψ ((hφψ | ⟨q, hq, rfl⟩) | hr)
  · rw [Set.mem_singleton_iff.mp hφψ]; exact hφ
  · exact hexcl q hq
  · exact hne ψ hr

/-- **Cell identification (@cite{bar-lev-fox-2020} footnote 21)**: when the cell
is consistent, the unique MI-set is `nonExcludable`, hence `II = nonExcludable`. -/
theorem II_eq_nonExcludable_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    II ALT φ = nonExcludable ALT φ := by
  have hD_compat := isIICompatible_nonExcludable_of_cell_nonempty ALT φ h
  ext r
  refine ⟨fun ⟨hrALT, hrMI⟩ => ?_, fun hr => ⟨hr.1, ?_⟩⟩
  · -- `nonExcludable` is itself an MI-set, and `r` belongs to every MI-set.
    have hD_MI : isMISet ALT φ (nonExcludable ALT φ) :=
      ⟨hD_compat, fun R' hR' _ => isIICompatible_subset_nonExcludable ALT φ hR'⟩
    exact hrMI _ hD_MI
  · -- For any MI-set `R`, the union `R ∪ {r}` is II-compatible (using the
    -- `nonExcludable` witness world), so by maximality `r ∈ R`.
    intro R hR
    have hR_sub := isIICompatible_subset_nonExcludable ALT φ hR.1
    have hRr_compat : isIICompatible ALT φ (R ∪ {r}) := by
      refine ⟨?_, ?_⟩
      · rintro s (hsR | hsr)
        · exact hR.1.1 hsR
        · rw [Set.mem_singleton_iff.mp hsr]; exact hr.1
      · obtain ⟨u, hu⟩ := hD_compat.2
        refine ⟨u, ?_⟩
        rintro ψ ((hφψ | hneg) | hRr)
        · exact hu ψ (Set.mem_union_left _ (Set.mem_union_left _ hφψ))
        · exact hu ψ (Set.mem_union_left _ (Set.mem_union_right _ hneg))
        · rcases hRr with hsR | hsr
          · exact hu ψ (Set.mem_union_right _ (hR_sub hsR))
          · rw [Set.mem_singleton_iff.mp hsr]
            exact hu r (Set.mem_union_right _ hr)
    exact hR.2 _ hRr_compat Set.subset_union_left (Set.mem_union_right _ rfl)

/-- **Cell identification (@cite{bar-lev-fox-2020} eq. 27)**: when the cell is
consistent, `exhIEII` coincides with `cell` — i.e., the IE+II exhaustivity
operator returns a complete answer (definite truth value for every alternative)
to the question induced by `ALT`. -/
theorem exhIEII_eq_cell_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    exhIEII ALT φ = cell ALT φ := by
  have hII := II_eq_nonExcludable_of_cell_nonempty ALT φ h
  ext w
  refine ⟨fun ⟨hφ, hexcl, hII_w⟩ => ⟨hφ, hexcl, fun r hr => ?_⟩,
          fun ⟨hφ, hexcl, hne⟩ => ⟨hφ, hexcl, fun r hr_II => ?_⟩⟩
  · exact hII_w r (show r ∈ II ALT φ by rw [hII]; exact hr)
  · have : r ∈ nonExcludable ALT φ := by rw [← hII]; exact hr_II
    exact hne r this

/-- **Sufficient condition for II membership via a cell witness world.**

Given any world `w` that witnesses cell consistency (satisfies the prejacent,
falsifies all IE-excludable alternatives, and verifies all non-excludable
alternatives), every alternative true at `w` is innocently includable.

This is the abstract content of @cite{bar-lev-fox-2020}'s free-choice
derivation: each disjunct is true at the "separately-A-B" world, which is the
cell witness for `Alt(◇(a∨b))`. -/
theorem mem_II_of_cell_witness {target : Set World}
    (htarget_alt : target ∈ ALT) (w : World)
    (hwitness : cell ALT φ w) (htarget : target w) :
    target ∈ II ALT φ := by
  rw [II_eq_nonExcludable_of_cell_nonempty ALT φ ⟨w, hwitness⟩]
  exact ⟨htarget_alt, fun hexc => hwitness.2.1 target hexc htarget⟩

-- ============================================================================
-- SECTION: Decidable IE for finite types
-- ============================================================================

/-!
## Decidable Innocent Exclusion

The `exhIE` above is a specification: it quantifies over all `Set (Set World)`,
so it cannot be evaluated computationally. The functions below implement the same
algorithm over `[Fintype World]` types using `Bool`-valued meanings and explicit
subset enumeration. This makes them usable by `native_decide` and `rsa_predict`.
-/

section Decidable

variable {W : Type}

/-- Satisfiability check over an explicit list of worlds. -/
def isSatBool (worlds : List W) (f : W → Bool) : Bool :=
  worlds.any f

/-- Pointwise entailment over an explicit list of worlds. -/
def entailsBool (worlds : List W) (f g : W → Bool) : Bool :=
  worlds.all λ w => !f w || g w

/-- All sublists (subsets) of a list of indices. -/
def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as => let ss := sublists as; (ss.map (a :: ·)) ++ ss

/-- Innocent Exclusion over `Bool`-valued meanings: find indices of alternatives
    that appear in every maximal consistent exclusion set.
    `worlds` must enumerate all inhabitants of `W`. -/
def ieIndicesBool (worlds : List W) (prejacent : W → Bool)
    (alts : List (W → Bool)) : List Nat :=
  let indices := List.range alts.length
  let nonEnt := indices.filter λ i =>
    match alts[i]? with
    | some alt => !entailsBool worlds prejacent alt
    | _ => false
  let subsets := sublists nonEnt
  let consistent := subsets.filter λ s =>
    isSatBool worlds λ w => prejacent w && s.all λ i =>
      match alts[i]? with
      | some alt => !alt w
      | _ => true
  let maximal := consistent.filter λ s =>
    !consistent.any λ t =>
      s.length < t.length && s.all λ i => t.contains i
  if maximal.isEmpty then []
  else nonEnt.filter λ i => maximal.all λ m => m.contains i

/-- Apply Innocent Exclusion: conjoin prejacent with negations of IE alternatives.
    `worlds` must enumerate all inhabitants of `W`. -/
def applyIEBool (worlds : List W) (prejacent : W → Bool)
    (alts : List (W → Bool)) : W → Bool :=
  let ie := ieIndicesBool worlds prejacent alts
  λ w => prejacent w && ie.all λ i =>
    match alts[i]? with
    | some alt => !alt w
    | _ => true

end Decidable

-- ============================================================================
-- ANTIEXHAUSTIVE ENRICHMENT (O⁻)
-- ============================================================================

/-!
## @cite{chierchia-2006} Antiexhaustive Operator O⁻

Chierchia's O⁻ is distinct from O (exhaustification/only) and E (even-like
enrichment). While O negates stronger alternatives, O⁻ requires that
**every** alternative in C entails every other — i.e., the alternative set
is a complete join semilattice. This yields "antiexhaustive" universal-like
force from an existential base.

Formally: O⁻_C(p) = p ∧ ∀q ∈ C. q
(the assertion together with every alternative being true)

The key use: when C = D-variants (subdomain alternatives) of an existential
∃x∈D.P(x), asserting all D-variants gives ∀D'⊆D. ∃x∈D'.P(x), which
amounts to a distribution requirement across subdomains — universal force.

### Set-theoretic definition
-/

section Antiexhaustive

variable {World : Type*}

/-- Antiexhaustive enrichment O⁻: assert the prejacent and every alternative.

    Simplified from @cite{chierchia-2006} definition (108c) / (62).
    The paper defines O⁻_C(p) = p ∧ ∀q,q'∈C [q → q'] where q' has
    domain complementary to q — i.e., mutual entailment between all
    domain-alternative pairs. We simplify to the equivalent truth conditions
    `p ∧ ∀q∈C. q` (asserting all alternatives), which produces the same
    result when C consists of subdomain existentials forming a lattice.

    When C is a set of D-variants (subdomain existentials), asserting all
    of them yields: for every subdomain D' of D, ∃x∈D'.P(x). This is
    antiexhaustive — it distributes the existential across all subdomains,
    producing universal-like force. -/
def oMinus (C : Set (Set World)) (p : Set World) : Set World :=
  λ w => p w ∧ ∀ q ∈ C, q w

/-- O⁻ is a strengthening operation: O⁻_C(p) ⊆ₚ p. -/
theorem oMinus_entails (C : Set (Set World)) (p : Set World) :
    oMinus C p ⊆ₚ p :=
  λ _ ⟨hp, _⟩ => hp

/-- O⁻ is at least as strong as any individual alternative. -/
theorem oMinus_entails_alt (C : Set (Set World)) (p : Set World) (q : Set World)
    (hq : q ∈ C) : oMinus C p ⊆ₚ q :=
  λ _ ⟨_, hall⟩ => hall q hq

end Antiexhaustive

-- ============================================================================
-- ANTIEXHAUSTIVE ENRICHMENT (O⁻) — Computable Bool version
-- ============================================================================

section AntiexhaustiveBool

variable {W : Type}

/-- Computable antiexhaustive operator: assert prejacent + all alternatives.

    @cite{chierchia-2006} (108c): O⁻_C(p)(w) = p(w) ∧ ∀q∈C. q(w)

    This is the Bool version for finite model checking. -/
def oMinusB (alts : List (W → Bool)) (p : W → Bool) : W → Bool :=
  λ w => p w && alts.all (· w)

/-- O⁻ entails the prejacent. -/
theorem oMinusB_entails_prejacent {alts : List (W → Bool)} {p : W → Bool}
    {w : W} (h : oMinusB alts p w = true) : p w = true := by
  simp only [oMinusB, Bool.and_eq_true] at h
  exact h.1

/-- O⁻ entails every alternative. -/
theorem oMinusB_entails_all {alts : List (W → Bool)} {p : W → Bool}
    {w : W} (h : oMinusB alts p w = true) :
    ∀ q ∈ alts, q w = true := by
  simp only [oMinusB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

end AntiexhaustiveBool

-- ============================================================================
-- DOMAIN WIDENING ANTIEXHAUSTIVENESS DERIVATION
-- ============================================================================

/-!
## Deriving Universal Force from Antiexhaustive Enrichment

@cite{chierchia-2006} §5.1: When O⁻ is applied to an existential ∃x∈D.P(x)
with D-MIN alternatives (all subdomains), the enriched meaning requires
the existential to hold over every subdomain — equivalent to universal force.

This is the formal engine behind FCI universal readings.
-/

section UniversalFromAntiexh

variable {Entity : Type*} {World : Type*}

/-- An existential over a finite domain (list-based for computability). -/
def existsIn (D : List Entity) (P : Entity → Set World) : Set World :=
  λ w => ∃ x ∈ D, P x w

/-- D-MIN alternatives: existentials over all sublists (subdomains). -/
def dMinAlts (D : List Entity) (P : Entity → Set World) : Set (Set World) :=
  {q | ∃ D' : List Entity, (∀ x ∈ D', x ∈ D) ∧ q = existsIn D' P}

/-- **Antiexhaustiveness yields universal distribution.**

    O⁻ applied to ∃x∈D.P(x) with D-MIN alternatives entails that for
    every individual a ∈ D, P(a) holds — i.e., universal force.

    This is Chierchia 2006's key formal result: the "birth of universal
    readings" (§5.1) from antiexhaustive enrichment of an existential base. -/
theorem antiexh_yields_universal
    (D : List Entity) (P : Entity → Set World) (w : World)
    (h : oMinus (dMinAlts D P) (existsIn D P) w) :
    ∀ a ∈ D, P a w := by
  intro a ha
  obtain ⟨_, hall⟩ := h
  have hmem : existsIn [a] P ∈ dMinAlts D P := by
    unfold dMinAlts
    exact ⟨[a], λ x hx => by simp at hx; rw [hx]; exact ha, rfl⟩
  have := hall _ hmem
  unfold existsIn at this
  obtain ⟨x, hx, hPx⟩ := this
  simp at hx
  rw [hx] at hPx
  exact hPx

end UniversalFromAntiexh

end Exhaustification
