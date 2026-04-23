import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# Exhaustivity Operators: `exhMW` and `exhIE`
@cite{groenendijk-stokhof-1984} @cite{spector-2016} @cite{wang-2025} @cite{chierchia-2013}

Formalization of @cite{spector-2016} "Comparing exhaustivity operators"
(Semantics & Pragmatics 9, Article 11: 1–33).

## Paper structure

* §2.1 Definitions 1–4: `≤_ALT`, `exhMW`, compatible sets, MC-sets,
  `IE`, `exhIE`
* §3.4 Propositions 6, 7, Corollary 8: `exhMW ⊆ exhIE` and characterisation
* §3.5 Theorem 9 (main result): closure under `∧` gives `exhMW = exhIE`
* §3.6 Theorem 10, Corollary 11: closure under `∨` is vacuous for `exhIE`
* §5.3 Lemmas 1, 2, 3: minimal-world ↔ MC-set connection
* §5.4 Proof of Theorem 9

Set-theoretic operators use mathlib primitives directly: `⊆` (subset),
`·ᶜ` (complement), `∩` (intersection), `⋂₀` (sInter), `⋃₀` (sUnion).

## Relation to the Finset / `Excluder` API

This file is the *reference* formalization of Spector 2016, faithful
to the paper's prose and the natural home for paper-level theorems
(Props 6/7, Cor 8, Thm 9, Thm 10). The computational refinement lives
in `Exhaustification/Innocent.lean` (the Finset-canonical version,
plugged into the `Excluder` strategy interface from `Excluder.lean`).
`Exhaustification/SetFinsetBridge.lean` proves the two agree on
`IsCompatible`, `IsMCSet`, `IE`, and `IsInnocentlyExcludable`, so
results proven on either side are usable from the other. New code
that needs decidability or `Excluder` uniformity should prefer the
Finset side.
-/

namespace Exhaustification

-- Re-export `ContextPolarity` from the consolidated polarity module.
open Semantics.Entailment.Polarity (ContextPolarity)

variable {World : Type*}

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
def IsMinimal (u : World) : Prop :=
  φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)

-- Basic property
theorem exhMW_entails : exhMW ALT φ ⊆ φ :=
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
def IsCompatible (E : Set (Set World)) : Prop :=
  φ ∈ E ∧
  (∀ ψ ∈ E, ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ) ∧
  SetConsistent E

/--
Definition 3.3: MC_(ALT,φ)-sets

A set is maximal (ALT, φ)-compatible (MC_(ALT,φ)-set for short) if it is
(ALT, φ)-compatible and is not properly included in any other
(ALT, φ)-compatible set.
-/
def IsMCSet (E : Set (Set World)) : Prop :=
  IsCompatible ALT φ E ∧
  ∀ E', IsCompatible ALT φ E' → E ⊆ E' → E' ⊆ E

/--
Definition 3.4: IE_(ALT,φ) = {ψ : ψ belongs to every MC_(ALT,φ)-set}

"Note that, somewhat counter-intuitively, the set IE_(ALT,φ) is not the set of
innocently excludable alternatives, but rather the set that contains φ and all
the negations of innocently excludable alternatives."
-/
def IE : Set (Set World) :=
  {ψ | ∀ E, IsMCSet ALT φ E → ψ ∈ E}

/--
Definition 3.5: An alternative a is innocently excludable given ALT and φ
if and only if ¬a ∈ IE_(ALT,φ).
-/
def IsInnocentlyExcludable (a : Set World) : Prop :=
  a ∈ ALT ∧ (aᶜ) ∈ IE ALT φ

/--
Sufficient condition for innocent excludability: every alternative is IE
when there exists a world where φ holds and every alternative is false.

The set `S = {φ} ∪ {bᶜ | b ∈ ALT}` is then the unique MC-set: it is
compatible by hypothesis, and every compatible set is a subset of it
(by Definition 3.2(b), every element is `φ` or `bᶜ` for some `b ∈ ALT`).
By maximality, every MC-set equals `S`. Since `aᶜ ∈ S` for every `a ∈ ALT`,
each alternative is innocently excludable.

This is the typical situation in alternative-set scenarios where the
prejacent and the negations of all alternatives are jointly satisfiable
(e.g., 3-button conditional perfection paradigms).
-/
theorem IsInnocentlyExcludable.of_full_exclusion_consistent
    {a : Set World} (ha : a ∈ ALT)
    (h_consist : ∃ w, φ w ∧ ∀ b ∈ ALT, ¬ b w) :
    IsInnocentlyExcludable ALT φ a := by
  refine ⟨ha, ?_⟩
  intro E hE_mc
  -- S_max = {ψ | ψ = φ ∨ ∃ b ∈ ALT, ψ = bᶜ}
  let S_max : Set (Set World) := fun ψ => ψ = φ ∨ ∃ b ∈ ALT, ψ = bᶜ
  -- Step 1: E ⊆ S_max (from compatibility: every element is φ or b'ᶜ)
  have h_sub : E ⊆ S_max := by
    intro ψ hψ
    rcases hE_mc.1.2.1 ψ hψ with h | ⟨b', hb'_mem, hb'_eq⟩
    · exact Or.inl h
    · exact Or.inr ⟨b', hb'_mem, hb'_eq⟩
  -- Step 2: S_max is compatible (φ ∈ S_max, every element is φ or bᶜ, consistent)
  have h_compat : IsCompatible ALT φ S_max := by
    refine ⟨Or.inl rfl, fun ψ hψ => hψ, ?_⟩
    obtain ⟨w, hw_phi, hw_not⟩ := h_consist
    exact ⟨w, fun ψ hψ => by
      rcases hψ with h | ⟨b', hb', heq⟩
      · rw [h]; exact hw_phi
      · rw [heq]; exact hw_not b' hb'⟩
  -- Step 3: By maximality of E, S_max ⊆ E
  have h_sup : S_max ⊆ E := hE_mc.2 _ h_compat h_sub
  -- Step 4: aᶜ ∈ S_max, so aᶜ ∈ E
  exact h_sup (Or.inr ⟨a, ha, rfl⟩)

-- DEFINITION 4: exh_ie (Spector p.8)

/--
Definition 4: Exhaustivity operator based on innocent exclusion (exh_ie)

  exh_ie(ALT, φ) = {u : ∀ψ(ψ ∈ IE_(ALT,φ) → ψ(u) = 1)}

Equivalently: exh_ie(ALT, φ) = ⋂₀ IE_(ALT,φ)

Equivalently: exh_ie(ALT, φ) = φ ∧ ⋂₀ {¬a : a is a member of ALT that is
                                       innocently excludable given ALT and φ}
-/
def exhIE : Set World :=
  λ u => ∀ ψ ∈ IE ALT φ, ψ u

-- DEFINITION 5: Closure under conjunction/disjunction (Spector p.11)

/--
A set ALT is closed under conjunction if for any subset X of ALT,
⋂₀ X ∈ ALT.

(Definition 5 in Spector)
-/
def closedUnderConj : Prop :=
  ∀ X : Set (Set World), X ⊆ ALT → (⋂₀ X) ∈ ALT

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
    ∃ u, IsMinimal ALT φ u := by
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
  {φ} ∪ {ψ | ∃ a ∈ ALT, ψ = aᶜ ∧ ¬(a u)}

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
      have hna_in_Xu : (aᶜ) ∈ X_of_world ALT φ u := by
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hau⟩
      have hna_in_Xv := hsub hna_in_Xu
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hna_in_Xv
      rcases hna_in_Xv with heq | ⟨a', ha', heq', hav'⟩
      · -- aᶜ = φ: contradiction since φ v but (aᶜ) v means ¬(a v)
        have : (aᶜ) v := by rw [heq]; exact hv
        exact this hav
      · -- aᶜ = a'ᶜ with ¬(a' v): need a = a'
        rw [compl_injective heq'] at hav; exact hav' hav
  · -- Backward: X(v) ⊆ X(u) ∧ ¬X(u) ⊆ X(v) → u <_ALT v
    intro ⟨hsub, hnsub⟩
    constructor
    · -- u ≤_ALT v
      intro a ha hau
      by_contra hav
      have hna_in_Xv : (aᶜ) ∈ X_of_world ALT φ v := by
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hav⟩
      have hna_in_Xu := hsub hna_in_Xv
      simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hna_in_Xu
      rcases hna_in_Xu with heq | ⟨a', ha', heq', hau'⟩
      · have : (aᶜ) u := by rw [heq]; exact hu
        exact this hau
      · rw [compl_injective heq'] at hau; exact hau' hau
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
    ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ := by
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
theorem X_is_compatible (u : World) (hu : φ u) : IsCompatible ALT φ (X_of_world ALT φ u) := by
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
theorem minimal_iff_MCset (u : World) (hu : φ u) :
    IsMinimal ALT φ u ↔ IsMCSet ALT φ (X_of_world ALT φ u) := by
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
      -- ψ ∈ E, so ψ = φ or ψ = aᶜ for some a ∈ ALT
      obtain ⟨hφE, hE_form, hE_cons⟩ := hE_compat
      have hψ_form := hE_form ψ hψE
      rcases hψ_form with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
      · -- ψ = φ: But φ ∈ X(u), contradiction
        rw [hψ_eq_φ] at hψ_not_Xu
        exact hψ_not_Xu (X_contains_phi ALT φ u)
      · -- ψ = aᶜ for some a ∈ ALT
        rw [hψ_eq_na] at hψ_not_Xu hψE
        -- Since aᶜ ∉ X(u), we have a(u) = 1 (otherwise aᶜ would be in X(u))
        have hau : a u := by
          by_contra hau_not
          apply hψ_not_Xu
          simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          right; exact ⟨a, ha, rfl, hau_not⟩
        -- E is consistent, so there exists v satisfying everything in E
        obtain ⟨v, hv_sat⟩ := hE_cons
        -- v satisfies φ (since φ ∈ E)
        have hφv : φ v := hv_sat φ hφE
        -- v satisfies aᶜ (since aᶜ ∈ E)
        have hna_v : (aᶜ) v := hv_sat (aᶜ) hψE
        -- So v <_ALT u
        have hv_lt_u : v <[ALT] u := by
          constructor
          · -- v ≤_ALT u: for any b ∈ ALT, if b(v) = 1 then b(u) = 1
            intro b hb hbv
            by_contra hbu
            have hnb_in_Xu : (bᶜ) ∈ X_of_world ALT φ u := by
              simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
              right; exact ⟨b, hb, rfl, hbu⟩
            have hnb_in_E := hXu_sub_E hnb_in_Xu
            have hnb_v : (bᶜ) v := hv_sat (bᶜ) hnb_in_E
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
      have hXv_compat : IsCompatible ALT φ (X_of_world ALT φ v) := X_is_compatible ALT φ v hφv
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
theorem exists_MCset_of_minimal (hmin : ∃ u, IsMinimal ALT φ u) : ∃ E, IsMCSet ALT φ E := by
  obtain ⟨u, hu_min⟩ := hmin
  exact ⟨X_of_world ALT φ u, (minimal_iff_MCset ALT φ u hu_min.1).mp hu_min⟩

/--
MC-set existence for finite ALT: When ALT is finite and φ is satisfiable,
an MC-set exists.

This combines:
1. exists_minimal_of_finite: finite ALT + satisfiable φ → minimal world exists
2. exists_MCset_of_minimal: minimal world exists → MC-set exists
-/
theorem exists_MCset (hfin : Set.Finite ALT) (hsat : ∃ w, φ w) : ∃ E, IsMCSet ALT φ E :=
  exists_MCset_of_minimal ALT φ (exists_minimal_of_finite ALT φ hfin hsat)

/--
Every element of IE is either φ or aᶜ for some a ∈ ALT.
This follows from the structure of compatible sets.

Note: Requires finite ALT to ensure MC-sets exist.
-/
theorem IE_structure (hfin : Set.Finite ALT) (ψ : Set World) (hψ : ψ ∈ IE ALT φ)
    (hsat : ∃ w, φ w) : ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ := by
  -- Since an MC-set exists (by exists_MCset), ψ is in some MC-set
  obtain ⟨E, hE_mc⟩ := exists_MCset ALT φ hfin hsat
  have hψ_in_E := hψ E hE_mc
  -- By compatibility, elements of E are φ or aᶜ
  exact hE_mc.1.2.1 ψ hψ_in_E


/--
Lemma 2 (Spector p.23, Core Lemma):
For every proposition φ, every set of alternatives ALT, and every world u,
  exh_mw(ALT, φ)(u) = 1 ⟺ there is an MC_(ALT,φ)-set X that u satisfies.

Equivalently: u is a minimal φ-world relative to <_ALT ⟺
              there is an MC_(ALT,φ)-set X that u satisfies.
-/
theorem exhMW_iff_satisfies_MCset (u : World) :
    exhMW ALT φ u ↔ ∃ E, IsMCSet ALT φ E ∧ (∀ ψ ∈ E, ψ u) := by
  constructor
  · -- Forward: exhMW u → ∃MC-set satisfied by u
    intro ⟨hu, hmin⟩
    -- By Lemma 1, X(u) is an MC-set
    have hXu_mc : IsMCSet ALT φ (X_of_world ALT φ u) :=
      (minimal_iff_MCset ALT φ u hu).mp ⟨hu, hmin⟩
    -- u satisfies X(u)
    have hu_sat_Xu := u_satisfies_X ALT φ u hu
    exact ⟨X_of_world ALT φ u, hXu_mc, hu_sat_Xu⟩
  · -- Backward: (∃MC-set satisfied by u) → exhMW u
    intro ⟨E, hE_mc, hu_sat_E⟩
    -- Extract components of MC-set (keeping hE_mc available)
    have hE_compat : IsCompatible ALT φ E := hE_mc.1
    have hE_max : ∀ E', IsCompatible ALT φ E' → E ⊆ E' → E' ⊆ E := hE_mc.2
    -- u satisfies E, so φ u (since φ ∈ E)
    have hφE : φ ∈ E := hE_compat.1
    have hE_form : ∀ ψ ∈ E, ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ := hE_compat.2.1
    have hu : φ u := hu_sat_E φ hφE
    -- We show u is minimal by showing X(u) = E
    -- First, E ⊆ X(u): every ψ ∈ E is in X(u)
    have hE_sub_Xu : E ⊆ X_of_world ALT φ u := by
      intro ψ hψE
      rcases hE_form ψ hψE with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
      · -- ψ = φ: φ ∈ X(u)
        rw [hψ_eq_φ]; exact X_contains_phi ALT φ u
      · -- ψ = aᶜ: since u satisfies ψ, we have ¬(a u), so aᶜ ∈ X(u)
        rw [hψ_eq_na]
        have hna_u : (aᶜ) u := hu_sat_E (aᶜ) (hψ_eq_na ▸ hψE)
        simp only [X_of_world, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
        right; exact ⟨a, ha, rfl, hna_u⟩
    -- X(u) is compatible
    have hXu_compat : IsCompatible ALT φ (X_of_world ALT φ u) := X_is_compatible ALT φ u hu
    -- By maximality of E: E ⊆ X(u) and X(u) compatible → X(u) ⊆ E
    have hXu_sub_E : X_of_world ALT φ u ⊆ E := hE_max (X_of_world ALT φ u) hXu_compat hE_sub_Xu
    -- So E = X(u)
    have hE_eq_Xu : E = X_of_world ALT φ u := Set.Subset.antisymm hE_sub_Xu hXu_sub_E
    -- X(u) is an MC-set (since E is and E = X(u))
    have hXu_mc : IsMCSet ALT φ (X_of_world ALT φ u) := hE_eq_Xu ▸ hE_mc
    -- By Lemma 1, u is minimal
    exact (minimal_iff_MCset ALT φ u hu).mpr hXu_mc

/--
Lemma 3 (reformulation of Lemma 2):
  exh_mw(ALT, φ) = ⋃₀ {⋂₀ X : X is an MC_(ALT,φ)-set}

The minimal-worlds exhaustification is the disjunction of the conjunctions
of all MC-sets.
-/
theorem exhMW_eq_disj_MCsets :
    exhMW ALT φ = {u | ∃ E, IsMCSet ALT φ E ∧ (∀ ψ ∈ E, ψ u)} := by
  apply Set.Subset.antisymm
  · intro u hmw
    exact (exhMW_iff_satisfies_MCset ALT φ u).mp hmw
  · intro u hex
    exact (exhMW_iff_satisfies_MCset ALT φ u).mpr hex

-- SECTION 3.4: Relationship between exh_mw and exh_ie (Spector p.12)

/--
Proposition 6 (Spector p.12): For any proposition φ with alternatives ALT,
exh_mw(ALT, φ) entails exh_ie(ALT, φ).

Proof idea: Any world satisfying exh_mw satisfies some MC-set, hence satisfies
the intersection of all MC-sets, hence satisfies IE.
-/
theorem exhMW_entails_exhIE : exhMW ALT φ ⊆ exhIE ALT φ := by
  intro u hmw
  -- By Lemma 2, u satisfies some MC-set E
  obtain ⟨E, hmc, hsat⟩ := (exhMW_iff_satisfies_MCset ALT φ u).mp hmw
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
theorem isInnocentlyExcludable_iff_exhMW_entails_neg (a : Set World) (ha : a ∈ ALT) :
    IsInnocentlyExcludable ALT φ a ↔ (exhMW ALT φ ⊆ aᶜ) := by
  constructor
  · -- Forward: a is IE → exh_mw ⊆ aᶜ
    intro ⟨_, hna_in_IE⟩ u hmw
    -- By Lemma 2, u satisfies some MC-set E
    obtain ⟨E, hE_mc, hu_sat_E⟩ := (exhMW_iff_satisfies_MCset ALT φ u).mp hmw
    -- aᶜ ∈ IE means aᶜ is in every MC-set, including E
    have hna_in_E : (aᶜ) ∈ E := hna_in_IE E hE_mc
    -- u satisfies E, so u satisfies aᶜ
    exact hu_sat_E (aᶜ) hna_in_E
  · -- Backward: exh_mw ⊆ aᶜ → a is IE
    intro hmw_entails_na
    constructor
    · exact ha
    · -- Show aᶜ ∈ IE, i.e., aᶜ is in every MC-set
      intro E hE_mc
      -- E is consistent, so there exists v satisfying E
      have hE_compat := hE_mc.1
      obtain ⟨v, hv_sat_E⟩ := hE_compat.2.2
      -- v satisfies φ (since φ ∈ E)
      have hφv : φ v := hv_sat_E φ hE_compat.1
      -- v satisfies E (an MC-set), so by Lemma 2, exh_mw(v) holds
      have hmw_v : exhMW ALT φ v :=
        (exhMW_iff_satisfies_MCset ALT φ v).mpr ⟨E, hE_mc, hv_sat_E⟩
      -- By hypothesis, exh_mw ⊆ aᶜ, so (aᶜ) v
      have hna_v : (aᶜ) v := hmw_entails_na hmw_v
      -- E ∪ {aᶜ} is consistent (witnessed by v)
      have hE_union_consistent : SetConsistent (E ∪ {aᶜ}) := by
        use v
        intro ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
        rcases hψ with hψE | rfl
        · exact hv_sat_E ψ hψE
        · exact hna_v
      -- E ∪ {aᶜ} is compatible (φ ∈ E ⊆ E ∪ {aᶜ}, and elements are φ or negations)
      have hE_union_compat : IsCompatible ALT φ (E ∪ {aᶜ}) := by
        constructor
        · exact Set.mem_union_left {aᶜ} hE_compat.1
        constructor
        · intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hψE | rfl
          · exact hE_compat.2.1 ψ hψE
          · right; exact ⟨a, ha, rfl⟩
        · exact hE_union_consistent
      -- By maximality of E: E ⊆ E ∪ {aᶜ} and E ∪ {aᶜ} compatible → E ∪ {aᶜ} ⊆ E
      have hE_max := hE_mc.2
      have hsub : E ⊆ E ∪ {aᶜ} := Set.subset_union_left
      have hE_union_sub_E := hE_max (E ∪ {aᶜ}) hE_union_compat hsub
      -- So aᶜ ∈ E
      have hna_in_union : (aᶜ) ∈ E ∪ {aᶜ} := Set.mem_union_right E rfl
      exact hE_union_sub_E hna_in_union

/--
Corollary 8 (Spector p.12):
exh_ie(ALT, φ) = φ ∧ ⋂₀ {¬a : a ∈ ALT ∧ exh_mw(ALT, φ) ⊆ ¬a}

This gives an alternative characterization of exh_ie in terms of exh_mw.

Note: The backward direction requires finite ALT for IE_structure.
-/
theorem exhIE_eq_phi_and_exhMW_negated (hfin : Set.Finite ALT) :
    exhIE ALT φ = {u | φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ aᶜ) → ¬(a u)} := by
  apply Set.Subset.antisymm
  · -- exh_ie ⊆ (φ ∧ ⋂₀ {¬a : exh_mw ⊆ ¬a})
    intro u hie
    constructor
    · -- φ u: φ ∈ IE (since φ is in every MC-set by compatibility)
      have hφ_in_IE : φ ∈ IE ALT φ := λ E hE_mc => hE_mc.1.1
      exact hie φ hφ_in_IE
    · -- For all a ∈ ALT, if exh_mw ⊆ ¬a then ¬(a u)
      intro a ha hmw_na
      have hIE_a : IsInnocentlyExcludable ALT φ a :=
        (isInnocentlyExcludable_iff_exhMW_entails_neg ALT φ a ha).mpr hmw_na
      have hna_u := hie (aᶜ) hIE_a.2
      exact hna_u
  · -- (φ ∧ ⋂₀ {¬a : exh_mw ⊆ ¬a}) ⊆ exh_ie
    -- We need to show: ∀ ψ ∈ IE, ψ u
    intro u ⟨hu, hall⟩ ψ hψ_IE
    -- Use IE_structure to determine ψ's form
    have hsat : ∃ w, φ w := ⟨u, hu⟩
    rcases IE_structure ALT φ hfin ψ hψ_IE hsat with hψ_eq_φ | ⟨a, ha, hψ_eq_na⟩
    · -- Case: ψ = φ
      rw [hψ_eq_φ]; exact hu
    · -- Case: ψ = aᶜ for some a ∈ ALT
      rw [hψ_eq_na]
      -- aᶜ ∈ IE means a is innocently excludable
      have hna_IE : (aᶜ) ∈ IE ALT φ := hψ_eq_na ▸ hψ_IE
      have hIE_a : IsInnocentlyExcludable ALT φ a := ⟨ha, hna_IE⟩
      -- By Prop 7, exh_mw ⊆ aᶜ
      have hmw_na : exhMW ALT φ ⊆ aᶜ :=
        (isInnocentlyExcludable_iff_exhMW_entails_neg ALT φ a ha).mp hIE_a
      -- By hypothesis hall, ¬(a u)
      have hna_u : ¬(a u) := hall a ha hmw_na
      -- So (aᶜ) u holds
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
a negation of some member of A. Consider ⋂₀ A. Since every MC-set has a member
whose negation is in A, ⋂₀ A is false in every world satisfying an MC-set.
Therefore ¬(⋂₀ A) is consistent with every MC-set.

Since ALT is closed under conjunction, ⋂₀ A ∈ ALT. Since ¬(⋂₀ A) is consistent
with every MC-set and MC-sets are maximal, ¬(⋂₀ A) ∈ IE. But (⋂₀ A)(u) = 1,
so u fails to satisfy IE, hence exh_ie(φ)(u) = 0.
-/
theorem exhMW_eq_exhIE_of_closedUnderConj (hclosed : closedUnderConj ALT) :
    exhMW ALT φ = exhIE ALT φ := by
  apply Set.Subset.antisymm
  · -- exh_mw ⊆ exh_ie: This is Proposition 6
    exact exhMW_entails_exhIE ALT φ
  · -- exh_ie ⊆ exh_mw: Requires closure under conjunction
    intro u hie
    -- First, φ u holds (since φ ∈ IE by compatibility)
    have hφ_in_IE : φ ∈ IE ALT φ := λ E hE_mc => hE_mc.1.1
    have hu : φ u := hie φ hφ_in_IE
    -- We show u is minimal by contradiction
    -- Suppose u is not minimal: ∃v, φ v ∧ v <_ALT u
    by_contra hmw_not
    change ¬ (φ u ∧ ¬∃ v, φ v ∧ (v <[ALT] u)) at hmw_not
    push Not at hmw_not
    obtain ⟨v, hφv, hv_lt_u⟩ := hmw_not hu
    -- Define A = {a ∈ ALT : a(u) = 1} (alternatives true at u)
    let A : Set (Set World) := {a ∈ ALT | a u}
    -- Since v <_ALT u, there exists a ∈ A with ¬(a v)
    -- (i.e., alternatives true at u but not all true at v)
    have hA_sub_ALT : A ⊆ ALT := λ a ha => ha.1
    -- ⋂₀ A ∈ ALT by closure under conjunction
    have hconjA_in_ALT : (⋂₀ A) ∈ ALT := hclosed A hA_sub_ALT
    -- (⋂₀ A)(u) = 1 since all a ∈ A are true at u
    have hconjA_u : (⋂₀ A) u := by
      intro a ha
      exact ha.2
    -- v <_ALT u means: alternatives true at v ⊂ alternatives true at u
    -- So there exists a ∈ ALT with a u but ¬(a v)
    -- Extract v ≤_ALT u and ¬(u ≤_ALT v) from v <_ALT u
    have hv_le_u : v ≤[ALT] u := hv_lt_u.1
    have hnot_u_le_v : ¬(u ≤[ALT] v) := hv_lt_u.2
    -- Need to unfold leALT before push_neg can work
    simp only [leALT] at hnot_u_le_v
    push Not at hnot_u_le_v
    obtain ⟨a₀, ha₀_ALT, ha₀_u, hna₀_v⟩ := hnot_u_le_v
    -- a₀ ∈ A (since a₀ ∈ ALT and a₀ u)
    have ha₀_A : a₀ ∈ A := ⟨ha₀_ALT, ha₀_u⟩
    -- Since a₀ ∈ A and ¬(a₀ v), we have ¬((⋂₀ A) v)
    have hconjA_not_v : ¬((⋂₀ A) v) := by
      intro hconj_v
      exact hna₀_v (hconj_v a₀ ha₀_A)
    -- ¬(⋂₀ A) is true at v
    have hneg_conjA_v : ((⋂₀ A)ᶜ) v := hconjA_not_v
    -- Now we need to show ¬(⋂₀ A) ∈ IE
    -- For this, we show ¬(⋂₀ A) is in every MC-set E
    have hneg_conjA_in_IE : ((⋂₀ A)ᶜ) ∈ IE ALT φ := by
      intro E hE_mc
      -- E is an MC-set. By consistency, there exists w satisfying E.
      obtain ⟨w, hw_sat_E⟩ := hE_mc.1.2.2
      have hφw : φ w := hw_sat_E φ hE_mc.1.1
      have hmw_w : exhMW ALT φ w :=
        (exhMW_iff_satisfies_MCset ALT φ w).mpr ⟨E, hE_mc, hw_sat_E⟩
      -- w is minimal, so ¬∃w', φ w' ∧ w' <_ALT w
      obtain ⟨_, hmin_w⟩ := hmw_w
      -- Key claim: ¬((⋂₀ A) w)
      -- We prove this by contradiction.
      have hconjA_not_w : ¬((⋂₀ A) w) := by
        intro hconjA_w
        -- hconjA_w : (⋂₀ A) w, i.e., ∀ a ∈ A, a w
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
      -- So ((⋂₀ A)ᶜ) w holds
      have hneg_conjA_w : ((⋂₀ A)ᶜ) w := hconjA_not_w
      -- E ∪ {(⋂₀ A)ᶜ} is consistent (witnessed by w)
      have hE_union_consistent : SetConsistent (E ∪ {(⋂₀ A)ᶜ}) := by
        use w
        intro ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
        rcases hψ with hψE | rfl
        · exact hw_sat_E ψ hψE
        · exact hneg_conjA_w
      -- E ∪ {(⋂₀ A)ᶜ} is compatible
      have hE_union_compat : IsCompatible ALT φ (E ∪ {(⋂₀ A)ᶜ}) := by
        constructor
        · exact Set.mem_union_left _ hE_mc.1.1
        constructor
        · intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hψE | rfl
          · exact hE_mc.1.2.1 ψ hψE
          · right; exact ⟨⋂₀ A, hconjA_in_ALT, rfl⟩
        · exact hE_union_consistent
      -- By maximality of E: E ⊆ E ∪ {(⋂₀ A)ᶜ} and E ∪ {(⋂₀ A)ᶜ} compatible → E ∪ {(⋂₀ A)ᶜ} ⊆ E
      have hE_max := hE_mc.2
      have hsub : E ⊆ E ∪ {(⋂₀ A)ᶜ} := Set.subset_union_left
      have hE_union_sub_E := hE_max (E ∪ {(⋂₀ A)ᶜ}) hE_union_compat hsub
      -- So (⋂₀ A)ᶜ ∈ E
      have hneg_in_union : ((⋂₀ A)ᶜ) ∈ E ∪ {(⋂₀ A)ᶜ} := Set.mem_union_right E rfl
      exact hE_union_sub_E hneg_in_union
    -- So ¬(⋂₀ A) ∈ IE. u satisfies IE, so u satisfies ¬(⋂₀ A).
    have hneg_conjA_u : ((⋂₀ A)ᶜ) u := hie ((⋂₀ A)ᶜ) hneg_conjA_in_IE
    -- But (⋂₀ A) u is true, contradiction
    exact hneg_conjA_u hconjA_u

-- SECTION 3.6: Consequences (Spector p.13)

-- Helper lemmas for Theorem 10

/--
De Morgan for big disjunction: ¬(⋃₀ X) at w iff ∀ a ∈ X, ¬a at w
-/
lemma neg_bigDisj_iff (X : Set (Set World)) (w : World) :
    ((⋃₀ X)ᶜ) w ↔ ∀ a ∈ X, (aᶜ) w := by
  show ¬ (∃ a ∈ X, w ∈ a) ↔ ∀ a ∈ X, w ∉ a
  push Not
  rfl

/--
The disjunction closure contains the original set (via singleton disjunctions).
-/
lemma subset_disjClosure (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) :
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
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) (p : Set World) :
    p ∈ ALT' ↔ ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X := by
  rw [h]; rfl

/--
Key lemma: The preorder ≤_ALT is unchanged by disjunction closure.

If ALT' is the disjunction closure of ALT, then u ≤_{ALT} v ↔ u ≤_{ALT'} v.

Proof: If a disjunction (⋃₀ X) is true at u where X ⊆ ALT, then some b ∈ X is true at u.
If u ≤_{ALT} v, then b is true at v, so (⋃₀ X) is true at v.
-/
lemma leALT_disjClosure_eq (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) (u v : World) :
    leALT ALT u v ↔ leALT ALT' u v := by
  constructor
  · -- ALT ≤ implies ALT' ≤
    intro hle a ha_ALT' hau
    rw [h] at ha_ALT'
    obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
    -- a = ⋃₀ X, a u means ∃ b ∈ X, b u
    rw [ha_eq] at hau ⊢
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
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) (u v : World) :
    ltALT ALT u v ↔ ltALT ALT' u v := by
  simp only [ltALT, leALT_disjClosure_eq ALT ALT' h]

/--
Corollary: exh_mw is unchanged by disjunction closure.
-/
lemma exhMW_disjClosure_eq (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) :
    exhMW ALT φ = exhMW ALT' φ := by
  apply Set.Subset.antisymm
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
  exhIE ALT φ ≡ₚ λ u => φ u ∧ ∀ a ∈ ALT, (exhMW ALT φ ⊆ aᶜ) → ¬(a u)

Since exhMW is unchanged by disjunction closure, we just need to check that
the extra conditions for ALT' (disjunctions) are implied by the ALT conditions.
-/
theorem exhIE_disjClosure_eq (hfin : Set.Finite ALT) (ALT' : Set (Set World))
    (h : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}) :
    exhIE ALT φ = exhIE ALT' φ := by
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
    have heq : {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}
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
  have hc8_ALT := exhIE_eq_phi_and_exhMW_negated ALT φ hfin
  have hc8_ALT' := exhIE_eq_phi_and_exhMW_negated ALT' φ hfin'
  -- We need to show the two characterizations are equivalent
  apply Set.Subset.antisymm
  · -- exhIE ALT φ ⊆ exhIE ALT' φ
    intro u hie
    -- By Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ aᶜ) → ¬(a u)
    have ⟨hφu, hALT_cond⟩ := hc8_ALT.subset hie
    -- Need to show Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ aᶜ) → ¬(a u)
    refine hc8_ALT'.symm.subset ⟨hφu, ?_⟩
    intro a ha_ALT' hexhMW'_sub_neg_a
    -- a ∈ ALT', so a = ⋃₀ X for some X ⊆ ALT
    rw [h] at ha_ALT'
    obtain ⟨X, hX_sub, ha_eq⟩ := ha_ALT'
    have hb_conds : ∀ b ∈ X, exhMW ALT φ ⊆ bᶜ := by
      intro b hb_X w hmw
      have hmw' : exhMW ALT' φ w := hmw_eq.subset hmw
      have : (aᶜ) w := hexhMW'_sub_neg_a hmw'
      rw [ha_eq] at this
      exact (neg_bigDisj_iff X w).mp this b hb_X
    have hb_not_u : ∀ b ∈ X, ¬(b u) := λ b hb => hALT_cond b (hX_sub hb) (hb_conds b hb)
    rw [ha_eq]
    show ¬ ∃ b ∈ X, u ∈ b
    push Not
    exact hb_not_u
  · -- exhIE ALT' φ ⊆ exhIE ALT φ
    intro u hie'
    -- By Corollary 8 for ALT': φ u ∧ ∀ a ∈ ALT', (exhMW' ⊆ aᶜ) → ¬(a u)
    have ⟨hφu, hALT'_cond⟩ := hc8_ALT'.subset hie'
    -- Need to show Corollary 8 for ALT: φ u ∧ ∀ a ∈ ALT, (exhMW ⊆ aᶜ) → ¬(a u)
    refine hc8_ALT.symm.subset ⟨hφu, ?_⟩
    intro a ha_ALT hexhMW_sub_neg_a
    -- a ∈ ALT ⊆ ALT'
    have ha_ALT' : a ∈ ALT' := subset_disjClosure ALT ALT' h ha_ALT
    -- exhMW ALT φ ⊆ aᶜ, and exhMW ALT' φ = exhMW ALT φ
    have hexhMW'_sub : exhMW ALT' φ ⊆ aᶜ := by
      intro w hmw'
      have hmw : exhMW ALT φ w := hmw_eq.symm.subset hmw'
      exact hexhMW_sub_neg_a hmw
    exact hALT'_cond a ha_ALT' hexhMW'_sub

/--
Corollary 11 (Spector p.13): For any proposition φ and any alternative set ALT,
if ALT∨ = ALT∨∧, then exh_mw(ALT, φ) = exh_ie(ALT, φ).

"If the closure of ALT under disjunction is closed under conjunction,
applying exh_mw and exh_ie give rise to equivalent results."
-/
theorem exhMW_eq_exhIE_of_disjClosure_closedUnderConj (hfin : Set.Finite ALT)
    (hcond : closedUnderConj {p | ∃ Y : Set (Set World), Y ⊆ ALT ∧ p = ⋃₀ Y}) :
    exhMW ALT φ = exhIE ALT φ := by
  -- Let ALT∨ be the disjunction closure of ALT
  let ALT' : Set (Set World) := {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X}
  have hALT' : ALT' = {p | ∃ X : Set (Set World), X ⊆ ALT ∧ p = ⋃₀ X} := rfl
  -- Step 1: exh_mw(ALT) = exh_mw(ALT∨) (disjunction closure is vacuous for exh_mw)
  have hmw_eq : exhMW ALT φ = exhMW ALT' φ := exhMW_disjClosure_eq ALT φ ALT' hALT'
  -- Step 2: exh_ie(ALT) = exh_ie(ALT∨) (Theorem 10)
  have hie_eq : exhIE ALT φ = exhIE ALT' φ := exhIE_disjClosure_eq ALT φ hfin ALT' hALT'
  -- Step 3: ALT∨ is closed under conjunction (by hypothesis)
  -- Therefore exh_mw(ALT∨) = exh_ie(ALT∨) (by Theorem 9)
  have h9 : exhMW ALT' φ = exhIE ALT' φ := exhMW_eq_exhIE_of_closedUnderConj ALT' φ hcond
  -- Combine: exh_mw(ALT) = exh_mw(ALT∨) = exh_ie(ALT∨) = exh_ie(ALT)
  rw [hmw_eq, h9, ← hie_eq]




end Exhaustification
