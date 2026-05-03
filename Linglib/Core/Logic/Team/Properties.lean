import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.Insert

/-!
# Team-semantic properties of formulas (Anttila 2021 §2.2)

@cite{anttila-2021}

The four canonical properties of formulas in a team-semantic logic, from
Anttila's "The Logic of Free Choice Axiomatizations of State-based Modal
Logics" (MSc Thesis, ILLC 2021), Definition 2.2.1:

- **Downward closure**: support survives subset
- **Union closure**: support survives binary union (binary; n-ary follows by induction)
- **Empty team property**: support holds vacuously on the empty team
- **Flatness**: support equivalent to pointwise support at each point in the team

The central technical theorem is **Proposition 2.2.2**: φ is flat iff φ has all
three of downward closure, union closure, and the empty team property.

This file is the foundational substrate for all team-semantic logics in linglib
— BSML and BSML* currently; QBSML (Aloni & van Ormondt 2023), inquisitive,
dependence logic, modal team logic when added. Each logic provides its own
`support : Model → Form → Finset Point → Prop` function; this file delivers
the properties + flatness theorem generically over the support relation.

## Provenance

Anttila axiomatizes six team-semantic logics (PT⁺, MDᵂ, SMLᵂ, SGMLᵂ, BSML,
BSMLᵂ) using this chassis. Anttila Proposition 2.2.8 (NE-free formulas have
downward + empty; ⨼-free formulas are union closed) becomes a per-logic theorem
proved against this substrate; the corollary "NE-free + ⨼-free → flat" is then
a direct application of `flat_iff_downwardClosed_unionClosed_emptyState` below.

## Mathlib-shape rationale

The properties are NOT a typeclass — they are predicates parameterized over a
support relation. Different consumers can speak about the same formula under
different support relations (e.g., support vs anti-support in bilateral logics).
A typeclass would either commit to a canonical support relation per Form (too
rigid) or require disambiguation at every site (more friction than the
parameter-passing). Parametric polymorphism fits cleanly.

## Naming: "team" vs "state"

Anttila §2.2 calls the property "the empty *state* property" and similar.
We use "team" (Hodges 1997, Väänänen 2007) — the foundational umbrella term
that generalizes uniformly across BSML (team = set of worlds), QBSML (team =
set of (world, assignment) indices), dependence logic (team = set of
assignments), etc. The two terms are interchangeable in this layer.
-/

namespace Core.Logic.Team

variable {W : Type*} [DecidableEq W]
variable {Form : Type*}
variable {Model : Type*}

-- ============================================================================
-- §1 The four team-semantic properties (Anttila Definition 2.2.1)
-- ============================================================================

/-- Downward closure: support is preserved under taking subsets of the team.
    Anttila Definition 2.2.1.

    NE-bearing formulas typically lack this (Anttila Proposition 2.2.8). -/
def downwardClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s t : Finset W), t ⊆ s → support M φ s → support M φ t

/-- Union closure (binary form): support is preserved under binary union.

    Anttila Definition 2.2.1 uses the n-ary form `∀ S ≠ ∅, (∀s ∈ S, support M φ s)
    → support M φ (⋃S)`. Binary closure + the empty team property give the
    n-ary form by induction (see `unionClosed_finset` below).

    The global / inquisitive disjunction ⨼ in Anttila's BSMLᵂ is the source
    of union-closure failure (Anttila Proposition 2.2.8 part 2). BSML proper
    (without ⨼) has all formulas union-closed. -/
def unionClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s t : Finset W), support M φ s → support M φ t → support M φ (s ∪ t)

/-- Empty team property: φ is supported on ∅ in every model.

    Most formulas have this. The exception is NE (Anttila Definition 2.1.5):
    `M, s ⊨ NE` iff `s ≠ ∅`, so NE fails on ∅. -/
def emptyTeam (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model), support M φ ∅

/-- Flatness: team-support equals pointwise support at each point in the team.

    Anttila Definition 2.2.1 (note: the thesis writes "for all w ∈ W" but
    proves and uses "for all w ∈ s" — see Proposition 2.2.2 proof). The
    standard team-semantic notion (Yang & Väänänen 2017) is "for all w ∈ s",
    which is what we use here.

    Flat formulas reduce to classical modal logic on singleton teams
    (Anttila Proposition 2.2.16). -/
def flat (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ (M : Model) (s : Finset W), support M φ s ↔ ∀ w ∈ s, support M φ {w}

-- ============================================================================
-- §2 Anttila Proposition 2.2.2: flatness ↔ downward + union + empty
-- ============================================================================

/-- **Anttila Proposition 2.2.2**: A formula has the flatness property if and
    only if it has the downward closure, union closure, and empty team
    properties.

    This is the central technical lemma derivative results across all
    team-semantic logics depend on. The conservative-extension theorem
    (Anttila Proposition 2.2.13/2.2.15: SGMLᵂ and BSMLᵂ both extend ML)
    follows from this + per-logic proofs that NE-free formulas have all
    three properties. -/
theorem flat_iff_downwardClosed_unionClosed_emptyTeam
    (support : Model → Form → Finset W → Prop) (φ : Form) :
    flat support φ ↔
      downwardClosed support φ ∧ unionClosed support φ ∧ emptyTeam support φ := by
  constructor
  · -- Forward direction: flatness gives all three properties
    intro hFlat
    refine ⟨?_, ?_, ?_⟩
    · -- Downward closure
      intro M s t hsub hsupp
      rw [hFlat]
      intro w hw
      exact (hFlat M s).mp hsupp w (hsub hw)
    · -- Union closure
      intro M s t hs ht
      rw [hFlat]
      intro w hw
      simp only [Finset.mem_union] at hw
      cases hw with
      | inl h => exact (hFlat M s).mp hs w h
      | inr h => exact (hFlat M t).mp ht w h
    · -- Empty team property
      intro M
      rw [hFlat]
      intro w hw
      simp at hw
  · -- Reverse direction: three properties give flatness
    rintro ⟨hd, hu, he⟩ M s
    constructor
    · -- support s → ∀ w ∈ s, support {w}
      intro hsupp w hw
      exact hd M s {w} (Finset.singleton_subset_iff.mpr hw) hsupp
    · -- (∀ w ∈ s, support {w}) → support s
      intro h
      induction s using Finset.induction_on with
      | empty => exact he M
      | @insert w t hw ih =>
        have hw_supp : support M φ {w} := h w (Finset.mem_insert_self w t)
        have ht_supp : support M φ t := by
          apply ih
          intro v hv
          exact h v (Finset.mem_insert_of_mem hv)
        have heq : insert w t = ({w} : Finset W) ∪ t := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        rw [heq]
        exact hu M {w} t hw_supp ht_supp

-- ============================================================================
-- §3 Convenience corollaries
-- ============================================================================

/-- If φ is flat, then it is downward-closed. -/
theorem downwardClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : downwardClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).1

/-- If φ is flat, then it is union-closed. -/
theorem unionClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : unionClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.1

/-- If φ is flat, then it satisfies the empty team property. -/
theorem emptyTeam_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : emptyTeam support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.2

/-- Constructive form of Anttila 2.2.2: combine the three properties to get
    flatness. -/
theorem flat_of_downwardClosed_unionClosed_emptyTeam
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (hd : downwardClosed support φ) (hu : unionClosed support φ)
    (he : emptyTeam support φ) : flat support φ :=
  (flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mpr ⟨hd, hu, he⟩

-- ============================================================================
-- §4 N-ary union closure (derived from binary + empty)
-- ============================================================================

/-- N-ary union closure, derived from binary union closure + empty team property.
    Matches Anttila Definition 2.2.1's original n-ary statement. -/
theorem unionClosed_finset
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (hu : unionClosed support φ) (he : emptyTeam support φ)
    (M : Model) (S : Finset (Finset W))
    (h : ∀ s ∈ S, support M φ s) :
    support M φ (S.sup id) := by
  induction S using Finset.induction_on with
  | empty => simp; exact he M
  | @insert s T hs ih =>
    have hs_supp : support M φ s := h s (Finset.mem_insert_self s T)
    have hT_supp : support M φ (T.sup id) := by
      apply ih
      intro t ht
      exact h t (Finset.mem_insert_of_mem ht)
    rw [Finset.sup_insert]
    exact hu M s (T.sup id) hs_supp hT_supp

end Core.Logic.Team
