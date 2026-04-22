import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Lattice

/-!
# Preference Structures
@cite{condoravdi-lauer-2012} @cite{lauer-2013} @cite{condoravdi-lauer-2016}
@cite{condoravdi-lauer-2011}

A **preference structure** (@cite{condoravdi-lauer-2012} (65)) is a pair
`⟨P, ≺⟩` where `P ⊆ ℘(W)` is a set of propositions and `≺` is a strict
partial order on `P`.

## Layout

* `PreferenceStructure W` — the bare carrier; a strict order on
  `prefs.Elem` packaged as an `IsStrictOrder` instance for compatibility
  with mathlib's order API.
* `maxElts` (eq. 70) — maximal elements, returned as `Set (Set W)` so
  consumers don't have to package membership proofs.
* `consistent (B : Set W)` (eq. 66) — strong, subset-quantified version
  (distinct from the pairwise `consistent` of @cite{condoravdi-lauer-2011};
  fn. 29 of the anankastics paper). Quantifies over arbitrary `X ⊆ prefs`.
* `realistic (B : Set W)` (eq. 67) — preferences are belief-compatible.
* `consistent_implies_realistic` — eq. 67 derived from eq. 66 via the
  singleton-`X` case.
-/

namespace Core.Order

universe u

variable {W : Type u}

/-- A **preference structure**: a set of propositions equipped with a
    strict partial order on the subtype.

    `prec : prefs → prefs → Prop` is typed on the subtype, so the
    `IsStrictOrder` instance is meaningful (no vacuous-off-prefs trap).
    For ergonomic raw access, use `prec p q` with elements of
    `prefs.Elem` (i.e., `⟨_, _⟩` packaged with their membership proof). -/
structure PreferenceStructure (W : Type u) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking on the subtype of preferences. `prec p q` reads
      "q is strictly preferred to p". -/
  prec : prefs → prefs → Prop
  /-- The strict-partial-order axioms, packaged as a mathlib typeclass. -/
  isStrictOrder : IsStrictOrder prefs prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder P.prefs P.prec := P.isStrictOrder

/-- The maximal elements of the preference structure
    (@cite{condoravdi-lauer-2016} (70)), returned as
    propositions in `Set (Set W)`. -/
def maxElts : Set (Set W) :=
  Subtype.val '' { p : P.prefs | ∀ q : P.prefs, ¬ P.prec p q }

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := by
  rintro _ ⟨⟨_, hp⟩, _, rfl⟩; exact hp

/-- Membership in `maxElts` unwrapped: `φ` is maximal iff it's in `prefs`
    and no preference in `prefs` is strictly above it. -/
theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ ∃ hp : φ ∈ P.prefs, ∀ q : P.prefs, ¬ P.prec ⟨φ, hp⟩ q := by
  constructor
  · rintro ⟨⟨_, hp⟩, hmax, rfl⟩; exact ⟨hp, hmax⟩
  · rintro ⟨hp, hmax⟩; exact ⟨⟨φ, hp⟩, hmax, rfl⟩

/-- **Consistency** w.r.t. an information state `B`
    (@cite{condoravdi-lauer-2016} (66)): for any subfamily of
    preferences whose joint realization is incompatible with `B`, some
    pair is strictly ranked. The quantification over arbitrary `X ⊆ prefs`
    (not just pairs) is the strong form, distinct from
    @cite{condoravdi-lauer-2011}'s pairwise variant (fn. 29). -/
def consistent (B : Set W) : Prop :=
  ∀ X : Set (Set W), X ⊆ P.prefs → B ∩ ⋂ p ∈ X, p = ∅ →
    ∃ p ∈ X, ∃ q ∈ X, ∃ (hp : p ∈ P.prefs) (hq : q ∈ P.prefs),
      P.prec ⟨p, hp⟩ ⟨q, hq⟩

/-- **Realism** w.r.t. an information state
    (@cite{condoravdi-lauer-2016} (67)): every preference is
    belief-compatible. -/
def realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

/-- @cite{condoravdi-lauer-2016} fn. 30: realism follows from
    consistency via the singleton-`X` case combined with irreflexivity. -/
theorem consistent_implies_realistic {B : Set W} (hC : P.consistent B) :
    P.realistic B := by
  intro p hp hpB
  have h := hC {p} (Set.singleton_subset_iff.mpr hp) (by
    rw [Set.biInter_singleton, Set.inter_comm]; exact hpB)
  simp only [Set.mem_singleton_iff] at h
  obtain ⟨_, rfl, _, rfl, _, _, hpq⟩ := h
  exact Std.Irrefl.irrefl (r := P.prec) _ hpq

/-- **Pair belief-consistency of maximal preferences** — abstract version
    of @cite{condoravdi-lauer-2016} p. 30 (end of § 5.4): given
    `consistent B`, two maximal preferences cannot have an empty
    intersection w.r.t. `B`. The four cases of the consistency conclusion
    `∃ p, q ∈ {φ, ψ}, prec p q` are blocked by `IsStrictOrder`
    irreflexivity (diagonal pairs) and maximality (off-diagonal pairs). -/
theorem maxElts_pair_belief_compatible {B : Set W} (hC : P.consistent B)
    {φ ψ : Set W} (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) :
    (φ ∩ ψ) ∩ B ≠ ∅ := by
  intro hEmpty
  obtain ⟨hφP, hφmax⟩ := P.mem_maxElts.mp hφ
  obtain ⟨hψP, hψmax⟩ := P.mem_maxElts.mp hψ
  have hX_sub : ({φ, ψ} : Set (Set W)) ⊆ P.prefs :=
    Set.insert_subset hφP (Set.singleton_subset_iff.mpr hψP)
  have hX_int : B ∩ ⋂ p ∈ ({φ, ψ} : Set (Set W)), p = ∅ := by
    rw [Set.biInter_pair, Set.inter_comm]; exact hEmpty
  obtain ⟨p, hpX, q, hqX, hpP, hqP, hpq⟩ := hC _ hX_sub hX_int
  have hpDisj : p = φ ∨ p = ψ := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hpX; exact hpX
  have hqDisj : q = φ ∨ q = ψ := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hqX; exact hqX
  -- Use term-mode `▸` rewrites since `rw` can't handle the dependent
  -- types in `Subtype.mk p hpP` (the proof's type changes when p is
  -- rewritten). The four cases collapse via Subtype proof irrelevance.
  rcases hpDisj with hp | hp <;> rcases hqDisj with hq | hq
  · -- p = φ, q = φ: irreflexivity (after equating the two Subtypes)
    have hpq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨p, hpP⟩ := Subtype.ext (hq.trans hp.symm)
    exact Std.Irrefl.irrefl (⟨p, hpP⟩ : P.prefs) (hpq_eq ▸ hpq)
  · -- p = φ, q = ψ: φ-maximality forbids φ ≺ ψ
    have hp_eq : (⟨p, hpP⟩ : P.prefs) = ⟨φ, hp ▸ hpP⟩ := Subtype.ext hp
    have hq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨ψ, hq ▸ hqP⟩ := Subtype.ext hq
    exact hφmax ⟨ψ, hq ▸ hqP⟩ (hp_eq ▸ hq_eq ▸ hpq)
  · -- p = ψ, q = φ: ψ-maximality forbids ψ ≺ φ
    have hp_eq : (⟨p, hpP⟩ : P.prefs) = ⟨ψ, hp ▸ hpP⟩ := Subtype.ext hp
    have hq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨φ, hq ▸ hqP⟩ := Subtype.ext hq
    exact hψmax ⟨φ, hq ▸ hqP⟩ (hp_eq ▸ hq_eq ▸ hpq)
  · -- p = ψ, q = ψ
    have hpq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨p, hpP⟩ := Subtype.ext (hq.trans hp.symm)
    exact Std.Irrefl.irrefl (⟨p, hpP⟩ : P.prefs) (hpq_eq ▸ hpq)

end PreferenceStructure

end Core.Order
