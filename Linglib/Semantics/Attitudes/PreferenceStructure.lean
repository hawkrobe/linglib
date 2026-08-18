import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Lattice

/-!
# Preference structures

A **preference structure** ([condoravdi-lauer-2012] (65)) is a pair
`⟨P, ≺⟩` where `P ⊆ ℘(W)` is a set of propositions and `≺` is a strict
partial order on `P` — the mathematical spine of Condoravdi & Lauer's
effective-preference framework ([condoravdi-lauer-2011], [lauer-2013],
[condoravdi-lauer-2016]), consumed by the *want* semantics of
`CondoravdiLauer.lean` and the dynamic necessity operator of
`Semantics/Dynamic/UpdateSemantics/Necessity.lean`.

`maxElts` (their eq. 70) collects the maximal elements. Relative to an
information state `B`, `consistent` (eq. 66) demands that any subfamily
of preferences jointly incompatible with `B` contain a strictly ranked
pair — the strong, subset-quantified form, distinct from
[condoravdi-lauer-2011]'s pairwise variant — and `realistic` (eq. 67)
demands every preference be belief-compatible. Realism is *derivable*
from consistency (`consistent_implies_realistic`, their fn. 30), so the
`EffectivePreference` refinement — the agent's designated,
action-guiding structure — carries consistency as its sole axiom, with
realism as the theorem `EffectivePreference.realistic`; C&L present
both as axioms.

`maxInducedLe` is the world-side preorder induced by maximal
preferences — the Kratzer-style ([kratzer-1981]) derivation of a world
ordering from an ordering source, applied to `maxElts`; the bridge to a
`List`-valued `Modality.Kratzer.OrderingSource` requires a finiteness
witness and lives downstream.
-/

variable {W : Type*}

/-- A preference structure: a set of propositions equipped with a
    strict partial order on the subtype.

    `prec : prefs → prefs → Prop` is typed on the subtype, so the
    `IsStrictOrder` instance is meaningful (no vacuous-off-prefs trap).
    For ergonomic raw access, use `prec p q` with elements of
    `prefs.Elem` (i.e., `⟨_, _⟩` packaged with their membership proof). -/
structure PreferenceStructure (W : Type*) where
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

/-- The maximal elements of the preference structure, returned as
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

/-- Consistency w.r.t. an information state `B`: for any subfamily of
    preferences whose joint realization is incompatible with `B`, some
    pair is strictly ranked. -/
def consistent (B : Set W) : Prop :=
  ∀ X : Set (Set W), X ⊆ P.prefs → B ∩ ⋂ p ∈ X, p = ∅ →
    ∃ p ∈ X, ∃ q ∈ X, ∃ (hp : p ∈ P.prefs) (hq : q ∈ P.prefs),
      P.prec ⟨p, hp⟩ ⟨q, hq⟩

/-- Realism w.r.t. an information state: every preference is
    belief-compatible. -/
def realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

/-- Realism follows from consistency via the singleton-`X` case combined
    with irreflexivity. -/
theorem consistent_implies_realistic {B : Set W} (hC : P.consistent B) :
    P.realistic B := by
  intro p hp hpB
  have h := hC {p} (Set.singleton_subset_iff.mpr hp) (by
    rw [Set.biInter_singleton, Set.inter_comm]; exact hpB)
  simp only [Set.mem_singleton_iff] at h
  obtain ⟨_, rfl, _, rfl, _, _, hpq⟩ := h
  exact Std.Irrefl.irrefl (r := P.prec) _ hpq

/-- Pair belief-consistency of maximal preferences: given `consistent B`,
    two maximal preferences cannot have an empty intersection w.r.t. `B`.
    The four cases of the consistency conclusion are blocked by
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
  · have hpq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨p, hpP⟩ := Subtype.ext (hq.trans hp.symm)
    exact Std.Irrefl.irrefl (⟨p, hpP⟩ : P.prefs) (hpq_eq ▸ hpq)
  · have hp_eq : (⟨p, hpP⟩ : P.prefs) = ⟨φ, hp ▸ hpP⟩ := Subtype.ext hp
    have hq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨ψ, hq ▸ hqP⟩ := Subtype.ext hq
    exact hφmax ⟨ψ, hq ▸ hqP⟩ (hp_eq ▸ hq_eq ▸ hpq)
  · have hp_eq : (⟨p, hpP⟩ : P.prefs) = ⟨ψ, hp ▸ hpP⟩ := Subtype.ext hp
    have hq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨φ, hq ▸ hqP⟩ := Subtype.ext hq
    exact hψmax ⟨φ, hq ▸ hqP⟩ (hp_eq ▸ hq_eq ▸ hpq)
  · have hpq_eq : (⟨q, hqP⟩ : P.prefs) = ⟨p, hpP⟩ := Subtype.ext (hq.trans hp.symm)
    exact Std.Irrefl.irrefl (⟨p, hpP⟩ : P.prefs) (hpq_eq ▸ hpq)

/-! ### The world preorder induced by maximal preferences -/

/-- The world-level preorder induced by maximal preferences:
    `maxInducedLe w v` iff `w` verifies every maximal preference that
    `v` verifies. -/
def maxInducedLe : W → W → Prop :=
  fun w v => ∀ p ∈ P.maxElts, v ∈ p → w ∈ p

theorem maxInducedLe_refl (w : W) :
    P.maxInducedLe w w := fun _ _ hw => hw

theorem maxInducedLe_trans {w v u : W}
    (hwv : P.maxInducedLe w v) (hvu : P.maxInducedLe v u) :
    P.maxInducedLe w u :=
  fun p hp hu => hwv p hp (hvu p hp hu)

end PreferenceStructure

/-! ### Effective preference structures -/

/-- The agent's *effective* preference structure at a world, relative to
    the information state `B`: the designated, action-guiding
    `PreferenceStructure`, distinguished by consistency. Realism is the
    derived `EffectivePreference.realistic`. -/
structure EffectivePreference (W : Type*) (B : Set W)
    extends PreferenceStructure W where
  /-- Consistency w.r.t. the information state. -/
  isConsistent : toPreferenceStructure.consistent B

namespace EffectivePreference

variable {B : Set W}

/-- Effective preferences are realistic: derived from consistency. -/
theorem realistic (E : EffectivePreference W B) :
    E.toPreferenceStructure.realistic B :=
  E.toPreferenceStructure.consistent_implies_realistic E.isConsistent

end EffectivePreference
