import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Lattice

/-!
# Preference structures

A **preference structure** ([condoravdi-lauer-2012] (65)) is a pair
`⟨P, ≺⟩` where `P ⊆ ℘(W)` is a set of propositions and `≺` is a strict
partial order — the mathematical spine of Condoravdi & Lauer's
effective-preference framework ([condoravdi-lauer-2011], [lauer-2013],
[condoravdi-lauer-2016]), consumed by the *want* semantics in
`Desire.lean` and the dynamic necessity operator of
`Semantics/Dynamic/UpdateSemantics/Necessity.lean`. The ranking is
carried as a relation on all of `Set W` with quantification scoped to
`prefs` (the `maximals`-style encoding); its values off `prefs` are
never observed.

`maxElts` (their eq. 70) collects the maximal elements. Relative to an
information state `B`, `consistent` (eq. 66) demands that any subfamily
of preferences jointly incompatible with `B` contain a strictly ranked
pair — the strong, subset-quantified form, distinct from
[condoravdi-lauer-2011]'s pairwise variant — and `realistic` (eq. 67)
demands every preference be belief-compatible. Realism is *derivable*
from consistency (`consistent_implies_realistic`, their fn. 30), so the
agent's designated *effective* preference function ((68)) is rendered
as a background of preference structures pointwise `consistent` with
the belief state — a hypothesis, not a bundled refinement.
`maxElts_pair_belief_compatible` is the conflicting-desires blocker:
two maximal preferences of a consistent structure meet inside `B`.

`maxInducedLe` is the world-side preorder induced by maximal
preferences — the Kratzer-style ([kratzer-1981]) derivation of a world
ordering from an ordering source, applied to `maxElts`; the bridge to a
`List`-valued `Modality.Kratzer.OrderingSource` requires a finiteness
witness and lives downstream.
-/

variable {W : Type*}

/-- A preference structure: a set of propositions `prefs` and a strict
    ranking `prec`, with `prec p q` read "q is strictly preferred to p".
    The ranking is a relation on all of `Set W`; only its restriction to
    `prefs` is ever observed. -/
structure PreferenceStructure (W : Type*) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking. `prec p q` reads "q is strictly preferred
      to p". -/
  prec : Set W → Set W → Prop
  /-- The strict-partial-order axioms, packaged as a mathlib typeclass. -/
  isStrictOrder : IsStrictOrder (Set W) prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder (Set W) P.prec := P.isStrictOrder

/-- The maximal elements of the preference structure: the preferences
    with nothing in `prefs` strictly above them. -/
def maxElts : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := fun _ h => h.1

/-- Consistency w.r.t. an information state `B`: any subfamily of
    preferences whose joint realization is incompatible with `B`
    contains a strictly ranked pair. -/
def consistent (B : Set W) : Prop :=
  ∀ X : Set (Set W), X ⊆ P.prefs → B ∩ ⋂ p ∈ X, p = ∅ →
    ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- Realism w.r.t. an information state: every preference is
    belief-compatible. -/
def realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

/-- Realism follows from consistency via the singleton-`X` case combined
    with irreflexivity. -/
theorem consistent_implies_realistic {B : Set W} (hC : P.consistent B) :
    P.realistic B := by
  intro p hp hpB
  obtain ⟨q, hq, r, hr, hqr⟩ := hC {p} (Set.singleton_subset_iff.mpr hp) (by
    rw [Set.biInter_singleton, Set.inter_comm]; exact hpB)
  rw [Set.mem_singleton_iff] at hq hr
  rw [hq, hr] at hqr
  exact irrefl_of P.prec p hqr

/-- Pair belief-consistency of maximal preferences: given `consistent B`,
    two maximal preferences cannot have an empty intersection w.r.t. `B`.
    The four cases of the consistency conclusion are blocked by
    irreflexivity (diagonal pairs) and maximality (off-diagonal pairs). -/
theorem maxElts_pair_belief_compatible {B : Set W} (hC : P.consistent B)
    {φ ψ : Set W} (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) :
    (φ ∩ ψ) ∩ B ≠ ∅ := by
  intro hEmpty
  obtain ⟨hφP, hφmax⟩ := hφ
  obtain ⟨hψP, hψmax⟩ := hψ
  have hX_sub : ({φ, ψ} : Set (Set W)) ⊆ P.prefs :=
    Set.insert_subset hφP (Set.singleton_subset_iff.mpr hψP)
  have hX_int : B ∩ ⋂ p ∈ ({φ, ψ} : Set (Set W)), p = ∅ := by
    rw [Set.biInter_pair, Set.inter_comm]; exact hEmpty
  obtain ⟨p, hpX, q, hqX, hpq⟩ := hC _ hX_sub hX_int
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpX hqX
  rcases hpX with hp | hp <;> rcases hqX with hq | hq <;> rw [hp, hq] at hpq
  · exact irrefl_of P.prec φ hpq
  · exact hφmax ψ hψP hpq
  · exact hψmax φ hφP hpq
  · exact irrefl_of P.prec ψ hpq

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
