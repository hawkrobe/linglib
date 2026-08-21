import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Filter
import Linglib.Core.Order.PreorderLattice

/-!
# Similarity orderings

A `SimilarityOrdering W` is a family of comparative-similarity preorders on worlds, one
for each center: `closer w₀ w₁ w₂` says that `w₁` is at least as similar to `w₀` as `w₂`
is ([lewis-1973], [stalnaker-1968]). Each `closer w₀` is reflexive and transitive
(`Std.Refl`, `IsTrans` instances) and decidable. `closest w₀ s` is the set of `s`-worlds
maximally similar to `w₀` — the minimal elements of `s` under `closer w₀` — with
`closestWorlds` its `Finset` form; the Limit Assumption (`closest_nonempty`,
`closestWorlds_nonempty`) is `Set.Finite.exists_minimal`. `isCentered` is strong
centering, and `w₁ ≤[sim, w₀] w₂` is notation for `sim.closer w₀ w₁ w₂`.
-/

namespace Semantics.Conditionals

/-! ## Structure -/

/-- A family of comparative-similarity preorders, one for each center `w₀`:
`closer w₀ w₁ w₂` says that `w₁` is at least as similar to `w₀` as `w₂` is. -/
structure SimilarityOrdering (W : Type*) where
  /-- `w₁` is at least as similar to `w₀` as `w₂` is. -/
  closer : W → W → W → Prop
  closer_refl : ∀ w₀ w, closer w₀ w w
  closer_trans :
    ∀ w₀ w₁ w₂ w₃, closer w₀ w₁ w₂ → closer w₀ w₂ w₃ → closer w₀ w₁ w₃
  /-- Closeness is decidable at each center. -/
  decClose : ∀ w₀ w₁ w₂, Decidable (closer w₀ w₁ w₂)

namespace SimilarityOrdering

variable {W : Type*} (sim : SimilarityOrdering W) (w₀ : W)

instance (w₁ w₂ : W) : Decidable (sim.closer w₀ w₁ w₂) := sim.decClose w₀ w₁ w₂

instance : Std.Refl (sim.closer w₀) := ⟨sim.closer_refl w₀⟩

instance : IsTrans W (sim.closer w₀) := ⟨sim.closer_trans w₀⟩

/-- The preorder centered at `w₀`, for local use in proofs. -/
@[reducible] def atCenter : Preorder W :=
  Preorder.ofLE (sim.closer w₀) (sim.closer_refl w₀) (sim.closer_trans w₀)

/-! ## Constructors -/

/-- Construct a `SimilarityOrdering` from a `Bool`-valued function.
    Reflexivity and transitivity can typically be discharged by `decide`. -/
def ofBool (f : W → W → W → Bool)
    (hrefl : ∀ w₀ w, f w₀ w w = true)
    (htrans : ∀ w₀ w₁ w₂ w₃, f w₀ w₁ w₂ = true → f w₀ w₂ w₃ = true →
      f w₀ w₁ w₃ = true) :
    SimilarityOrdering W where
  closer w₀ w₁ w₂ := f w₀ w₁ w₂ = true
  closer_refl := hrefl
  closer_trans := htrans
  decClose w₀ w₁ w₂ := inferInstanceAs (Decidable (f w₀ w₁ w₂ = true))

/-! ## Centering -/

/-- A **strongly centered** similarity ordering: every world is strictly
    closest to itself ([lewis-1973]'s centering axiom). -/
def isCentered (sim : SimilarityOrdering W) : Prop :=
  ∀ w w' : W, w ≠ w' → sim.closer w w w' ∧ ¬sim.closer w w' w

/-! ## Closest worlds -/

/-- The closest `A`-worlds to `w₀`: the minimal elements of `A` under the
    similarity preorder centered at `w₀`. -/
def closestWorlds [DecidableEq W] (sim : SimilarityOrdering W) (w₀ : W)
    (A : Finset W) : Finset W :=
  A.filter fun w' => ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w'

@[simp]
theorem closestWorlds_empty [DecidableEq W] (sim : SimilarityOrdering W) (w₀ : W) :
    sim.closestWorlds w₀ ∅ = ∅ := by
  simp only [closestWorlds, Finset.filter_empty]

theorem closestWorlds_subset [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) (A : Finset W) : sim.closestWorlds w₀ A ⊆ A :=
  Finset.filter_subset _ A

theorem mem_closestWorlds [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) (A : Finset W) (w' : W) :
    w' ∈ sim.closestWorlds w₀ A ↔
      w' ∈ A ∧ ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w' := by
  simp only [closestWorlds, Finset.mem_filter]

/-- **Closest-world membership is preserved when restricting to a subset.** -/
theorem mem_closestWorlds_of_subset [DecidableEq W] (sim : SimilarityOrdering W)
    {w₀ w : W} {A B : Finset W} (hBA : B ⊆ A)
    (hw : w ∈ sim.closestWorlds w₀ A) (hwB : w ∈ B) :
    w ∈ sim.closestWorlds w₀ B := by
  rw [mem_closestWorlds] at hw ⊢
  exact ⟨hwB, fun w'' hw'' => hw.2 w'' (hBA hw'')⟩

/-- **Limit Assumption** ([lewis-1973]): every non-empty `Finset` has a
    closest world. Routes through `Set.Finite.exists_minimal` on the
    preorder centered at `w₀`. -/
theorem closestWorlds_nonempty [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) {A : Finset W} (hne : A.Nonempty) :
    (sim.closestWorlds w₀ A).Nonempty := by
  let _ : Preorder W := sim.atCenter w₀
  obtain ⟨m, hmA, hmin⟩ :=
    A.finite_toSet.exists_minimal (Finset.coe_nonempty.mpr hne)
  refine ⟨m, ?_⟩
  rw [mem_closestWorlds]
  refine ⟨hmA, fun w'' hw'' => ?_⟩
  by_cases h : sim.closer w₀ w'' m
  · exact Or.inl (hmin hw'' h)
  · exact Or.inr h

/-! ## Closest worlds of a set -/

/-- The closest `s`-worlds to `w₀`: the minimal elements of `s` under the similarity
preorder centered at `w₀`. `closestWorlds` is the `Finset` form. -/
def closest (sim : SimilarityOrdering W) (w₀ : W) (s : Set W) : Set W :=
  {w ∈ s | ∀ w' ∈ s, sim.closer w₀ w w' ∨ ¬ sim.closer w₀ w' w}

theorem closest_subset (sim : SimilarityOrdering W) (w₀ : W) (s : Set W) :
    sim.closest w₀ s ⊆ s :=
  Set.sep_subset _ _

@[simp, norm_cast]
theorem coe_closestWorlds [DecidableEq W] (sim : SimilarityOrdering W) (w₀ : W) (A : Finset W) :
    (sim.closestWorlds w₀ A : Set W) = sim.closest w₀ A := by
  ext; simp [closestWorlds, closest]

/-- The Limit Assumption for finite sets. -/
theorem closest_nonempty (sim : SimilarityOrdering W) (w₀ : W) {s : Set W} (hs : s.Finite)
    (hne : s.Nonempty) : (sim.closest w₀ s).Nonempty := by
  let _ : Preorder W := sim.atCenter w₀
  obtain ⟨m, hm, hmin⟩ := hs.exists_minimal hne
  refine ⟨m, hm, fun w' hw' => ?_⟩
  by_cases h : sim.closer w₀ w' m
  · exact Or.inl (hmin hw' h)
  · exact Or.inr h

instance [Fintype W] (sim : SimilarityOrdering W) (w₀ : W) (s : Set W)
    [DecidablePred (· ∈ s)] : DecidablePred (· ∈ sim.closest w₀ s) :=
  fun w => inferInstanceAs
    (Decidable (w ∈ s ∧ ∀ w' ∈ s, sim.closer w₀ w w' ∨ ¬ sim.closer w₀ w' w))

end SimilarityOrdering

/-! ## Selection-function bridge primitives -/

/-- **Candidate selection set**: the worlds in `A ∩ domain` that are minimal
    at `w` under the similarity ordering. -/
def candidateSelections {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (w : W) (A : Set W) : Set W :=
  let pWorlds := A ∩ domain
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, sim.closer w w' w'' }

/-- **Comparative-closeness notation** ([lewis-1973]): `w₁ ≤[sim, w₀] w₂`
    reads "`w₁` is at least as similar to `w₀` as `w₂` is". -/
notation:50 w₁ " ≤[" sim "," w₀ "] " w₂ =>
  SimilarityOrdering.closer sim w₀ w₁ w₂

end Semantics.Conditionals
