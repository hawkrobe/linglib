import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Filter
import Linglib.Core.Order.Normality

/-!
# Similarity orderings

@cite{lewis-1973} @cite{stalnaker-1968}

A `SimilarityOrdering W` equips a type of worlds with a *centered* ternary
relation `closer w₀ w₁ w₂` ("`w₁` is at least as close to `w₀` as `w₂` is")
that is reflexive and transitive in the second/third arguments at every
center. This is the order-theoretic substrate of variably-strict
counterfactuals (@cite{lewis-1973} / @cite{stalnaker-1968}) and of any
"closest-world" semantics — selectional, supervaluation, homogeneity, etc.

The structure lives in `Core.Order` (not `Conditionals`) because it is a
general-purpose primitive: it is used directly by counterfactual operators
in `Theories/Semantics/Conditionals/`, by alternative-sensitive operators
(@cite{santorio-2018}), by causal psycholinguistic models in
`Theories/Semantics/Causation/`, and by any future "closest match" theory.

## Key operations

- `closer w₀ w₁ w₂` — the relation itself (reflexive, transitive)
- `closestWorlds w₀ A` — minimal elements of a `Finset` under `closer`
- `atCenter w₀` — coerce to a `Core.Order.NormalityOrder` centered at `w₀`
- `isCentered` — strong centering: `w` is the unique closest world to itself
- `candidateSelections` — the set of selection-function candidates induced
  by the ordering (bridge to Stalnaker selection)
- `≤[sim, w₀]` notation: `w₁ ≤[sim, w₀] w₂` reads "`w₁` is at least as
  similar to `w₀` as `w₂` is" (@cite{lewis-1973}-style notation)

## Connection to selection functions

`Core.SelectionFunction` and `SimilarityOrdering` are dual presentations of
the same intuition. A coherent selection function induces a similarity
ordering via the `coherentSelectionToSimilarity` constructor (which lives
in `Theories/Semantics/Conditionals/Basic.lean` because it depends on
selection-function machinery from `Core.SelectionFunction`).
-/

namespace Core.Order

/-! ## Structure -/

/-- A **similarity ordering** on worlds: a centered ternary relation
    `closer w₀ w₁ w₂` saying that `w₁` is at least as close to `w₀` as
    `w₂` is, reflexive and transitive in `w₁`/`w₂`/`w₃` at each center
    `w₀`. -/
structure SimilarityOrdering (W : Type*) where
  /-- `closer w₀ w₁ w₂` means `w₁` is at least as close to `w₀` as `w₂` is. -/
  closer : W → W → W → Prop
  /-- Every world is at least as close to any center as itself. -/
  closer_refl (w₀ w : W) : closer w₀ w w
  /-- Transitivity in the candidate arguments at a fixed center. -/
  closer_trans (w₀ w₁ w₂ w₃ : W) :
    closer w₀ w₁ w₂ → closer w₀ w₂ w₃ → closer w₀ w₁ w₃
  /-- The relation is decidable. -/
  closerDec (w₀ w₁ w₂ : W) : Decidable (closer w₀ w₁ w₂)

instance {W : Type*} (sim : SimilarityOrdering W) (w₀ w₁ w₂ : W) :
    Decidable (sim.closer w₀ w₁ w₂) :=
  sim.closerDec w₀ w₁ w₂

namespace SimilarityOrdering

variable {W : Type*}

/-! ## Constructors -/

/-- Construct a `SimilarityOrdering` from a `Bool`-valued function.
    Reflexivity and transitivity proofs can typically be discharged by
    `decide` on finite types. -/
def ofBool (f : W → W → W → Bool)
    (hrefl : ∀ w₀ w, f w₀ w w = true)
    (htrans : ∀ w₀ w₁ w₂ w₃, f w₀ w₁ w₂ = true → f w₀ w₂ w₃ = true →
      f w₀ w₁ w₃ = true) :
    SimilarityOrdering W where
  closer w₀ w₁ w₂ := f w₀ w₁ w₂ = true
  closer_refl := hrefl
  closer_trans w₀ w₁ w₂ w₃ := htrans w₀ w₁ w₂ w₃
  closerDec _ _ _ := inferInstance

/-- The `NormalityOrder` centered at world `w₀`: `le w₁ w₂` iff `w₁` is
    at least as close to `w₀` as `w₂` is. Bridges variably-strict
    semantics to the default-reasoning infrastructure (`optimal`,
    `refine`, `respects`, CR1–CR4) in `Core.Order.Normality`. -/
def atCenter (sim : SimilarityOrdering W) (w₀ : W) : NormalityOrder W where
  le := sim.closer w₀
  le_refl w := sim.closer_refl w₀ w
  le_trans w₁ w₂ w₃ := sim.closer_trans w₀ w₁ w₂ w₃

/-! ## Centering -/

/-- A **strongly centered** similarity ordering: every world is *strictly*
    closest to itself. This is the centering axiom of @cite{lewis-1973}
    that licenses the inference from variably-strict to material truth. -/
def isCentered (sim : SimilarityOrdering W) : Prop :=
  ∀ w w' : W, w ≠ w' → sim.closer w w w' ∧ ¬sim.closer w w' w

/-! ## Closest worlds -/

/-- The closest `A`-worlds to `w₀`: the minimal elements of `A` under the
    similarity preorder centered at `w₀`. In @cite{lewis-1973}'s notation,
    `min_{≤_w}(A) = {w' ∈ A : ¬∃ w'' ∈ A. w'' <_w w'}`. -/
def closestWorlds [DecidableEq W] (sim : SimilarityOrdering W) (w₀ : W)
    (A : Finset W) : Finset W :=
  A.filter fun w' => ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w'

@[simp]
theorem closestWorlds_empty [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) :
    sim.closestWorlds w₀ ∅ = ∅ := by
  simp only [closestWorlds, Finset.filter_empty]

theorem closestWorlds_subset [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) (A : Finset W) :
    sim.closestWorlds w₀ A ⊆ A :=
  Finset.filter_subset _ A

theorem mem_closestWorlds [DecidableEq W] (sim : SimilarityOrdering W)
    (w₀ : W) (A : Finset W) (w' : W) :
    w' ∈ sim.closestWorlds w₀ A ↔
      w' ∈ A ∧ ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w' := by
  simp only [closestWorlds, Finset.mem_filter]

/-- **Closest-world membership is preserved when restricting to a
    subset.** If `B ⊆ A` and `w` is a closest `A`-world that lies in
    `B`, then `w` is also a closest `B`-world. (Restricting to fewer
    competitors can only preserve, never lose, "closest" status.)

    This is the structural lemma underlying the
    @cite{ciardelli-zhang-champollion-2018} §1.2 argument that any
    minimal-change semantics inherits the switches falsification: at the
    actual world, the closest worlds in `A̅ ∪ B̅` decompose into closest
    worlds in `A̅` or `B̅` individually. -/
theorem mem_closestWorlds_of_subset [DecidableEq W]
    (sim : SimilarityOrdering W)
    {w₀ w : W} {A B : Finset W} (hBA : B ⊆ A)
    (hw : w ∈ sim.closestWorlds w₀ A) (hwB : w ∈ B) :
    w ∈ sim.closestWorlds w₀ B := by
  rw [mem_closestWorlds] at hw ⊢
  exact ⟨hwB, fun w'' hw'' => hw.2 w'' (hBA hw'')⟩

end SimilarityOrdering

/-! ## Selection-function bridge primitives

These derive selection-function-flavoured notions from a similarity
ordering without depending on `Core.SelectionFunction` itself, so they
can sit in `Core.Order`. The full selection-function ↔ similarity
duality (`coherentSelectionToSimilarity`) lives in
`Theories/Semantics/Conditionals/Basic.lean` where both sides of the
bridge are imported. -/

/-- **Candidate selection set**: the worlds in `A ∩ domain` that are
    minimal at `w` under the similarity ordering. Any selection function
    `s` with `s(w, A) ∈ candidateSelections sim domain w A` is
    "legitimate" with respect to `sim`. -/
def candidateSelections {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (w : W) (A : Set W) : Set W :=
  let pWorlds := A ∩ domain
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, sim.closer w w' w'' }

/-- **Comparative-closeness notation** (@cite{lewis-1973}): `w₁ ≤[sim, w₀] w₂`
    reads "`w₁` is at least as similar to `w₀` as `w₂` is". A direct
    @cite{lewis-1973}-style alias for `sim.closer w₀ w₁ w₂`. -/
notation:50 w₁ " ≤[" sim "," w₀ "] " w₂ =>
  SimilarityOrdering.closer sim w₀ w₁ w₂

end Core.Order
