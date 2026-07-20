import Linglib.Morphology.Exponence.Select
import Mathlib.Data.Finset.Card

/-!
# Feature-decomposition exponence and the Subset Principle

The realizational engine for privative **feature-decomposition** accounts of
syncretism ([caha-2009], [bobaljik-2012]): a cell space is decomposed into
feature sets `D : Cell → Finset K`, and a rule applies where its feature
specification is contained in the cell's — the **Subset Principle**. Competition
is [halle-1997]'s feature counting: the applicable rule of greatest
specification wins, as the shared core's `selectBy` on `feats.card`.

Where the linear containment engine (`Exponence/Containment/`) orders spans by a
single threshold, this engine orders arbitrary feature *sets* by inclusion, so
`card`-maximization is genuine specificity only when the applicable
specifications happen to be nested; the general soundness lives in the
`IsWinner` strict-competition predicate rather than the core's linear
`selectBy_isElsewhereWinner`. The linear engine embeds as the chain
decomposition `chainDecomp i = Finset.Iic i` (`Exponence/Containment/Selection.lean`).

## Main declarations

* `Rule` — a feature specification plus an exponent; `Applies` is Subset
  containment
* `pattern` — the surface exponent at each cell, `selectBy` on `feats.card`
* `IsWinner` — strict feature-count competition
* `noABA` — the order-theoretic *ABA exclusion for a cell triple whose
  decomposition nests the middle cell between the outer two
-/

namespace Morphology.Decomposition

open Morphology Morphology.Exponence

variable {K : Type*} [DecidableEq K]

/-- A rule of exponence over a feature decomposition `D`: a feature
specification and an exponent. Applicability is the **Subset Principle** — the
rule's features are a subset of the cell's ([halle-1997]). -/
structure Rule (Cell : Type*) (D : Cell → Finset K) (F : Type*) where
  /-- The rule's feature specification. -/
  feats : Finset K
  /-- The exponent inserted. -/
  exponent : F
  deriving DecidableEq

variable {Cell F : Type*} {D : Cell → Finset K}

instance : Exponence.Rule (Rule Cell D F) Cell F :=
  ⟨Rule.exponent, fun r c => r.feats ⊆ D c⟩

instance : Exponence.DecidableApplies (Rule Cell D F) Cell :=
  fun c r => inferInstanceAs (Decidable (r.feats ⊆ D c))

omit [DecidableEq K] in
@[simp] theorem applies_iff {r : Rule Cell D F} {c : Cell} :
    Exponence.Applies r c ↔ r.feats ⊆ D c := Iff.rfl

/-- The specificity preorder: applicability-set inclusion, so the engine
participates in the shared core's Elsewhere selection theory
(`Exponence/Select.lean`). Unlike the linear containment order this is only a
preorder — incomparable specifications (No Case Containment) are the point. -/
instance : Preorder (Rule Cell D F) := Exponence.toPreorder

omit [DecidableEq K] in
/-- Specificity unfolds to applicability-set inclusion: `r ≤ s` iff `r` applies
wherever `s` does. -/
theorem le_iff {r s : Rule Cell D F} :
    r ≤ s ↔ ∀ ⦃c⦄, Exponence.Applies r c → Exponence.Applies s c :=
  Iff.rfl

/-- The surface pattern of a vocabulary: at each cell, the exponent of the most
highly specified applicable rule — the Elsewhere Principle as `selectBy` on
feature cardinality ([halle-1997]'s counting formulation). -/
def pattern (v : List (Rule Cell D F)) (c : Cell) : Option F :=
  (selectBy (fun r : Rule Cell D F => r.feats.card) v c).map Rule.exponent

/-- Strict competition: `r` beats every other applicable rule on feature
cardinality. -/
def IsWinner (v : List (Rule Cell D F)) (c : Cell) (r : Rule Cell D F) : Prop :=
  r ∈ v ∧ r.feats ⊆ D c ∧
    ∀ s ∈ v, s.feats ⊆ D c → s ≠ r → s.feats.card < r.feats.card

/-- ***ABA, order-theoretically**: whenever the middle cell `y` nests between
the outer cells — `D y ⊆ D z` (appliers at `y` persist to `z`) and
`D x ∩ D z ⊆ D y` (appliers at both outer cells reach `y`) — a rule winning both
`x` and `z` also wins `y`, so no exponent can interrupt an A_A pattern with a
distinct middle B. The hypotheses are the shared profile of Strong and Weak Case
Containment; No Case Containment violates the first. -/
theorem noABA {v : List (Rule Cell D F)} {A B : Rule Cell D F} {x y z : Cell}
    (h1 : D y ⊆ D z) (h2 : D x ∩ D z ⊆ D y)
    (hx : IsWinner v x A) (hz : IsWinner v z A) (hy : IsWinner v y B) : B = A := by
  by_contra hne
  have hAy : A.feats ⊆ D y := fun k hk =>
    h2 (Finset.mem_inter.mpr ⟨hx.2.1 hk, hz.2.1 hk⟩)
  have hAB : A.feats.card < B.feats.card :=
    hy.2.2 A hx.1 hAy (fun h => hne h.symm)
  have hBz : B.feats ⊆ D z := fun k hk => h1 (hy.2.1 hk)
  exact absurd (hz.2.2 B hy.1 hBz hne) (Nat.lt_asymm hAB)

end Morphology.Decomposition
