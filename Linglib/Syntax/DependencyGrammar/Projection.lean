import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Core.Relation.ReflTransGen
import Mathlib.Logic.Relation
import Mathlib.Data.List.Sort

/-!
# Projections of dependency graphs

BFS-computed projections (yields) of positions, their interval/gap/block
analysis, and Prop-level dominance as the reflexive-transitive closure of
the graph adjacency, bridged to BFS membership.
[kuhlmann-nivre-2006], [kuhlmann-2013].

## Main declarations

* `projection`, `Dominates` — the computable yield and its Prop-level
  counterpart (reachability in `Graph.toDigraph`).
* `mem_projection_iff` — projection membership is dominance, by
  construction (decidable dominance via `Core/Relation/ReflTransGen.lean`).
* `gapDegreeAt`, `Graph.gapDegree`, `blockDegreeAt`, `Graph.blockDegree`,
  `isProjective` — the projectivity hierarchy.

## Implementation notes

* `insertionSort`, not `mergeSort`: the former is structurally recursive and
  reduces under `decide`/`rfl`; `mergeSort` uses well-founded recursion and
  does not reduce in the kernel.
* The interval/gap/block combinatorics is stated over `List Nat`
  (projection values), independent of the graph carrier.
-/

namespace DependencyGrammar

/-! ### Interval combinatorics on sorted position lists -/

/-- Whether a sorted list of positions forms an interval with no internal
    gaps. A projection is an interval iff its node has gap degree 0. -/
def isInterval (sorted : List Nat) : Bool :=
  match sorted with
  | [] | [_] => true
  | _ => sorted.getLast! - sorted.head! + 1 == sorted.length

/-- The **gaps** in a sorted projection: adjacent pairs (jₖ, jₖ₊₁) with
    jₖ₊₁ − jₖ > 1. ([kuhlmann-nivre-2006], Definition 6) -/
def gaps (sorted : List Nat) : List (Nat × Nat) :=
  sorted.zip (sorted.drop 1) |>.filter λ (a, b) => b - a > 1

/-- The **blocks** of a sorted projection: maximal contiguous segments.
    The number of blocks equals gap degree + 1 and corresponds to the
    fan-out of the LCFRS rule extracted for that node. -/
def blocks : List Nat → List (List Nat)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest =>
    if b = a + 1 then
      match blocks (b :: rest) with
      | [] => [[a]]
      | first :: remaining => (a :: first) :: remaining
    else [a] :: blocks (b :: rest)


/-! ### Dominance and projection -/

section Projection

variable {n : ℕ}

/-- Prop-level dominance: reachability in the graph's digraph. -/
def Dominates (g : Graph n) (v x : Fin n) : Prop :=
  Relation.ReflTransGen g.Adj v x

/-- Dominance is decidable: adjacency is decidable and successors lie in
    `finRange n` (`Core/Relation/ReflTransGen.lean`). -/
instance (g : Graph n) : DecidableRel (Dominates g) :=
  Relation.ReflTransGen.decidable_of_finite (List.finRange n)
    (λ _ b _ => List.mem_finRange b)

@[refl] theorem Dominates.refl {g : Graph n} {v : Fin n} : Dominates g v v :=
  Relation.ReflTransGen.refl

theorem Dominates.step {g : Graph n} {v w x : Fin n}
    (hvw : g.Adj v w) (hwx : Dominates g w x) : Dominates g v x :=
  Relation.ReflTransGen.head hvw hwx

theorem Dominates.trans {g : Graph n} {v w x : Fin n}
    (h₁ : Dominates g v w) (h₂ : Dominates g w x) : Dominates g v x :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Dominates.edge {g : Graph n} {v w : Fin n} (h : g.Adj v w) :
    Dominates g v w :=
  Relation.ReflTransGen.single h

/-- Head-first induction on dominance. -/
@[elab_as_elim]
theorem Dominates.head_induction_on {g : Graph n} {v x : Fin n}
    {motive : (w : Fin n) → Dominates g w x → Prop}
    (h : Dominates g v x)
    (refl : motive x .refl)
    (step : ∀ {v w : Fin n} (hedge : g.Adj v w) (hdom : Dominates g w x),
      motive w hdom → motive v (.step hedge hdom)) :
    motive v h :=
  Relation.ReflTransGen.head_induction_on h refl step

/-- **Projection** π(v): the yield of position v — all positions it
    dominates, including itself — in ascending position order.
    ([kuhlmann-nivre-2006], Definition 3: a graph is projective iff every
    projection is an interval.) -/
def projection (g : Graph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (λ x => decide (Dominates g v x))

/-- **Bridge**: projection membership is dominance. -/
@[simp] theorem mem_projection_iff {g : Graph n} {v x : Fin n} :
    x ∈ projection g v ↔ Dominates g v x := by
  simp [projection]

/-- The projection as position values, for the interval combinatorics. -/
def projectionVals (g : Graph n) (v : Fin n) : List Nat :=
  (projection g v).map (·.val)

/-- The projection is strictly increasing: it filters the ascending
    `finRange`. -/
theorem projection_chain (g : Graph n) (v : Fin n) :
    (projectionVals g v).IsChain (· < ·) := by
  refine List.isChain_iff_pairwise.mpr (List.Pairwise.map _ (λ a b h => h) ?_)
  exact (List.pairwise_lt_finRange n).filter _

/-- **Gap degree** of a position. ([kuhlmann-nivre-2006], Definition 6) -/
def gapDegreeAt (g : Graph n) (v : Fin n) : Nat :=
  (gaps (projectionVals g v)).length

/-- **Gap degree** of a graph: max over positions.
    ([kuhlmann-nivre-2006], Definition 7). Gap degree 0 ⟺ projective. -/
def Graph.gapDegree (g : Graph n) : Nat :=
  (List.finRange n).map (gapDegreeAt g) |>.foldl max 0

/-- **Block-degree** of a position: blocks in its projection.
    Block-degree = gap degree + 1 = fan-out of the extracted LCFRS rule. -/
def blockDegreeAt (g : Graph n) (v : Fin n) : Nat :=
  (blocks (projectionVals g v)).length

/-- **Block-degree** of a graph: max over positions. Block-degree 1 ⟺
    projective. Bounded block-degree + well-nestedness give polynomial
    parsing ([kuhlmann-2013], Lemma 10). -/
def Graph.blockDegree (g : Graph n) : Nat :=
  (List.finRange n).map (blockDegreeAt g) |>.foldl max 0

/-- **Projectivity**: every projection is an interval.
    ([kuhlmann-nivre-2006], Definition 3) -/
def isProjective (g : Graph n) : Bool :=
  (List.finRange n).all λ v => isInterval (projectionVals g v)

/-! ### Well-formedness -/

/-- The graph is a dependency tree: nothing points at the root, every other
    position has exactly one head, and no position dominates itself. On
    `Fin n` these imply rootedness and connectivity — every non-root
    position's head chain terminates at the unique headless position. -/
structure Graph.IsTree (g : Graph n) : Prop where
  not_adj_root : ∀ v, ¬ g.Adj v g.root
  existsUnique_adj : ∀ w, w ≠ g.root → ∃! v, g.Adj v w
  acyclic : ∀ v, ¬ Relation.TransGen g.Adj v v

theorem Graph.isTree_iff (g : Graph n) :
    g.IsTree ↔ (∀ v, ¬ g.Adj v g.root) ∧
      (∀ w, w ≠ g.root → ∃! v, g.Adj v w) ∧
      (∀ v, ¬ Relation.TransGen g.Adj v v) :=
  ⟨λ h => ⟨h.1, h.2, h.3⟩, λ h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (g : Graph n) (v w : Fin n) : Decidable (Relation.TransGen g.Adj v w) :=
  decidable_of_iff (∃ u, g.Adj v u ∧ Dominates g u w)
    Relation.TransGen.head'_iff.symm

instance (g : Graph n) (w : Fin n) : Decidable (∃! v, g.Adj v w) :=
  decidable_of_iff (∃ v, g.Adj v w ∧ ∀ u, g.Adj u w → u = v) Iff.rfl

instance (g : Graph n) : Decidable g.IsTree :=
  decidable_of_iff _ (g.isTree_iff).symm

/-- No arc closes a dominance cycle, on acyclic graphs. -/
theorem not_adj_dominates {g : Graph n}
    (hacyc : ∀ v, ¬ Relation.TransGen g.Adj v v)
    {v w : Fin n} (hadj : g.Adj v w) (hdom : Dominates g w v) : False :=
  hacyc v (Relation.TransGen.head' hadj hdom)

/-- Dominance is antisymmetric on acyclic graphs. -/
theorem Dominates.antisymm {g : Graph n}
    (hacyc : ∀ v, ¬ Relation.TransGen g.Adj v v)
    {v w : Fin n} (hvw : Dominates g v w) (hwv : Dominates g w v) : v = w := by
  rcases Relation.ReflTransGen.cases_head hvw with rfl | ⟨u, hvu, huw⟩
  · rfl
  · exact absurd (huw.trans hwv) (λ h => not_adj_dominates hacyc hvu h)

end Projection

end DependencyGrammar
