import Linglib.Syntax.DependencyGrammar.Basic
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
* `dominates_iff_mem_projection` — the bridge (port in progress).
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


/-! ### Projection -/

section Projection

variable {n : ℕ}

/-- **Projection** π(v): the yield of position v — all positions it
    transitively dominates, including itself — sorted ascending.
    ([kuhlmann-nivre-2006], Definition 3: a graph is projective iff every
    projection is an interval.) -/
def projection (g : Graph n) (v : Fin n) : List (Fin n) :=
  let rec go (queue : List (Fin n)) (visited : List (Fin n)) (fuel : Nat) :
      List (Fin n) :=
    match fuel, queue with
    | 0, _ => visited
    | _, [] => visited
    | fuel' + 1, node :: rest =>
      if visited.contains node then go rest visited fuel'
      else go (rest ++ g.children node) (node :: visited) fuel'
  (go [v] [] (n + 1)).insertionSort (· ≤ ·)

/-- The projection as position values, for the interval combinatorics. -/
def projectionVals (g : Graph n) (v : Fin n) : List Nat :=
  (projection g v).map (·.val)

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

/-- BFS `go` produces a Nodup list from a Nodup `visited`. -/
private theorem go_nodup (g : Graph n) (queue visited : List (Fin n))
    (fuel : Nat) (hv : visited.Nodup) :
    (projection.go g queue visited fuel).Nodup := by
  induction fuel generalizing queue visited with
  | zero => exact hv
  | succ fuel' ih =>
    match queue with
    | [] => exact hv
    | node :: rest =>
      simp only [projection.go]
      split
      · exact ih rest visited hv
      · rename_i hnotcontains
        apply ih
        have hnotin : node ∉ visited := by
          intro hmem
          exact hnotcontains (by simpa using hmem)
        exact List.nodup_cons.mpr ⟨hnotin, hv⟩

/-- The projection is strictly increasing. -/
theorem projection_chain (g : Graph n) (v : Fin n) :
    (projectionVals g v).IsChain (· < ·) := by
  sorry -- TODO(port): via go_nodup + perm_insertionSort + pairwise, then map ·.val strict mono

/-- Prop-level dominance: reachability in the graph's digraph. -/
def Dominates (g : Graph n) (v x : Fin n) : Prop :=
  Relation.ReflTransGen g.Adj v x

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

/-- **Bridge**: BFS projection membership ↔ dominance. -/
theorem dominates_iff_mem_projection (g : Graph n) (v x : Fin n) :
    Dominates g v x ↔ x ∈ projection g v := by
  sorry -- TODO(port): both directions from the old go_dominates_of_mem / go_children_complete suite

end Projection

end DependencyGrammar
