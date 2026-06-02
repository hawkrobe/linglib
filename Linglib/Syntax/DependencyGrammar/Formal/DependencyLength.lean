import Linglib.Syntax.DependencyGrammar.Formal.NonProjective

/-!
# Dependency Length Minimization

Formalises the core quantity behind [futrell-gibson-2020]'s claim that
natural languages minimise total dependency length beyond what independent
constraints predict, together with [behaghel-1909]'s "Oberstes Gesetz"
threshold predicate. The two short-before-long arithmetic lemmas record the
*direction* of the DLM savings at the lemma level; the per-paper example trees
and cross-linguistic data sit in `Studies/FutrellEtAl2020.lean`,
`Studies/ArnoldEtAl2000.lean`, and `Studies/FedzechkinaEtAl2017.lean`.

## Main declarations

* `depLength` — linear distance `|headIdx - depIdx|` for a single dependency.
* `totalDepLength` — sum of `depLength` over a tree's dependencies; the quantity
  DLM minimises.
* `oberstesGesetz` — Behaghel's threshold predicate: every dependency has
  length ≤ `threshold`.
* `single_dep_direction_irrelevant` — head-before-dependent and
  dependent-before-head yield equal length.

## Implementation notes

`depLength` is `max - min` rather than absolute value to stay in `Nat`. The
consumers (`Studies/FutrellEtAl2020`, `HarmonicOrder`, `EnhancedDependencies`)
open `DepGrammar.DependencyLength` to pick up `depLength`/`totalDepLength`.
-/

namespace DepGrammar.DependencyLength

open DepGrammar

/-! ### Core quantities -/

/-- Linear distance between head and dependent, `|headIdx - depIdx|`. -/
def depLength (d : Dependency) : Nat :=
  max d.headIdx d.depIdx - min d.headIdx d.depIdx

/-- Total dependency length of a tree: the quantity minimised by DLM. -/
def totalDepLength (t : DepTree) : Nat :=
  t.deps.foldl (λ acc d => acc + depLength d) 0

/-! ### Behaghel's Oberstes Gesetz -/

/-- [behaghel-1932]'s Oberstes Gesetz: every dependency has length at
most `threshold`. -/
def oberstesGesetz (t : DepTree) (threshold : Nat) : Bool :=
  t.deps.all λ d => depLength d ≤ threshold

/-! ### Short-before-long -/

/-- Smaller subtree closer to the head has no greater contribution to dep
length than larger subtree closer. Base arithmetic case: subtree of size `s1`
at distance 1 versus size `s2` at distance `s1 + 2`. -/
theorem short_before_long_minimizes (s1 s2 : Nat) (h : s1 ≤ s2) :
    1 + (s1 + 2) ≤ 1 + (s2 + 2) := by omega

/-- The arithmetic savings of placing the smaller subtree first. -/
theorem short_before_long_savings (s1 s2 : Nat) (_ : s1 ≤ s2) :
    1 + (s2 + 2) - (1 + (s1 + 2)) = s2 - s1 := by omega

/-! ### Symmetry -/

/-- Head and dependent are interchangeable in `depLength`. -/
theorem single_dep_direction_irrelevant (h d : Nat) :
    depLength ⟨h, d, .nsubj⟩ = depLength ⟨d, h, .nsubj⟩ := by
  simp only [depLength, Nat.max_comm, Nat.min_comm]

/-- `depLength` ignores the dependency relation. -/
theorem depLength_symmetric (h d : Nat) (r : UD.DepRel) :
    depLength ⟨h, d, r⟩ = depLength ⟨d, h, r⟩ := by
  simp only [depLength, Nat.max_comm, Nat.min_comm]

/-- An adjacent dependency has length 1. -/
theorem adjacent_dep_length (h : Nat) :
    depLength ⟨h, h + 1, .nsubj⟩ = 1 := by
  simp [depLength]

/-- A self-loop has length 0. -/
theorem self_loop_length (i : Nat) :
    depLength ⟨i, i, .nsubj⟩ = 0 := by
  simp [depLength]

/-- An empty tree has total length 0. -/
theorem empty_tree_dep_length :
    totalDepLength { words := [], deps := [], rootIdx := 0 } = 0 := rfl

end DepGrammar.DependencyLength
