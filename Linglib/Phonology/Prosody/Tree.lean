import Linglib.Core.Combinatorics.RootedTree.Planar
import Linglib.Core.Combinatorics.RootedTree.DecEq
import Linglib.Features.Prosody
import Linglib.Phonology.Prosody.Syllable
import Linglib.Phonology.Prosody.Word

/-!
# Prosodic trees

The recursive prosodic constituent ([ito-mester-2003]): an ω/φ/… tree over the
prosodic hierarchy. We do **not** define a new tree type — a prosodic tree *is*
the Core labeled ordered rose tree `RootedTree.Planar` instantiated at the
prosodic-level labels, so it inherits `Branching`, `DecidableEq`, `map`, and the
`TreePath` dominance order for free. The prosody layer adds only the
hierarchy-specific reading: containment, recursion, and the yield. (ω-min/ω-max
projections land with the first study that targets prosodic domains.)

Scoring functions are plain `ProsTree → ℕ` (e.g. `recursionCount`); a grammar is
the lex-minimum of the candidates under their violation profile — mathlib's
`Order.Minimal` (computably, `Core.Optimization`'s `argMinSet`) under
`Order.Preimage profile LexLE`, with no bespoke constraint/tableau structure.
The syntax→prosody Match constraints ([ishihara-kalivoda-2022]) build on the
faithfulness machinery (`OptimalityTheory.Correspondence`, Max/Dep) — future work.

## Main definitions

* `Prosody.PLabel` — a node label: a `ProsodicLevel`, plus a mora weight (σ only).
* `Prosody.ProsTree` — `RootedTree.Planar PLabel`; the prosodic constituent.
* `Prosody.ProsTree.Containment` — child level ≤ parent level ([ito-mester-2003]).
* `Prosody.ProsTree.recursionCount` — parses of one element into the same level
  (= No-Recursion violations); recursion is *representable*, its cost is a constraint.
* `Prosody.ProsTree.yield` — the terminal weight profile, as a `Word`.
-/

namespace Prosody

open RootedTree Features.Prosody

/-- A prosodic node label: a hierarchy `level`, plus a mora `weight` that is
    meaningful only at the σ level (terminals). -/
structure PLabel where
  level  : ProsodicLevel
  weight : Syllable.Weight := 0
  deriving DecidableEq, Repr

/-- A prosodic tree: the Core ordered rose tree `RootedTree.Planar` labeled by
    prosodic levels. Ordered children give No-Tangling by construction. -/
abbrev ProsTree := Planar PLabel

namespace ProsTree

/-- All nodes of the tree (self + descendants), via the Core `Branching` API. -/
def nodes (t : ProsTree) : List ProsTree := Core.Order.Branching.subtrees t

/-- Containment / weak Strict Layer ([ito-mester-2003]): every child's level
    is ≤ its parent's in the prosodic hierarchy. Equality (recursion) is allowed;
    its cost is `recursionCount`, not a ban here. -/
def Containment (t : ProsTree) : Prop :=
  ∀ s ∈ t.nodes, ∀ c ∈ s.children, c.label.level ≤ s.label.level

mutual
/-- No-Recursion violation count ([ito-mester-2003]): parent–child pairs
    that share a level (an element parsed twice into one category). Defined by
    structural recursion (mutual with the list aux), so it reduces under `decide`
    on concrete trees — unlike a `subtrees`-fold via `WellFounded.fix`. -/
def recursionCount : ProsTree → Nat
  | .node a cs =>
      (cs.filter (fun c => decide (c.label.level = a.level))).length
        + recursionCountList cs
/-- Auxiliary: total recursion count across a list of subtrees. -/
def recursionCountList : List ProsTree → Nat
  | [] => 0
  | t :: ts => recursionCount t + recursionCountList ts
end

/-- The terminal weight profile (σ-leaves, left to right) as a `Word` — the
    σ → ω bridge to the unparsed weight profile. -/
def yield (t : ProsTree) : Word :=
  ⟨(t.nodes.filter (fun s => s.children.isEmpty)).map (fun s => s.label.weight)⟩

end ProsTree
end Prosody
