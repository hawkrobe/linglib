import Linglib.Core.Combinatorics.RootedTree.Planar
import Linglib.Core.Combinatorics.RootedTree.DecEq
import Linglib.Features.Prosody
import Linglib.Phonology.Prosody.Syllable

/-!
# Prosodic trees

The recursive prosodic constituent ([ito-mester-2003]): an ω/φ/… tree over the
prosodic hierarchy. We do **not** define a new tree type — a prosodic tree *is*
the Core labeled ordered rose tree `RootedTree.Planar` instantiated at the
prosodic-level labels, so it inherits `Branching`, `DecidableEq`, `map`, and the
`TreePath` dominance order for free. The prosody layer adds only the
hierarchy-specific reading: containment, recursion, and the yield. (ω-min/ω-max
projections land with the first study that targets prosodic domains.)

Scoring functions are plain `Tree → ℕ` (e.g. `recursionCount`); a grammar is
the lex-minimum of the candidates under their violation profile — mathlib's
`Order.Minimal` (computably, `Core.Optimization`'s `argMinSet`) under
`Order.Preimage profile LexLE`, with no bespoke constraint/tableau structure.
The syntax→prosody Match constraints ([ishihara-kalivoda-2022]) build on the
faithfulness machinery (`OptimalityTheory.Correspondence`, Max/Dep) — future work.

## Main definitions

* `Prosody.Constituent` — a node: a `ProsodicLevel`, a mora `weight` (σ only), and
  `isHead`; with smart constructors `om`/`ph`/`ft`/`syl`.
* `Prosody.Tree` — `RootedTree.Planar Constituent`; the prosodic constituent.
* `Prosody.Tree.Containment` — child level ≤ parent level ([ito-mester-2003]).
* `Prosody.Tree.recursionCount` — parses of one element into the same level
  (= No-Recursion violations); recursion is *representable*, its cost is a constraint.
* `Prosody.Tree.yield` — the terminal weight profile, as a `Yield`.
-/

namespace Prosody

open RootedTree Features.Prosody

/-- A prosodic node: a hierarchy `level`, a mora `weight` (meaningful only at σ),
    and `isHead` — whether it heads its parent (meaningful at σ/foot). Unifies the
    former `PLabel` with the (now-removed) `Features.Prosody.ProsodicConstituent`.
    `weight`/`isHead` are inert at levels where they don't apply (every algorithm
    guards on `level`), so a flat record with defaults — built via the smart
    constructors below — is preferred over a per-level sum. -/
structure Constituent where
  level  : ProsodicLevel
  weight : Syllable.Weight := 0
  isHead : Bool := false
  deriving DecidableEq, Repr

namespace Constituent
/-- ω, a prosodic word. -/
abbrev om : Constituent := { level := .ω }
/-- φ, a phonological phrase. -/
abbrev ph : Constituent := { level := .φ }
/-- A foot, optionally the head of its parent. -/
abbrev ft (isHead : Bool := false) : Constituent := { level := .f, isHead := isHead }
/-- A syllable of the given `weight`, optionally the head of its foot. -/
abbrev syl (weight : Syllable.Weight := 0) (isHead : Bool := false) : Constituent :=
  { level := .σ, weight := weight, isHead := isHead }
end Constituent

/-- A prosodic tree: the Core ordered rose tree `RootedTree.Planar` labeled by
    `Constituent`s. Ordered children give No-Tangling by construction. -/
abbrev Tree := Planar Constituent

namespace Tree

/-- All nodes of the tree (self + descendants), via the Core `Branching` API. -/
def nodes (t : Tree) : List Tree := Core.Order.Branching.subtrees t

/-- Containment / weak Strict Layer ([ito-mester-2003]): every child's level
    is ≤ its parent's in the prosodic hierarchy. Equality (recursion) is allowed;
    its cost is `recursionCount`, not a ban here. -/
def Containment (t : Tree) : Prop :=
  ∀ s ∈ t.nodes, ∀ c ∈ s.children, c.label.level ≤ s.label.level

mutual
/-- No-Recursion violation count ([ito-mester-2003]): parent–child pairs
    that share a level (an element parsed twice into one category). Defined by
    structural recursion (mutual with the list aux), so it reduces under `decide`
    on concrete trees — unlike a `subtrees`-fold via `WellFounded.fix`. -/
def recursionCount : Tree → Nat
  | .node a cs =>
      (cs.filter (fun c => decide (c.label.level = a.level))).length
        + recursionCountList cs
/-- Auxiliary: total recursion count across a list of subtrees. -/
def recursionCountList : List Tree → Nat
  | [] => 0
  | t :: ts => recursionCount t + recursionCountList ts
end

/-- The terminal weight profile (σ-leaves, left to right) as a `Yield` — the
    unparsed σ-weight string. (The headed ω parse is `Prosody.Word`.) -/
def yield (t : Tree) : Yield :=
  (t.nodes.filter (fun s => s.children.isEmpty)).map (fun s => s.label.weight)

end Tree
end Prosody
