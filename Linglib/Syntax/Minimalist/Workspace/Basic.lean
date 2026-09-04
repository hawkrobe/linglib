/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Workspaces

A workspace is a forest, a finite multiset, of syntactic objects. The forest product is disjoint
union with unit the empty forest, so a workspace is exactly what `of'` lifts into the Hopf algebra
`ConnesKreimer ℤ (UnorderedTree Vertex)`. A moved element occupies repeated isomorphic components,
and the number of copies is the chain's multiplicity (`Workspace.chainMultiplicity`): chain
identity lives at the workspace level, with no index on the trace leaf. Merge on workspaces and
its identity with the algebraic Merge operator are in `Merge/SyntacticObject.lean`.

## Main definitions

* `Minimalist.Workspace`: forests of syntactic objects.
* `Minimalist.Workspace.chainMultiplicity`: the multiplicity of a syntactic object in a workspace.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.1)
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-- A workspace is a forest of syntactic objects. -/
abbrev Workspace : Type := Forest SyntacticObject

/-- `chainMultiplicity S W = W.count S`, the number of isomorphic copies of `S` in `W`. -/
def Workspace.chainMultiplicity (S : SyntacticObject) (W : Workspace) : Nat := W.count S

/-- Two isomorphic components form a chain of two. -/
example : Workspace.chainMultiplicity SyntacticObject.trace
    {SyntacticObject.trace, SyntacticObject.trace} = 2 := by decide

end Minimalist
