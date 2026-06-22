/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Basic

/-!
# Scan direction

The orientation of a left-to-right vs right-to-left scan, shared by the transducer
machines and the side-determinacy predicates of `Core/Computability/Subregular/Function/`.
Extracted to its own leaf so the footprint-predicate file (`SideDeterminacy.lean`) does
not have to depend on the transducer machine file just to name a `left`/`right` tag.
-/

namespace Subregular

/-- The orientation of an FST scan: `left` consumes input head-first, `right`
tail-first (via `List.reverse` conjugation). The two scan modes give rise to
distinct function classes — isomorphic under reversal but not equal as
subclasses of the regular functions over un-reversed strings. -/
inductive Direction
  | left
  | right
  deriving DecidableEq, Repr

end Subregular
