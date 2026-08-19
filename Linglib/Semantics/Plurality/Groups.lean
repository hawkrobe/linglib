import Linglib.Semantics.Mereology

/-!
# Group formation and dissolution

[landman-1989] [landman-2000]

Landman's group operators over a part-of domain: `up` packs a plural sum
into a group atom — *the committee* as a singular entity over its
members — and `down` dissolves the group back into the underlying sum.
The carrier is any `SemilatticeSup`, so the operators serve the domain of
individuals and the domain of events alike ([landman-2000]); in the event
domain, a symmetric verb's atomic event dissolves into the sum of its
directional sub-events ([siloni-2012] §4.1).

## Main declarations

* `GroupStructure` — `up`/`down` with the atomicity and dissolution laws.
* `GroupStructure.up_injective` — distinct sums form distinct groups.
-/

namespace Semantics.Plurality

/-- Landman's group structure: `up` packs a sum into a group atom, `down`
    recovers the underlying sum. The two laws are the operative core of
    [landman-1989]'s postulates. -/
structure GroupStructure (E : Type*) [SemilatticeSup E] where
  /-- Group formation (Landman's `↑`). -/
  up : E → E
  /-- Group dissolution (Landman's `↓`). -/
  down : E → E
  /-- A group is an atom: it has no proper parts. -/
  atom_up (x : E) : Mereology.Atom (up x)
  /-- Dissolution inverts formation. -/
  down_up (x : E) : down (up x) = x

namespace GroupStructure

variable {E : Type*} [SemilatticeSup E] (G : GroupStructure E)

/-- Distinct sums form distinct group atoms. -/
theorem up_injective : Function.Injective G.up :=
  Function.LeftInverse.injective G.down_up

end GroupStructure

end Semantics.Plurality
