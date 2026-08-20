import Mathlib.Data.Fintype.EquivFin

/-!
# Roots

The Root terminal of Distributed Morphology: List 1's acategorial atom,
individuated by an arbitrary index and carrying no form or meaning — form
arrives at Vocabulary Insertion, meaning at alloseme selection. `Root` is
a tagged copy of ℕ (`Root.equivNat`), so the root inventory is unbounded
(`Infinite Root`): List 1 is an open class, in contrast with the closed
categorizer inventory (`card_categorizer`).

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [H. Harley, *On the identity of roots*][harley-2014]
-/

namespace DistributedMorphology

/-- A Root terminal node, individuated by an arbitrary index alone — with
deliberately no form or meaning fields, following [harley-2014]'s answer to
what roots are. It receives its form at Vocabulary Insertion. A different
object from the comparative-concept root of `Morphology/Root/Basic.lean`,
which is a contentful morph. -/
@[ext]
structure Root where
  /-- The individuating index. -/
  index : Nat
  deriving DecidableEq, Repr

/-- Roots are their indices and nothing more. -/
def Root.equivNat : Root ≃ ℕ where
  toFun := Root.index
  invFun := Root.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The root inventory is unbounded: List 1 is an open class. -/
instance : Infinite Root := Root.equivNat.infinite_iff.mpr inferInstance

end DistributedMorphology
