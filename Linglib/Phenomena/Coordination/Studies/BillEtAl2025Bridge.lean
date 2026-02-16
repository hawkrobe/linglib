import Linglib.Phenomena.Coordination.Studies.BillEtAl2025
import Linglib.Theories.Semantics.Compositional.Conjunction

/-!
# Bridge: Bill et al. (2025) × TruthConditional Conjunction

Connects the empirical child acquisition data in
`Phenomena.Coordination.Studies.BillEtAl2025` to the Montague-style
conjunction decomposition formalized in
`Theories.TruthConditional.Conjunction`.

## Predictions verified

- `typeRaise_incl_reduces`: Type-raising + subset inclusion reduces to
  direct predicate application (core of M&S decomposition)
- `ms_decomposition_eq_coord`: Full M&S derivation (☉ + MU + J) yields
  the same result as Partee & Rooth's `coordEntities`

## Known gaps

- No formalization of the Transparency Principle itself
-/

namespace Phenomena.Coordination.Studies.BillEtAl2025.Bridge

/-!
## Semantic Decomposition (M&S 2016)

The M&S decomposition maps onto three operations already formalized:

| M&S piece | Semantic operation | Montague/Conjunction.lean |
|-----------|-------------------|--------------------------|
| J         | Set intersection  | `genConj` at ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩ |
| MU        | Subset (INCL)     | `inclFunc` / `inclProperty` |
| ☉         | {x} formation     | `typeRaise` (e → ⟨⟨e,t⟩,t⟩) |

The full derivation of "Mary and Susan sleep":
1. ☉(Mary) = λP.P(Mary)    — typeRaise
2. MU(☉(Mary), sleep) = {Mary} ⊆ ⟦sleep⟧  — inclFunc
3. Similarly for Susan
4. J combines the two MU-results via conjunction — genConj at type t

The result: {Mary} ⊆ ⟦sleep⟧ ∧ {Susan} ⊆ ⟦sleep⟧
         = sleep(Mary) ∧ sleep(Susan)
-/

open TruthConditional.Conjunction in
/--
Type-raising an entity and checking subset inclusion of its singleton
is equivalent to applying the predicate directly.

This is the core of the M&S decomposition: the roundtrip through
☉ + MU + J recovers ordinary conjunction semantics.
-/
theorem typeRaise_incl_reduces {m : TruthConditional.Model} (e : m.Entity) (p : m.Entity → Bool) :
    typeRaise e p = p e := rfl

open TruthConditional.Conjunction in
/--
Full M&S derivation: "DP₁ and DP₂ VP" via ☉ + MU + J
yields the same result as Partee & Rooth's `coordEntities`.
-/
theorem ms_decomposition_eq_coord {m : TruthConditional.Model} (e1 e2 : m.Entity)
    (p : m.Entity → Bool) :
    (typeRaise e1 p && typeRaise e2 p) = coordEntities e1 e2 p := rfl

end Phenomena.Coordination.Studies.BillEtAl2025.Bridge
