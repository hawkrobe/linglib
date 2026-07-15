import Linglib.Core.Logic.Assignment

/-!
# Fibered variable lookup
[hofmann-2025], [charlow-2019]

The lookup interface of dynamic semantics: `iLookup : Ctx → V → W → M E`
returns the `M`-family of values for a variable at a world. Frameworks
diverge on what a lookup *returns* when a variable has no referent —
Hofmann's `.star` (`M = Entity`, instance in `ICDRT/Basic.lean`), Charlow's
`∅` (`M = Set`, instance in `Studies/Charlow2019.lean`), plain values for
the extensional baseline (`M = Id`, the `Assignment` instance below) — and
the shared signature is what makes per-family lookups comparable
(`Reference/PronounDenotation.lean`'s `interpPronoun_eq_iLookup`).

The class is data-only (the `Membership`/`GetElem` pattern): update laws
and accessibility predicates are each family's own commitments and live in
the family's file; the comparisons live in the studies that draw them
(`Studies/Hofmann2025.lean`, `Studies/Charlow2019.lean`).
-/

namespace Semantics.Dynamic.Context

open _root_.Core (Assignment)

universe u v w x

/-- Fibered lookup: `iLookup i v w : M E` returns the `M`-family of values
for variable `v` at world `w` — `M = Entity` (ICDRT), `M = Set` (Charlow's
marginal), `M = Id` (extensional baseline). `M` is `outParam`: each `Ctx`
carries exactly one effect functor. -/
class HasFiberedLookup (M : outParam (Type u → Type u))
    (Ctx : Type v) (V : outParam (Type w))
    (W : outParam (Type x)) (E : outParam (Type u)) where
  /-- Look up the M-family of values for variable `v` at world `w`. -/
  iLookup : Ctx → V → W → M E

/-- Assignments as the *extensional* dynamic-semantic context, with
`M = Id` (no effect) and `W = PUnit` (no world parameter) — the baseline
shared by [groenendijk-stokhof-1991] DPL, [muskens-1996] CDRT, and
[kamp-reyle-1993] DRT, whose state types are all definitionally
`Nat → E = Assignment E`. Lookup is function application. -/
instance instAssignmentHasFiberedLookup (E : Type u) :
    HasFiberedLookup Id (Assignment E) Nat PUnit.{u + 1} E where
  iLookup g v _ := g v

end Semantics.Dynamic.Context
