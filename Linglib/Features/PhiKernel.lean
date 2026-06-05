import Linglib.Features.Person.Decomposition
import Linglib.Features.Number.Decomposition

/-!
# The Phi Kernel
[harbour-2016]

Person and number features share a carrier skeleton: each is a bivalent
pair under containment, so `Person.Features ≃ Number.Features` through the
`ContainmentPair` hub (`phiKernelEquiv`). `Gender.Features`, Bantu animacy,
and honorific level join the same web via their `ContainmentPairLike`
presentations.

[harbour-2016] (ch. 9, "The Form of the Phi Kernel") draws the
person/number parallel, but locates it elsewhere than this carrier
equivalence: his kernel commonalities are that features denote
*operations* richer than first-order predicates (§9.2 — order of
composition matters), that neither order of composition nor cooccurrence
is extrinsically constrained (§9.3–9.4), and that both families are
*bivalent* with semantically active `−` values (§9.5: person's `±` denote
`⊕`/`⊖` on person lattices, number's `+` the identity and `−` a
type-flexible `¬`). That calculus lives at `Syntax/Minimalist/Phi/` and
`Studies/Harbour2016.lean`. `phiKernelEquiv` formalizes the *descriptive*
residue of the parallel — same two-feature containment carrier — and
equates carriers, not denotations.

## Main declarations

* `phiKernelEquiv` — `Person.Features ≃ Number.Features`, composing each
  domain's `featuresEquiv` through the `ContainmentPair` hub.
-/

namespace Features

/-- Person and number feature carriers are the same containment-pair
skeleton, composed through the `ContainmentPair` hub: `1st ↔ singular`,
`2nd ↔ dual`, `3rd ↔ plural`. One edge of the φ-feature iso-web; equates
carriers, not denotations ([harbour-2016] §9.5.1 — the two domains'
feature values denote differently). -/
def phiKernelEquiv : Person.Features ≃ Number.Features :=
  Person.featuresEquiv.trans Number.featuresEquiv.symm

end Features
