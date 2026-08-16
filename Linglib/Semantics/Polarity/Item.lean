/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.LicensingContext
import Linglib.Semantics.Entailment.NaturalLogic

/-!
# Polarity items
[ladusaw-1979] [zwarts-1998] [haspelmath-1997] [lahiri-1998]
[israel-1996] [israel-2001] [israel-2011] [chierchia-2006]

`Polarity.Item`, the lexical record for polarity-sensitive items, with its
licensing parameters instantiated directly: `licensor` is the minimum
Zwarts strength an environment must supply (`none` = not
strength-licensed), `freeChoice` marks licensing by the generic-indefinite
mechanism, and `ppi` marks positive-polarity blocking. Class labels are
derived (`isNPI`, `isFCI`, `isPPI`), not stipulated: a weak NPI is an item
with `licensor = some .weak`, a strict negative-concord item one with
`some .antiMorphic` (clausal negation is the only anti-morphic
environment), a non-strict one `some .antiAdditive` (concord under a
negative quantifier is anti-additive licensing at this grain — the same
requirement as an English strong NPI; the concord phenomenology itself is
`Features/NegativeConcord.lean` territory). The item↔context licensing
relation `LicensingContext.licenses` lives in
`Semantics/Polarity/Licensing.lean`.

The record also carries the [israel-1996] scalar direction and the
[lahiri-1998]-style morphological-composition typology. The full
[israel-2001] scalar-model classification is the extension bundle
`ScalarItem` in `Semantics/Polarity/ScalarModel.lean`, built only for
items that have one.

## Main declarations

* `Item` — the polarity-item record.
* `Item.isNPI`, `Item.isFCI`, `Item.isPPI` — derived class labels.
* `ScalarDirection` — strengthening vs attenuating rhetorical force.
* `NPIMorphology`, `AlternativeType` — composition typology.
-/

namespace Semantics.Polarity

open Features (LicensingContext)

/-! ### Scalar direction -/

/-- Rhetorical force: strengthening items (*ever*, *any*) make the
    assertion stronger than its scalar alternatives, attenuating ones
    (*all that*, *long*) weaker ([israel-1996], [israel-2011]).
    `nonScalar` is an editorial slot — Israel classifies most minimizers,
    including *lift a finger*, as scalar; leave the item's field `none`
    if unsure. -/
inductive ScalarDirection where
  | strengthening
  | attenuating
  | nonScalar
  deriving DecidableEq, Repr

/-! ### Force and composition typology -/

/-- Base quantificational force (when interpretable). -/
inductive BaseForce where
  | existential   -- ∃ (any, some)
  | universal     -- ∀ (every)
  | degree        -- degree/extent (at all, in the least)
  | temporal      -- time reference (ever, yet)
  | manner        -- manner/way (whatsoever)
  | additive      -- additive particle (either, also, too)
  deriving DecidableEq, Repr

/-- Morphological composition of a polarity-sensitive item
    ([lahiri-1998]: Hindi NPIs are transparently indefinite + *even*).
    `indefPlusNeg` covers genuine indefinite + negation morphology
    (Romanian *nimic*, some Slavic n-words). -/
inductive NPIMorphology where
  | indefPlusEven  -- indefinite + 'even'/'also' particle (Hindi bhii,
                   -- Japanese -mo, Korean -to; [haspelmath-1997] A.38.2, A.39.2)
  | indefPlusNeg   -- indefinite + negation (Romanian nimic; some Slavic n-words)
  | plain          -- morphologically simple (English 'any', 'ever')
  | idiomatic      -- frozen idiom ('lift a finger')
  deriving DecidableEq, Repr

/-- Type of alternatives the item activates: cardinality (*ek bhii*),
    contextually salient properties (*koii bhii*) ([lahiri-1998]), or
    subdomain alternatives ([chierchia-2006]). -/
inductive AlternativeType where
  | cardinality
  | contextualProperty
  | domain
  | unspecified
  deriving DecidableEq, Repr

/-! ### The polarity item -/

/-- A lexical entry for a polarity-sensitive item, with the licensing
    parameters instantiated directly: `licensor` (minimum Zwarts strength
    of a licensing environment), `freeChoice` (generic-indefinite
    mechanism), `ppi` (blocked in DE). Class labels derive from these —
    see `isNPI`/`isFCI`/`isPPI` and the docstring conventions in the
    module header. `licensingContexts` is the attested distribution the
    keystone (`LicensingContext.licenses`) checks the parameters
    against. -/
structure Item where
  /-- Surface form -/
  form : String
  /-- Base quantificational/semantic force -/
  baseForce : BaseForce
  /-- Minimum Zwarts strength of a licensing environment
      (`none` = not strength-licensed). -/
  licensor : Option NaturalLogic.DEStrength := none
  /-- Licensed by the generic-indefinite mechanism
      (modals, generics, imperatives, free relatives). -/
  freeChoice : Bool := false
  /-- Positive polarity: blocked in DE environments. -/
  ppi : Bool := false
  /-- Attested licensing environments (empty = needs positive contexts). -/
  licensingContexts : List LicensingContext
  /-- Scalar direction ([israel-1996]); `none` = unclassified. -/
  scalarDirection : Option ScalarDirection := none
  /-- Morphological composition ([lahiri-1998]) -/
  morphology : NPIMorphology := .plain
  /-- Type of alternatives introduced -/
  alternativeType : AlternativeType := .unspecified
  deriving Repr

/-! ### Derived class labels -/

/-- An NPI is an item with a strength requirement. -/
abbrev Item.isNPI (e : Item) : Prop := e.licensor.isSome

/-- A free choice item is one licensed by the generic-indefinite
    mechanism (dual NPI/FCIs like *any* also carry a `licensor`). -/
abbrev Item.isFCI (e : Item) : Prop := e.freeChoice = true

/-- A positive polarity item. -/
abbrev Item.isPPI (e : Item) : Prop := e.ppi = true

end Semantics.Polarity

-- Re-export `LicensingContext` from `Features/` into `Semantics.Polarity` so
-- consumers doing `open Semantics.Polarity` see its constructors in scope.
namespace Semantics.Polarity
export Features (LicensingContext)
end Semantics.Polarity
