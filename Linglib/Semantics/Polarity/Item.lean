/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.LicensingContext
import Linglib.Semantics.NaturalLogic

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

The record also carries the [israel-2001] scalar-model annotations
(`ScalarValue` × `ScalarDirection` × `Canonicity` × `LikelihoodEffect`;
predictions in `Semantics/Polarity/Israel.lean`) and the
[lahiri-1998]-style morphological-composition typology.

## Main declarations

* `Item` — the polarity-item record.
* `Item.isNPI`, `Item.isFCI`, `Item.isPPI` — derived class labels.
* `ScalarValue`, `ScalarDirection`, `Canonicity`, `LikelihoodEffect` —
  the Israel scalar-model axes.
* `NPIMorphology`, `AlternativeType` — composition typology.
-/

namespace Semantics.Polarity

open Features (LicensingContext)

/-! ### The Israel scalar-model axes -/

/-- Where the item sits on its scale relative to the norm: emphatic NPIs
    typically denote low values (*a wink*), emphatic PPIs high ones
    (*tons*); inverted items reverse the pattern ([israel-2001]). -/
inductive ScalarValue where
  | high
  | low
  | unknown
  deriving DecidableEq, Repr

/-- Rhetorical force: strengthening items (*ever*, *any*) make the
    assertion stronger than its scalar alternatives, attenuating ones
    (*all that*, *long*) weaker ([israel-1996], [israel-2011]).
    `nonScalar` is an editorial slot — Israel classifies most minimizers,
    including *lift a finger*, as scalar; prefer `unknown` if unsure. -/
inductive ScalarDirection where
  | strengthening
  | attenuating
  | nonScalar
  | unknown
  deriving DecidableEq, Repr

/-- Whether scalar value tracks polarity in the default way (canonical
    emphatic NPIs low, PPIs high) or inversely (*wild horses*, *at the
    drop of a hat*); inversion tracks propositional role
    ([israel-2001]). -/
inductive Canonicity where
  | canonical
  | inverted
  | unknown
  deriving DecidableEq, Repr

/-- How increasing the referent's scalar value affects event likelihood:
    facilitating roles (agent, stimulus, reward) invert the scale,
    impeding roles (patient, increment, expense) keep it canonical —
    [israel-2001]'s resolution of the maximizer/minimizer puzzle. -/
inductive LikelihoodEffect where
  | facilitating
  | impeding
  | unknown
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
  /-- Scalar direction ([israel-1996]) -/
  scalarDirection : ScalarDirection := .unknown
  /-- Scalar value ([israel-2001]) -/
  scalarValue : ScalarValue := .unknown
  /-- Canonical or inverted ([israel-2001]) -/
  canonicity : Canonicity := .unknown
  /-- Propositional role's likelihood effect ([israel-2001]) -/
  likelihoodEffect : LikelihoodEffect := .unknown
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
