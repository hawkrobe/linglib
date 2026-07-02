/-!
# Proto-role attribution data schema

Typed schema for the per-argument proto-role entailment attributions that
[dowty-1991] states explicitly in the text. Generated rows live in
`Data/ProtoRoles/<Paper>.lean`, emitted from the canonical `<Paper>.json` by
`scripts/gen_protoroles.py`.

This is substrate: it imports nothing from `Linglib/`. Consumers (the paper's
study file, `Studies/Dowty1991.lean`) import the generated module and supply
their own adapters to theory types such as
`ArgumentStructure.EntailmentProfile`.

Each entailment field is `Option Bool`: `some true`/`some false` only where
the paper explicitly attributes or denies the entailment for that argument;
`none` where it is silent. Rows never interpolate — hedged attributions
(e.g. [dowty-1991] p. 577's "(mostly)") stay `none`.

## Main definitions
* `ArgPosition` — grammatical slot of the argument the attribution concerns.
* `ProtoRoleDatum` — one verb argument's attributed entailments plus a
  locator into the source text.
-/

namespace Dowty1991

/-- Grammatical slot of the attributed argument. `nonsubject` is for
    alternating argument pairs attributed jointly without a fixed frame
    ([dowty-1991] (64 I) on spray/load: "both nonsubject arguments"). -/
inductive ArgPosition where
  | subject
  | object
  | oblique
  | nonsubject
  deriving DecidableEq, Repr, Inhabited

/-- One explicit per-argument entailment attribution ([dowty-1991]).
    The ten fields follow the (27)/(28) proto-role lists: five Proto-Agent,
    five Proto-Patient. `locator` cites the example number and page. -/
structure ProtoRoleDatum where
  /-- The attributing predicate, as named in the text. -/
  verb : String
  /-- Grammatical slot of the argument. -/
  arg : ArgPosition
  /-- Short gloss of the argument (e.g. "the fence (location)"). -/
  argDesc : String
  /-- (27a) volitional involvement. -/
  volition : Option Bool := none
  /-- (27b) sentience/perception. -/
  sentience : Option Bool := none
  /-- (27c) causing an event or change of state. -/
  causation : Option Bool := none
  /-- (27d) movement relative to another participant. -/
  movement : Option Bool := none
  /-- (27e) exists independently of the event. -/
  independentExistence : Option Bool := none
  /-- (28a) undergoes change of state. -/
  changeOfState : Option Bool := none
  /-- (28b) incremental theme. -/
  incrementalTheme : Option Bool := none
  /-- (28c) causally affected by another participant. -/
  causallyAffected : Option Bool := none
  /-- (28d) stationary relative to another participant. -/
  stationary : Option Bool := none
  /-- (28e) does not exist independently of the event. -/
  dependentExistence : Option Bool := none
  /-- Example number and page in the source text. -/
  locator : String
  deriving DecidableEq, Repr

end Dowty1991
