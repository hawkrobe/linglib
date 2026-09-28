module

public import Mathlib.Tactic.DeriveFintype

/-!
# Polarity-marking strategies

This file defines the typology of devices by which a language marks a switch from negative to
positive polarity. A `PolarityMarker.Strategy` is the form class of a device: a
sentence-internal affirmative particle, Verum focus on the finite verb, a polarity-reversing
particle, another device, or no marking. A `PolarityMarker.Env` is a position or discourse
context in which a device is available, and a `PolarityMarker` is a language's device
with its form, its prosodic target, its environments and its strategy. Fragments for Dutch,
English, Italian and Spanish populate the schema, and the German Verum focus of
[turco-braun-dimroth-2014] is recorded in that study.

## Implementation notes

The schema records form-class properties in the tradition of [hohle-1992], [sudhoff-2012],
[lohnstein-bluhdorn-2012] and [turco-braun-dimroth-2014], which pairs polarity contrast with
specific lexical or prosodic devices; the polarity-reversing class follows [holmberg-2016].
[matic-nikolaeva-2018] reject the form-class encoding in favour of a pragmatic salient
polarity, and [garassino-jacob-2018] concur; the non-equivalence of the two is stated in
`Studies/MaticNikolaeva2018.lean`. Syntactic position beyond sentence-internality is not
encoded, so entries under one strategy may differ in it. This is a separate system from the
`PolarityItem` licensing API. Polarity particles, including the polarity-reversing Swedish
*jo* and French *si* of [holmberg-2016], are a language's `PolarityParticle`s, which each
framework interprets; under [holmberg-2016]'s `AnswerFeature.reversing` the negative context a
marker's environments record is derived.

## References

* [turco-braun-dimroth-2014]
* [sudhoff-2012]
* [lohnstein-bluhdorn-2012]
* [hohle-1992]
* [holmberg-2016]
* [matic-nikolaeva-2018]
* [garassino-jacob-2018]
-/

@[expose] public section

namespace PolarityMarker

/-- How a language marks polarity switches (neg → affirm). -/
inductive Strategy where
  /-- Sentence-internal affirmative particle (e.g., Dutch *wel*) -/
  | particle
  /-- Pitch accent on the finite verb ([hohle-1992] Verum focus) -/
  | verumFocus
  /-- Polarity-reversing construction: affirms [+Pol] against a negative or contrasting
  context, clause-initially (Italian *sì che*, Spanish *sí que*). -/
  | polarityReversal
  /-- Other strategy (e.g., pre-utterance particle, intonation pattern) -/
  | other
  /-- No overt polarity marking -/
  | unmarked
  deriving DecidableEq, Repr

/-- Environments / contexts a polarity-marking strategy may be available
    in. Bundles the structural-position dimension (`sentenceInternal`
    vs. pre-utterance) with the discourse-context dimensions (`contrast`,
    `correction`) so per-language entries record one set rather than
    three parallel Bools. -/
inductive Env where
  /-- Position: marker appears sentence-internally (vs. pre-utterance). -/
  | sentenceInternal
  /-- Discourse: marker is available in contrast contexts. -/
  | contrast
  /-- Discourse: marker is available in correction contexts. -/
  | correction
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A cross-linguistic polarity-marking entry.

    Unified structure for all strategies — particles (Dutch *wel*),
    prosodic (German VF), or other. Language-specific Fragment files
    instantiate this with appropriate optional fields. The
    `environments` field records the set of `Env`
    positions/contexts the marker is available in.

    Syntactic position beyond sentence-internality is not encoded, so entries under the
    same `strategy` may differ in it. -/
structure _root_.PolarityMarker where
  /-- Descriptive label (e.g., "wel", "Verum focus", "doch (pre-utterance)") -/
  label : String
  /-- Surface form, if the strategy is a particle -/
  form : Option String := none
  /-- What bears prosodic prominence, if the strategy is prosodic -/
  prosodicTarget : Option String := none
  /-- Set of positions/contexts in which this marker is available. -/
  environments : Set Env
  /-- The polarity-marking strategy category -/
  strategy : Strategy

end PolarityMarker
