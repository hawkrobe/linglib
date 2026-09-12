import Linglib.Syntax.Coordination
import Linglib.Fragments.English.Coordination
import Linglib.Fragments.Japanese.Coordination
import Linglib.Fragments.Hungarian.Coordination
import Linglib.Fragments.Georgian.Coordination
import Linglib.Fragments.Latin.Coordination
import Linglib.Fragments.Korean.Coordination

/-!
# Mitrović and Sauerland (2016): Two Conjunctions Are Better Than One

This file formalizes the universal two-head system for nominal coordination proposed by
[mitrovic-sauerland-2016]. The head μ combines with a single individual and the head J with
two arguments of truth-value type, and languages differ in which heads they pronounce.
Coordinators of the J kind, such as English *and*, have propositional uses, do not double,
and lack additive and quantificational uses; coordinators of the μ kind, such as Japanese
*mo*, combine noun phrases, double, and serve as additive particles. Some languages realize
both heads at once, triadic exponency, which the paper attests in Southeastern Macedonian,
Hungarian, and Avar (`hasAllThreeStrategies`, `hungarian_triadic`). The generalizations
stated over the sample are that every language has a J-only strategy (`j_is_universal`) and
that every μ morpheme is also the language's additive particle
(`mu_additive_generalization`).

## Implementation notes

The language records carry the J and μ classification of each language's coordinators,
which are the fragment entries; Georgian, Korean, and Slovenian follow [mitrovic-2021],
and Southeastern Macedonian, Avar, and Serbo-Croatian are not in the sample.

## References

* [mitrovic-sauerland-2016]
* [mitrovic-sauerland-2014]
* [mitrovic-2021]
* [haspelmath-2007]
-/

namespace MitrovicSauerland2016

open Syntax.Coordination

/-- English has only J, *and*: *both … and* is not productively additive, and there is no
μ-only conjunction. -/
def english : ConjunctionSystem :=
  { language := "English"
  , morphemes := [ { entry := English.Coordination.and_ } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "eng" }

/-- Japanese *to* is J, from the comitative marker, and *mo* is μ, also the additive
particle. -/
def japanese : ConjunctionSystem :=
  { language := "Japanese"
  , morphemes :=
    [ { entry := Japanese.Coordination.to_
      , source := some .comitative }
    , { entry := Japanese.Coordination.mo
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "jpn" }

/-- Hungarian *és* is J, free and prepositive, and *is* is μ, free and postpositive, also
the additive focus particle; the language realizes J and two μ heads at once, the paper's
triadic exponency. -/
def hungarian : ConjunctionSystem :=
  { language := "Hungarian"
  , morphemes :=
    [ { entry := Hungarian.Coordination.es }
    , { entry := Hungarian.Coordination.is_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "hun" }

/-- Georgian *da* is J, free, and *-c* is μ, a bound clitic and the additive particle; the
triadic classification follows [mitrovic-2021]. -/
def georgian : ConjunctionSystem :=
  { language := "Georgian"
  , morphemes :=
    [ { entry := Georgian.Coordination.da }
    , { entry := Georgian.Coordination.c_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly, .jMu]
  , patterns := [.a_co_b, .a'co_b'co]
  , iso := "kat" }

/-- Latin *et* is J, free and prepositive, and *-que* is μ, a bound enclitic. -/
def latin : ConjunctionSystem :=
  { language := "Latin"
  , morphemes :=
    [ { entry := Latin.Coordination.et }
    , { entry := Latin.Coordination.que
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a_co_b, .a_b'co, .co'a_b'co]
  , iso := "lat" }

/-- Korean *-(i)rang* is J, bound and postpositive, and *-to* is μ, bound and additive,
following [mitrovic-2021]. -/
def korean : ConjunctionSystem :=
  { language := "Korean"
  , morphemes :=
    [ { entry := Korean.Coordination.irang }
    , { entry := Korean.Coordination.to_
      , source := some .focusParticle } ]
  , strategies := [.jOnly, .muOnly]
  , patterns := [.a'co_b, .a'co_b'co]
  , iso := "kor" }

/-- Slovenian *in* is J, free and prepositive. -/
def slovenian : ConjunctionSystem :=
  { language := "Slovenian"
  , morphemes :=
    [ { entry := { form := "in", gloss := "and", role := .j, kind := .free } } ]
  , strategies := [.jOnly]
  , patterns := [.a_co_b]
  , iso := "slv" }

/-- The seven-language sample. -/
def msLanguages : List ConjunctionSystem :=
  [english, japanese, hungarian, georgian, latin, korean, slovenian]

/-- Triadic exponency: the J-only, μ-only, and J-with-μ strategies are all attested. -/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Prop :=
  sys.hasStrategy .jOnly ∧ sys.hasStrategy .muOnly ∧ sys.hasStrategy .jMu

instance (sys : ConjunctionSystem) : Decidable (hasAllThreeStrategies sys) := by
  unfold hasAllThreeStrategies; infer_instance

/-- Hungarian realizes all three strategies, *Kati is (és) Mari is*. -/
theorem hungarian_triadic : hasAllThreeStrategies hungarian := by decide

/-- Every language with a μ coordinator uses the same morpheme as its additive particle. -/
theorem mu_additive_generalization :
    ∀ sys ∈ msLanguages, (∃ m ∈ sys.morphemes, m.entry.role = .mu) → sys.muIsAdditive := by
  decide

/-- Every language in the sample has a J-only strategy. -/
theorem j_is_universal : ∀ sys ∈ msLanguages, sys.hasStrategy .jOnly := by
  decide

end MitrovicSauerland2016
