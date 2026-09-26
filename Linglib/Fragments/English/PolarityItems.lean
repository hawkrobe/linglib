module

public import Linglib.Semantics.Polarity.Licensing

/-!
# English polarity items

This file defines the English polarity-sensitive items as `PolarityItem` entries. The weak
negative polarity items *any*, *ever*, *yet*, *anymore*, *at all*, *in the least*, *a single*
and *whatsoever* are licensed by any downward-entailing operator; the strong ones, *lift a
finger*, *budge an inch*, *in years*, *until* and additive *either*, need an anti-additive
licenser, and Gajewski shows that *either* is out under *only* although *only* is Strawson
downward-entailing. *Any* and the free relatives *whatever*, *whoever* and *whichever* have
free choice readings. The positive polarity items divide, in Israel's terms, into the
attenuating *some*, *somewhat* and *rather* and the emphatic *tons of* and *utterly*, beside
*already* and additive *too*, the positive counterpart of *either*; the idioms *wild horses*,
*all the tea in China*, *a ten-foot pole* and *in a million years* are his maximizer negative
polarity items and *at the drop of a hat*, *in a jiffy*, *for a pittance* and *for a song* his
minimizer positive ones. Each entry carries its licenser strength, its attested licensing
contexts and its scalar direction; Israel's classification by quantity and propositional role
is the matter of `Studies/Israel2001.lean`.

## Main definitions

* `English.PolarityItems.weakNPIs`, `English.PolarityItems.strongNPIs`,
  `English.PolarityItems.invertedNPIs`, `English.PolarityItems.allFCIs`,
  `English.PolarityItems.canonicalPPIs`, `English.PolarityItems.invertedPPIs`: the classes.
* `English.PolarityItems.allPolarityItems`: the lexicon.

## Main results

* `English.PolarityItems.english_licensing_sound`: every attested context of every entry is
  predicted to license it.

## References

* [israel-2011]
* [gajewski-2011]
* [chierchia-2006]
* [rullmann-2003]
* [ladd-1981]
-/

@[expose] public section

namespace English.PolarityItems

open PolarityItem

/-! ### Weak NPIs -/

/-- *any*, the prototypical dual NPI/FCI, with domain alternatives
    ([chierchia-2006]). -/
def any : PolarityItem :=
  { form := "any"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .conditionalAntecedent, .question
      , .modalPossibility, .modalNecessity, .imperative, .generic
      , .onlyFocus, .adversative ]
  , scalarDirection := some .strengthening
  , alternativeType := .domain }

/-- *ever*, temporal NPI with domain alternatives ([chierchia-2006]). -/
def ever : PolarityItem :=
  { form := "ever"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts :=
      [ .negation, .nobody, .conditionalAntecedent, .question
      , .superlative, .clausalComparative, .onlyFocus, .adversative ]
  , scalarDirection := some .strengthening
  , alternativeType := .domain }

/-- *yet*, temporal NPI. -/
def yet : PolarityItem :=
  { form := "yet"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .question] }

/-- *anymore*, temporal NPI. -/
def anymore : PolarityItem :=
  { form := "anymore"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation] }

/-- *at all*, degree NPI. -/
def atAll : PolarityItem :=
  { form := "at all"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts :=
      [.negation, .nobody, .conditionalAntecedent, .question]
  , scalarDirection := some .strengthening }

/-- *in the least*, degree NPI. -/
def inTheLeast : PolarityItem :=
  { form := "in the least"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation, .question] }

/-- *a single*, emphatic existential NPI. -/
def aSingle : PolarityItem :=
  { form := "a single"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause] }

/-- *whatsoever*, emphatic post-nominal NPI. -/
def whatsoever : PolarityItem :=
  { form := "whatsoever"
  , licensor := some .weak
  , baseForce := .manner
  , licensingContexts := [.negation, .nobody] }

/-! ### Strong NPIs -/

/-- *lift a finger*, idiomatic minimizer, anti-additive licensor. -/
def liftAFinger : PolarityItem :=
  { form := "lift a finger"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *budge an inch*, idiomatic minimizer, anti-additive licensor. -/
def budgeAnInch : PolarityItem :=
  { form := "budge an inch"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in years*, temporal strong NPI. -/
def inYears : PolarityItem :=
  { form := "in years"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody] }

/-- *until*, temporal strong NPI (in some analyses). -/
def until_ : PolarityItem :=
  { form := "until"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation] }

/-- *either*, additive strong NPI ([rullmann-2003], [gajewski-2011]):
    ungrammatical under Strawson-DE operators (*Only John likes
    pancakes, either*) despite [von-fintel-1999] having shown those
    contexts Strawson-DE ([gajewski-2011] p. 120). -/
def either_npi : PolarityItem :=
  { form := "either"
  , licensor := some .antiAdditive
  , baseForce := .additive
  , licensingContexts := [.negation, .nobody] }

/-! ### Free choice items -/

/-- *whatever*, free-relative FCI. -/
def whatever : PolarityItem :=
  { form := "whatever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-- *whoever*, free-relative FCI. -/
def whoever : PolarityItem :=
  { form := "whoever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-- *whichever*, free-relative FCI. -/
def whichever : PolarityItem :=
  { form := "whichever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-! ### Positive polarity items -/

/-- *some* (stressed), PPI reading; attenuating (weaker than
    *many*/*all*). -/
def some_ppi : PolarityItem :=
  { form := "some (stressed)"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *already*, temporal PPI. -/
def already : PolarityItem :=
  { form := "already"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

/-- *too*, additive PPI, the positive counterpart of *either* ([ladd-1981]). -/
def too : PolarityItem :=
  { form := "too"
  , ppi := true
  , baseForce := .additive
  , licensingContexts := [] }

/-- *somewhat*, degree PPI; attenuating (weaker than *very*). -/
def somewhat : PolarityItem :=
  { form := "somewhat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *rather*, degree PPI; attenuating (weaker than *very*). -/
def rather : PolarityItem :=
  { form := "rather"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *tons of*, emphatic PPI, as in *She has tons of friends.* -/
def tonsOf : PolarityItem :=
  { form := "tons of"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening }

/-- *utterly*, emphatic PPI, as in *I was utterly depressed.* -/
def utterly : PolarityItem :=
  { form := "utterly"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening }

/-! ### Maximizer NPIs -/

/-- *wild horses*, idiomatic maximizer NPI, as in *Wild horses couldn't keep
    me away.* -/
def wildHorses : PolarityItem :=
  { form := "wild horses"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *all the tea in China*, idiomatic maximizer NPI, as in *I wouldn't do it
    for all the tea in China.* -/
def allTheTeaInChina : PolarityItem :=
  { form := "all the tea in China"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *a ten-foot pole*, idiomatic maximizer NPI, as in *I wouldn't touch it
    with a ten-foot pole.* -/
def aTenFootPole : PolarityItem :=
  { form := "a ten-foot pole"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in a million years*, idiomatic maximizer NPI, as in *I wouldn't marry
    that woman in a million years.* -/
def inAMillionYears : PolarityItem :=
  { form := "in a million years"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-! ### Minimizer PPIs -/

/-- *at the drop of a hat*, idiomatic minimizer PPI, as in *He'd quit at the
    drop of a hat.* -/
def atTheDropOfAHat : PolarityItem :=
  { form := "at the drop of a hat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in a jiffy*, idiomatic minimizer PPI, as in *We'll be back in a jiffy.* -/
def inAJiffy : PolarityItem :=
  { form := "in a jiffy"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *for a pittance*, idiomatic minimizer PPI, as in *He got Madonna to play
    for peanuts.* -/
def forAPittance : PolarityItem :=
  { form := "for a pittance"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *for a song*, idiomatic minimizer PPI, as in *He bought that painting for
    a song.* -/
def forASong : PolarityItem :=
  { form := "for a song"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-! ### Lexicon access -/

/-- The weak NPIs. -/
def weakNPIs : List PolarityItem :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- The strong NPIs. -/
def strongNPIs : List PolarityItem :=
  [liftAFinger, budgeAnInch, inYears, until_]

/-- The maximizer NPIs. -/
def invertedNPIs : List PolarityItem :=
  [wildHorses, allTheTeaInChina, aTenFootPole, inAMillionYears]

/-- All NPIs (weak + strong + maximizer). -/
def allNPIs : List PolarityItem := weakNPIs ++ strongNPIs ++ invertedNPIs

/-- The FCIs. -/
def allFCIs : List PolarityItem :=
  [any, whatever, whoever, whichever]

/-- The plain PPIs. -/
def canonicalPPIs : List PolarityItem :=
  [some_ppi, already, too, somewhat, rather, tonsOf, utterly]

/-- The minimizer PPIs. -/
def invertedPPIs : List PolarityItem :=
  [atTheDropOfAHat, inAJiffy, forAPittance, forASong]

/-- All PPIs. -/
def allPPIs : List PolarityItem :=
  canonicalPPIs ++ invertedPPIs

/-- The full lexicon. -/
def allPolarityItems : List PolarityItem :=
  weakNPIs ++ strongNPIs ++ invertedNPIs ++
  [whatever, whoever, whichever] ++ allPPIs

/-! ### Verification -/

example : any.isNPI := by decide
example : any.isFCI := by decide
example : ever.isNPI := by decide
example : ¬ ever.isFCI := by decide
example : whatever.isFCI := by decide

/-- Positive polarity items list no licensing contexts, since they need positive environments. -/
example : ∀ e ∈ allPPIs, e.licensingContexts = [] := by decide

/-- Every attested context of every entry is predicted licensed. -/
theorem english_licensing_sound :
    ∀ e ∈ allPolarityItems, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

end English.PolarityItems
