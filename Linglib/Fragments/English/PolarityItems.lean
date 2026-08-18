import Linglib.Semantics.Polarity.Licensing

/-!
# English Polarity-Sensitive Items

English polarity items, typed by `Polarity.Item`: weak NPIs
(*any*, *ever*, *at all*), strong NPIs (*lift a finger*, *in years*,
*either*), free-relative FCIs (*whatever*, *whoever*), maximizer NPIs
(*wild horses*, *all the tea in China*), and PPIs both plain (*some*,
*already*, *somewhat*) and idiomatic (*at the drop of a hat*, *for a
pittance*). Entries carry licensing parameters, attested contexts, and
scalar direction; the [israel-2001] scalar-model classifications
(value, canonicity, likelihood effect) live with their consuming study
in `Studies/Israel2001.lean` as `ScalarItem`s over these entries.

## References

* [israel-1996]
* [gajewski-2011], p. 120
* [rullmann-2003]
-/

namespace English.PolarityItems

open Polarity

/-! ### Weak NPIs -/

/-- *any* — the prototypical dual NPI/FCI, with domain alternatives
    ([chierchia-2006]). -/
def any : Item :=
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

/-- *ever* — temporal NPI with domain alternatives ([chierchia-2006]). -/
def ever : Item :=
  { form := "ever"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts :=
      [ .negation, .nobody, .conditionalAntecedent, .question
      , .superlative, .clausalComparative, .onlyFocus, .adversative ]
  , scalarDirection := some .strengthening
  , alternativeType := .domain }

/-- *yet* — temporal NPI. -/
def yet : Item :=
  { form := "yet"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .question] }

/-- *anymore* — temporal NPI. -/
def anymore : Item :=
  { form := "anymore"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation] }

/-- *at all* — degree NPI. -/
def atAll : Item :=
  { form := "at all"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts :=
      [.negation, .nobody, .conditionalAntecedent, .question]
  , scalarDirection := some .strengthening }

/-- *in the least* — degree NPI. -/
def inTheLeast : Item :=
  { form := "in the least"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation, .question] }

/-- *a single* — emphatic existential NPI. -/
def aSingle : Item :=
  { form := "a single"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause] }

/-- *whatsoever* — emphatic post-nominal NPI. -/
def whatsoever : Item :=
  { form := "whatsoever"
  , licensor := some .weak
  , baseForce := .manner
  , licensingContexts := [.negation, .nobody] }

/-! ### Strong NPIs -/

/-- *lift a finger* — idiomatic minimizer, anti-additive licensor. -/
def liftAFinger : Item :=
  { form := "lift a finger"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *budge an inch* — idiomatic minimizer, anti-additive licensor. -/
def budgeAnInch : Item :=
  { form := "budge an inch"
  , licensor := some .antiAdditive
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in years* — temporal strong NPI. -/
def inYears : Item :=
  { form := "in years"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody] }

/-- *until* — temporal strong NPI (in some analyses). -/
def until_ : Item :=
  { form := "until"
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation] }

/-- *either* — additive strong NPI ([rullmann-2003], [gajewski-2011]):
    ungrammatical under Strawson-DE operators (*Only John likes
    pancakes, either*) despite [von-fintel-1999] having shown those
    contexts Strawson-DE ([gajewski-2011] p. 120). -/
def either_npi : Item :=
  { form := "either"
  , licensor := some .antiAdditive
  , baseForce := .additive
  , licensingContexts := [.negation, .nobody] }

/-! ### Free choice items -/

/-- *whatever* — free-relative FCI. -/
def whatever : Item :=
  { form := "whatever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-- *whoever* — free-relative FCI. -/
def whoever : Item :=
  { form := "whoever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-- *whichever* — free-relative FCI. -/
def whichever : Item :=
  { form := "whichever"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic, .freeRelative] }

/-! ### Positive polarity items -/

/-- *some* (stressed) — PPI reading; attenuating (weaker than
    *many*/*all*). -/
def some_ppi : Item :=
  { form := "some (stressed)"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *already* — temporal PPI. -/
def already : Item :=
  { form := "already"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

/-- *somewhat* — degree PPI; attenuating (weaker than *very*). -/
def somewhat : Item :=
  { form := "somewhat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *rather* — degree PPI; attenuating (weaker than *very*). -/
def rather : Item :=
  { form := "rather"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .attenuating }

/-- *tons of* — emphatic PPI: *She has tons of friends.* -/
def tonsOf : Item :=
  { form := "tons of"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening }

/-- *utterly* — emphatic PPI: *I was utterly depressed.* -/
def utterly : Item :=
  { form := "utterly"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening }

/-! ### Maximizer NPIs -/

/-- *wild horses* — idiomatic maximizer NPI: *Wild horses couldn't keep
    me away.* -/
def wildHorses : Item :=
  { form := "wild horses"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *all the tea in China* — idiomatic maximizer NPI: *I wouldn't do it
    for all the tea in China.* -/
def allTheTeaInChina : Item :=
  { form := "all the tea in China"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *a ten-foot pole* — idiomatic maximizer NPI: *I wouldn't touch it
    with a ten-foot pole.* -/
def aTenFootPole : Item :=
  { form := "a ten-foot pole"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in a million years* — idiomatic maximizer NPI: *I wouldn't marry
    that woman in a million years.* -/
def inAMillionYears : Item :=
  { form := "in a million years"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-! ### Minimizer PPIs -/

/-- *at the drop of a hat* — idiomatic minimizer PPI: *He'd quit at the
    drop of a hat.* -/
def atTheDropOfAHat : Item :=
  { form := "at the drop of a hat"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *in a jiffy* — idiomatic minimizer PPI: *We'll be back in a jiffy.* -/
def inAJiffy : Item :=
  { form := "in a jiffy"
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *for a pittance* — idiomatic minimizer PPI: *He got Madonna to play
    for peanuts.* -/
def forAPittance : Item :=
  { form := "for a pittance"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-- *for a song* — idiomatic minimizer PPI: *He bought that painting for
    a song.* -/
def forASong : Item :=
  { form := "for a song"
  , ppi := true
  , baseForce := .degree
  , licensingContexts := []
  , scalarDirection := some .strengthening
  , morphology := .idiomatic }

/-! ### Lexicon access -/

/-- The weak NPIs. -/
def weakNPIs : List Item :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- The strong NPIs. -/
def strongNPIs : List Item :=
  [liftAFinger, budgeAnInch, inYears, until_]

/-- The maximizer NPIs. -/
def invertedNPIs : List Item :=
  [wildHorses, allTheTeaInChina, aTenFootPole, inAMillionYears]

/-- All NPIs (weak + strong + maximizer). -/
def allNPIs : List Item := weakNPIs ++ strongNPIs ++ invertedNPIs

/-- The FCIs. -/
def allFCIs : List Item :=
  [any, whatever, whoever, whichever]

/-- The plain PPIs. -/
def canonicalPPIs : List Item :=
  [some_ppi, already, somewhat, rather, tonsOf, utterly]

/-- The minimizer PPIs. -/
def invertedPPIs : List Item :=
  [atTheDropOfAHat, inAJiffy, forAPittance, forASong]

/-- All PPIs. -/
def allPPIs : List Item :=
  canonicalPPIs ++ invertedPPIs

/-- The full lexicon. -/
def allPolarityItems : List Item :=
  weakNPIs ++ strongNPIs ++ invertedNPIs ++
  [whatever, whoever, whichever] ++ allPPIs

/-- Lookup by form. -/
def lookup (form : String) : Option Item :=
  allPolarityItems.find? λ p => p.form == form

/-! ### Verification -/

example : any.isNPI := by decide
example : any.isFCI := by decide
example : ever.isNPI := by decide
example : ¬ ever.isFCI := by decide
example : whatever.isFCI := by decide

/-- PPIs list no licensing contexts: they need positive environments. -/
example : ∀ e ∈ allPPIs, e.licensingContexts = [] := by decide

/-- Every attested context of every entry is predicted licensed. -/
theorem english_licensing_sound :
    ∀ e ∈ allPolarityItems, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

end English.PolarityItems
