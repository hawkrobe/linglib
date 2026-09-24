module

public import Linglib.Semantics.Polarity.Item

/-!
# Spanish polarity items

The negative words *nadie* 'nobody', *nada* 'nothing', *ninguno* 'none', *nunca* and *jamás*
'never' stand alone before the verb, *nadie vino* 'no one came', and after it require a negative
before it, *no vino nadie*; only one negative word may precede the verb, never *nadie no sabía la
verdad*, and every later word that can be negated is, *nunca hay nada nuevo en ninguna parte*
'there's never anything new anywhere'. The same words mean 'anyone', 'anything', 'ever' after a
comparative or a superlative, after expressions of doubt, denial, impossibility or too much, in
questions expecting the answer 'no', and after *antes de*, *antes que* and *sin*: *más que nada*
'more than anything', *sin nada ni nadie* 'without anything or anybody'. *Jamás* is never used
after a comparative, *ahora más que nunca* 'now more than ever' ([butt-benjamin-2019]). The
series is [haspelmath-1997]'s type of negative indefinites that co-occur with verbal negation in
some positions and not in others.

## References

* [butt-benjamin-2019]
* [haspelmath-1997]
-/

@[expose] public section

namespace Spanish.PolarityItems

open PolarityItem

/-- *nadie* 'nobody', 'anybody': *es dudoso que nadie pueda pasar por nativo* 'it's doubtful
whether anyone can pass as a native', *la mayor tontería que haya dicho nadie* 'the most stupid
thing anyone has said', *él tenía la culpa por llegar antes que nadie* 'it was his fault for
arriving before anyone else'. -/
def nadie : PolarityItem :=
  { form := "nadie", licensor := some .weak, baseForce := .existential,
    licensingContexts :=
      [.negation, .nobody, .superlative, .doubtVerb, .denyVerb, .sinceTemporal, .tooTo,
        .adversative, .question, .beforeClause, .withoutClause],
    scalarDirection := some .strengthening }

/-- *nada* 'nothing', 'anything': *más que nada, es taimado* 'more than anything, he's cunning',
*pocos libros dirían nada semejante* 'few books would say anything similar', *he venido sin nada*
'I've come without anything'. -/
def nada : PolarityItem :=
  { form := "nada", licensor := some .weak, baseForce := .existential,
    licensingContexts :=
      [.negation, .nobody, .phrasalComparative, .few, .question, .beforeClause, .withoutClause],
    scalarDirection := some .strengthening }

/-- *ninguno* 'none', 'any': *es más lista que ninguno de los otros* 'she's cleverer than any of
the others', literary *si he sido insincero con ninguno de vosotros* 'if I have been insincere
with any of you'. -/
def ninguno : PolarityItem :=
  { form := "ninguno", licensor := some .weak, baseForce := .existential,
    licensingContexts := [.negation, .nobody, .phrasalComparative, .conditionalAntecedent],
    scalarDirection := some .strengthening }

/-- *nunca* 'never', 'ever': *salió más temprano que nunca* 'she went out earlier than ever
before', *¿quién hubiera pensado nunca que se casaría con Julia?* 'who would ever have thought
he'd have married Julia?'. -/
def nunca : PolarityItem :=
  { form := "nunca", licensor := some .weak, baseForce := .temporal,
    licensingContexts := [.negation, .nobody, .phrasalComparative, .superlative, .question],
    scalarDirection := some .strengthening }

/-- *jamás* 'never', 'ever', stronger and less common than *nunca*: *el mejor que jamás hubiera*
'the best that ever was'. -/
def jamás : PolarityItem :=
  { form := "jamás", licensor := some .weak, baseForce := .temporal,
    licensingContexts := [.negation, .superlative, .question],
    scalarDirection := some .strengthening }

/-- The polarity items. -/
def items : List PolarityItem := [nadie, nada, ninguno, nunca, jamás]

end Spanish.PolarityItems
