module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Italian polarity items

Italian gives the negative polarity and free choice uses that English *any* combines to separate
items ([chierchia-2006]). The n-words *nessuno* 'no one', *niente* 'nothing' and *neanche* 'not
even, neither' take part in negative concord: after the verb they need a preceding negation, *Non ho
detto niente a nessuno* 'I haven't said anything to anybody', while before the verb they are
themselves negative, *Nessuno ha telefonato* 'Nobody called'; like strong NPIs they are restricted
to roughly the anti-additive environments ([chierchia-2013]), and *nessuno* is not licensed in the
restriction of *ogni* 'every' ([chierchia-2006]). *Mai* 'ever' and the high-register *alcuno* 'any'
are weak NPIs without free choice uses. *Qualsiasi* and its variant *qualunque* head two free choice
constructions, [*qualsiasi* N], read universally, and [*un* N *qualsiasi*], read existentially,
neither of them an NPI ([chierchia-2006]). *Pur* 'even' needs its clause negated, and *affatto* 'at
all' is an NPI as well ([napoli-nespor-1976]).

## References

* [chierchia-2006]
* [chierchia-2013]
* [napoli-nespor-1976]
-/

@[expose] public section

namespace Italian.PolarityItems

open PolarityItem

/-! ### N-words -/

/-- *nessuno* 'no one', the n-word built on *uno* 'one': *Gianni non ha telefonato a nessuno*
'Gianni didn't call anybody', *Nessuno ha telefonato* 'Nobody called', and with a second
negation the double negation reading *Nessuno non ha protestato* 'everybody protested'. -/
def nessuno : PolarityItem :=
  { form := "nessuno"
  , licensor := some .antiAdditive
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening
  , alternativeType := .domain }

/-- *niente*, or *nulla*, 'nothing': *Non ho detto niente a nessuno* 'I haven't said anything
to anybody'. -/
def niente : PolarityItem :=
  { form := "niente/nulla"
  , licensor := some .antiAdditive
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := some .strengthening }

/-- *neanche* 'not even, neither', with the variants *nemmeno* and *neppure*: *Non vengo neanche
io* 'I'm not coming either', against *\*Vengo neanche io*. -/
def neanche : PolarityItem :=
  { form := "neanche/nemmeno/neppure"
  , licensor := some .antiAdditive
  , baseForce := .additive
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := some .strengthening }

/-! ### Weak NPIs -/

/-- *mai* 'ever', a weak NPI without free choice uses whose distribution is close to that of
*any*. -/
def mai : PolarityItem :=
  { form := "mai"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts :=
      [.negation, .nobody, .withoutClause, .question, .conditionalAntecedent]
  , scalarDirection := some .strengthening
  , alternativeType := .domain }

/-- *alcuno* 'any', a high-register weak NPI without free choice uses: *Non ho comprato alcun
libro* 'I didn't buy any book', *Dubito che Gianni abbia comprato alcun libro* 'I doubt that
Gianni bought any book', *Se Gianni avesse comprato alcun libro, ce lo avrebbe detto* 'If Gianni
had bought any book, he would have told us', against *\*Ho comprato alcun libro*. The plural
*alcuni* 'some' is a plain indefinite. -/
def alcuno : PolarityItem :=
  { form := "alcuno"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .doubtVerb, .conditionalAntecedent]
  , scalarDirection := some .strengthening }

/-- *pur* 'even' in *pur con tutta la fantasia del mondo* 'even with all the fantasy in the
world', which needs the verb of its clause negated: *Non puoi immaginarlo, pur con tutta la
fantasia del mondo* against *\*Puoi immaginarlo, …*. -/
def pur : PolarityItem :=
  { form := "pur"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening }

/-- *affatto* 'at all', a negative polarity item. -/
def affatto : PolarityItem :=
  { form := "affatto"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening }

/-! ### Free choice items -/

/-- *qualsiasi*, or *qualunque*, before the noun, the universal free choice item: *Prendi
qualunque dolce* 'take any sweet'. Episodically it needs a modifier, *Ieri ho parlato con
qualsiasi filosofo che fosse interessato a parlarmi* against *??Ieri ho parlato con qualsiasi
filosofo*, and under negation an unmodified one has only the rhetorical 'not just any' reading,
*Non leggerò qualunque libro*. -/
def qualsiasi : PolarityItem :=
  { form := "qualsiasi/qualunque"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative]
  , alternativeType := .domain }

/-- *un* N *qualsiasi*, or *qualunque*, the existential free choice item: *Prendi un dolce
qualunque* 'take a sweet whatever'. It is marginal in a plain episodic sentence, *??Ieri ho
parlato con un qualsiasi filosofo*, and under negation it has only the rhetorical reading, *Non
leggerò un libro qualunque*. -/
def unoQualsiasi : PolarityItem :=
  { form := "un N qualsiasi"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative]
  , alternativeType := .domain }

/-- The polarity items. -/
def items : List PolarityItem :=
  [nessuno, niente, neanche, mai, alcuno, pur, affatto, qualsiasi, unoQualsiasi]

/-- Every attested context of every entry is predicted licensed. -/
theorem italian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

end Italian.PolarityItems
