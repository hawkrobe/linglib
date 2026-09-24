module

public import Linglib.Fragments.Hungarian.Indefinites
public import Linglib.Semantics.Polarity.Licensing

/-!
# Hungarian polarity items

This file types the person members of the Hungarian negative and free-choice series of
`Hungarian.Indefinites` as polarity items. *senki* 'nobody' is a strict negative-concord item:
it requires clausemate negation, and under negation in a higher clause it gives way to *valaki
is*, as Kenesei, Vago and Fenyvesi show (§1.4.3, §1.4.5), who call *senki* and *semmi*
universal negative polarity items. *akárki* and *bárki* 'anyone' are free-choice items, as in
*Akárki jöhet a konferenciára* 'Anyone may come to the conference'.

## TODO

Haspelmath (A.26) admits the *akár*- and *bár*-series in comparatives, under indirect negation
and, with an emphatic value, in conditionals, and stars both series under direct negation and in
questions. The licensing relation cannot record this: an item with any `licensor` is licensed by
clausal negation, and an item licensed in a conditional antecedent is also licensed in
questions. The free-choice entries therefore carry no `licensor`.

## References

* [haspelmath-1997]
* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
-/

@[expose] public section

namespace Hungarian.PolarityItems

open PolarityItem

/-- *senki* 'nobody' is licensed by clausemate negation alone. -/
def senki : PolarityItem :=
  { form := Indefinites.senki.form
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation] }

/-- *akárki* 'anyone' is a free-choice item, attested under a possibility modal and, in its
series, in the free relative *Akármit mondasz, elindulok holnap* 'No matter what you say, I'm
leaving tomorrow'. -/
def akárki : PolarityItem :=
  { form := Indefinites.akárki.form
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .freeRelative] }

/-- *bárki* 'anyone' is a free-choice item, attested under a possibility modal. -/
def bárki : PolarityItem :=
  { form := Indefinites.bárki.form
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility] }

/-- *senki* is licensed exactly under clausemate negation. -/
theorem senki_licensing_characterized :
    ∀ c, c.licenses senki ↔ c ∈ senki.licensingContexts := by decide

/-- The free-choice items are licensed in every context they are attested in. -/
theorem freeChoice_licensing_sound :
    ∀ e ∈ [akárki, bárki], ∀ c ∈ e.licensingContexts, c.licenses e := by decide

/-- Neither free-choice item is licensed by clausal negation or in a question, where Haspelmath
stars both series. -/
theorem freeChoice_not_negation_question :
    ∀ e ∈ [akárki, bárki], ¬ LicensingContext.negation.licenses e ∧
      ¬ LicensingContext.question.licenses e := by decide

end Hungarian.PolarityItems
