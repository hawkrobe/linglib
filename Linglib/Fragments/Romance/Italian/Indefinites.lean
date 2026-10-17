module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Italian indefinite pronouns

Italian has three major series of indefinite pronouns: the general *qualche*-series (*qualcuno*),
the negative *nessuno*-series, and the free-choice series in *-unque* (*chiunque*), the only
formally homogeneous one and built on the interrogatives. The members are those of Haspelmath's
table, which parenthesizes *mai* in the *nessuno*-series as no member of it; he elsewhere doubts
that *in nessun luogo* is grammaticalized. The n-word *nessuno* is also
`Italian.PolarityItems.nessuno`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Italian.Indefinites

/-- *qualcuno*, of the *qualche*-series. -/
def qualcuno : IndefinitePronoun := { form := "qualcuno", ontology := .person }

/-- *nessuno* 'no one', from the negation *nec* and *uno* 'one'. -/
def nessuno : IndefinitePronoun := { form := "nessuno", ontology := .person }

/-- *chiunque*, the interrogative *chi* with *-unque*. -/
def chiunque : IndefinitePronoun := { form := "chiunque", ontology := .person }

/-! ### The series -/

/-- The *qualche*-series. -/
def qualcheSeries : IndefinitePronoun.Series :=
  ⟨"qualche-", {qualcuno, ⟨{ form := "qualche cosa" }, .thing⟩, ⟨{ form := "qualcosa" }, .thing⟩,
    ⟨{ form := "in qualche luogo" }, .place⟩, ⟨{ form := "qualche volta" }, .time⟩,
    ⟨{ form := "in qualche modo" }, .manner⟩, ⟨{ form := "qualche" }, .determiner⟩}⟩

/-- The *nessuno*-series. -/
def nessunoSeries : IndefinitePronoun.Series :=
  ⟨"nessuno", {nessuno, ⟨{ form := "niente" }, .thing⟩, ⟨{ form := "nulla" }, .thing⟩,
    ⟨{ form := "in nessun luogo" }, .place⟩, ⟨{ form := "nessuno" }, .determiner⟩}⟩

/-- The *-unque* series, which has no member for a thing, a time or a manner. -/
def unqueSeries : IndefinitePronoun.Series :=
  ⟨"-unque", {chiunque, ⟨{ form := "dovunque" }, .place⟩, ⟨{ form := "qualunque" }, .determiner⟩}⟩

end Italian.Indefinites
