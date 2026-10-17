module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Korean indefinite pronouns

Korean uses its bare interrogatives as indefinites, as *nwukwu* 'who' for 'someone'. Its series are
the general *-nka*-series and the free-choice *-na*- and *-tunci*-series on the interrogatives
(*nwukwu-nka*, *nwukwu-na*, *nwukwu-tunci*), whose free-choice series also occur on the determiner
*amu* with a generic noun, and the negative *-to*-series of *amu* with a generic noun (*amu
(salam)-to*). Beside it is an incomplete *-to*-series on the interrogatives, which has *nwukwu-to*
'nobody' but no *mues-to* 'nothing'. Haspelmath does not distinguish the indefinites on the
interrogatives from those on *amu*, which do not differ in distribution, so the *-to* series has a
member of each. The members are those of Haspelmath's table, with *amu salam-to* for his *amu
(salam)-to*, and a determiner frame is cited with its noun as *…* or *X*, as he cites it. The
*amu*-members of the *-na*- and *-tunci*-series, which his table omits as analogous to those of the
*-to*-series, are not entered.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Korean.Indefinites

/-- Bare *nwukwu* 'who' used as an indefinite. -/
def nwukwu : IndefinitePronoun :=
  { form := "nwukwu", script := some "누구", ontology := .person }

/-- *nwukwu-nka*, the interrogative with *-nka*. -/
def nwukwuNka : IndefinitePronoun :=
  { form := "nwukwu-nka", ontology := .person }

/-- *nwukwu-to* 'nobody', the interrogative with *-to* 'also'. -/
def nwukwuTo : IndefinitePronoun :=
  { form := "nwukwu-to", script := some "누구도", ontology := .person }

/-- *amu salam-to* 'nobody', the determiner *amu* with the generic noun *salam*, which may be
omitted, and *-to*. -/
def amuSalamTo : IndefinitePronoun :=
  { form := "amu salam-to", ontology := .person }

/-- *nwukwu-na*, the interrogative with *-na*. -/
def nwukwuNa : IndefinitePronoun :=
  { form := "nwukwu-na", script := some "누구나", ontology := .person }

/-- *nwukwu-tunci*, the interrogative with *-tunci*. -/
def nwukwuTunci : IndefinitePronoun :=
  { form := "nwukwu-tunci", ontology := .person }

/-! ### The series -/

/-- The bare interrogatives used as indefinites. -/
def interrogativeSeries : IndefinitePronoun.Series :=
  ⟨"bare interrogative", {nwukwu, ⟨{ form := "mues" }, .thing⟩, ⟨{ form := "etten" }, .property⟩,
    ⟨{ form := "eti" }, .place⟩, ⟨{ form := "encey" }, .time⟩, ⟨{ form := "enu" }, .determiner⟩}⟩

/-- The *-nka*-series. -/
def nkaSeries : IndefinitePronoun.Series :=
  ⟨"-nka", {nwukwuNka, ⟨{ form := "mue-nka" }, .thing⟩, ⟨{ form := "eti-sunka" }, .place⟩,
    ⟨{ form := "encey-nka" }, .time⟩}⟩

/-- The *-to*-series, on the interrogatives and on *amu*. -/
def toSeries : IndefinitePronoun.Series :=
  ⟨"-to", {nwukwuTo, amuSalamTo, ⟨{ form := "amu kes-to" }, .thing⟩,
    ⟨{ form := "amu kos-to" }, .place⟩, ⟨{ form := "amu ttay-to" }, .time⟩,
    ⟨{ form := "amu X-to" }, .determiner⟩}⟩

/-- The *-na*-series. -/
def naSeries : IndefinitePronoun.Series :=
  ⟨"-na", {nwukwuNa, ⟨{ form := "mues-ina" }, .thing⟩, ⟨{ form := "etten …-na" }, .property⟩,
    ⟨{ form := "eti-na" }, .place⟩, ⟨{ form := "encey-na" }, .time⟩,
    ⟨{ form := "enu …-na" }, .determiner⟩}⟩

/-- The *-tunci*-series. -/
def tunciSeries : IndefinitePronoun.Series :=
  ⟨"-tunci", {nwukwuTunci, ⟨{ form := "mues-itunci" }, .thing⟩,
    ⟨{ form := "etten …-tunci" }, .property⟩, ⟨{ form := "eti-tunci" }, .place⟩,
    ⟨{ form := "encey-tunci" }, .time⟩, ⟨{ form := "enu …-tunci" }, .determiner⟩}⟩

end Korean.Indefinites
