module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Kannada indefinite pronouns

Kannada builds its indefinite pronouns by suffixing a particle to an interrogative pronoun, three
series on *yaaru* 'who': *yaar-oo* 'someone', with *-oo* 'or', for a referent the speaker
presupposes but cannot identify; *yaar-aadaruu* 'anyone', with *-aadaruu* 'even if it be', for
irrealis non-specific reference and in questions and conditionals; and *yaar-uu*, with *-uu* 'also,
even', under negation, in comparatives and for free choice. No series is used for a referent the
speaker has in mind. The members are those of Haspelmath's table, as he segments them; both the
masculine and the feminine determiner of the *-oo* series are entered, and the determiner of the
*-uu* series is cited with its noun as *X*, as he cites it.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

@[expose] public section

namespace Kannada.Indefinites

/-- *yaar-oo* 'someone'. -/
def yaarOo : IndefinitePronoun := { form := "yaar-oo", ontology := .person }

/-- *yaar-aadaruu* 'anyone'. -/
def yaarAadaruu : IndefinitePronoun := { form := "yaar-aadaruu", ontology := .person }

/-- *yaar-uu* 'anyone, no one'. -/
def yaarUu : IndefinitePronoun := { form := "yaar-uu", ontology := .person }

/-! ### The series -/

/-- The *-oo* series. -/
def ooSeries : IndefinitePronoun.Series :=
  ⟨"-oo", {yaarOo, ⟨{ form := "een-oo" }, .thing⟩, ⟨{ form := "elliy-oo" }, .place⟩,
    ⟨{ form := "yaavaagal-oo" }, .time⟩, ⟨{ form := "heeg-oo" }, .manner⟩,
    ⟨{ form := "eṣṭ-oo" }, .amount⟩, ⟨{ form := "yaava-n-oo" }, .determiner⟩,
    ⟨{ form := "yaava-ḷ-oo" }, .determiner⟩}⟩

/-- The *-aadaruu* series. -/
def aadaruuSeries : IndefinitePronoun.Series :=
  ⟨"-aadaruu", {yaarAadaruu, ⟨{ form := "een-aadaruu" }, .thing⟩,
    ⟨{ form := "elliy-aadaruu" }, .place⟩, ⟨{ form := "yaavaagal-aadaruu" }, .time⟩,
    ⟨{ form := "heeg-aadaruu" }, .manner⟩, ⟨{ form := "eṣṭ-aadaruu" }, .amount⟩,
    ⟨{ form := "yaavanaadaruu" }, .determiner⟩}⟩

/-- The *-uu* series. -/
def uuSeries : IndefinitePronoun.Series :=
  ⟨"-uu", {yaarUu, ⟨{ form := "een-uu" }, .thing⟩, ⟨{ form := "elliy-uu" }, .place⟩,
    ⟨{ form := "yaavaagal-uu" }, .time⟩, ⟨{ form := "heeg-uu" }, .manner⟩,
    ⟨{ form := "eṣṭ-uu" }, .amount⟩, ⟨{ form := "yaava X-uu" }, .determiner⟩}⟩

end Kannada.Indefinites
