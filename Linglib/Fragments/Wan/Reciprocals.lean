import Linglib.Syntax.Category.Pronoun.Logophoric
import Linglib.Syntax.Category.Pronoun.Reciprocal
import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Wan pronouns and reciprocal

Wan (Mande, Côte d'Ivoire) refers to the person whose speech or mental state is reported with a
logophoric pronoun ([nikitina-2012]), as in the complement of the speech verb *gé* 'say'; the
plural logophor *mɔ̄* can antecede the reciprocal
*ɔ̄ŋ̄*, which in (28) follows the reflexive *ē*. The forms are those Tatiana Nikitina provided
to Dalrymple and Haug, read from the printed page.

## TODO

* [nikitina-2012] prints the plural logophor with a nasalized vowel, *mɔ̰̄*; Dalrymple and Haug's
  (28) has plain *mɔ̄*, the form kept here.

## References

* [M. Dalrymple and D. T. T. Haug, *Constraints on reciprocal scope* (2024)][dalrymple-haug-2024]
* [T. Nikitina, *Logophoric Discourse and First Person Reporting in Wan (West Africa)*
  (2012)][nikitina-2012]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

namespace Wan.Reciprocals

/-- *mɔ̄* — the plural logophoric pronoun (LOG.PL), the subject of the report in (28) and
    (31). The logophoric pronouns stand for the person whose speech is reported and, with verbs
    of mental activity such as 'know' and 'imagine', for the person the state is attributed to,
    so the antecedent need only be a self; they do not distinguish a second from a third
    person antecedent ([nikitina-2012]). -/
def logPl : LogophoricPronoun := { form := "mɔ̄", number := some .plural, requiredRole := .self }

/-- *à̰* — the ordinary third-person plural pronoun ((32)). -/
def ordinaryPl : PersonalPronoun := { form := "à̰", person := some .third, number := some .plural }

/-- *ē* — the reflexive (REFL) of (28). -/
def reflexive : ReflexivePronoun := { form := "ē" }

/-- *ɔ̄ŋ̄* — the reciprocal (RECIP) of (28) and (32). -/
def reciprocal : ReciprocalPronoun := { form := "ɔ̄ŋ̄" }

end Wan.Reciprocals
