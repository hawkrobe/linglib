import Linglib.Syntax.Category.Pronoun.Logophoric
import Linglib.Syntax.Category.Pronoun.Reciprocal
import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Wan pronouns and reciprocal

Wan (Mande, Côte d'Ivoire) refers to the reported speaker in the complement of the speech verb
*gé* 'say' with a logophoric pronoun; the plural logophor *mɔ̄* can antecede the reciprocal
*ɔ̄ŋ̄*, which in (28) follows the reflexive *ē*. The forms are those Tatiana Nikitina provided
to Dalrymple and Haug, read from the printed page.

## References

* [M. Dalrymple and D. T. T. Haug, *Constraints on reciprocal scope* (2024)][dalrymple-haug-2024]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

namespace Wan.Reciprocals

open Pronoun

/-- *mɔ̄* — the plural logophoric pronoun (LOG.PL), the subject of the report in (28) and
    (31). It refers to the reported speaker under *gé* 'say', [sells-1987]'s source. -/
-- UNVERIFIED: whether a verb of thinking also licenses *mɔ̄*, which would lower the role to self.
def logPl : LogophoricPronoun := { form := "mɔ̄", number := some .plural, requiredRole := .source }

/-- *à̰* — the ordinary third-person plural pronoun ((32)). -/
def ordinaryPl : PersonalPronoun := { form := "à̰", person := some .third, number := some .plural }

/-- *ē* — the reflexive (REFL) of (28). -/
def reflexive : ReflexivePronoun := { form := "ē" }

/-- *ɔ̄ŋ̄* — the reciprocal (RECIP) of (28) and (32). -/
def reciprocal : ReciprocalPronoun := { form := "ɔ̄ŋ̄" }

end Wan.Reciprocals
