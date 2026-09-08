import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Wan pronouns and reciprocal

Wan (Mande, Côte d'Ivoire) refers to the reported speaker in the complement of the speech verb
*gé* 'say' with a logophoric pronoun; the plural logophor *mɔ̄* can antecede the reciprocal
*ɔ̄ŋ̄*, which in (28) follows the reflexive *ē*. The forms are those Tatiana Nikitina provided
to Dalrymple and Haug, read from the printed page.

## References

* [M. Dalrymple and D. T. T. Haug, *Constraints on reciprocal scope* (2024)][dalrymple-haug-2024]
-/

namespace Wan.Reciprocals

open Pronoun

/-- *mɔ̄* — the plural logophoric pronoun (LOG.PL), the subject of the report in (28) and
    (31). -/
def logPl : PersonalPronoun := { form := "mɔ̄", number := some .plural }

/-- *à̰* — the ordinary third-person plural pronoun ((32)). -/
def ordinaryPl : PersonalPronoun := { form := "à̰", person := some .third, number := some .plural }

/-- *ē* — the reflexive (REFL) of (28). -/
def reflexive : Pronoun := { form := "ē", bindingClass := some .reflexive }

/-- *ɔ̄ŋ̄* — the reciprocal (RECIP) of (28) and (32). -/
def reciprocal : ReciprocalPronoun := { form := "ɔ̄ŋ̄" }

end Wan.Reciprocals
