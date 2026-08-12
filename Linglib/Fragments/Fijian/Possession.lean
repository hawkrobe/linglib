import Linglib.Features.Possession

/-!
# Fijian possession

Fijian possesses inalienables by direct suffixation of the possessor to the
noun (*na liga-qu* "my hand") and alienables through a classifier: *ke-* for
things to eat (*na ke-qu kakana* "my food"), *me-* for things to drink
(*na me-qu ti* "my tea"), *no-* for general property (*na no-qu vale* "my
house"). WALS 59A nonetheless codes Fijian as *No possessive classification*
under Nichols & Bickel's criterion; the values here follow the descriptive
four-class tradition.

## References

[stassen-2009] [nichols-1986] [heine-1997]
-/

namespace Fijian.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .threeOrMore
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .headMarking

end Fijian.Possession
