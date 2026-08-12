import Linglib.Features.Possession

/-!
# Hawaiian possession profile

Per-language possession values for Hawaiian (Polynesian, ISO `haw`), coded from
[elbert-pukui-1979] and consumed by `Studies/NicholsBickel2013`; of the WALS
possession chapters only 57A samples Hawaiian.

The two possessive classes are relation-based ([wilson-1976]): relations the
possessor controls — creates or instigates — take a-class (*kaʻu puke* "my
book"; children, spouses, food, implements), while uncontrolled relations
(body parts, parents, siblings, chiefs) and those where the possessed serves
as the possessor's location (houses, clothing, ridden animals) take o-class
(*koʻu makuahine* "my mother"). Not classic Oceanic alienability: the same
noun shifts class with the relation, *koʻu hale* "my house (I live in)" vs
*kaʻu hale* "my house (that I built)".
-/

set_option autoImplicit false

namespace Hawaiian.Possession

open _root_.Possession

/-- Possessives are free determiners; no noun requires one ([elbert-pukui-1979]). -/
def obligatoryPossession : Obligatoriness := .noObligatory

/-- The a-class vs o-class contrast ([wilson-1976]). WALS 59A splits on parallel
    Polynesian systems — Rapanui and Tongan two classes, Māori none — so this
    follows the descriptive tradition. -/
def possessiveClassification : Classification := .twoWay

/-- *He puke kaʻu* "I have a book": existential possessee with genitive
    possessor, the type WALS 117A assigns to Māori and Tahitian ([stassen-2013b]). -/
def predicativeStrategy : PredicativeStrategy := .genitive

/-- The possessor carries the genitive particle *a* or *o* (*ka hale o Pua*
    "Pua's house"); the possessum is unmarked ([nichols-1986]). -/
def adnominalStrategy : AdnominalMarking := .dependentMarking

end Hawaiian.Possession
