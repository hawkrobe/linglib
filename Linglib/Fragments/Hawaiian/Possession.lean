import Linglib.Features.Possession

/-!
# Hawaiian possession

Hawaiian possessive particles come in pairs distinguished by the vowels *a*
and *o*: *kaʻu puke* "my book" vs *koʻu makuahine* "my mother". The choice is
relation-based rather than a lexical noun class ([wilson-1976]): relations
the possessor creates or instigates take *a* (children, spouses, food,
implements), while relations outside the possessor's control (body parts,
parents, siblings, chiefs) take *o*, as do those in which the possessed
serves as the possessor's location (houses, clothing, ridden animals). The
same noun shifts class with the relation: *koʻu hale* "my house (I live in)"
vs *kaʻu hale* "my house (that I built)".

Hawaiian has no verb "to have" ([elbert-pukui-1979]): predicative possession
is a verbless sentence with a genitive possessor — *He puke kaʻu* "I have a
book" (lit. "a book of-mine"), the *pepeke nonoʻa* of [bardwell-etal-2024].
Adnominal possessors carry the particle *a* or *o* (*ka hale o Pua* "Pua's
house") while the possessum stays unmarked, and no noun requires possessive
marking.

## References

* [wilson-1976] — the control analysis of the a-class vs o-class contrast
* [elbert-pukui-1979] — reference grammar; possessives and verbless ownership
  sentences §8.4, the a-form vs o-form possessives §9.6
* [bardwell-etal-2024] — the possessive sentence (*pepeke nonoʻa*)
* [stassen-2013b] — WALS 117A, the Genitive predicative type
-/

namespace Hawaiian.Possession

open _root_.Possession

/-- No Hawaiian noun requires a possessor. -/
def obligatoryPossession : Obligatoriness := .noObligatory

/-- The a-class vs o-class contrast. WALS 59A codes the parallel Māori
    system as unclassified and Rapanui as two-class. -/
def possessiveClassification : Classification := .twoWay

/-- The *pepeke nonoʻa* possessive sentence *He puke kaʻu* "I have a book",
    an existential possessee with a genitive possessor and no locative
    marking. WALS 117A assigns this type to Māori and Tahitian. -/
def predicativeStrategy : PredicativeStrategy := .genitive

/-- The possessor carries the genitive particle *a* or *o* while the
    possessum stays unmarked (*ka hale o Pua* "Pua's house"). -/
def adnominalStrategy : AdnominalMarking := .dependentMarking

end Hawaiian.Possession
