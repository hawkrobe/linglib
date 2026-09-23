module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Korean complementizers and clause-embedding verbs

Korean embeds a clause in three ways: a bare clause in the declarative ending *-ta* followed
by the connective *-ko*; a *-ta*-clause under the adnominal ending *-nun* and the light noun
*kes* 'thing'; and a bare adnominal clause under *kes*. The three endings are complementizer
entries, *kes* a word, and the matrix verbs of Bondarenko's Korean data verb entries; her
assignment of *-ta* to the Cont head and of *-nun* and *-ko* to allomorphs of Comp is the
matter of `Studies/Bondarenko2022.lean`.

## References

* [bogal-allbritten-moulton-2018]
* [bondarenko-2022]
-/

@[expose] public section

namespace Korean.Complementizers

/-! ### Clause-typing morphemes -/

/-- *-ta*, the declarative ending, on finite verbs and on bare embedded clauses
(*ilk-ess-ta-ko*). -/
def ta : Complementizer where
  morphs := [.suff "ta"]
  verbForm := some .Fin
  force := some .declarative

/-- *-nun*, the adnominal ending, which turns a clause into a noun modifier and under *kes*
'thing' yields a nominalized complement. -/
def nun : Complementizer where
  morphs := [.suff "nun"]
  verbForm := some .Part
  licenser := some .nominal

/-- *-ko*, the connective ending on bare embedded clauses, adjacent to the verb. -/
def ko : Complementizer where
  morphs := [.suff "ko"]
  verbForm := some .Conv
  licenser := some .verbal

/-- The clause-typing inventory. -/
def complementizers : List Complementizer := [ta, nun, ko]

/-! ### The light noun *kes* -/

/-- *kes* 'thing', the light noun under adnominal clauses. -/
def kes : Morphology.Word := { form := "kes", cat := .NOUN }

/-! ### Matrix verbs -/

/-- *yukamsulewehay-ta* 'regret', a stative negative preference. -/
def yukamsulewehayta : Verb where
  form := "yukamsulewehay-ta"
  frames := [ArgumentFrame.finiteClause]
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

/-- *mit-ta* 'believe', a stative non-veridical doxastic. -/
def mitta : Verb where
  form := "mit-ta"
  frames := [ArgumentFrame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  opaqueContext := true

/-- *sayngkakha-ta* 'think', a non-veridical doxastic activity. -/
def sayngkakhata : Verb where
  form := "sayngkakha-ta"
  frames := [ArgumentFrame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* 'interpret'. -/
def haysekhata : Verb where
  form := "haysekha-ta"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* 'explain', which takes its clause as a theme argument. -/
def selmyenghata : Verb where
  form := "selmyengha-ta"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .accomplishment

end Korean.Complementizers
