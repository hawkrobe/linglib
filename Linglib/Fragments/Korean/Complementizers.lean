import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

open Morphology (Word)

/-!
# Korean Complementizers and Clause-Embedding Verbs
[bondarenko-2022] [bogal-allbritten-moulton-2018] [kim-min-joo-2009]

Korean embeds clauses three ways ([bondarenko-2022] §4.3.2 ex. 45): a
bare clause in the declarative ending *-ta* plus the connective *-ko*; a
*-ta*-clause under the adnominal ending *-nun* and the light noun *kes*
'thing'; and a bare adnominal clause under *kes*. The three endings are
root `Complementizer` entries, *kes* a `Word`, and the matrix verbs of
the thesis's Korean data `Verb` entries. The head assignment *-ta* ⇔
Cont, *-nun*/*-ko* ⇔ Comp allomorphs (ex. 46) is the thesis's analysis,
not a field.
-/

namespace Korean.Complementizers



/-! ### Clause-typing morphemes -/

/-- *-ta* — the declarative ending, on finite verbs and on bare
embedded clauses (*ilk-ess-ta-ko*, ex. 45a). -/
def ta : Complementizer where
  morphs := [.suff "ta"]
  verbForm := some .Fin
  force := some .declarative

/-- *-nun* — the adnominal ending, turning a clause into a noun
modifier; under *kes* 'thing' it yields nominalized complements
(ex. 45b–c). -/
def nun : Complementizer where
  morphs := [.suff "nun"]
  verbForm := some .Part
  licenser := some .nominal

/-- *-ko* — the connective ending on bare embedded clauses, adjacent
to the verb (ex. 45a). -/
def ko : Complementizer where
  morphs := [.suff "ko"]
  verbForm := some .Conv
  licenser := some .verbal

/-- The clause-typing inventory. -/
def complementizers : List Complementizer := [ta, nun, ko]

/-! ### The light noun *kes* -/

/-- *kes* — 'thing', the light noun under adnominal clauses
([kim-min-joo-2009]). -/
def kes : Word := { form := "kes", cat := .NOUN }

/-! ### Matrix verbs -/

/-- *yukamsulewehay-ta* — 'regret'. Preferential negative, stative
(ex. 45). -/
def yukamsulewehayta : Verb where
  form := "yukamsulewehay-ta"
  frames := [Frame.finiteClause]
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

/-- *mit-ta* — 'believe'. Doxastic non-veridical, stative. -/
def mitta : Verb where
  form := "mit-ta"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  opaqueContext := true

/-- *sayngkakha-ta* — 'think'. Doxastic non-veridical, activity. -/
def sayngkakhata : Verb where
  form := "sayngkakha-ta"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* — 'interpret' (§2.5). -/
def haysekhata : Verb where
  form := "haysekha-ta"
  frames := [Frame.finiteClause]
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* — 'explain', the §4.4.2 Theme-argument verb
(ex. 106–107). -/
def selmyenghata : Verb where
  form := "selmyengha-ta"
  frames := [Frame.finiteClause]
  vendlerClass := some .accomplishment

end Korean.Complementizers
