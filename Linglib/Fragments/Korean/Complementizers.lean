import Linglib.Semantics.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

open Morphology (Word)

/-!
# Korean Complementizers and Clause-Embedding Verbs
[bondarenko-2022] [bogal-allbritten-moulton-2018] [kim-min-joo-2009]

Korean clause-typing morphology and matrix verbs that select bare vs.
nominalized embedded clauses ([bondarenko-2022] §4.3.2).

## Three clause-typing morphemes (Bondarenko's specific decomposition)

- **-ta** — declarative ending. [bondarenko-2022] §4.3.2
  (following [bogal-allbritten-moulton-2018]) analyses *-ta* as
  the overt exponent of ContP, the projection introducing the CONT
  function. **NOT the consensus view**: alternative analyses
  (Shim & Ihsane 2015; [kim-min-joo-2009]) treat *-ta*
  differently (clause-typing morpheme without specific structural
  decomposition). This Fragment file exposes the morpheme; the
  ContP-bearing claim is paper-specific apparatus and lives in
  `Studies/Bondarenko2022.lean`.
- **-nun** — adnominal ending; turns a clause into a noun-modifier.
  Co-occurs with *kes* in nominalized complement clauses.
- **-ko** — connective / quotative complementizer. Used in serialised
  predicate constructions and as a quotative complementizer.

## The lexical noun *kes*

- **kes** — 'thing'. Light noun (M.-J. Kim 2009) that combines with
  an adnominal-clause modifier to yield a nominalized clause that
  can saturate a DP argument slot. The Korean version of the
  "Saxon-genitive D + N" Bondarenko's general analysis posits.

## Scope

Per the project Fragment-discipline rule (textbook-consensus
metadata only): only the morphological inventory and verb entries
belong here. The Bondarenko-specific Cont/Comp split projection
lives in the `Bondarenko2022` Studies file.

## Matrix verbs

- *yukamsulewehay-ta* 'regret' — preferential negative, stative
- *mit-ta* 'believe' — doxastic non-veridical
- *sayngkakha-ta* 'think' — doxastic non-veridical
- *haysekha-ta* 'interpret' — speech act / doxastic
- *selmyengha-ta* 'explain' — accomplishment (the *explain*-class
  verb anchoring §4.4.2 theme-arg analysis)
-/

namespace Korean.Complementizers



-- ════════════════════════════════════════════════════════════════
-- § 1. Clause-typing morpheme inventory
-- ════════════════════════════════════════════════════════════════

/-- *-ta* — declarative ending. [bondarenko-2022] §4.3.2 (following
    [bogal-allbritten-moulton-2018]) analyses it as the overt ContP
    exponent — that decomposition is Studies-local
    (`Bondarenko2022.koreanAnalysis`); the consensus view
    (Shim & Ihsane 2015, [kim-min-joo-2009]) treats it as a
    clause-typing morpheme without that structural decomposition. -/
def ta : Complementizer where
  form := "-ta"
  position := some .postfixed
  verbForm := some .Fin
  clauseForm := some .declarative

/-- *-nun* — adnominal ending; turns a clause into a noun modifier
    (typically followed by *kes* 'thing' in nominalized clauses). -/
def nun : Complementizer where
  form := "-nun"
  position := some .postfixed
  verbForm := some .Part
  licenser := some .nominal

/-- *-ko* — connective / quotative complementizer; verb-adjacent Comp
    allomorph, paired with adnominal *-nun* (§4.3.2 ex. 46 of
    [bondarenko-2022]). -/
def ko : Complementizer where
  form := "-ko"
  position := some .postfixed
  verbForm := some .Conv
  licenser := some .verbal

/-- The clause-typing inventory. -/
def complementizers : List Complementizer := [ta, nun, ko]

-- ════════════════════════════════════════════════════════════════
-- § 2. The lexical noun *kes*
-- ════════════════════════════════════════════════════════════════

/-- *kes* — 'thing'. Light noun analysed by [kim-min-joo-2009]
    as null-D + N. Combines with an adnominal *-nun*-marked clause
    to yield a nominalized DP that can saturate argument slots. -/
def kes : Word := { form := "kes", cat := .NOUN }

-- ════════════════════════════════════════════════════════════════
-- § 3. Matrix verb entries
-- ════════════════════════════════════════════════════════════════

/-- *yukamsulewehay-ta* — 'regret'. Preferential negative, stative.
    [bondarenko-2022] §4.3.2. -/
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
  passivizable := false
  opaqueContext := true

/-- *sayngkakha-ta* — 'think'. Doxastic non-veridical, activity. -/
def sayngkakhata : Verb where
  form := "sayngkakha-ta"
  frames := [Frame.finiteClause]
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* — 'interpret'. -/
def haysekhata : Verb where
  form := "haysekha-ta"
  frames := [Frame.finiteClause]
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* — 'explain'. Accomplishment; central to
    [bondarenko-2022] §4.4.2 theme-argument analysis. -/
def selmyenghata : Verb where
  form := "selmyengha-ta"
  frames := [Frame.finiteClause]
  vendlerClass := some .accomplishment

end Korean.Complementizers
