import Linglib.Semantics.Lexical.VerbEntry

/-!
# Korean Complementizers and Clause-Embedding Verbs
@cite{bondarenko-2022} @cite{bogal-allbritten-moulton-2018} @cite{kim-min-joo-2009}

Korean clause-typing morphology and matrix verbs that select bare vs.
nominalized embedded clauses (@cite{bondarenko-2022} §4.3.2).

## Three clause-typing morphemes (Bondarenko's specific decomposition)

- **-ta** — declarative ending. @cite{bondarenko-2022} §4.3.2
  (following @cite{bogal-allbritten-moulton-2018}) analyses *-ta* as
  the overt exponent of ContP, the projection introducing the CONT
  function. **NOT the consensus view**: alternative analyses
  (Shim & Ihsane 2015; @cite{kim-min-joo-2009}) treat *-ta*
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

open Semantics.Lexical (VerbCore)

-- ════════════════════════════════════════════════════════════════
-- § 1. Clause-typing morpheme inventory
-- ════════════════════════════════════════════════════════════════

/-- The three clause-typing morphemes covered here. -/
inductive KoreanClauseSuffix where
  /-- *-ta* — declarative ending. Bondarenko-specific decomposition
      treats it as overt ContP per @cite{bogal-allbritten-moulton-2018};
      the consensus view (Shim & Ihsane 2015, M.-J. Kim 2009) treats
      it as a clause-typing morpheme without that specific structural
      decomposition. -/
  | ta
  /-- *-nun* — adnominal ending; turns a clause into a noun modifier
      (typically followed by *kes* "thing" in nominalized clauses). -/
  | nun
  /-- *-ko* — connective / quotative complementizer. -/
  | ko
  deriving DecidableEq, Repr

/-- Phonological form. -/
def KoreanClauseSuffix.form : KoreanClauseSuffix → String
  | .ta  => "-ta"
  | .nun => "-nun"
  | .ko  => "-ko"

/-- Whether the suffix typically appears in nominalized clauses
    (consensus across analyses, including Bondarenko, M.-J. Kim,
    Shim & Ihsane). The adnominal *-nun* is the canonical
    nominalization morpheme; *-ta* and *-ko* are not. -/
def KoreanClauseSuffix.isAdnominal : KoreanClauseSuffix → Bool
  | .nun => true
  | _    => false

/-- The three suffixes are pairwise distinct. -/
theorem suffixes_distinct :
    KoreanClauseSuffix.ta ≠ .nun ∧
    KoreanClauseSuffix.ta ≠ .ko ∧
    KoreanClauseSuffix.nun ≠ .ko := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 2. The lexical noun *kes*
-- ════════════════════════════════════════════════════════════════

/-- *kes* — 'thing'. Light noun analysed by @cite{kim-min-joo-2009}
    as null-D + N. Combines with an adnominal *-nun*-marked clause
    to yield a nominalized DP that can saturate argument slots. -/
def kes : { form : String // form = "kes" } :=
  ⟨"kes", rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Matrix verb entries
-- ════════════════════════════════════════════════════════════════

/-- *yukamsulewehay-ta* — 'regret'. Preferential negative, stative.
    @cite{bondarenko-2022} §4.3.2. -/
def yukamsulewehayta : VerbCore where
  form := "yukamsulewehay-ta"
  complementType := .finiteClause
  attitude := some (.preferential (.degreeComparison .negative))
  vendlerClass := some .state

/-- *mit-ta* — 'believe'. Doxastic non-veridical, stative. -/
def mitta : VerbCore where
  form := "mit-ta"
  complementType := .finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true

/-- *sayngkakha-ta* — 'think'. Doxastic non-veridical, activity. -/
def sayngkakhata : VerbCore where
  form := "sayngkakha-ta"
  complementType := .finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* — 'interpret'. -/
def haysekhata : VerbCore where
  form := "haysekha-ta"
  complementType := .finiteClause
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* — 'explain'. Accomplishment; central to
    @cite{bondarenko-2022} §4.4.2 theme-argument analysis. -/
def selmyenghata : VerbCore where
  form := "selmyengha-ta"
  complementType := .finiteClause
  vendlerClass := some .accomplishment

-- ════════════════════════════════════════════════════════════════
-- § 4. Theorems
-- ════════════════════════════════════════════════════════════════

/-- Stativity split: *yukamsulewehay-ta* and *mit-ta* are stative;
    *sayngkakha-ta*, *haysekha-ta*, *selmyengha-ta* are eventive. -/
theorem stativity_split :
    yukamsulewehayta.vendlerClass = some .state ∧
    mitta.vendlerClass = some .state ∧
    sayngkakhata.vendlerClass = some .activity ∧
    haysekhata.vendlerClass = some .activity ∧
    selmyenghata.vendlerClass = some .accomplishment :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Korean.Complementizers
