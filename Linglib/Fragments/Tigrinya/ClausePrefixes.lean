import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Morphology.Core.Circumfix

/-!
# Tigrinya Clausal Prefixes @cite{cacchioli-2025}

Lexical entries for Tigrinya's four clause-initial morphemes, analyzed as
spell-outs of distinct heads in a cartographic left periphery (Rizzi 1997).

## The four prefixes

| Prefix | Gloss | Head | Clause type |
|--------|-------|------|-------------|
| zɨ-    | REL   | Rel  | relative / general subordination |
| kɨ-    | SBJV  | Fin  | subjunctive / irrealis |
| kəmzi- | COMP  | Force | factive complementizer |
| ʔay-...-n | NEG | Neg  | negative (circumfix) |

## Key empirical facts

1. **Mutual exclusion**: The four prefixes are in complementary distribution
   (no stacking of zɨ- + kɨ-, etc.)
2. **Fixed position**: All precede the verbal complex
3. **Agreement**: kɨ- and ʔay-...-n take agreement suffixes; zɨ- does not
4. **Discontinuity**: Only ʔay-...-n is discontinuous (circumfix)
5. **Selection**: Matrix verb class determines which prefix appears
   (knowledge → kəmzi-, desiderative → kɨ-, etc.)

## References

- Cacchioli, S. (2025). The Syntax of Clausal Prefixes in Tigrinya.
  PhD dissertation.
-/

namespace Fragments.Tigrinya.ClausePrefixes

open Minimalism
open Morphology.Circumfix

-- ============================================================================
-- Clause type
-- ============================================================================

/-- Clause types in Tigrinya, determined by the clausal prefix. -/
inductive TigrinyaClauseType where
  | relative       -- zɨ-: relative clause or general subordination
  | subjunctive    -- kɨ-: subjunctive / irrealis
  | factive        -- kəmzi-: factive complement
  | negative       -- ʔay-...-n: negated clause
  | matrix         -- unmarked: root declarative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Clausal prefix entry
-- ============================================================================

/-- A Tigrinya clausal prefix lexical entry. -/
structure ClausePrefixEntry where
  /-- Surface form of the prefix -/
  prefix_ : String
  /-- Gloss -/
  gloss : String
  /-- Syntactic head this prefix spells out -/
  headCat : Cat
  /-- Clause type selected -/
  clauseType : TigrinyaClauseType
  /-- Whether the prefix takes an agreement suffix -/
  takesAgreementSuffix : Bool
  /-- Whether the exponence is discontinuous (circumfix) -/
  isDiscontinuous : Bool := false
  /-- Suffix form for circumfixes (empty if not discontinuous) -/
  suffix_ : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- zɨ- : relativizer / general subordinator.
    Spells out Rel (Rizzi 2001). Does not take agreement.
    "zɨ-mäs'ə" = REL-come = "who came" -/
def zi : ClausePrefixEntry where
  prefix_ := "zɨ-"
  gloss := "REL"
  headCat := .Rel
  clauseType := .relative
  takesAgreementSuffix := false

/-- kɨ- : subjunctive / irrealis marker.
    Spells out Fin (Rizzi 1997) with [-finite].
    Selected by desiderative/manipulative verbs.
    "kɨ-mäs'ə" = SBJV-come = "to come" -/
def ki : ClausePrefixEntry where
  prefix_ := "kɨ-"
  gloss := "SBJV"
  headCat := .Fin
  clauseType := .subjunctive
  takesAgreementSuffix := true

/-- kəmzi- : factive complementizer.
    Spells out Force (Rizzi 1997 split-CP).
    Selected by knowledge/commentative verbs.
    "kəmzi-mäs'ə" = COMP-come = "that (he) came" (factive) -/
def kemzi : ClausePrefixEntry where
  prefix_ := "kəmzi-"
  gloss := "COMP.FACT"
  headCat := .Force
  clauseType := .factive
  takesAgreementSuffix := false

/-- ʔay-...-n : negative circumfix.
    Spells out Neg (Pollock 1989).
    The verbal stem is wrapped: ʔay-mäs'ə-n = NEG-come-NEG = "did not come".
    Discontinuous exponence derived from V-to-Neg head movement. -/
def ay_n : ClausePrefixEntry where
  prefix_ := "ʔay-"
  gloss := "NEG"
  headCat := .Neg
  clauseType := .negative
  takesAgreementSuffix := true
  isDiscontinuous := true
  suffix_ := "-n"

-- ============================================================================
-- Collections
-- ============================================================================

/-- All four clausal prefix entries. -/
def allPrefixes : List ClausePrefixEntry := [zi, ki, kemzi, ay_n]

-- ============================================================================
-- Circumfix construction
-- ============================================================================

/-- Construct a `CircumfixExponence` from the negative circumfix entry. -/
def negCircumfix (verbStem : String) : CircumfixExponence where
  prefix_ := ay_n.prefix_
  suffix_ := ay_n.suffix_
  stem := verbStem
  gloss := ay_n.gloss

/-- The negative circumfix surfaces correctly. -/
theorem neg_circumfix_example :
    (negCircumfix "mäs'ə").realize = "ʔay-mäs'ə-n" := rfl

-- ============================================================================
-- Per-entry verification theorems
-- ============================================================================

theorem zi_targets_rel : zi.headCat = .Rel := rfl
theorem ki_targets_fin : ki.headCat = .Fin := rfl
theorem kemzi_targets_force : kemzi.headCat = .Force := rfl
theorem ay_targets_neg : ay_n.headCat = .Neg := rfl

theorem zi_no_agreement : zi.takesAgreementSuffix = false := rfl
theorem ki_has_agreement : ki.takesAgreementSuffix = true := rfl
theorem ay_is_discontinuous : ay_n.isDiscontinuous = true := rfl
theorem ki_is_continuous : ki.isDiscontinuous = false := rfl

end Fragments.Tigrinya.ClausePrefixes
