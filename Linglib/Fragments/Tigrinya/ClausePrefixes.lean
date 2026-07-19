import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Morphology.Word.Structure

/-!
# Tigrinya Clausal Prefixes [cacchioli-2025]
[pollock-1989] [rizzi-1997]

Lexical entries for Tigrinya's four clause-initial morphemes, as
`Complementizer`-schema entries with the Tigrinya-specific fields
(`gloss`, `clauseType`, circumfixal `suffix_`).

## The four prefixes

| Prefix | Gloss | Clause type |
|--------|-------|-------------|
| zɨ-    | REL   | relative / general subordination |
| kɨ-    | SBJV  | subjunctive / irrealis |
| kəmzi- | COMP  | factive complementizer |
| ʔay-...-n | NEG | negative (circumfix) |

## Key empirical facts

1. **Mutual exclusion**: The four prefixes are in complementary distribution
   (no stacking of zɨ- + kɨ-, etc.)
2. **Fixed position**: All precede the verbal complex
3. **Agreement**: kɨ- and ʔay-...-n take agreement suffixes; zɨ- does not
4. **Discontinuity**: Only ʔay-...-n is discontinuous (circumfix)
5. **Selection**: Matrix verb class determines which prefix appears
   (knowledge → kəmzi-, desiderative → kɨ-, etc.)

[cacchioli-2025]'s cartographic head assignment (zɨ- = Rel, kɨ- = Fin,
kəmzi- = Force, ʔay- = Neg in a [rizzi-1997] split CP) is paper-specific
and lives as the `headCat` projection in `Studies/Cacchioli2025.lean`.
-/

namespace Tigrinya.ClausePrefixes

open Morphology

/-- Clause types in Tigrinya, determined by the clausal prefix. -/
inductive TigrinyaClauseType where
  | relative       -- zɨ-: relative clause or general subordination
  | subjunctive    -- kɨ-: subjunctive / irrealis
  | factive        -- kəmzi-: factive complement
  | negative       -- ʔay-...-n: negated clause
  | matrix         -- unmarked: root declarative
  deriving DecidableEq, Repr

/-- A Tigrinya clausal prefix lexical entry: the root `Complementizer`
schema plus the Tigrinya-specific fields. The form is the prefix half;
the discontinuous negative also sets `suffix_`. -/
structure ClausePrefixEntry extends Complementizer where
  /-- Gloss -/
  gloss : String
  /-- Clause type selected -/
  clauseType : TigrinyaClauseType
  /-- Suffix form for circumfixes (empty if not discontinuous) -/
  suffix_ : String := ""
  deriving Repr, BEq, DecidableEq

/-- zɨ- : relativizer / general subordinator. Does not take agreement.
    "zɨ-mäs'ə" = REL-come = "who came" -/
def zi : ClausePrefixEntry where
  form := "zɨ-"
  position := some .praefixed
  agrees := some false
  gloss := "REL"
  clauseType := .relative

/-- kɨ- : subjunctive / irrealis marker. Takes an agreement suffix.
    Selected by desiderative/manipulative verbs.
    "kɨ-mäs'ə" = SBJV-come = "to come" -/
def ki : ClausePrefixEntry where
  form := "kɨ-"
  position := some .praefixed
  noonanType := some .subjunctive
  agrees := some true
  gloss := "SBJV"
  clauseType := .subjunctive

/-- kəmzi- : factive complementizer. Selected by knowledge/commentative
    verbs. "kəmzi-mäs'ə" = COMP-come = "that (he) came" (factive) -/
def kemzi : ClausePrefixEntry where
  form := "kəmzi-"
  position := some .praefixed
  noonanType := some .indicative
  agrees := some false
  factive := some true
  gloss := "COMP.FACT"
  clauseType := .factive

/-- ʔay-...-n : negative circumfix. The verbal stem is wrapped:
    ʔay-mäs'ə-n = NEG-come-NEG = "did not come". Discontinuous exponence
    derived from V-to-Neg head movement. -/
def ay_n : ClausePrefixEntry where
  form := "ʔay-"
  position := some .circumfixed
  agrees := some true
  gloss := "NEG"
  clauseType := .negative
  suffix_ := "-n"

/-- All four clausal prefix entries. -/
def allPrefixes : List ClausePrefixEntry := [zi, ki, kemzi, ay_n]

/-- The negative circumfix as word structure: the verb stem wrapped by
*ʔay-* and *-n* (an inflectional circumfixation, [haspelmath-2020]'s
prefix-plus-suffix construction reading). -/
def negCircumfix (verbStem : String) : Word.Structure :=
  .circumfixed ⟨Morph.pref ay_n.form, ay_n.gloss⟩
    (.root ⟨Morph.free verbStem, ""⟩)
    ⟨Morph.suff ay_n.suffix_, ay_n.gloss⟩
    .inflectional

/-- The negative circumfix surfaces correctly. -/
theorem neg_circumfix_example :
    (negCircumfix "mäs'ə").surface = "ʔay-mäs'ə-n" := rfl

/-- Discontinuous exponence: the circumfixed structure has no
morph-sequence projection (`toExponent = none`) — the circumfix is a
construction, not a morph ([haspelmath-2020]). -/
theorem neg_circumfix_no_exponent (s : String) :
    (negCircumfix s).toExponent = none := rfl

end Tigrinya.ClausePrefixes
