/-
# Left-Nested Conditionals: Empirical Data

Theory-neutral empirical observations about left-nested conditionals (LNCs)
from Lassiter (2025) "Sorting out left-nested conditionals."

## Overview

LNCs have the form "If (B if A), C" - a conditional whose antecedent is
itself a conditional.

This file documents:
1. Gibbard's classic example and discourse effects
2. Cross-linguistic markers (Japanese, German)
3. NPI/PPI licensing patterns
4. Coordination constraints
5. *Only* + inversion patterns
6. Modal/generic exceptions

## References

- Lassiter (2025). Sorting out left-nested conditionals.
- Gibbard (1981). Two recent theories of conditionals.
- McGee (1985). A counterexample to modus ponens.
- Iatridou (1991). Topics in Conditionals.
- Haegeman (2003). Conditional clauses: External and internal syntax.
-/

import Linglib.Phenomena.Core.EmpiricalData

namespace Phenomena.Conditionals.LeftNested

-- Data Structure

/--
Left-nested conditional empirical datum.

Captures a single LNC example with its properties and judgments.
-/
structure LNCDatum where
  /-- The full sentence -/
  sentence : String
  /-- The inner conditional ("B if A") -/
  innerConditional : String
  /-- The outer consequent ("C") -/
  outerConsequent : String
  /-- Content type: "bare", "modal", "generic", "quantAdv" -/
  content : String
  /-- Optional discourse context that improves acceptability -/
  discourseContext : Option String
  /-- Acceptability judgment: "ok", "odd", "marginal" -/
  acceptability : String
  /-- Preferred interpretation: "PC", "HC", "ambiguous" -/
  interpretation : String
  /-- Additional notes -/
  notes : String
  deriving Repr

-- Gibbard's Example

/-!
## Gibbard's Example (1981)

The classic example of a left-nested conditional, discussed extensively
in the philosophical literature on conditionals.
-/

/-- Gibbard's classic LNC (out of the blue) -/
def gibbardOutOfBlue : LNCDatum :=
  { sentence := "If Kripke was there if Strawson was, Anscomb was there"
    innerConditional := "Kripke was there if Strawson was"
    outerConsequent := "Anscomb was there"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "PC"
    notes := "Gibbard (1981) example 4. Odd without discourse context."
  }

/-- Gibbard's example with discourse context -/
def gibbardWithContext : LNCDatum :=
  { sentence := "If Kripke was there if Strawson was, Anscomb was there"
    innerConditional := "Kripke was there if Strawson was"
    outerConsequent := "Anscomb was there"
    content := "bare"
    discourseContext := some "A: 'I think Kripke was there if Strawson was.' B: (reply)"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Acceptable when inner conditional echoes prior discourse."
  }

-- Discourse Contextualization (Examples 11-14)

/-!
## Discourse Effects

LNCs improve dramatically when the inner conditional is established
in prior discourse.
-/

/-- Example 11: Decontextualized LNC -/
def ex11_decontextualized : LNCDatum :=
  { sentence := "If the fish will die if you don't change the water, you should change the water"
    innerConditional := "the fish will die if you don't change the water"
    outerConsequent := "you should change the water"
    content := "bare"
    discourseContext := none
    acceptability := "marginal"
    interpretation := "PC"
    notes := "Example 11. Marginal without context."
  }

/-- Example 12: Contextualized LNC -/
def ex12_contextualized : LNCDatum :=
  { sentence := "If the fish will die if you don't change the water, you should change the water"
    innerConditional := "the fish will die if you don't change the water"
    outerConsequent := "you should change the water"
    content := "bare"
    discourseContext := some "Context: The pet store owner tells you 'The fish will die if you don't change the water regularly.'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 12. Good with discourse anchor."
  }

/-- Example 13: Another LNC -/
def ex13_contextual : LNCDatum :=
  { sentence := "If this phone will break if you drop it, you'd better be careful"
    innerConditional := "this phone will break if you drop it"
    outerConsequent := "you'd better be careful"
    content := "bare"
    discourseContext := some "Context: Someone just told you 'This phone will break if you drop it.'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 13. Echoes prior warning."
  }

/-- Example 14: LNC with given-that paraphrase -/
def ex14_givenThat : LNCDatum :=
  { sentence := "Given that the fish will die if you don't change the water, you should change the water"
    innerConditional := "the fish will die if you don't change the water"
    outerConsequent := "you should change the water"
    content := "bare"
    discourseContext := some "Context: Pet store advice established."
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 14. 'Given that' paraphrase confirms PC reading."
  }

-- Cross-Linguistic: Japanese (Examples 15-19)

/-!
## Japanese Conditional Markers

Japanese distinguishes:
- **-ra** / **-tara**: HC-only marker
- **nara**: Can mark PCs

LNCs with nara are acceptable; with -ra they are not.
-/

/-- Example 15: Japanese nara in LNC -/
def ex15_japaneseNara : LNCDatum :=
  { sentence := "Strawson-ga kite-ita nara Kripke-ga kite-ita nara, Anscomb-ga kite-ita"
    innerConditional := "Kripke came if Strawson came (nara)"
    outerConsequent := "Anscomb came"
    content := "bare"
    discourseContext := some "Prior: 'Strawson-ga kite-ita nara Kripke-ga kite-ita.'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 15. Japanese nara can mark PCs, so LNC is ok."
  }

/-- Example 16: Japanese -ra in LNC -/
def ex16_japaneseRa : LNCDatum :=
  { sentence := "*Strawson-ga kite-ita-ra Kripke-ga kite-ita-ra, Anscomb-ga kite-ita"
    innerConditional := "Kripke came if Strawson came (-ra)"
    outerConsequent := "Anscomb came"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "blocked"
    notes := "Example 16. Japanese -ra is HC-only; LNC blocked."
  }

/-- Example 17: Japanese nara echoing discourse -/
def ex17_naraEcho : LNCDatum :=
  { sentence := "A: Strawson-ga kite-ita nara Kripke-ga kite-ita. B: Sou nara, Anscomb-mo kite-ita"
    innerConditional := "Kripke came if Strawson came"
    outerConsequent := "Anscomb also came"
    content := "bare"
    discourseContext := some "A's assertion provides discourse anchor"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 17. 'Sou nara' = 'if so' echoes A's conditional."
  }

-- Cross-Linguistic: German (Examples 20-24)

/-!
## German Conditional Markers

German distinguishes:
- **falls**: HC-only marker (implies speaker uncertainty)
- **wenn**: Can mark either HC or PC

LNCs with wenn are acceptable; with falls they are marginal/bad.
-/

/-- Example 20: German wenn in LNC -/
def ex20_germanWenn : LNCDatum :=
  { sentence := "Wenn Strawson da war, wenn Kripke da war, war Anscomb da"
    innerConditional := "Kripke was there if Strawson was (wenn)"
    outerConsequent := "Anscomb was there"
    content := "bare"
    discourseContext := some "Prior: 'Wenn Strawson da war, war Kripke da.'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 20. German wenn can mark PCs."
  }

/-- Example 21: German falls in LNC -/
def ex21_germanFalls : LNCDatum :=
  { sentence := "?Falls Strawson da war, falls Kripke da war, war Anscomb da"
    innerConditional := "Kripke was there if Strawson was (falls)"
    outerConsequent := "Anscomb was there"
    content := "bare"
    discourseContext := none
    acceptability := "marginal"
    interpretation := "blocked"
    notes := "Example 21. German falls is HC-only; LNC degraded."
  }

/-- Example 22: German falls with modal -/
def ex22_fallsModal : LNCDatum :=
  { sentence := "Falls der Fisch sterben würde, falls du das Wasser nicht wechselst, solltest du es wechseln"
    innerConditional := "the fish would die if you don't change the water"
    outerConsequent := "you should change it"
    content := "modal"
    discourseContext := none
    acceptability := "ok"
    interpretation := "HC"
    notes := "Example 22. Modal content allows falls in LNC."
  }

-- NPI/PPI Licensing (Examples 29-32)

/-!
## Polarity Patterns

The PC analysis predicts specific polarity patterns in LNCs:
- PPIs licensed in embedded consequent (B position)
- NPIs blocked in embedded consequent (B position)
-/

/-- Example 29: PPI in embedded consequent (ok) -/
def ex29_ppiOk : LNCDatum :=
  { sentence := "If John helped someone if asked, we're in good shape"
    innerConditional := "John helped someone if asked"
    outerConsequent := "we're in good shape"
    content := "bare"
    discourseContext := some "Prior: 'Did John help someone if asked?'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 29. PPI 'someone' licensed in B position (PC reading)."
  }

/-- Example 30: NPI in embedded consequent (bad) -/
def ex30_npiBad : LNCDatum :=
  { sentence := "*If John helped anyone if asked, we're in good shape"
    innerConditional := "John helped anyone if asked"
    outerConsequent := "we're in good shape"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "PC"
    notes := "Example 30. NPI 'anyone' blocked in B position (PC doesn't license NPIs)."
  }

/-- Example 31: Another PPI case -/
def ex31_ppiSomeone : LNCDatum :=
  { sentence := "If Mary talked to someone if prompted, the experiment succeeded"
    innerConditional := "Mary talked to someone if prompted"
    outerConsequent := "the experiment succeeded"
    content := "bare"
    discourseContext := some "Prior experimental expectation"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 31. PPI 'someone' ok in embedded consequent."
  }

/-- Example 32: Another NPI case -/
def ex32_npiAnyone : LNCDatum :=
  { sentence := "*If Mary talked to anyone if prompted, the experiment succeeded"
    innerConditional := "Mary talked to anyone if prompted"
    outerConsequent := "the experiment succeeded"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "PC"
    notes := "Example 32. NPI 'anyone' blocked in embedded consequent."
  }

-- Coordination Constraints (Examples 33-35)

/-!
## Coordination Constraints

Haegeman (2003): Premise conditionals resist coordination with other
conditional clauses. This extends to LNCs.
-/

/-- Example 33: Coordinated HCs (ok) -/
def ex33_coordinatedHC : LNCDatum :=
  { sentence := "If you're hungry and if you want some food, there are biscuits"
    innerConditional := "N/A (not LNC)"
    outerConsequent := "there are biscuits"
    content := "bare"
    discourseContext := none
    acceptability := "ok"
    interpretation := "HC"
    notes := "Example 33. Regular HCs can coordinate."
  }

/-- Example 34: Coordinated with LNC (bad) -/
def ex34_coordinatedLNC : LNCDatum :=
  { sentence := "*If Mary left if John did and if Sue is upset, we have a problem"
    innerConditional := "Mary left if John did"
    outerConsequent := "we have a problem"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "PC"
    notes := "Example 34. LNC (PC) resists coordination with regular conditional."
  }

/-- Example 35: Coordination diagnostic -/
def ex35_coordinationDiagnostic : LNCDatum :=
  { sentence := "?If the fish will die if you don't change the water and if you care about the fish, change the water"
    innerConditional := "the fish will die if you don't change the water"
    outerConsequent := "change the water"
    content := "bare"
    discourseContext := some "Pet store context"
    acceptability := "marginal"
    interpretation := "PC"
    notes := "Example 35. Coordination constraint even with discourse support."
  }

-- Only + Inversion (Examples 36-39)

/-!
## *Only* + Inversion

Another diagnostic from Haegeman (2003): PCs block *only* + subject-aux
inversion, while HCs allow it.
-/

/-- Example 36: Only-inversion with HC (ok) -/
def ex36_onlyInversionHC : LNCDatum :=
  { sentence := "Only if you leave will I stay"
    innerConditional := "N/A (not LNC)"
    outerConsequent := "I will stay"
    content := "bare"
    discourseContext := none
    acceptability := "ok"
    interpretation := "HC"
    notes := "Example 36. Regular HC allows only-inversion."
  }

/-- Example 37: Only-inversion with LNC (bad) -/
def ex37_onlyInversionLNC : LNCDatum :=
  { sentence := "*Only if Mary left if John did will we have a problem"
    innerConditional := "Mary left if John did"
    outerConsequent := "we will have a problem"
    content := "bare"
    discourseContext := none
    acceptability := "odd"
    interpretation := "blocked"
    notes := "Example 37. LNC (PC) blocks only-inversion."
  }

/-- Example 38: Without inversion (ok) -/
def ex38_noInversion : LNCDatum :=
  { sentence := "We will have a problem only if Mary left if John did"
    innerConditional := "Mary left if John did"
    outerConsequent := "we will have a problem"
    content := "bare"
    discourseContext := some "Prior: 'I think Mary left if John did.'"
    acceptability := "ok"
    interpretation := "PC"
    notes := "Example 38. LNC ok without inversion."
  }

-- Modal/Generic Exceptions (Examples 40-43)

/-!
## Modal and Generic Exceptions

LNCs with modals, quantificational adverbs, or generic interpretations
CAN be interpreted as HCs, allowing broader distribution.
-/

/-- Example 40: Modal in inner conditional -/
def ex40_modal : LNCDatum :=
  { sentence := "If the fish would die if you didn't change the water, you should change it"
    innerConditional := "the fish would die if you didn't change the water"
    outerConsequent := "you should change it"
    content := "modal"
    discourseContext := none
    acceptability := "ok"
    interpretation := "HC"
    notes := "Example 40. Modal 'would' allows HC reading."
  }

/-- Example 41: Quantificational adverb -/
def ex41_quantAdv : LNCDatum :=
  { sentence := "If a car usually starts if you turn the key, it's probably reliable"
    innerConditional := "a car usually starts if you turn the key"
    outerConsequent := "it's probably reliable"
    content := "quantAdv"
    discourseContext := none
    acceptability := "ok"
    interpretation := "ambiguous"
    notes := "Example 41. 'Usually' provides quantificational content."
  }

/-- Example 42: Generic reading -/
def ex42_generic : LNCDatum :=
  { sentence := "If dogs bark if provoked, we should keep them away from the children"
    innerConditional := "dogs bark if provoked"
    outerConsequent := "we should keep them away from the children"
    content := "generic"
    discourseContext := none
    acceptability := "ok"
    interpretation := "HC"
    notes := "Example 42. Generic interpretation allows HC reading."
  }

/-- Example 43: Habitual reading -/
def ex43_habitual : LNCDatum :=
  { sentence := "If John cries if scolded, we shouldn't be too hard on him"
    innerConditional := "John cries if scolded"
    outerConsequent := "we shouldn't be too hard on him"
    content := "generic"
    discourseContext := none
    acceptability := "ok"
    interpretation := "ambiguous"
    notes := "Example 43. Habitual reading allows HC."
  }

-- Aggregate Data

/-- All Gibbard-related examples -/
def gibbardData : List LNCDatum :=
  [gibbardOutOfBlue, gibbardWithContext]

/-- All discourse contextualization examples -/
def discourseData : List LNCDatum :=
  [ex11_decontextualized, ex12_contextualized, ex13_contextual, ex14_givenThat]

/-- All Japanese examples -/
def japaneseData : List LNCDatum :=
  [ex15_japaneseNara, ex16_japaneseRa, ex17_naraEcho]

/-- All German examples -/
def germanData : List LNCDatum :=
  [ex20_germanWenn, ex21_germanFalls, ex22_fallsModal]

/-- All polarity examples -/
def polarityData : List LNCDatum :=
  [ex29_ppiOk, ex30_npiBad, ex31_ppiSomeone, ex32_npiAnyone]

/-- All coordination examples -/
def coordinationData : List LNCDatum :=
  [ex33_coordinatedHC, ex34_coordinatedLNC, ex35_coordinationDiagnostic]

/-- All only-inversion examples -/
def onlyInversionData : List LNCDatum :=
  [ex36_onlyInversionHC, ex37_onlyInversionLNC, ex38_noInversion]

/-- All modal/generic exception examples -/
def exceptionData : List LNCDatum :=
  [ex40_modal, ex41_quantAdv, ex42_generic, ex43_habitual]

/-- All LNC data -/
def allData : List LNCDatum :=
  gibbardData ++ discourseData ++ japaneseData ++ germanData ++
  polarityData ++ coordinationData ++ onlyInversionData ++ exceptionData

-- Empirical Generalizations

/-!
## Core Empirical Generalizations

### 1. Discourse Anchoring
Bare LNCs improve dramatically when the inner conditional is established
in prior discourse.

### 2. Cross-Linguistic Markers
Languages with distinct HC/PC markers show that LNCs pattern with PCs:
- Japanese: nara (PC-compatible) ok, -ra (HC-only) blocked
- German: wenn (both) ok, falls (HC-only) degraded

### 3. Polarity Patterns
- PPIs licensed in embedded consequent (B position)
- NPIs blocked in embedded consequent (B position)
Consistent with PC (not HC) reading.

### 4. Coordination Constraints
LNCs resist coordination with other conditional clauses,
like other PCs (Haegeman 2003).

### 5. *Only* + Inversion
LNCs block *only* + subject-aux inversion,
like other PCs (Haegeman 2003).

### 6. Modal/Generic Exception
LNCs with modals, quantificational adverbs, or generic interpretation
CAN be HCs, because these provide "object-level" content that can be
genuinely supposed without prior discourse.
-/

-- Guards for Data Consistency

-- Bare LNCs without context are odd
#guard gibbardOutOfBlue.acceptability == "odd"

-- Bare LNCs with context are ok
#guard gibbardWithContext.acceptability == "ok"

-- Japanese nara ok, -ra blocked
#guard ex15_japaneseNara.acceptability == "ok"
#guard ex16_japaneseRa.acceptability == "odd"

-- German wenn ok, falls marginal
#guard ex20_germanWenn.acceptability == "ok"
#guard ex21_germanFalls.acceptability == "marginal"

-- PPI ok, NPI blocked in embedded consequent
#guard ex29_ppiOk.acceptability == "ok"
#guard ex30_npiBad.acceptability == "odd"

-- Modal allows HC reading
#guard ex40_modal.content == "modal"
#guard ex40_modal.interpretation == "HC"

-- Generic allows HC reading
#guard ex42_generic.content == "generic"
#guard ex42_generic.interpretation == "HC"

end Phenomena.Conditionals.LeftNested
