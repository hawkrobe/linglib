/-
# Cross-Sentential Anaphora

Empirical data on pronouns whose antecedents are in earlier sentences.

## Main definitions

- `CrossSententialDatum`: Data structure for cross-sentential anaphora
- `indefinitePersists`, `universalBlocks`: Key examples of persistence and blocking

## References

- Karttunen, L. (1969). Discourse Referents.
- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Kamp, H. (1981). A Theory of Truth and Semantic Representation.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
-/

namespace Phenomena.Anaphora.CrossSententialAnaphora

/-- Cross-sentential anaphora datum. -/
structure CrossSententialDatum where
  sentences : List String
  pronounSentenceIdx : Nat
  pronoun : String
  antecedentSentenceIdx : Nat
  antecedent : String
  felicitous : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Basic indefinite persistence -/
def indefinitePersists : CrossSententialDatum := {
  sentences := ["A man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "a man"
  felicitous := true
  notes := "Classic example: indefinite introduces persistent dref"
  source := "Karttunen (1969)"
}

/-- Multi-sentence discourse -/
def multiSentence : CrossSententialDatum := {
  sentences := ["A man walked in.", "He looked around.", "He sat down."]
  pronounSentenceIdx := 2
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "a man"
  felicitous := true
  notes := "Drefs persist across multiple sentences"
  source := "Heim (1982)"
}

/-- Multiple drefs -/
def multipleDrefs : CrossSententialDatum := {
  sentences := ["A man met a woman.", "He greeted her."]
  pronounSentenceIdx := 1
  pronoun := "he/her"
  antecedentSentenceIdx := 0
  antecedent := "a man/a woman"
  felicitous := true
  notes := "Multiple drefs can be introduced and accessed"
  source := "Heim (1982)"
}

-- Part 2: Quantifier Effects

/-- Universal blocks cross-sentential anaphora -/
def universalBlocks : CrossSententialDatum := {
  sentences := ["Every man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "every man"
  felicitous := false
  notes := "Universal doesn't introduce accessible dref"
  source := "Karttunen (1969)"
}

/-- Negative quantifier blocks -/
def negativeBlocks : CrossSententialDatum := {
  sentences := ["No man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "no man"
  felicitous := false
  notes := "Negative quantifier doesn't introduce accessible dref"
  source := "Karttunen (1969)"
}

/-- "Most" blocks? -/
def mostBlocks : CrossSententialDatum := {
  sentences := ["Most men walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "most men"
  felicitous := false
  notes := "Proportional quantifiers also block"
  source := "Heim (1982)"
}

-- Part 3: Scope and Embedding

/-- Indefinite in relative clause -/
def relativeClauseScope : CrossSententialDatum := {
  sentences := ["A man who owns a donkey walked in.", "He beat it."]
  pronounSentenceIdx := 1
  pronoun := "it"
  antecedentSentenceIdx := 0
  antecedent := "a donkey"
  felicitous := true
  notes := "Indefinite in relative clause still introduces accessible dref"
  source := "Groenendijk & Stokhof (1991)"
}

/-- Indefinite under if-clause -/
def conditionalAntecedent : CrossSententialDatum := {
  sentences := ["If a man walks in, he sits down.", "He orders coffee."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "a man"
  felicitous := false
  notes := "Indefinite in if-clause doesn't persist past the conditional"
  source := "Heim (1982)"
}

/-- Indefinite in then-clause -/
def conditionalConsequent : CrossSententialDatum := {
  sentences := ["If it rains, a man will come.", "He will fix the roof."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "a man"
  felicitous := false
  notes := "Indefinite in consequent is hypothetical"
  source := "Heim (1982)"
}

-- Part 4: Negation Effects (Standard vs. Bathroom)

/-- Standard negation blocks -/
def standardNegationBlocks : CrossSententialDatum := {
  sentences := ["John didn't see a bird.", "It was singing."]
  pronounSentenceIdx := 1
  pronoun := "it"
  antecedentSentenceIdx := 0
  antecedent := "a bird"
  felicitous := false
  notes := "Negation typically blocks dref introduction"
  source := "Heim (1982)"
}

/-- Double negation special case -/
def doubleNegation : CrossSententialDatum := {
  sentences := ["It's not the case that John didn't see a bird.", "It was singing."]
  pronounSentenceIdx := 1
  pronoun := "it"
  antecedentSentenceIdx := 0
  antecedent := "a bird"
  felicitous := true
  notes := "Double negation can enable anaphora (relevant for BUS/ICDRT)"
  source := "Elliott & Sudo (2025)"
}

-- Part 5: Definites vs. Indefinites

/-- Definite reference -/
def definiteReference : CrossSententialDatum := {
  sentences := ["The man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "the man"
  felicitous := true
  notes := "Definites also introduce accessible drefs"
  source := "Heim (1982)"
}

/-- Specific indefinite -/
def specificIndefinite : CrossSententialDatum := {
  sentences := ["A certain man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  pronoun := "he"
  antecedentSentenceIdx := 0
  antecedent := "a certain man"
  felicitous := true
  notes := "Specific indefinites introduce drefs"
  source := "Fodor & Sag (1982)"
}

/-- Bare plurals -/
def barePlural : CrossSententialDatum := {
  sentences := ["Dogs were barking.", "They woke me up."]
  pronounSentenceIdx := 1
  pronoun := "they"
  antecedentSentenceIdx := 0
  antecedent := "dogs"
  felicitous := true
  notes := "Bare plurals can introduce drefs"
  source := "Carlson (1977)"
}

-- Part 6: Collected Data

/-- All cross-sentential anaphora examples -/
def allData : List CrossSententialDatum := [
  indefinitePersists,
  multiSentence,
  multipleDrefs,
  universalBlocks,
  negativeBlocks,
  mostBlocks,
  relativeClauseScope,
  conditionalAntecedent,
  conditionalConsequent,
  standardNegationBlocks,
  doubleNegation,
  definiteReference,
  specificIndefinite,
  barePlural
]

/-- Felicitous examples -/
def felicitousExamples : List CrossSententialDatum :=
  allData.filter (·.felicitous)

/-- Infelicitous examples -/
def infelicitousExamples : List CrossSententialDatum :=
  allData.filter (!·.felicitous)

end Phenomena.Anaphora.CrossSententialAnaphora
