/-
# Determiner-Noun Agreement

## The Phenomenon

In English, certain determiners must agree in number with their head noun.
Singular determiners (a, this, every) require singular nouns.
Plural determiners (these, many, few) require plural nouns.
Some determiners (the, some) are compatible with either.

## The Data

  (1a)  a girl                       ✓  sg det, sg noun
  (1b) *a girls                      ✗  sg det, pl noun

  (2a)  this book                    ✓  sg det, sg noun
  (2b) *this books                   ✗  sg det, pl noun

  (3a)  these books                  ✓  pl det, pl noun
  (3b) *these book                   ✗  pl det, sg noun

  (4a)  many cats                    ✓  pl det, pl noun
  (4b) *many cat                     ✗  pl det, sg noun

  (5a)  the girl                     ✓  neutral det, sg noun
  (5b)  the girls                    ✓  neutral det, pl noun
-/

import Linglib.Core.Basic

namespace Phenomena.Agreement.DetNoun

/-- Determiner-noun agreement data.

Pure empirical data with no theoretical commitments.
Theories interpret this via their Bridge modules. -/
def data : StringPhenomenonData := {
  name := "Determiner-Noun Agreement"
  generalization := "Determiners must agree with their head noun in number"
  pairs := [
    -- Singular determiners with singular/plural nouns
    { grammatical := "a girl"
      ungrammatical := "a girls"
      clauseType := .declarative
      description := "Singular 'a' requires singular noun" },

    { grammatical := "this book"
      ungrammatical := "this books"
      clauseType := .declarative
      description := "Singular 'this' requires singular noun" },

    { grammatical := "every cat"
      ungrammatical := "every cats"
      clauseType := .declarative
      description := "Singular 'every' requires singular noun" },

    -- Plural determiners with singular/plural nouns
    { grammatical := "these books"
      ungrammatical := "these book"
      clauseType := .declarative
      description := "Plural 'these' requires plural noun" },

    { grammatical := "many cats"
      ungrammatical := "many cat"
      clauseType := .declarative
      description := "Plural 'many' requires plural noun" },

    { grammatical := "few dogs"
      ungrammatical := "few dog"
      clauseType := .declarative
      description := "Plural 'few' requires plural noun" }
  ]
}

end Phenomena.Agreement.DetNoun
