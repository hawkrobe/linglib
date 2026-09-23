module

public import Linglib.Semantics.Mood.Defs

/-!
# Temporal connectives

This file defines the lexical entry of a temporal connective, a subordinator or preposition
that locates the time of its host clause relative to the time of its complement: *before*,
*after*, *when*, *while*, *until*, *since*, *by* and *whenever*. An entry records the relation
the word lexicalizes, drawn from the inventory of [heinamaki-1974]; whether it is a punctual
rather than a durative *until*, [karttunen-1974]'s two *until*s, which English leaves to one word
and Greek, Finnish, Dutch and Icelandic lexicalize apart; and the grammatical mood its complement
takes where the language marks one.

An entry carries no truth conditions. What *before* means is contested, from the quantificational
relations of [anscombe-1964] and [heinamaki-1974] to the branching-time analysis of
[beaver-condoravdi-2003] and the scalar one of [rett-2020a], so a study assigns denotations to
the relations it treats and derives veridicality and polarity licensing from them; a fragment says
only which relation a word lexicalizes.

## Main declarations

* `Tense.Connective`: the lexical entry, with its `relation`, `punctual` flag and `mood`.
* `Tense.Connective.Relation`: the eight relations a connective can lexicalize.

## References

* [heinamaki-1974]
* [karttunen-1974]
* [anscombe-1964]
* [beaver-condoravdi-2003]
* [rett-2020a]
-/

@[expose] public section

namespace Tense

/-- The temporal relation a connective lexicalizes, [heinamaki-1974]'s inventory: the host
precedes or follows the complement, the two coincide or the host lies within the complement, the
host persists to or from the complement time, the host is done by it, or the host recurs with the
complement. -/
inductive Connective.Relation where
  | before
  | after
  | when_
  | while_
  | until_
  | since
  | by_
  | whenever
  deriving DecidableEq, Repr

/-- A temporal connective: a subordinator or preposition relating the time of its host clause to
that of its complement. A punctual connective is a lexeme for [karttunen-1974]'s punctual *until*,
which locates an event at the complement time and, in English, needs negation; a durative *until*
marks how long a state or process persists. -/
structure Connective where
  /-- The surface form. -/
  form : String
  /-- The relation the connective lexicalizes. -/
  relation : Connective.Relation
  /-- Whether the connective is a punctual *until*. -/
  punctual : Prop := False
  [decidablePunctual : Decidable punctual]
  /-- The grammatical mood of the complement, where the language marks one. -/
  mood : Option Mood.Grammatical := none

instance (c : Connective) : Decidable c.punctual := c.decidablePunctual

end Tense
