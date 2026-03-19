import Linglib.Core.Discourse.QUD
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin
import Linglib.Theories.Semantics.Questions.Denotation.Partition

/-!
# Inquisitive Semantics Bridge
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{thomas-2026} @cite{roberts-2012}

Bridges between Hamblin/partition question types and the inquisitive
`Discourse.Issue` type (defined in Core/Discourse/QUD.lean).

Core types (`Discourse.InfoState`, `Discourse.Issue`, `Discourse.supports`,
`Discourse.propEntails`) and @cite{roberts-2012} QUD structure
(`Discourse.moveRelevant`, `Discourse.partiallyAnswers`,
`Discourse.questionEntails`) are defined in `Core/Discourse/QUD.lean`.

-/

namespace Semantics.Questions.Inquisitive

open Discourse
open Semantics.Questions

-- Conversion from Other Question Types

/-- Convert a Hamblin question to an Issue.

Hamblin questions denote sets of propositions (possible answers).
Each proposition becomes an alternative (the set of worlds satisfying it). -/
def issueOfHamblin {W : Type*} (h : Hamblin.QuestionDen W)
    (candidateProps : List (W → Bool)) : Issue W :=
  let relevantProps := candidateProps.filter h
  { alternatives := relevantProps }

/-- Convert a G&S partition question to an Issue.

A partition question Q partitions worlds into equivalence classes.
Each equivalence class becomes an alternative. -/
def issueOfPartition {W : Type*} (q : GSQuestion W) (worlds : List W) : Issue W :=
  let cells := q.toCells worlds
  { alternatives := cells }

/-- Partition-derived issues preserve cell count as alternative count. -/
theorem issueOfPartition_preserves_cells {W : Type*} (q : GSQuestion W) (worlds : List W) :
    (issueOfPartition q worlds).numAlternatives = (q.toCells worlds).length := rfl

-- GSQuestion ↔ Issue Bridge

/-- Convert a GSQuestion to an Issue via its partition cells.

This is a convenience method wrapping `issueOfPartition`. The alternatives
of the resulting issue correspond exactly to the cells of the partition. -/
def toIssue {W : Type*} (q : GSQuestion W) (worlds : List W) : Issue W :=
  issueOfPartition q worlds

/-- The alternatives of `toIssue` are exactly the partition cells. -/
theorem toIssue_alternatives {W : Type*} (q : GSQuestion W) (worlds : List W) :
    (toIssue q worlds).alternatives = q.toCells worlds := rfl

end Semantics.Questions.Inquisitive
