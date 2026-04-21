import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.Basic
import Linglib.Core.Question.Granularity
import Linglib.Core.Mood.PartitionAsInquiry

/-!
# Inquisitive Semantics Bridge — `QUD → Core.Question` via Setoid embedding
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{thomas-2026} @cite{roberts-2012}

A `QUD` partitions a meaning space via an equivalence relation. Through
`QUD.toSetoid` and `Core.Question.fromSetoid` (the
`Setoid → Question` embedding from `Core/Mood/PartitionAsInquiry.lean`),
every QUD induces an inquisitive content whose alternatives are exactly
the QUD's equivalence classes.

This bridge is one-way: not every `Core.Question` arises from a `QUD`
(mention-some, intermediate-exhaustive, and conditional-question
alternatives are non-disjoint or non-exhaustive and so are not
representable as the cells of any equivalence relation —
@cite{theiler-etal-2018}).
-/

namespace Semantics.Questions.Inquisitive

universe u

/-- Convert a QUD to a `Core.Question` via its induced equivalence relation.
    The alternatives of the resulting issue are exactly the
    `q.toSetoid`-equivalence classes (the QUD's partition cells). -/
def toIssue {W : Type u} (q : QUD W) : Core.Question W :=
  Core.Question.fromSetoid q.toSetoid

end Semantics.Questions.Inquisitive
