import Linglib.Core.QUD.Basic
import Linglib.Core.Issue.Basic
import Linglib.Core.Issue.Granularity
import Linglib.Core.Mood.PartitionAsInquiry

/-!
# Inquisitive Semantics Bridge — `QUD → Core.Issue` via Setoid embedding
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{thomas-2026} @cite{roberts-2012}

A `QUD` partitions a meaning space via an equivalence relation. Through
`QUD.toSetoid` and `Core.Issue.fromSetoid` (the
`Setoid → Issue` embedding from `Core/Mood/PartitionAsInquiry.lean`),
every QUD induces an inquisitive content whose alternatives are exactly
the QUD's equivalence classes.

This bridge is one-way: not every `Core.Issue` arises from a `QUD`
(mention-some, intermediate-exhaustive, and conditional-question
alternatives are non-disjoint or non-exhaustive and so are not
representable as the cells of any equivalence relation —
@cite{theiler-etal-2018}).
-/

namespace Semantics.Questions.Inquisitive

universe u

/-- Convert a QUD to a `Core.Issue` via its induced equivalence relation.
    The alternatives of the resulting issue are exactly the
    `q.toSetoid`-equivalence classes (the QUD's partition cells). -/
def toIssue {W : Type u} (q : QUD W) : Core.Issue W :=
  Core.Issue.fromSetoid q.toSetoid

end Semantics.Questions.Inquisitive
