import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.Partition.Lattice
import Linglib.Core.Question.Partition.Cells
import Linglib.Core.Question.Partition.Binary

/-!
# Negative Attributes via Proper Coarsening
@cite{merin-1999}

Epistemic, syntax-independent characterization of negativity:

* `isProperCoarsening q q' elements` — Q coarsens Q' and has strictly fewer
  cells over `elements`.
* `isNegativeAttribute R q elements` — `binaryPartition R` is a proper
  coarsening of `q`.

@cite{merin-1999}: a predicate is negative not because of morphological
form (`un-`, `not`, etc.) but because its yes/no distinction is strictly
coarser than the partition under discussion — answering "does R hold?"
discards information `q` distinguishes.
-/

namespace QUD

variable {M : Type*}

/-- Q is a proper coarsening of Q' over a finite domain iff Q coarsens Q'
and has strictly fewer cells.

@cite{merin-1999} defines negative attributes via proper coarsening:
R is a *negative attribute* with respect to partition F iff for some Q ∈ F,
{R, Q} is a proper coarsening of F. This characterization is purely epistemic
and syntax-independent — negativity is a matter of partition kinetics, not
morphological form. -/
def isProperCoarsening [DecidableEq M] (q q' : QUD M) (elements : List M) : Prop :=
  q.coarsens q' ∧ q.numCells elements < q'.numCells elements

/-- A predicate R is a *negative attribute* with respect to partition Q over
a finite domain iff the binary partition of R is a proper coarsening of Q.

@cite{merin-1999}: negativity is not a syntactic property (presence of "un-",
"not", etc.) but a partition-kinetic one. R is negative relative to Q when
the R/¬R distinction is strictly coarser than Q's partition — answering
whether R holds loses information that Q distinguishes. -/
def isNegativeAttribute [DecidableEq M] (R : M → Bool) (q : QUD M)
    (elements : List M) : Prop :=
  isProperCoarsening (binaryPartition R) q elements

end QUD
