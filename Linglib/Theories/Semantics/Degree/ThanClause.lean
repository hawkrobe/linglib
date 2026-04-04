import Linglib.Core.Scales.Extent
import Linglib.Theories.Semantics.Degree.Core

/-!
# Than-Clause Semantics
@cite{bhatt-pancheva-2004} @cite{heim-2006} @cite{von-stechow-1984}

Compositional semantics for the than-clause in comparative constructions.
The than-clause introduces the standard of comparison and determines
the degree set against which the matrix predicate is evaluated.

## Key Issues

1. **Max operator**: the than-clause denotes a degree set, and the
   comparative requires its maximum (`max(than-clause)`) to compare
   against the matrix degree.

2. **Phrasal vs. clausal**: phrasal "than Bill" vs. clausal "than Bill
   is tall" — the clausal than-clause makes the degree abstraction explicit.

3. **Scope**: the than-clause interacts with scope-taking elements
   (quantifiers, modals, negation).

-/

namespace Semantics.Degree.ThanClause

-- ════════════════════════════════════════════════════
-- § 1. Than-Clause Denotation
-- ════════════════════════════════════════════════════

/-- A than-clause denotes a degree predicate: the set of degrees
    that the standard entity has.

    "than Bill is tall" → λd. height(Bill) ≥ d = {d | d ≤ height(Bill)}

    This is a downward-closed set (initial segment) when the predicate
    is a positive adjective. -/
def thanClauseDenotation {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (standard : Entity) : Set D :=
  { d | d ≤ μ standard }

-- ════════════════════════════════════════════════════
-- § 2. Maximum of Than-Clause
-- ════════════════════════════════════════════════════

/-- The maximum of a than-clause denotation is the degree of the
    standard entity: max({d | d ≤ μ(b)}) = μ(b). -/
def thanClauseMax {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (standard : Entity) : D :=
  μ standard

/-- μ(b) is the greatest element of the than-clause denotation.
    This is `isGreatest_Iic` specialized to degree semantics: the
    maximum of {d | d ≤ μ(b)} is μ(b). -/
theorem thanClauseMax_isGreatest {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (b : Entity) :
    IsGreatest (thanClauseDenotation μ b) (thanClauseMax μ b) :=
  isGreatest_Iic

-- ════════════════════════════════════════════════════
-- § 3. Phrasal vs. Clausal Standards
-- ════════════════════════════════════════════════════

/-- The two syntactic forms of than-clauses. -/
inductive ThanClauseType where
  | phrasal   -- "than Bill" — DP complement
  | clausal   -- "than Bill is tall" — CP complement
  deriving DecidableEq, Repr

/-- Phrasal and clausal than-clauses yield the same degree when the
    elided material is the same predicate. "taller than Bill" and
    "taller than Bill is tall" have the same truth conditions. -/
theorem phrasal_clausal_equivalence {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (b : Entity) :
    thanClauseMax μ b = μ b :=
  rfl

-- ════════════════════════════════════════════════════
-- § 4. Bridge to Extent Functions
-- ════════════════════════════════════════════════════

/-- The than-clause denotation is the positive extent of the standard
    entity — the same algebraic object that Kennedy calls "degree set"
    and Schwarzschild calls "positive interval". -/
theorem thanClause_eq_posExt {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (b : Entity) :
    thanClauseDenotation μ b = Core.Scale.posExt μ b :=
  rfl

end Semantics.Degree.ThanClause
