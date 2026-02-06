import Linglib.Core.Basic

/-!
# Combination Schema Interface

Theory-neutral interface for Müller's (2013) three universal combination schemata.

All syntactic theories (Minimalism, HPSG, CCG, CxG, DG) converge on three
fundamental modes of combination:

| Schema | Minimalism | HPSG | CCG | DG |
|--------|-----------|------|-----|-----|
| Head-Complement | Ext Merge (1st) | Head-Comp | fapp/bapp | obj/det/... dep |
| Head-Specifier | Ext Merge (later) | Head-Subj | T+bapp | subj dep |
| Head-Filler | Int Merge | Head-Filler | fcomp/bcomp | non-proj dep |

## Reference

Müller, S. (2013). Unifying Everything: Some Remarks on Simpler Syntax,
Construction Grammar, Minimalism, and HPSG. Language, 89(4), 920–950.
-/

namespace Core.Interfaces

/-- Müller's three universal combination schemata (§2).

Every syntactic theory implements these three modes of combination,
though they use different terminology and formalisms. -/
inductive CombinationKind where
  /-- Head combines with its complement (first-merged argument).
      Minimalism: External Merge (first); HPSG: Head-Complement Schema;
      CCG: forward/backward application; DG: core dependency (obj, det, ...). -/
  | headComplement
  /-- Head combines with its specifier (later-merged argument).
      Minimalism: External Merge (later); HPSG: Head-Subject Schema;
      CCG: type-raise + backward app; DG: subject dependency. -/
  | headSpecifier
  /-- Filler combines with a gapped structure (long-distance dependency).
      Minimalism: Internal Merge; HPSG: Head-Filler Schema;
      CCG: forward/backward composition; DG: non-projective dependency. -/
  | headFiller
  deriving Repr, DecidableEq, BEq

/-- Core convergence: a theory provides three combination schemata.

This is the minimal interface for Müller's convergence claim.
`T` is a theory tag type (e.g., `Minimalism`, `HPSG`).
`Expr` is the theory's expression type (e.g., `SyntacticObject`, `Sign`). -/
class HasCombinationSchemata (T : Type) where
  /-- The expression type for this theory -/
  Expr : Type
  /-- Classify a combination of head + nonHead → result as one of the three schemata -/
  classify : Expr → Expr → Expr → Option CombinationKind
  /-- Get the category of an expression (if available) -/
  catOf : Expr → Option UD.UPOS

/-- Müller's labeling claim (§2.1): the head determines the category of the result.

This is the Head Feature Principle: in any combination, the category
of the resulting phrase equals the category of the head daughter. -/
class HasHeadFeaturePrinciple (T : Type) extends HasCombinationSchemata T where
  /-- The head's category determines the result's category -/
  headDeterminesLabel : ∀ head nonHead result,
    classify head nonHead result ≠ none →
    catOf result = catOf head

/-- Coordination diagnostic (§2.2): same category required.

Coordination is a diagnostic for constituency: only expressions of the
same category can coordinate. This holds across all theories. -/
class HasCoordination (T : Type) extends HasCombinationSchemata T where
  /-- Whether two expressions can coordinate -/
  canCoordinate : Expr → Expr → Bool

end Core.Interfaces
