/-!
# Combination Schemata

Theory-neutral combination kinds based on HPSG's three immediate dominance
schemata (@cite{pollard-sag-1994}), which @cite{mueller-2013} argues are
universal across Minimalism, CCG, DG, and Construction Grammar.
-/

namespace Core.Interfaces

/-- Mueller's three universal combination schemata.

Every syntactic theory implements these three modes of combination,
though they use different terminology and formalisms. -/
inductive CombinationKind where
  /-- Head combines with its complement (first-merged argument).
      Minimalism: External Merge (first); HPSG: Head-Complement Schema;
      CCG: forward/backward application; DG: core dependency (obj, det,...). -/
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

end Core.Interfaces
