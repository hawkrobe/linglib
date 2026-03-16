/-!
# Combination Schemata

Three universal combination schemata shared across syntactic theories.
@cite{mueller-2013} argues that Minimalism, HPSG, CCG, DG, and Construction
Grammar converge on these three modes of binary combination, though with
different terminology and formalisms. Abstracted from HPSG's immediate
dominance schemata (@cite{pollard-sag-1994}).
-/

namespace Core

/-- Three universal combination schemata shared across syntactic theories.

@cite{mueller-2013} argues that every syntactic theory implements these
three modes of combination, though with different terminology. -/
inductive CombinationKind where
  /-- Head combines with its complement (selected argument).
      Minimalism: External Merge (with selection); HPSG: Head-Complement Schema;
      CCG: forward/backward application; DG: core dependency (obj, det,...). -/
  | headComplement
  /-- Head combines with its specifier (non-selected argument).
      Minimalism: External Merge (without selection); HPSG: Head-Subject Schema;
      CCG: backward application (subject may be type-raised);
      DG: subject dependency. -/
  | headSpecifier
  /-- Filler combines with a gapped structure (long-distance dependency).
      Minimalism: Internal Merge; HPSG: Head-Filler Schema;
      CCG: harmonic composition (primarily; composition also serves other
      functions like heavy NP shift); DG: non-projective dependency. -/
  | headFiller
  deriving Repr, DecidableEq, BEq

end Core
