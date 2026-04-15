/-
# Syntax-Semantics Interface

Documents compositional homomorphism requirement and syntax-agnostic nature of Montague semantics.

## Main definitions

`TypeAssignment`, `CompositionalSemantics`, `MontagueSyntax`, `MontagueBenefits`

-/

import Linglib.Core.IntensionalLogic.Frame

namespace Semantics.Montague.Interface.SyntaxInterface

open Core.IntensionalLogic

/-- Type assignment maps syntactic categories to semantic types -/
structure TypeAssignment (SynCat : Type) where
  typeOf : SynCat → Ty

/-- Compositional semantics maps derivations to meanings -/
class CompositionalSemantics (SynCat : Type) (Deriv : Type) where
  types : TypeAssignment SynCat
  frame : Frame
  interp : Deriv → (cat : SynCat) → frame.Denot (types.typeOf cat)

/-- Requirements for a syntax to interface with Montague semantics -/
class MontagueSyntax (SynCat : Type) (Deriv : Type) where
  catOf : Deriv → SynCat
  typeOf : SynCat → Ty
  wellFormed : Deriv → Prop
  interp : (d : Deriv) → (F : Frame) → F.Denot (typeOf (catOf d))

/-- Results that Montague provides to any compatible syntax -/
structure MontagueBenefits (SynCat : Type) (Deriv : Type) [MontagueSyntax SynCat Deriv] where
  trueIn : Deriv → Frame → Bool
  entails : Deriv → Deriv → Frame → Bool

end Semantics.Montague.Interface.SyntaxInterface
