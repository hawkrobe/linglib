/-
# Syntax-Semantics Interface

Documents compositional homomorphism requirement and syntax-agnostic nature of Montague semantics.

## Main definitions

`TypeAssignment`, `CompositionalSemantics`, `MontagueSyntax`, `MontagueBenefits`

## References

Montague (1973)
-/

import Linglib.Theories.Semantics.Compositional.Basic

namespace TruthConditional.Interface.SyntaxInterface

open TruthConditional

/-- Type assignment maps syntactic categories to semantic types -/
structure TypeAssignment (SynCat : Type) where
  typeOf : SynCat → Ty

/-- Compositional semantics maps derivations to meanings -/
class CompositionalSemantics (SynCat : Type) (Deriv : Type) where
  types : TypeAssignment SynCat
  model : Model
  interp : Deriv → (cat : SynCat) → model.interpTy (types.typeOf cat)

/-- Requirements for a syntax to interface with Montague semantics -/
class MontagueSyntax (SynCat : Type) (Deriv : Type) where
  catOf : Deriv → SynCat
  typeOf : SynCat → Ty
  wellFormed : Deriv → Prop
  interp : (d : Deriv) → (m : Model) → m.interpTy (typeOf (catOf d))

/-- Results that Montague provides to any compatible syntax -/
structure MontagueBenefits (SynCat : Type) (Deriv : Type) [MontagueSyntax SynCat Deriv] where
  trueIn : Deriv → Model → Bool
  entails : Deriv → Deriv → Model → Bool

end TruthConditional.Interface.SyntaxInterface

-- Backward compatibility alias
namespace TruthConditional.SyntaxInterface
  export TruthConditional.Interface.SyntaxInterface (TypeAssignment CompositionalSemantics MontagueSyntax MontagueBenefits)
end TruthConditional.SyntaxInterface
