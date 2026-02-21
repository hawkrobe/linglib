import Linglib.Theories.Semantics.Degree.Wellwood

/-!
# DEPRECATED: Compositional Comparative Derivation (re-export shim)

Content has moved to `Theories.Semantics.Degree.Wellwood`.
This file re-exports for backward compatibility.
-/

-- Re-export the namespace so existing `open Semantics.Lexical.Degree` works
namespace Semantics.Lexical.Degree

open Semantics.Degree.Wellwood

abbrev ComparativeDomain := Semantics.Degree.Wellwood.ComparativeDomain

def comparativeTruth {Entity Time Measured : Type*} [LE Time]
    (role : Entity → Semantics.Events.Ev Time → Prop)
    (P : Semantics.Events.EvPred Time)
    (extract : Semantics.Events.Ev Time → Measured)
    (μ : Measured → ℚ)
    (a b : Entity) : Prop :=
  Semantics.Degree.Wellwood.comparativeTruth role P extract μ a b

end Semantics.Lexical.Degree
