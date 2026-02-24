import Linglib.Theories.Pragmatics.NeoGricean.Presuppositions
import Linglib.Phenomena.Presupposition.Basic

/-!
# Bridge: NeoGricean Presuppositions to Phenomena

Connects the NeoGricean presupposition infrastructure (trigger types, derivation
tracking, SI interaction) to empirical presupposition data from
`Phenomena.Presupposition.Basic`.

Provides example derivations wrapping the King, conditional, and factive verb
examples from Phenomena for NeoGricean SI computation.

## References

- Kracht (2003). Mathematics of Language, Section 4.7
- Heim (1983). On the projection problem for presuppositions
- Karttunen (1974). Presupposition and linguistic context
-/


namespace Phenomena.Presupposition.NeoGriceanBridge

open Core.Presupposition
open NeoGricean.Presuppositions
open Phenomena.Presupposition

/--
Wrap the King example from Phenomena for NeoGricean use.

This creates a PresupDerivation from the theory-neutral King example,
adding trigger information for SI computation.
-/
def kingBaldDerivation : PresupDerivation KingWorld :=
  { meaning := kingBald
  , triggers := [⟨0, .definite⟩]  -- "the" at position 0
  , polarity := .upward
  , surface := ["the", "king", "is", "bald"]
  }

/--
The conditional "If the king exists, the king is bald" as a derivation.

Note: No presupposition triggers project because filtering eliminates them.
-/
def ifKingThenBaldDerivation : PresupDerivation KingWorld :=
  { meaning := ifKingThenBald
  , triggers := []  -- Presupposition filtered out
  , polarity := .upward
  , surface := ["if", "the", "king", "exists", ",", "the", "king", "is", "bald"]
  }

/--
Factive verb example as a derivation.
-/
def johnKnowsRainingDerivation : PresupDerivation RainWorld :=
  { meaning := johnKnowsRaining
  , triggers := [⟨1, .factive⟩]  -- "knows" at position 1
  , polarity := .upward
  , surface := ["John", "knows", "that", "it's", "raining"]
  }

/--
Filtering affects which triggers are relevant for SI.

When a presupposition is filtered (locally satisfied), the corresponding
trigger no longer contributes to global presupposition, and alternatives
involving that trigger may behave differently.
-/
theorem filtering_removes_trigger :
    ifKingThenBaldDerivation.triggers = [] := rfl

end Phenomena.Presupposition.NeoGriceanBridge
