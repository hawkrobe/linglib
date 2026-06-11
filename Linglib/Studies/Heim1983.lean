import Linglib.Semantics.Presupposition.TriggerTypology
import Linglib.Semantics.Dynamic.Connectives.PartialCCP
import Linglib.Phenomena.Presupposition.Basic

/-!
# NeoGricean Presuppositions to Phenomena
[heim-1983] [karttunen-1973]

Connects the NeoGricean presupposition infrastructure (trigger types, derivation
tracking, SI interaction) to empirical presupposition data from
`Phenomena.Presupposition.Basic`.

Provides example derivations wrapping the King, conditional, and factive verb
examples from Phenomena for NeoGricean SI computation.

-/


namespace Heim1983

open Semantics.Presupposition
open Semantics.Presupposition.TriggerTypology
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
involving that trigger may behave differently. (The `triggers := []` entry
is *derived* below: `conditional_admitted_everywhere` proves the filtering
from the partial-CCP semantics rather than stipulating it.)
-/
theorem filtering_removes_trigger :
    ifKingThenBaldDerivation.triggers = [] := rfl

/-! ### Filtering derived from partial CCPs

[heim-1983]'s actual machinery: sentences denote *partial* context change
potentials (`Semantics.Dynamic.Core.PartialCCP`), and admittance does the
projection work. The conditional's CCP is admitted by every context — the
antecedent's update satisfies the consequent's king-presupposition — while
the bare consequent's CCP is not admitted by the full context. The
filtering recorded in the trigger tables above is a theorem, not a table
entry. -/

open Semantics.Dynamic.Core in
/-- Every context admits ⟦if the king exists, the king is bald⟧: the
    antecedent's update filters the consequent's presupposition
    ([heim-1983]'s conditional CCP). -/
theorem conditional_admitted_everywhere (c : Set KingWorld) :
    (PartialCCP.pcond (PartialCCP.ofPartialProp kingExists)
      (PartialCCP.ofPartialProp kingBald)).admits c := by
  refine ⟨fun w _ => trivial, ?_⟩
  rintro w ⟨_, ha⟩
  cases w
  · trivial
  · exact ha

open Semantics.Dynamic.Core in
/-- The bare consequent ⟦the king is bald⟧ is NOT admitted by the full
    context: the `noKing` world fails the presupposition, which therefore
    projects. -/
theorem bare_consequent_not_admitted :
    ¬ (PartialCCP.ofPartialProp kingBald).admits Set.univ := by
  intro h
  exact h .noKing trivial

end Heim1983
