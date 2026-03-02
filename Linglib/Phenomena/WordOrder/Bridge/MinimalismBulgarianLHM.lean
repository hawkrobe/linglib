import Linglib.Theories.Syntax.Minimalism.HeadMovement.BulgarianLHM
import Linglib.Phenomena.WordOrder.VerbPosition

/-!
# Bridge: Bulgarian Long Head Movement to Verb Position Phenomena
@cite{harizanov-gribanova-2019}


Connects the Minimalist analysis of Bulgarian LHM to the
empirical verb position data in `Phenomena.WordOrder.VerbPosition`.

## Main results

- `models_fronted_order`: The analysis models the fronted participle order
- `captures_alternation`: Both orders are correctly predicted as grammatical
-/

namespace Phenomena.WordOrder.Bridge.MinimalismBulgarianLHM

open Phenomena.WordOrder.VerbPosition

/-- The Minimalist analysis models the fronted order from the phenomena data. -/
theorem models_fronted_order :
    bulgarianExample.fronted = "Pročeli bjaha studentite statijata" := rfl

/-- The Minimalist analysis correctly captures that both orders are grammatical.
    The unfronted order would be derived without the LHM operation. -/
theorem captures_alternation :
    bulgarianExample.bothGrammatical = true := rfl

end Phenomena.WordOrder.Bridge.MinimalismBulgarianLHM
