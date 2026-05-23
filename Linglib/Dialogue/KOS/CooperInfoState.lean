import Linglib.Dialogue.KOS.Defs
import Linglib.Semantics.TypeTheoretic.Discourse

/-!
# KOS-TIS ↔ Cooper-2023-InfoState Genealogy
@cite{ginzburg-2012} @cite{cooper-2023}

A genuine cross-framework bridge: @cite{cooper-2023}'s `InfoState` (§2.6)
is a simplified successor to @cite{ginzburg-2012}'s `TIS`. The
projection `tisToInfoState` makes the simplification explicit by
forgetting QUD, Pending, and genre information.

This is *not* a TTR-typed instantiation file — that's the sibling
`KOS/Austinian.lean`. This file is anchored on the *post-2012*
framework comparison: a chronologically-later author (Cooper 2023)
proposing a slimmed-down successor to a chronologically-earlier
formalism (Ginzburg 2012). The projection witnesses that Cooper's
representation is recoverable from Ginzburg's by quotient.

## Correspondence (`tisToInfoState`)

| TIS (Ginzburg 2012)     | InfoState (Cooper 2023) |
|-------------------------|-------------------------|
| `priv.agenda`           | `agenda`                |
| `dgb.moves.getLast?`    | `latestUtterance`       |
| `dgb.facts`             | `commitments`           |
| `dgb.qud`               | *(not represented)*     |
| `dgb.pending`           | *(not represented)*     |
| `priv.genre`            | *(not represented)*     |

The deletions are exactly what @cite{cooper-2023} drops to make TTR
dialogue tractable for incremental processing.
-/

namespace Dialogue.KOS.CooperInfoState

open Semantics.TypeTheoretic (InfoState)

/-- Project a TIS to a Cooper-style InfoState.

The projection loses QUD, Pending, and genre information — these are
the components that @cite{ginzburg-2012} adds beyond @cite{cooper-2023}. -/
def tisToInfoState {P QContent : Type*} {Fact Cont SignT : Type}
    (tis : TIS P Fact QContent Cont)
    (moveToSign : IllocMove Fact QContent → SignT) :
    InfoState SignT (List Fact) where
  agenda := tis.priv.agenda.map moveToSign
  latestUtterance := tis.dgb.latestMove.map moveToSign
  commitments := tis.dgb.facts

/-- The projection preserves commitments (= FACTS). -/
theorem tisToInfoState_commitments {P QContent : Type*} {Fact Cont SignT : Type}
    (tis : TIS P Fact QContent Cont) (f : IllocMove Fact QContent → SignT) :
    (tisToInfoState tis f).commitments = tis.dgb.facts := rfl

/-- The projection preserves the agenda map. -/
theorem tisToInfoState_agenda {P QContent : Type*} {Fact Cont SignT : Type}
    (tis : TIS P Fact QContent Cont) (f : IllocMove Fact QContent → SignT) :
    (tisToInfoState tis f).agenda = tis.priv.agenda.map f := rfl

/-- The projection preserves the latest utterance. -/
theorem tisToInfoState_latest {P QContent : Type*} {Fact Cont SignT : Type}
    (tis : TIS P Fact QContent Cont) (f : IllocMove Fact QContent → SignT) :
    (tisToInfoState tis f).latestUtterance = tis.dgb.latestMove.map f := rfl

end Dialogue.KOS.CooperInfoState
