import Linglib.Semantics.Mood.IllocutionaryMood

/-!
# Discourse Move
@cite{roberts-2023} @cite{lewis-1979}

An illocutionary move: speaker performs `mood F(p)` for some content `p`,
addressed to an interlocutor, possibly accepted.

@cite{roberts-2023} §2.1.1: M is the set of moves on the scoreboard, with
distinguished subsets A (assertions), Q (questions), D (directions),
Acc (accepted).

## Main definitions

* `Move W` — ⟨mood, content, agent, accepted⟩.
-/

namespace Discourse

open Semantics.Mood (IllocutionaryMood)

/-- An illocutionary move: a speech act performed by an agent. -/
structure Move (W : Type*) where
  /-- Which kind of speech act. -/
  mood : IllocutionaryMood
  /-- Propositional content (for assertions and questions; for directions,
      the propositional closure of the targeted property). -/
  content : W → Prop
  /-- Who made the move (agent index into interlocutors). -/
  agent : Nat
  /-- Whether this move has been accepted by the interlocutors. -/
  accepted : Prop := False
  deriving Inhabited

end Discourse
