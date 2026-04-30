import Linglib.Theories.Dialogue.KOS.Defs

/-!
# IllocMove ↔ Searle Bridge
@cite{ginzburg-2012} @cite{searle-1979}

Maps KOS's `IllocMove` constructors to @cite{searle-1979}'s five-class
illocutionary taxonomy and to direction-of-fit. Surfaces as:

- `IllocMove.toSearleClass`
- `IllocMove.directionOfFit`
- Class-level coherence theorems: assertives share mind-to-world fit;
  directives share world-to-mind fit; greetings have null fit.

These are pure projections from move constructors to substrate-shared
illocutionary primitives — they do not depend on the dialogue gameboard
machinery.
-/

namespace Dialogue.KOS

/-- Map an illocutionary move to @cite{searle-1979}'s five-class taxonomy.

Assert/accept/confirm are assertives (mind-to-world fit). Ask is a directive
(world-to-mind: the speaker tries to get the addressee to provide information).
Check is a directive (requesting confirmation). Greet/counterGreet are
expressives (null fit). -/
def IllocMove.toSearleClass {Fact QContent : Type} :
    IllocMove Fact QContent → Core.Discourse.SearleClass
  | .assert _   => .assertive
  | .accept _   => .assertive
  | .confirm _  => .assertive
  | .ask _      => .directive
  | .check _    => .directive
  | .greet      => .expressive
  | .counterGreet => .expressive

/-- Direction of fit for an illocutionary move, derived via Searle class. -/
def IllocMove.directionOfFit {Fact QContent : Type}
    (m : IllocMove Fact QContent) : Core.Discourse.DirectionOfFit :=
  m.toSearleClass.directionOfFit

/-- Assertions have mind-to-world fit: the speaker is responsible if p is false. -/
theorem IllocMove.assert_mind_to_world {Fact QContent : Type} (p : Fact) :
    (IllocMove.assert (QContent := QContent) p).directionOfFit = .mindToWorld := rfl

/-- Queries have world-to-mind fit: the speaker wants the addressee to act. -/
theorem IllocMove.ask_world_to_mind {Fact QContent : Type} (q : QContent) :
    (IllocMove.ask (Fact := Fact) q).directionOfFit = .worldToMind := rfl

/-- Greetings have null fit: they express social acknowledgement. -/
theorem IllocMove.greet_null_fit {Fact QContent : Type} :
    (IllocMove.greet : IllocMove Fact QContent).directionOfFit = .null := rfl

/-- All assertive-class moves (assert, accept, confirm) share mind-to-world fit:
the speaker takes responsibility for truth. -/
theorem assertive_moves_mind_to_world {Fact QContent : Type} (p : Fact) :
    (IllocMove.assert (QContent := QContent) p).directionOfFit = .mindToWorld ∧
    (IllocMove.accept (QContent := QContent) p).directionOfFit = .mindToWorld ∧
    (IllocMove.confirm (QContent := QContent) p).directionOfFit = .mindToWorld :=
  ⟨rfl, rfl, rfl⟩

/-- Directive moves (ask, check) share world-to-mind fit:
the speaker wants the addressee to act. -/
theorem directive_moves_world_to_mind {Fact QContent : Type}
    (q : QContent) (p : Fact) :
    (IllocMove.ask (Fact := Fact) q).directionOfFit = .worldToMind ∧
    (IllocMove.check (QContent := QContent) p).directionOfFit = .worldToMind :=
  ⟨rfl, rfl⟩

end Dialogue.KOS
