import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Dynamic.Partial

/-!
# Heim (1983): Projection and Partial Context Change
[heim-1983] [karttunen-1973]

The classic King and factive-verb examples, their `PartialProp` denotations,
and the filtering predictions derived from partial context change potentials.

## Main declarations

- `kingExists`, `kingBald`, `ifKingThenBald`: the King example, with
  `ifKingThenBald_no_presup` showing conditional filtering.
- `johnKnowsRaining`: the factive example.
- `conditional_admitted_everywhere` / `bare_consequent_not_admitted`:
  conditional filtering derived from `CCP.Partial` admittance rather than
  stipulated.
-/


namespace Heim1983

open Semantics.Presupposition

/--
World type for the king example.

Two possible states:
- kingExists: There is a (unique) king in this world
- noKing: There is no king in this world
-/
inductive KingWorld where
  | kingExists : KingWorld
  | noKing : KingWorld
  deriving DecidableEq, Repr, Inhabited

/--
"The king exists" — a presuppositionless assertion.

This sentence has:
- No presupposition (trivially true)
- Assertion: the king exists
-/
def kingExists : PartialProp KingWorld :=
  { presup := λ _ => True
  , assertion := λ w => match w with
      | .kingExists => True
      | .noKing => False
  }

/--
"The king is bald" — presupposes king exists.

This sentence has:
- Presupposition: the king exists
- Assertion: the king is bald (true when king exists)
-/
def kingBald : PartialProp KingWorld :=
  { presup := λ w => match w with
      | .kingExists => True
      | .noKing => False
  , assertion := λ _ => True
  }

/--
"If the king exists, the king is bald" — using filtering implication.

Demonstrates presupposition filtering: the antecedent's assertion
satisfies the consequent's presupposition.
-/
def ifKingThenBald : PartialProp KingWorld :=
  PartialProp.impFilter kingExists kingBald

/--
"If the king exists, the king is bald" has no presupposition.

This demonstrates presupposition filtering.
-/
theorem ifKingThenBald_no_presup : ifKingThenBald.presup = λ _ => True := by
  funext w
  simp only [ifKingThenBald, PartialProp.impFilter, kingExists, kingBald]
  cases w <;> simp

/--
World type for factive verb examples.

Models whether it's raining and whether John believes it.
-/
inductive RainWorld where
  | rainingBelieved    -- It's raining and John believes it
  | rainingNotBelieved -- It's raining but John doesn't believe it
  | notRaining         -- It's not raining
  deriving DecidableEq, Repr, Inhabited

/--
"John knows that it's raining" — factive presupposition.

Presupposes: it's raining
Asserts: John believes it's raining
-/
def johnKnowsRaining : PartialProp RainWorld :=
  { presup := λ w => match w with
      | .rainingBelieved => True
      | .rainingNotBelieved => True
      | .notRaining => False
  , assertion := λ w => match w with
      | .rainingBelieved => True
      | .rainingNotBelieved => False
      | .notRaining => False
  }

/-! ### Filtering derived from partial CCPs

[heim-1983]'s actual machinery: sentences denote *partial* context change
potentials (`DynamicSemantics.CCP.Partial`), and admittance does the
projection work. The conditional's CCP is admitted by every context — the
antecedent's update satisfies the consequent's king-presupposition — while
the bare consequent's CCP is not admitted by the full context. -/

open DynamicSemantics in
/-- Every context admits ⟦if the king exists, the king is bald⟧: the
    antecedent's update filters the consequent's presupposition
    ([heim-1983]'s conditional CCP). -/
theorem conditional_admitted_everywhere (c : Set KingWorld) :
    (CCP.Partial.cond (CCP.Partial.ofPartialProp kingExists)
      (CCP.Partial.ofPartialProp kingBald)).admits c := by
  refine ⟨fun w _ => trivial, ?_⟩
  rintro w ⟨_, ha⟩
  cases w
  · trivial
  · exact ha

open DynamicSemantics in
/-- The bare consequent ⟦the king is bald⟧ is NOT admitted by the full
    context: the `noKing` world fails the presupposition, which therefore
    projects. -/
theorem bare_consequent_not_admitted :
    ¬ (CCP.Partial.ofPartialProp kingBald).admits Set.univ := by
  intro h
  exact h (Set.mem_univ .noKing)

end Heim1983
