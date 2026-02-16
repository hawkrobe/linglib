import Linglib.Theories.IntensionalSemantics.Attitude.Doxastic
import Linglib.Core.SquareOfOpposition

/-!
# Neg-Raising as O→E Pragmatic Strengthening

Neg-raising is the phenomenon where the negation of an attitude verb is
interpreted as the attitude applied to the negated complement:

  "I don't think it's raining" ≈ "I think it's not raining"
  ¬Bel(p) → Bel(¬p)

In terms of the Square of Opposition, this is strengthening from the
O-corner (¬Bel(p)) to the E-corner (Bel(¬p)). This strengthening is
available precisely because belief and disbelief are **contraries**: one
can neither believe p nor believe ¬p (the "undecided" gap). The pragmatic
inference fills this gap by assuming the agent has a settled opinion.

## The Doxastic Square

```
        contraries
  Bel(p) ────────── Bel(¬p)
    │                  │
    │                  │
    │                  │
  ◇p ──────────────── ¬Bel(p)
       subcontraries
```

- **A** = Bel(p): agent believes p
- **E** = Bel(¬p): agent believes not-p (disbelieves p)
- **I** = ◇p: agent's beliefs are compatible with p
- **O** = ¬Bel(p): agent doesn't believe p

Neg-raising is available for `believe` and `think` (non-veridical: there is
a gap between ¬Bel(p) and Bel(¬p)) but NOT for `know` (veridical: ¬know(p)
includes cases where p is false, so strengthening to know(¬p) would require
¬p to be true, which is a factual claim the speaker may not intend).

## References

- Horn, L. (2001). A Natural History of Negation. §5.2.
- Bartsch, R. (1973). "Negative Transportation" gibt es nicht.
- Gajewski, J. (2007). Neg-raising and polarity.
-/

namespace IntensionalSemantics.Attitude.NegRaising

open Core.Proposition (BProp)
open Core.SquareOfOpposition (Square SquareRelations)
open IntensionalSemantics.Attitude.Doxastic
  (DoxasticPredicate Veridicality boxAt diaAt AccessRel)

-- ============================================================================
-- §1 The Doxastic Square
-- ============================================================================

/-- The doxastic square for a belief predicate.

Given an accessibility relation, agent, and proposition, produce the four
corners of the doxastic square of opposition:
- A = Bel(p): all doxastic alternatives satisfy p
- E = Bel(¬p): all doxastic alternatives satisfy ¬p
- I = ◇p: some doxastic alternative satisfies p
- O = ¬Bel(p): not all doxastic alternatives satisfy p -/
def doxasticSquare {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Bool) : Square (W → Bool) where
  A := λ w => boxAt R agent w worlds p
  E := λ w => boxAt R agent w worlds (λ w' => !p w')
  I := λ w => diaAt R agent w worlds p
  O := λ w => !(boxAt R agent w worlds p)

/-- The doxastic square satisfies the A–O contradiction diagonal. -/
theorem doxasticSquare_contradAO {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Bool) (w : W) :
    (doxasticSquare R agent worlds p).A w =
    !(doxasticSquare R agent worlds p).O w := by
  simp [doxasticSquare, Bool.not_not]

/-- The doxastic square satisfies the E–I contradiction diagonal.

This requires that `diaAt` is the dual of `boxAt`: ◇p = ¬□¬p.
We prove this from the definitions. -/
theorem doxasticSquare_contradEI {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Bool) (w : W) :
    (doxasticSquare R agent worlds p).E w =
    !(doxasticSquare R agent worlds p).I w := by
  simp only [doxasticSquare, boxAt, diaAt]
  -- Goal: (worlds.all f) = !(worlds.any g) where f w' = !R || !p, g w' = R && p
  -- This is list-level De Morgan: all(¬·) = ¬any(·)
  induction worlds with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, ih]
    cases R agent w hd <;> cases p hd <;> rfl

-- ============================================================================
-- §2 Neg-Raising Predicates
-- ============================================================================

/-- A neg-raising predicate is a doxastic predicate whose negation is
pragmatically strengthened from O (¬Bel(p)) to E (Bel(¬p)).

The `negRaises` field indicates whether the predicate supports this
inference. Structurally, neg-raising is available when the predicate
is non-veridical (belief, not knowledge). -/
structure NegRaisingPredicate (W E : Type*) extends DoxasticPredicate W E where
  /-- Whether negation of this predicate raises into the complement. -/
  negRaises : Bool

/-- Neg-raising is the pragmatic inference from O to E:
¬V(p) is strengthened to V(¬p).

This is the "excluded middle of belief": when a speaker says "I don't
think p", they implicate they have a settled opinion, namely Bel(¬p). -/
def negRaisesAt {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Bool) (w : W) : Prop :=
  boxAt R agent w worlds p = false →
  boxAt R agent w worlds (λ w' => !p w') = true

/-- Neg-raising is available exactly when the predicate admits a gap
between ¬Bel(p) and Bel(¬p) — i.e., when the O→E strengthening is
a genuine pragmatic move (not a semantic entailment).

For non-veridical predicates, ¬Bel(p) does NOT semantically entail
Bel(¬p) — there is a gap (the agent might be undecided). Neg-raising
fills this gap pragmatically.

For veridical predicates (know), ¬know(p) could mean either:
(a) p is true but agent doesn't know it, or
(b) p is false
Strengthening to know(¬p) would require (b), which is a factual
claim beyond pragmatic strengthening. -/
def negRaisingAvailable (v : Veridicality) : Bool :=
  match v with
  | .nonVeridical => true   -- believe, think: gap exists
  | .veridical => false     -- know: no neg-raising

-- ============================================================================
-- §3 Standard Predicate Classifications
-- ============================================================================

/-- "believe" supports neg-raising.
"I don't believe it's raining" ≈ "I believe it's not raining". -/
def believeNR {W E : Type*} (R : AccessRel W E) : NegRaisingPredicate W E :=
  { toDoxasticPredicate := Doxastic.believeTemplate R
    negRaises := true }

/-- "think" supports neg-raising.
"I don't think it's raining" ≈ "I think it's not raining". -/
def thinkNR {W E : Type*} (R : AccessRel W E) : NegRaisingPredicate W E :=
  { toDoxasticPredicate := Doxastic.thinkTemplate R
    negRaises := true }

/-- "know" does NOT support neg-raising.
"I don't know it's raining" ≠ "I know it's not raining". -/
def knowNR {W E : Type*} (R : AccessRel W E) : NegRaisingPredicate W E :=
  { toDoxasticPredicate := Doxastic.knowTemplate R
    negRaises := false }

-- ============================================================================
-- §4 Theorems
-- ============================================================================

/-- Neg-raising availability aligns with non-veridicality. -/
theorem negRaising_iff_nonVeridical (v : Veridicality) :
    negRaisingAvailable v = true ↔ v = .nonVeridical := by
  cases v <;> simp [negRaisingAvailable]

/-- "believe" is classified as neg-raising. -/
theorem believe_negRaises {W E : Type*} (R : AccessRel W E) :
    (believeNR R : NegRaisingPredicate W E).negRaises = true := rfl

/-- "think" is classified as neg-raising. -/
theorem think_negRaises {W E : Type*} (R : AccessRel W E) :
    (thinkNR R : NegRaisingPredicate W E).negRaises = true := rfl

/-- "know" is NOT classified as neg-raising. -/
theorem know_not_negRaises {W E : Type*} (R : AccessRel W E) :
    (knowNR R : NegRaisingPredicate W E).negRaises = false := rfl

/-- Neg-raising predicates are non-veridical. -/
theorem negRaising_implies_nonVeridical {W E : Type*}
    (V : NegRaisingPredicate W E) (hNR : V.negRaises = true)
    (hAlign : V.negRaises = negRaisingAvailable V.veridicality) :
    V.veridicality = .nonVeridical := by
  rw [hNR] at hAlign
  exact (negRaising_iff_nonVeridical V.veridicality).mp hAlign.symm

/-- The doxastic square for "believe" satisfies the contradiction diagonals. -/
theorem believe_square_contradictions {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Bool) (w : W) :
    (doxasticSquare R agent worlds p).A w =
      !(doxasticSquare R agent worlds p).O w ∧
    (doxasticSquare R agent worlds p).E w =
      !(doxasticSquare R agent worlds p).I w :=
  ⟨doxasticSquare_contradAO R agent worlds p w,
   doxasticSquare_contradEI R agent worlds p w⟩

end IntensionalSemantics.Attitude.NegRaising
