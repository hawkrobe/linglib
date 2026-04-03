/-
@cite{franke-2011}. Quantity implicatures, exhaustive interpretation, and
rational conversation. S&P 4(1):1-82.

IBR (iterated best response) converges to exhaustive interpretation (exhMW).

General IBR theory (InterpGame, strategies, convergence) is in
`Theories/Pragmatics/IBR/`. This file contains paper-specific results:
- Facts 1, 3, 4 connecting IBR to the exhaustification literature
- Alternative counting (eq. 107) and the R₁ characterization
- Concrete examples (scalar implicature, free choice disjunction)
-/

import Linglib.Theories.Pragmatics.IBR.Core
import Linglib.Theories.Pragmatics.IBR.ScalarGames

namespace RSA.IBR

open Exhaustification

-- SECTION 1: Alternative Counting (Franke eq. 107)

/-- Number of alternatives (messages) true at state s.
    This is |R⁻¹₀(s)| in Franke's notation. -/
def alternativeCount (G : InterpGame) (s : G.State) : ℕ :=
  (G.trueMessages s).card

/-- A state s is minimal among m-worlds if no m-world has fewer true alternatives.
    This characterizes R₁(m) per equation (107). -/
def isMinimalByAltCount (G : InterpGame) (m : G.Message) (s : G.State) : Prop :=
  G.meaning m s = true ∧
  ∀ s', G.meaning m s' = true → alternativeCount G s ≤ alternativeCount G s'

-- SECTION 2: Fact 1 — R₁ ⊆ ExhMW (Franke Section 10)

/-- **Franke Fact 1 (containment direction)**: Level-1 receiver interpretation
    is contained in minimal-models exhaustification.

    R₁(mₛ) ⊆ ExhMM(S)

    **Proof idea**: If s is selected by R₁ (minimum alternative count),
    then s is minimal with respect to <_ALT because:
    - s' <_ALT s means s' makes strictly fewer alternatives true
    - But R₁ already selected for minimum alternative count
    - So no such s' can exist among m-worlds

    This is the containment direction; equality requires "homogeneity". -/
theorem r1_subset_exhMW (G : InterpGame) (m : G.Message) (s : G.State)
    (h : isMinimalByAltCount G m s) :
    exhMW (toAlternatives G) (prejacent G m) s := by
  constructor
  · exact h.1
  · intro ⟨s', hs'_true, hs'_lt⟩
    have hssubset : G.trueMessages s' ⊂ G.trueMessages s :=
      ltALT_implies_trueMessages_ssubset G s' s hs'_lt
    have hcount : alternativeCount G s' < alternativeCount G s := by
      simp only [alternativeCount]
      exact Finset.card_lt_card hssubset
    have hmin := h.2 s' hs'_true
    omega

-- SECTION 3: Conditions for the Converse (ExhMW ⊆ R₁)

/-- The alternative ordering is **total** on m-worlds if for any two states
where m is true, one's true alternatives are a subset of the other's. -/
def altOrderingTotalOnMessage (G : InterpGame) (m : G.Message) : Prop :=
  ∀ s s', G.meaning m s = true → G.meaning m s' = true →
    (G.trueMessages s ⊆ G.trueMessages s') ∨ (G.trueMessages s' ⊆ G.trueMessages s)

/-- **Converse direction under totality**: ExhMW ⊆ R₁.

When <_ALT is total on m-worlds, minimal in the subset ordering implies
minimum cardinality. -/
theorem exhMW_subset_r1_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m)
    (hmw : exhMW (toAlternatives G) (prejacent G m) s) :
    isMinimalByAltCount G m s := by
  constructor
  · exact hmw.1
  · intro s' hs'_true
    cases hTotal s s' hmw.1 hs'_true with
    | inl hsub =>
      simp only [alternativeCount]
      exact Finset.card_le_card hsub
    | inr hsub' =>
      by_cases heq : G.trueMessages s' = G.trueMessages s
      · simp only [alternativeCount]
        rw [heq]
      · have hss : G.trueMessages s' ⊂ G.trueMessages s :=
          ⟨hsub', λ h => heq (Finset.Subset.antisymm hsub' h)⟩
        exact absurd ⟨s', hs'_true, trueMessages_ssubset_implies_ltALT G s' s hss⟩ hmw.2

/-- **R₁ = ExhMW under totality**: Full equivalence when alternatives form a chain.

This is the precise condition under which Franke's Fact 1 becomes an equality. -/
theorem r1_eq_exhMW_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m) :
    isMinimalByAltCount G m s ↔ exhMW (toAlternatives G) (prejacent G m) s :=
  ⟨r1_subset_exhMW G m s, exhMW_subset_r1_under_totality G m s hTotal⟩

-- SECTION 4: Fact 3 — ExhMW ⊆ ExhIE (Franke Appendix A)

/-- **Franke Fact 3 (Appendix A)**: ExhMW(S, Alt) ⊆ ExhIE(S, Alt)

    This is already proved as `prop6_exhMW_entails_exhIE` in
    Exhaustification/Operators.lean. -/
theorem fact3_exhMW_subset_exhIE (G : InterpGame) (m : G.Message) :
    exhMW (toAlternatives G) (prejacent G m) ⊆ₚ exhIE (toAlternatives G) (prejacent G m) :=
  prop6_exhMW_entails_exhIE (toAlternatives G) (prejacent G m)

-- SECTION 5: Fact 4 — ExhMW = ExhIE under closure (Franke Appendix A)

/-- **Franke Fact 4 (Appendix A)**: ExhMW = ExhIE when Alt is closed under ∧.

    This is proved as `theorem9_main` in Exhaustification/Operators.lean. -/
theorem fact4_exhMW_eq_exhIE_closed (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    exhMW (toAlternatives G) (prejacent G m) ≡ₚ exhIE (toAlternatives G) (prejacent G m) :=
  theorem9_main (toAlternatives G) (prejacent G m) hClosed

-- SECTION 6: Examples

/-!
## Scalar Implicature Example (Franke Section 3.1)

The classic "some" vs "all" example:
- States: {some-not-all, all}
- Messages: {some, all}
- Meaning: some true at both; all true only at all

IBR derivation:
- L₀: "some" → uniform over both states
- S₁ at "all": says "all" (more informative)
- S₁ at "some-not-all": says "some" (only option)
- L₂: "some" → "some-not-all" (scalar implicature!)
-/

/-- States for scalar implicature example -/
inductive ScalarState where
  | someNotAll : ScalarState  -- Some but not all
  | all : ScalarState         -- All
  deriving DecidableEq, Fintype, Repr

/-- Messages for scalar implicature example -/
inductive ScalarMessage where
  | some_ : ScalarMessage
  | all : ScalarMessage
  deriving DecidableEq, Fintype, Repr

/-- Scalar implicature interpretation game -/
def scalarGame : InterpGame where
  State := ScalarState
  Message := ScalarMessage
  meaning := λ m s => match m, s with
    | .some_, _ => true           -- "some" true at both states
    | .all, .all => true          -- "all" true only at all
    | .all, .someNotAll => false
  prior := λ _ => 1 / 2  -- Uniform prior

#guard (L0 scalarGame).respond .some_ .someNotAll == 1/2
#guard (L0 scalarGame).respond .some_ .all == 1/2
#guard (L0 scalarGame).respond .all .all == 1
#guard (L0 scalarGame).respond .all .someNotAll == 0

/-- The scalar implicature game IS a scalar game: truth sets are nested. -/
theorem scalarGame_is_scalar : isScalarGame scalarGame := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;>
    simp [scalarGame, InterpGame.trueStates, Finset.subset_iff, Finset.mem_filter]

/-- The scalar implicature game has distinct truth sets. -/
theorem scalarGame_distinct :
    ∀ m₁ m₂ : scalarGame.Message, scalarGame.trueStates m₁ = scalarGame.trueStates m₂ → m₁ = m₂ := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;> simp [scalarGame, InterpGame.trueStates] <;> decide

/-- The scalar game is an equivalence class game: each message level is a singleton. -/
theorem scalarGame_is_eqclass : isEquivalenceClassGame scalarGame := by
  intro m hNE; cases m <;> native_decide

/-- strongestAt verification: "some" is strongest at someNotAll. -/
example : strongestAt scalarGame .some_ .someNotAll := by
  refine ⟨rfl, fun m' hm' => ?_⟩
  cases m' with
  | some_ => exact Finset.Subset.refl _
  | all => simp [scalarGame] at hm'

/-- strongestAt verification: "all" is strongest at all. -/
example : strongestAt scalarGame .all .all := by
  refine ⟨rfl, fun m' hm' => ?_⟩
  cases m' with
  | some_ =>
    intro s hs
    simp only [scalarGame, InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs ⊢
  | all => exact Finset.Subset.refl _

/-- Negative check: "some" is NOT strongest at "all" — "all" is stronger. -/
example : ¬ strongestAt scalarGame .some_ .all := by
  intro ⟨_, hStr⟩
  have h := hStr .all rfl
  have : ScalarState.someNotAll ∈ scalarGame.trueStates .some_ :=
    scalarGame.mem_trueStates.mpr rfl
  have : ScalarState.someNotAll ∈ scalarGame.trueStates .all := h this
  simp [scalarGame, InterpGame.trueStates, Finset.mem_filter] at this

/-!
## Free Choice Disjunction (Franke Section 3.3)

"You may have cake or ice cream" → You may have either one.

States: {only-A, only-B, either, both}
Messages: {◇A, ◇B, ◇(A∨B), ◇(A∧B)}

The free choice inference emerges from IBR reasoning because:
- At "either" state, speaker uses ◇(A∨B) (most informative true message)
- L₂ infers "either" from ◇(A∨B) (scalar implicature pattern)
-/

/-- States for free choice example -/
inductive FCState where
  | onlyA : FCState    -- May have only A
  | onlyB : FCState    -- May have only B
  | either : FCState   -- May have either (free choice)
  | both : FCState     -- May have both together
  deriving DecidableEq, Fintype, Repr

/-- Messages for free choice example -/
inductive FCMessage where
  | mayA : FCMessage        -- ◇A
  | mayB : FCMessage        -- ◇B
  | mayAorB : FCMessage     -- ◇(A∨B)
  | mayAandB : FCMessage    -- ◇(A∧B)
  deriving DecidableEq, Fintype, Repr

/-- Free choice interpretation game -/
def freeChoiceGame : InterpGame where
  State := FCState
  Message := FCMessage
  meaning := λ m s => match m, s with
    | .mayA, .onlyA => true
    | .mayA, .either => true
    | .mayA, .both => true
    | .mayB, .onlyB => true
    | .mayB, .either => true
    | .mayB, .both => true
    | .mayAorB, _ => true        -- Always true under standard deontic logic
    | .mayAandB, .both => true
    | _, _ => false
  prior := λ _ => 1 / 4  -- Uniform prior

-- L0: ◇(A∨B) true everywhere → uniform over all 4 states
#guard (L0 freeChoiceGame).respond .mayAorB .either == 1/4
-- L2: ◇(A∨B) → "either" (free choice inference emerges from IBR)
#guard (ibrN freeChoiceGame 2).respond .mayAorB .either > 0
#guard (ibrN freeChoiceGame 2).respond .mayAorB .onlyA == 0

end RSA.IBR
