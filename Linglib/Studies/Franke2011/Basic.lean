import Mathlib.Tactic.DeriveFintype
import Linglib.Studies.Franke2011.ScalarGames

/-!
# Franke 2011: Quantity implicatures and rational conversation

[franke-2011], S&P 4(1): IBR (iterated best response) converges to exhaustive
interpretation (exhMW; the paper writes ExhMM).

The IBR machinery (`IBR.lean`, `ScalarGames.lean`, `Convergence.lean`,
`RSABridge.lean`) lives in this paper's directory over the shared
`InterpGame` carrier. This file contains the exhaustification facts and
worked examples:
- Facts 1, 3, 4 connecting IBR to the exhaustification literature
- Alternative counting (eq. (107)) and the R₁ characterization
- Concrete examples (scalar implicature, free choice disjunction)
-/

namespace Franke2011

open Exhaustification

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq M] (G : InterpGame T M)

/-! ### Alternative counting ([franke-2011] eq. (107)) -/

/-- Number of alternatives (messages) true at state s.
    This is |R⁻¹₀(s)| in Franke's notation. -/
def alternativeCount (s : T) : ℕ :=
  (G.trueMessages s).card

/-- A state s is minimal among m-worlds if no m-world has fewer true alternatives.
    This characterizes R₁(m) per equation (107). -/
def isMinimalByAltCount (m : M) (s : T) : Prop :=
  G.meaning m s ∧
  ∀ s', G.meaning m s' → alternativeCount G s ≤ alternativeCount G s'

/-! ### Fact 1: R₁ ⊆ ExhMW ([franke-2011] §10) -/

omit [Fintype T] [DecidableEq M] in
/-- **Franke Fact 1 (containment direction)**: Level-1 receiver interpretation
    is contained in minimal-models exhaustification.

    R₁(mₛ) ⊆ ExhMM(S)

    **Proof idea**: If s is selected by R₁ (minimum alternative count),
    then s is minimal with respect to <_ALT because:
    - s' <_ALT s means s' makes strictly fewer alternatives true
    - But R₁ already selected for minimum alternative count
    - So no such s' can exist among m-worlds

    This is the containment direction; equality requires "homogeneity". -/
theorem r1_subset_exhMW (m : M) (s : T)
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

/-! ### Conditions for the converse (ExhMW ⊆ R₁) -/

/-- The alternative ordering is **total** on m-worlds if for any two states
where m is true, one's true alternatives are a subset of the other's. -/
def altOrderingTotalOnMessage (m : M) : Prop :=
  ∀ s s', G.meaning m s → G.meaning m s' →
    (G.trueMessages s ⊆ G.trueMessages s') ∨ (G.trueMessages s' ⊆ G.trueMessages s)

omit [Fintype T] in
/-- **Converse direction under totality**: ExhMW ⊆ R₁.

When <_ALT is total on m-worlds, minimal in the subset ordering implies
minimum cardinality. -/
theorem exhMW_subset_r1_under_totality (m : M) (s : T)
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

omit [Fintype T] in
/-- **R₁ = ExhMW under totality**: Full equivalence when alternatives form a chain.

Totality is *a* sufficient condition for [franke-2011]'s Fact 1 to become an
equality; the paper's own sufficient condition is "homogeneity" of the
alternative set. -/
theorem r1_eq_exhMW_under_totality (m : M) (s : T)
    (hTotal : altOrderingTotalOnMessage G m) :
    isMinimalByAltCount G m s ↔ exhMW (toAlternatives G) (prejacent G m) s :=
  ⟨r1_subset_exhMW G m s, exhMW_subset_r1_under_totality G m s hTotal⟩

/-! ### Fact 3: ExhMW ⊆ ExhIE ([franke-2011] Appendix A) -/

omit [Fintype T] [Fintype M] [DecidableEq M] in
/-- **Franke Fact 3 (Appendix A)**: ExhMW(S, Alt) ⊆ ExhIE(S, Alt)

    This is already proved as `exhMW_entails_exhIE` in
    Exhaustification/Operators/Basic.lean. -/
theorem fact3_exhMW_subset_exhIE (m : M) :
    exhMW (toAlternatives G) (prejacent G m) ⊆ exhIE (toAlternatives G) (prejacent G m) :=
  exhMW_entails_exhIE (toAlternatives G) (prejacent G m)

/-! ### Fact 4: ExhMW = ExhIE under closure ([franke-2011] Appendix A) -/

omit [Fintype T] [Fintype M] [DecidableEq M] in
/-- **Franke Fact 4 (Appendix A)**: ExhMW = ExhIE when Alt is closed under ∧.

    This is proved as `exhMW_eq_exhIE_of_closedUnderConj` in
    Exhaustification/Operators/Basic.lean. -/
theorem fact4_exhMW_eq_exhIE_closed (m : M)
    (hClosed : closedUnderConj (toAlternatives G)) :
    exhMW (toAlternatives G) (prejacent G m) = exhIE (toAlternatives G) (prejacent G m) :=
  exhMW_eq_exhIE_of_closedUnderConj (toAlternatives G) (prejacent G m) hClosed

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
def scalarGame : InterpGame ScalarState ScalarMessage where
  meaning := λ m s => (match m, s with
    | .some_, _ => true           -- "some" true at both states
    | .all, .all => true          -- "all" true only at all
    | .all, .someNotAll => false) = true
  prior := λ _ => 1 / 2  -- Uniform prior

example : scalarGame.literal .some_ .someNotAll = 1/2 := by
  have h : (scalarGame.trueStates .some_).card = 2 := by decide
  simp only [InterpGame.literal,
    if_pos (show scalarGame.meaning .some_ .someNotAll by decide), h]
  norm_num
example : scalarGame.literal .some_ .all = 1/2 := by
  have h : (scalarGame.trueStates .some_).card = 2 := by decide
  simp only [InterpGame.literal,
    if_pos (show scalarGame.meaning .some_ .all by decide), h]
  norm_num
example : scalarGame.literal .all .all = 1 := by
  have h : (scalarGame.trueStates .all).card = 1 := by decide
  simp only [InterpGame.literal,
    if_pos (show scalarGame.meaning .all .all by decide), h]
  norm_num
example : scalarGame.literal .all .someNotAll = 0 := by
  simp only [InterpGame.literal,
    if_neg (show ¬ scalarGame.meaning .all .someNotAll by decide)]

/-- The scalar implicature game IS a scalar game: truth sets are nested. -/
theorem scalarGame_is_scalar : isScalarGame scalarGame := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;>
    simp only [scalarGame, InterpGame.trueStates] <;> decide

/-- The scalar implicature game has distinct truth sets. -/
theorem scalarGame_distinct : Function.Injective scalarGame.trueStates := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;> simp [scalarGame, InterpGame.trueStates] <;> decide

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
    simp only [scalarGame, InterpGame.trueStates]
    decide
  | all => exact Finset.Subset.refl _

/-- Negative check: "some" is NOT strongest at "all" — "all" is stronger. -/
example : ¬ strongestAt scalarGame .some_ .all := by
  intro ⟨_, hStr⟩
  have h := hStr .all rfl
  have h1 : ScalarState.someNotAll ∈ scalarGame.trueStates .some_ :=
    scalarGame.mem_trueStates.mpr rfl
  have h2 : ScalarState.someNotAll ∈ scalarGame.trueStates .all := h h1
  unfold InterpGame.trueStates at h2
  simp only [scalarGame] at h2
  exact absurd h2 (by decide)

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
def freeChoiceGame : InterpGame FCState FCMessage where
  meaning := λ m s => (match m, s with
    | .mayA, .onlyA => true
    | .mayA, .either => true
    | .mayA, .both => true
    | .mayB, .onlyB => true
    | .mayB, .either => true
    | .mayB, .both => true
    | .mayAorB, _ => true        -- Always true under standard deontic logic
    | .mayAandB, .both => true
    | _, _ => false) = true
  prior := λ _ => 1 / 4  -- Uniform prior

-- L0: ◇(A∨B) true everywhere → uniform over all 4 states
example : freeChoiceGame.literal .mayAorB .either = 1/4 := by
  have h : (freeChoiceGame.trueStates .mayAorB).card = 4 := by decide
  simp only [InterpGame.literal,
    if_pos (show freeChoiceGame.meaning .mayAorB .either by decide), h]
  norm_num
-- Level-2 hearer: ◇(A∨B) → "either" (free choice inference emerges from IBR).
-- `#guard` (compiler evaluation) rather than `decide`: `hearerBR` branches on
-- ℚ-equality propositions, and ℚ normalization runs `Nat.gcd` (well-founded
-- recursion), which kernel reduction cannot unfold.
#guard ibrN freeChoiceGame 2 .mayAorB .either > 0
#guard ibrN freeChoiceGame 2 .mayAorB .onlyA == 0

end Franke2011
