module

public import Linglib.Syntax.Agreement.ContainmentPair
public import Linglib.Phonology.Constraints.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Alternatives.Competition

/-!
# Maximize Presupposition

This file defines Maximize Presupposition ([heim-1991]) in its two formulations. As
competition, `Blocked`: an expression is blocked when an alternative with the same assertion
carries a strictly stronger presupposition, the anti-presupposition of [percus-2006] and
[sauerland-2008a], stated over any alternative source by `Alternatives.Blocked` and so shared
by the pragmatic reading, which derives it from Gricean reasoning ([schlenker-2012]), and the
grammatical, locally applied one ([singh-2011]). As a violable constraint, `mpConstraintOf`:
over candidates carrying a presuppositional strength, violations count the distance from the
maximal strength, so that Maximize Presupposition is antagonistic to a markedness penalty on
strength (`mp_reverses_markedness`); `phiMP` is its φ-feature instance, and `PragConstraint.MP`
of `Studies/Wang2025.lean` ranks it against internal coherence and felicity ([wang-2025]).

## Main definitions

* `Blocked` — blocked under Maximize Presupposition: a same-assertion alternative with a
  strictly stronger presupposition.
* `mpConstraintOf`, `markednessPenalty` — the constraint pair over a strength function.
* `phiMP`, `phiMarkedness` — the pair on φ-feature containment pairs.

## Main results

* `mp_reverses_markedness`, `mp_selects_strongest`, `markedness_selects_weakest` — the two
  constraints order candidates oppositely, and each selects its extreme.
* `phi_mp_selects_maximal`, `phi_mp_reverses_markedness` — the φ-feature instance.

## References

* [heim-1991]
* [percus-2006]
* [sauerland-2008a]
* [schlenker-2012]
* [singh-2011]
* [wang-2025]
-/

@[expose] public section

namespace Presupposition.MaximizePresupposition

open Agreement Constraints OptimalityTheory

/-- `φ` is blocked under Maximize Presupposition when an alternative with the same assertion
carries a strictly stronger presupposition. -/
def Blocked {S W : Type*} (alts : S → Set S) (presup assertion : S → Set W) (φ : S) : Prop :=
  Alternatives.Blocked (Alternatives.sameAssertion assertion alts) presup φ

/-! ### Abstract constraints

Two generic constraint constructors, parameterized by a presuppositional
strength function `strength : C → Nat`:

- **`mpConstraintOf`**: penalizes failure to maximize presupposition.
  Violation count = `maxStrength - strength c`.
- **`markednessPenalty`**: penalizes presuppositional strength directly.
  Violation count = `strength c`.

These are antagonistic: for any candidate `c`, `mpConstraintOf … c +
markednessPenalty … c = maxStrength` (when `strength c ≤ maxStrength`).
-/

/-- Build an MP constraint from a presuppositional strength function.
    Violation count = `maxStrength - strength c`: maximal presupposition
    → 0 violations, weaker presupposition → more. -/
def mpConstraintOf {C : Type*} (maxStrength : Nat)
    (strength : C → Nat) : Constraint C :=
  fun c => maxStrength - strength c

/-- A markedness constraint penalizing presuppositional strength.
    Violation count = `strength c`: stronger presupposition → more
    violations. This is the generic form of Wang2023's `todConstraint`
    (Taboo of Directness). -/
def markednessPenalty {C : Type*}
    (strength : C → Nat) : Constraint C :=
  strength

/-- Violation counts sum to maxStrength for any candidate whose
    strength does not exceed the maximum. -/
theorem mp_markedness_complementary {C : Type*} (maxStrength : Nat)
    (strength : C → Nat) (c : C) (h : strength c ≤ maxStrength) :
    (mpConstraintOf maxStrength strength) c +
    (markednessPenalty strength) c = maxStrength := by
  simp only [mpConstraintOf, markednessPenalty]; omega

/-! ### Structural properties

The core algebraic facts about MP and markedness as OT constraints.
These hold for any candidate type and strength function.
-/

/-- MP assigns 0 violations to the maximally presupposing candidate. -/
theorem mp_zero_at_max {C : Type*} (maxStrength : Nat) (strength : C → Nat)
    (c : C) (hMax : strength c = maxStrength) :
    (mpConstraintOf maxStrength strength) c = 0 := by
  simp [mpConstraintOf, hMax]

/-- Markedness assigns 0 violations to the minimally presupposing
    candidate. -/
theorem markedness_zero_at_min {C : Type*} (strength : C → Nat)
    (c : C) (hMin : strength c = 0) :
    (markednessPenalty strength) c = 0 := by
  simp [markednessPenalty, hMin]

/-- **MP and markedness impose opposite orderings**: fewer MP violations
    ↔ more markedness violations. This is the general form of Wang2023's
    `tod_reverses_mp`. -/
theorem mp_reverses_markedness {C : Type*} (maxStrength : Nat)
    (strength : C → Nat) (c₁ c₂ : C)
    (h₁ : strength c₁ ≤ maxStrength) (h₂ : strength c₂ ≤ maxStrength) :
    (markednessPenalty strength) c₁ < (markednessPenalty strength) c₂ ↔
    (mpConstraintOf maxStrength strength) c₁ >
    (mpConstraintOf maxStrength strength) c₂ := by
  simp only [markednessPenalty, mpConstraintOf]; omega

/-- **MP dominant → strongest wins**: when MP is the top-ranked constraint,
    all optimal candidates have maximal presuppositional strength.
    Proof via `optimal_zero_first` — a max-strength candidate has 0 MP
    violations, forcing all winners to have 0 as well. -/
theorem mp_selects_strongest {C : Type*} [DecidableEq C] (candidates : List C)
    (maxStrength : Nat) (strength : C → Nat)
    (rest : List (Constraint C))
    (hNE : candidates ≠ [])
    (hBound : ∀ c ∈ candidates, strength c ≤ maxStrength)
    (hExists : ∃ c₀ ∈ candidates, strength c₀ = maxStrength) :
    ∀ c ∈ (Tableau.ofRanking candidates
      (mpConstraintOf maxStrength strength :: rest) hNE).optimal,
      strength c = maxStrength := by
  intro c hc
  have hZero := Tableau.ofRanking_optimal_zero_first (mpConstraintOf maxStrength strength)
    rest
    (by obtain ⟨c₀, hm, hs⟩ := hExists
        exact ⟨c₀, hm, mp_zero_at_max maxStrength strength c₀ hs⟩) hc
  have hcBound := hBound c (Tableau.ofRanking_optimal_mem hc)
  simp only [mpConstraintOf] at hZero; omega

/-- **Markedness dominant → weakest wins**: when a markedness constraint
    is the top-ranked constraint, all optimal candidates have zero
    presuppositional strength. This is the general form of Wang2023's
    `tod_mp_only_minimal`. -/
theorem markedness_selects_weakest {C : Type*} [DecidableEq C] (candidates : List C)
    (strength : C → Nat)
    (rest : List (Constraint C))
    (hNE : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, strength c₀ = 0) :
    ∀ c ∈ (Tableau.ofRanking candidates
      (markednessPenalty strength :: rest) hNE).optimal,
      strength c = 0 := by
  intro c hc
  have hZero := Tableau.ofRanking_optimal_zero_first (markednessPenalty strength) rest
    (by obtain ⟨c₀, hm, hs⟩ := hExists
        exact ⟨c₀, hm, markedness_zero_at_min strength c₀ hs⟩) hc
  simp only [markednessPenalty] at hZero; exact hZero

/-! ### The φ-feature instance

The containment-pair cells with `specLevel` as strength are an instance of the competition:
a cell denotes a domain restriction, which asserts nothing, and the strength ordering is domain
containment (`IsLowerSet.inf_le_inf_of_card_le`). -/

/-- The φ-feature Maximize Presupposition constraint: `mpConstraintOf` at `specLevel`. -/
def phiMP : Constraint ContainmentPair :=
  mpConstraintOf ContainmentPair.maximal.specLevel ContainmentPair.specLevel

theorem phiMP_eval (c : ContainmentPair) :
    phiMP c = ContainmentPair.maximal.specLevel - c.specLevel := rfl

/-- The φ-feature markedness constraint, `markednessPenalty` at `specLevel`: the generic form
of the Taboo of Directness. -/
def phiMarkedness : Constraint ContainmentPair := markednessPenalty ContainmentPair.specLevel

theorem phiMarkedness_eval (c : ContainmentPair) : phiMarkedness c = c.specLevel := rfl

/-- MP over phi-features selects the maximal (most marked) cell when
    it is among the candidates. Instantiation of `mp_selects_strongest`
    to `ContainmentPair`.

    This is the normal-speech pattern: absent any politeness or
    context-sensitivity constraint, MP forces use of the form with the
    strongest presupposition (SG over PL, 1st over 3rd, DEF over INDEF).
    [sauerland-2003] derives the preference for singular from
    exactly this principle. -/
theorem phi_mp_selects_maximal (candidates : List ContainmentPair)
    (rest : List (Constraint ContainmentPair)) (hNE : candidates ≠ [])
    (hMax : ContainmentPair.maximal ∈ candidates) :
    ∀ c ∈ (Tableau.ofRanking candidates (phiMP :: rest) hNE).optimal,
      c.specLevel = ContainmentPair.maximal.specLevel :=
  mp_selects_strongest candidates _ ContainmentPair.specLevel rest hNE
    (fun c _ ↦ ContainmentPair.specLevel_le_two c) ⟨.maximal, hMax, rfl⟩

/-- MP and markedness reverse each other over phi-features.
    This is the algebraic core of `tod_reverses_mp` in `Wang2023`. -/
theorem phi_mp_reverses_markedness (c₁ c₂ : ContainmentPair) :
    phiMarkedness c₁ < phiMarkedness c₂ ↔ phiMP c₁ > phiMP c₂ :=
  mp_reverses_markedness _ ContainmentPair.specLevel c₁ c₂ (ContainmentPair.specLevel_le_two c₁)
    (ContainmentPair.specLevel_le_two c₂)

end Presupposition.MaximizePresupposition
