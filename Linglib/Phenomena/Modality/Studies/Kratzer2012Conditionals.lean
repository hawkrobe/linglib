import Linglib.Phenomena.Modality.Studies.Kratzer2012Scenario

/-!
# Conditional Modality Bridge — @cite{kratzer-2012} §2.9 Derivations

Proves that specific Kratzer parameter settings yield specific conditional types
(material, strict, ordered), and that a past-tense antecedent composes
transparently with the modal analysis via `atTime`.

## Section A: Conditional parameter derivations

1. Totally realistic base + empty ordering = material implication
2. Empty base + empty ordering = strict implication (fails: w1 counterexample)
3. Empty base + normalcy ordering = ordered conditional (succeeds: w1 eliminated)

## Section B: The ordering source resolves the counterexample

## Section C: Tensed conditional forces tense-modal composition

## Section D: Tensed conditional matches atemporal conditional

Reference: Kratzer, A. (2012). Modals and Conditionals. Oxford University Press. Ch. 2 §2.9.
-/

namespace Phenomena.Modality.ConditionalModality

open Semantics.Attitudes.Intensional (World)
open Semantics.Modality.Kratzer

/-! ## Section A: Conditional parameter derivations (§2.9) -/

/-- **Material implication** (§2.9): With a totally realistic modal base and
    empty ordering source, necessity over the restricted base equals material
    implication. At w0/w1 the single accessible world decides; at w2/w3
    the restricted base is vacuously satisfied (no rain-worlds accessible). -/
theorem conditional_material_implication (w : World) :
    necessity (restrictedBase totallyRealisticBg rained) emptyBackground streetWet w ↔
    implies rained streetWet w := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  unfold implies
  constructor
  · intro h hRained
    -- w itself is accessible: it satisfies rained (by hypothesis) and the totallyRealisticBg singleton
    have hAcc : w ∈ accessibleWorlds (restrictedBase totallyRealisticBg rained) w := by
      intro p hp
      simp [restrictedBase, totallyRealisticBg] at hp
      rcases hp with hp | hp
      · subst hp; exact hRained
      · subst hp; rfl
    exact h w hAcc
  · intro hImpl w' hAcc
    -- w' satisfies rained (it's in the restricted base)
    have hRainedW' : rained w' := hAcc rained (by simp [restrictedBase])
    -- w' must equal w (totallyRealisticBg gives only w as accessible)
    have hEqW' : w' = w := by
      have hMem : (λ z : World => z = w) ∈ (restrictedBase totallyRealisticBg rained) w := by
        simp [restrictedBase, totallyRealisticBg]
      exact hAcc (λ z : World => z = w) hMem
    subst hEqW'
    exact hImpl hRainedW'

/-- **Strict implication fails** (§2.9): With empty base and empty ordering,
    all worlds are accessible. Restricting by `rained` gives {w0, w1}, and
    since streetWet is false at w1, necessity fails at every evaluation world. -/
theorem strict_conditional_fails (w : World) :
    ¬ necessity (restrictedBase emptyBackground rained) emptyBackground streetWet w := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  intro h
  -- w1 is accessible: it satisfies rained, and emptyBackground gives universal access
  have hAccW1 : (.w1 : World) ∈ accessibleWorlds (restrictedBase emptyBackground rained) w := by
    intro p hp
    simp [restrictedBase, emptyBackground] at hp
    subst hp
    exact w1_rained_dry.1
  have := h .w1 hAccW1
  exact w1_rained_dry.2 this

/-- **Ordering conditional succeeds** (§2.9): With empty base and normalcy
    ordering, the rain-worlds {w0, w1} are ordered by normalcySource. Since w0
    satisfies the normalcy proposition (rain → wet) and w1 does not, w0 is
    strictly better. The best worlds are {w0}, and streetWet w0 = true. -/
theorem ordering_conditional_succeeds (w : World) :
    necessity (restrictedBase emptyBackground rained) normalcySource streetWet w := by
  rw [necessity_iff_all]
  intro w' hw'
  obtain ⟨hAcc, hBest⟩ := hw'
  -- w' satisfies rained (it's in the restricted base)
  have hRainedW' : rained w' := hAcc rained (by simp [restrictedBase])
  -- w0 is accessible (rained, and emptyBackground gives universal access)
  have hAccW0 : (.w0 : World) ∈ accessibleWorlds (restrictedBase emptyBackground rained) w := by
    intro p hp
    simp [restrictedBase, emptyBackground] at hp
    subst hp
    exact w0_rained_wet.1
  -- The normalcy proposition is satisfied at w0
  have hNormW0 : ¬ (rained .w0 ∧ ¬ streetWet .w0) := by
    intro ⟨_, hNotWet⟩; exact hNotWet w0_rained_wet.2
  -- So w' must satisfy the normalcy proposition (since w' is best)
  have hNormW' : ¬ (rained w' ∧ ¬ streetWet w') :=
    hBest .w0 hAccW0 (λ w' => ¬ (rained w' ∧ ¬ streetWet w')) (by simp [normalcySource]) hNormW0
  -- Now case on w': only w0, w2, w3 satisfy the normalcy proposition,
  -- and w' must satisfy rained, so w' = w0
  cases w' with
  | w0 => exact w0_rained_wet.2
  | w1 => exact absurd ⟨w1_rained_dry.1, w1_rained_dry.2⟩ hNormW'
  | w2 => exact absurd hRainedW' w2_dry_wet.1
  | w3 => exact absurd hRainedW' w3_dry_dry.1

/-! ## Section B: The ordering source makes the difference -/

/-- **The ordering source resolves the counterexample.** Strict implication
    fails because w1 (rained ∧ ¬streetWet) is accessible, but the normalcy
    ordering eliminates w1 as non-best. This is Kratzer's central insight:
    the ordering source handles graded possibility and anomalous worlds. -/
theorem ordering_resolves_counterexample :
    (∀ w, ¬ necessity (restrictedBase emptyBackground rained) emptyBackground streetWet w) ∧
    (∀ w, necessity (restrictedBase emptyBackground rained) normalcySource streetWet w) :=
  ⟨strict_conditional_fails, ordering_conditional_succeeds⟩

/-! ## Section C: Tensed conditional (forces tense-modal composition) -/

/-- **Tensed counterfactual succeeds**: "If it had rained (yesterday), the
    street would be wet (now)." The past-tense antecedent `atTime rainedAt (-1)`
    enters the Kratzer modal base via the type bridge `atTime`, and the
    normalcy-ordered analysis gives the correct prediction. -/
theorem tensed_counterfactual_succeeds (w : World) :
    necessity (restrictedBase emptyBackground (atTime rainedAt (-1)))
             normalcySource (atTime wetStreetAt 0) w := by
  rw [atTime_rainedAt_yesterday, atTime_wetStreetAt_now]
  exact ordering_conditional_succeeds w

/-! ## Section D: Composition bridge -/

/-- **Tensed matches atemporal**: The tensed conditional gives the same result
    as the atemporal one, witnessing that temporal projection via `atTime` is
    transparent to the modal analysis. -/
theorem tensed_matches_atemporal (w : World) :
    necessity (restrictedBase emptyBackground (atTime rainedAt (-1)))
             normalcySource (atTime wetStreetAt 0) w ↔
    necessity (restrictedBase emptyBackground rained)
             normalcySource streetWet w := by
  rw [atTime_rainedAt_yesterday, atTime_wetStreetAt_now]

end Phenomena.Modality.ConditionalModality
