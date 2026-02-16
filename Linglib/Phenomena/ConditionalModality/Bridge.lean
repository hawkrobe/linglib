import Linglib.Phenomena.ConditionalModality.Data

/-!
# Conditional Modality Bridge — Kratzer 2012 §2.9 Derivations

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

namespace Phenomena.ConditionalModality

open Semantics.Attitudes.Intensional (World)
open Semantics.Modality.Kratzer

/-! ## Section A: Conditional parameter derivations (§2.9) -/

/-- **Material implication** (§2.9): With a totally realistic modal base and
    empty ordering source, necessity over the restricted base equals material
    implication. At w0/w1 the single accessible world decides; at w2/w3
    the restricted base is vacuously satisfied (no rain-worlds accessible). -/
theorem conditional_material_implication (w : World) :
    necessity (restrictedBase totallyRealisticBg rained) emptyBackground streetWet w =
    materialImplication rained streetWet w := by
  cases w <;> native_decide

/-- **Strict implication fails** (§2.9): With empty base and empty ordering,
    all worlds are accessible. Restricting by `rained` gives {w0, w1}, and
    since streetWet is false at w1, necessity fails at every evaluation world. -/
theorem strict_conditional_fails (w : World) :
    necessity (restrictedBase emptyBackground rained) emptyBackground streetWet w =
    false := by
  cases w <;> native_decide

/-- **Ordering conditional succeeds** (§2.9): With empty base and normalcy
    ordering, the rain-worlds {w0, w1} are ordered by normalcySource. Since w0
    satisfies the normalcy proposition (rain → wet) and w1 does not, w0 is
    strictly better. The best worlds are {w0}, and streetWet w0 = true. -/
theorem ordering_conditional_succeeds (w : World) :
    necessity (restrictedBase emptyBackground rained) normalcySource streetWet w =
    true := by
  cases w <;> native_decide

/-! ## Section B: The ordering source makes the difference -/

/-- **The ordering source resolves the counterexample.** Strict implication
    fails because w1 (rained ∧ ¬streetWet) is accessible, but the normalcy
    ordering eliminates w1 as non-best. This is Kratzer's central insight:
    the ordering source handles graded possibility and anomalous worlds. -/
theorem ordering_resolves_counterexample :
    (∀ w, necessity (restrictedBase emptyBackground rained) emptyBackground streetWet w = false) ∧
    (∀ w, necessity (restrictedBase emptyBackground rained) normalcySource streetWet w = true) := by
  constructor <;> intro w <;> cases w <;> native_decide

/-! ## Section C: Tensed conditional (forces tense-modal composition) -/

/-- **Tensed counterfactual succeeds**: "If it had rained (yesterday), the
    street would be wet (now)." The past-tense antecedent `atTime rainedAt (-1)`
    enters the Kratzer modal base via the type bridge `atTime`, and the
    normalcy-ordered analysis gives the correct prediction. -/
theorem tensed_counterfactual_succeeds (w : World) :
    necessity (restrictedBase emptyBackground (atTime rainedAt (-1)))
             normalcySource (atTime wetStreetAt 0) w = true := by
  cases w <;> native_decide

/-! ## Section D: Composition bridge -/

/-- **Tensed matches atemporal**: The tensed conditional gives the same result
    as the atemporal one, witnessing that temporal projection via `atTime` is
    transparent to the modal analysis. -/
theorem tensed_matches_atemporal (w : World) :
    necessity (restrictedBase emptyBackground (atTime rainedAt (-1)))
             normalcySource (atTime wetStreetAt 0) w =
    necessity (restrictedBase emptyBackground rained)
             normalcySource streetWet w := by
  cases w <;> native_decide

end Phenomena.ConditionalModality
