import Linglib.Core.Order.ComparativeProbability.Defs

/-!
# Validity patterns for comparative probability

The intuitively valid (`V1`–`V13`) and invalid (`I1`–`I3`) inference patterns for
comparative epistemic modals ([holliday-icard-2013], Figure 1; [yalcin-2010]),
stated for an abstract likelihood relation `r` on a Boolean algebra and proved
**once** at the weakest axiom hypotheses. Concrete models (measures, world-ordering
lifts) discharge each pattern by supplying the relevant `ComparativeProbability.*`
instances, so no per-model reproof is needed.

`I1`–`I3` are stated but not proved here: they are *invalid* for additive models
(refuted by measure counterexamples) yet *valid* for the l-lifting, so their status
is model-specific.

## Main statements
* `patternV1_holds` — `V1` holds for every relation (pure logic).
* `patternV2`, `patternV3`, `patternV4`, `patternV5`, `patternV7` — from
  monotonicity (+ transitivity).
* `patternV6` — additionally needs additivity and non-triviality.
* `patternV11`, `patternV12` — from transitivity + complement reversal.
* `patternV13` — from monotonicity + additivity.
-/

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α] (r : α → α → Prop)

/-- V1: `△a → ¬△aᶜ`. -/
def patternV1 : Prop := ∀ a : α, Probably r a → ¬ Probably r aᶜ
/-- V2: `△(a ⊓ b) → △a ∧ △b`. -/
def patternV2 : Prop := ∀ a b : α, Probably r (a ⊓ b) → Probably r a ∧ Probably r b
/-- V3: `△a → △(a ⊔ b)`. -/
def patternV3 : Prop := ∀ a b : α, Probably r a → Probably r (a ⊔ b)
/-- V4: `a ≽ ⊥`. -/
def patternV4 : Prop := ∀ a : α, r a ⊥
/-- V5: `⊤ ≽ a`. -/
def patternV5 : Prop := ∀ a : α, r ⊤ a
/-- V6: `□a → △a`, where `□a` is `⊥ ≽ aᶜ`. -/
def patternV6 : Prop := ∀ a : α, r ⊥ aᶜ → Probably r a
/-- V7: `△a → ◇a`. -/
def patternV7 : Prop := ∀ a : α, Probably r a → Possibly r a
/-- V11: `b ≽ a → △a → △b`. -/
def patternV11 : Prop := ∀ a b : α, r b a → Probably r a → Probably r b
/-- V12: `b ≽ a → a ≽ aᶜ → b ≽ bᶜ`. -/
def patternV12 : Prop := ∀ a b : α, r b a → r a aᶜ → r b bᶜ
/-- V13: `(a \ b) ≻ ⊥ → (a ⊔ b) ≻ b`. -/
def patternV13 : Prop := ∀ a b : α, Strict r (a \ b) ⊥ → Strict r (a ⊔ b) b
/-- I1: `a ≽ b → a ≽ c → a ≽ (b ⊔ c)`. -/
def patternI1 : Prop := ∀ a b c : α, r a b → r a c → r a (b ⊔ c)
/-- I2: `a ≽ aᶜ → a ≽ b`. -/
def patternI2 : Prop := ∀ a b : α, r a aᶜ → r a b
/-- I3: `△a → a ≽ b`. -/
def patternI3 : Prop := ∀ a b : α, Probably r a → r a b

variable {r}

/-- V1 holds for **any** relation: it is pure logic about `Strict` and double
    complement, requiring no axioms. -/
theorem patternV1_holds : patternV1 r := by
  rintro a ⟨_, hanot⟩ ⟨hac, _⟩
  rw [compl_compl] at hac; exact hanot hac

/-- V2 from monotonicity and transitivity. -/
theorem patternV2_of [IsLikelihoodMono r] [IsTrans α r] : patternV2 r := by
  rintro a b ⟨hab, habnot⟩
  have hsa : r a (a ⊓ b) := mono _ _ inf_le_left
  have hsb : r b (a ⊓ b) := mono _ _ inf_le_right
  have hca : r (a ⊓ b)ᶜ aᶜ := mono _ _ (compl_le_compl inf_le_left)
  have hcb : r (a ⊓ b)ᶜ bᶜ := mono _ _ (compl_le_compl inf_le_right)
  refine ⟨⟨Trans.trans (Trans.trans hsa hab) hca, ?_⟩,
          ⟨Trans.trans (Trans.trans hsb hab) hcb, ?_⟩⟩
  · exact fun hc => habnot (Trans.trans (Trans.trans hca hc) hsa)
  · exact fun hc => habnot (Trans.trans (Trans.trans hcb hc) hsb)

/-- V3 from monotonicity and transitivity. -/
theorem patternV3_of [IsLikelihoodMono r] [IsTrans α r] : patternV3 r := by
  rintro a b ⟨hA, hAnot⟩
  have h1 : r (a ⊔ b) a := mono _ _ le_sup_left
  have h2 : r aᶜ (aᶜ ⊓ bᶜ) := mono _ _ inf_le_left
  refine ⟨?_, ?_⟩
  · rw [compl_sup]; exact Trans.trans (Trans.trans h1 hA) h2
  · rw [compl_sup]; exact fun hc => hAnot (Trans.trans (Trans.trans h2 hc) h1)

/-- V4 from monotonicity. -/
theorem patternV4_of [IsLikelihoodMono r] : patternV4 r := fun _ => mono _ _ bot_le

/-- V5 from monotonicity. -/
theorem patternV5_of [IsLikelihoodMono r] : patternV5 r := fun _ => mono _ _ le_top

/-- V6 from monotonicity, transitivity, additivity, and non-triviality. -/
theorem patternV6_of [IsLikelihoodMono r] [IsTrans α r] [hq : IsQualitativeAdditive r]
    [IsNontrivial r] : patternV6 r := by
  intro a h0ac
  have hA0 : r a ⊥ := mono _ _ bot_le
  refine ⟨Trans.trans hA0 h0ac, ?_⟩
  intro hAcA
  have h0A : r ⊥ a := Trans.trans h0ac hAcA
  have hAtop : r a ⊤ := by rw [hq.qadd a ⊤]; simpa using h0ac
  exact IsNontrivial.bot_not_ge_top (Trans.trans h0A hAtop)

/-- V7 from monotonicity and transitivity. -/
theorem patternV7_of [IsLikelihoodMono r] [IsTrans α r] : patternV7 r := by
  rintro a ⟨_, hAnot⟩ hempty
  exact hAnot (IsTrans.trans aᶜ ⊥ a (mono ⊥ aᶜ bot_le) hempty)

/-- V11 from transitivity and complement reversal. -/
theorem patternV11_of [IsTrans α r] [IsComplementReversing r] : patternV11 r := by
  rintro a b hba ⟨ha, hanot⟩
  have h2 : r aᶜ bᶜ := complRev _ _ hba
  refine ⟨Trans.trans (Trans.trans hba ha) h2, ?_⟩
  exact fun hc => hanot (Trans.trans (Trans.trans h2 hc) hba)

/-- V12 from transitivity and complement reversal. -/
theorem patternV12_of [IsTrans α r] [IsComplementReversing r] : patternV12 r := by
  intro a b hba ha
  exact Trans.trans (Trans.trans hba ha) (complRev _ _ hba)

/-- V13 from monotonicity and additivity. -/
theorem patternV13_of [IsLikelihoodMono r] [IsQualitativeAdditive r] : patternV13 r := by
  rintro a b ⟨_, hABnot⟩
  refine ⟨mono _ _ le_sup_right, ?_⟩
  intro hc
  apply hABnot
  have hb : b \ (a ⊔ b) = ⊥ := sdiff_eq_bot_iff.mpr le_sup_right
  have hab : (a ⊔ b) \ b = a \ b := sup_sdiff_right_self
  have hx := (qadd b (a ⊔ b)).mp hc
  rwa [hb, hab] at hx

end ComparativeProbability
