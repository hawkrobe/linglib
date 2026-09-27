module

public import Linglib.Logic.ComparativeProbability.Defs

/-!
# Validity patterns for comparative probability

The inference patterns against which semantics for the comparative epistemic modal *at least
as likely as* and for *probably* are assessed: the intuitively valid V1–V12 of [yalcin-2010],
the intuitively invalid I1–I3, and Conjunctivitis E1, in the numbering of
[holliday-icard-2013]'s Figure 1. Each is a predicate on a likelihood relation `r` on a
Boolean algebra, named by the paper's own labels with the figure's numbering in the docstrings.
V6 and V7 take the account's necessity and possibility modals as parameters and V8–V10 its
indicative conditional, since these vary across semantics; I1, the union property, is
`RightUnion` of `Defs`.

Each valid pattern is derived once from the axioms of comparative probability
(`Core/Order/Probability/Defs`), so a model discharges it by instance resolution: V1 for
every relation, V2–V5 and V7–V10 from monotonicity and transitivity, V11 and V12 from
transitivity and complement reversal, and V6 from additivity and non-triviality when the
necessity modal is the order's own `⊥ ≽ aᶜ`. The invalid patterns and E1 are refuted or
validated model by model in the studies.

## References

* [yalcin-2010]
* [holliday-icard-2013]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α] (r : α → α → Prop)

/-- V1, *probably* to not *probably* not: `△a → ¬△aᶜ`. -/
def ProbablyToNotProbablyNot : Prop := ∀ a : α, Probably r a → ¬ Probably r aᶜ
/-- V2, distribution over conjunction: `△(a ⊓ b) → △a ∧ △b`. -/
def ProbablyDistribInf : Prop := ∀ a b : α, Probably r (a ⊓ b) → Probably r a ∧ Probably r b
/-- V3, chancy disjunction introduction: `△a → △(a ⊔ b)`. -/
def ChancyDisjunctionIntro : Prop := ∀ a b : α, Probably r a → Probably r (a ⊔ b)
/-- V4, minimality: `a ≽ ⊥`. -/
def Minimality : Prop := ∀ a : α, r a ⊥
/-- V5, maximality: `⊤ ≽ a`. -/
def Maximality : Prop := ∀ a : α, r ⊤ a
/-- V6, *must* to *probably*: `□a → △a`, for the account's necessity modal. -/
def MustToProbably (must : α → Prop) : Prop := ∀ a : α, must a → Probably r a
/-- V7, *probably* to *might*: `△a → ◇a`, for the account's possibility modal. -/
def ProbablyToMight (might : α → Prop) : Prop := ∀ a : α, Probably r a → might a
/-- V8, chancy modus ponens, for the account's indicative conditional. -/
def ChancyModusPonens (ifThen : α → α → Prop) : Prop :=
  ∀ a b : α, ifThen a b → Probably r a → Probably r b
/-- V9, chancy modus tollens. -/
def ChancyModusTollens (ifThen : α → α → Prop) : Prop :=
  ∀ a b : α, ifThen a b → ¬ Probably r b → ¬ Probably r a
/-- V10, conditional to comparative: `(if a, b) → b ≽ a`. -/
def ConditionalToComparative (ifThen : α → α → Prop) : Prop := ∀ a b : α, ifThen a b → r b a
/-- V11, positive form transfer: `b ≽ a → △a → △b`. -/
def PositiveFormTransfer : Prop := ∀ a b : α, r b a → Probably r a → Probably r b
/-- V12, complement transfer: `b ≽ a → a ≽ aᶜ → b ≽ bᶜ`. -/
def ComplementTransfer : Prop := ∀ a b : α, r b a → r a aᶜ → r b bᶜ
/-- I2, collapse of equiprobability into certainty: `a ≽ aᶜ → a ≽ b`. -/
def EquiprobabilityCollapse : Prop := ∀ a b : α, r a aᶜ → r a b
/-- I3, Hamblin's collapse: `△a → a ≽ b`. -/
def HamblinCollapse : Prop := ∀ a b : α, Probably r a → r a b
/-- E1, Conjunctivitis: `△a → △b → △(a ⊓ b)`. -/
def Conjunctivitis : Prop := ∀ a b : α, Probably r a → Probably r b → Probably r (a ⊓ b)

variable {r}

/-- V1 holds for **any** relation: it is pure logic about `Strict` and double complement. -/
theorem probablyToNotProbablyNot : ProbablyToNotProbablyNot r := by
  rintro a ⟨_, hanot⟩ ⟨hac, _⟩
  rw [compl_compl] at hac; exact hanot hac

/-- V2 from monotonicity and transitivity. -/
theorem probablyDistribInf_of [IsLikelihoodMono r] [IsTrans α r] : ProbablyDistribInf r := by
  rintro a b ⟨hab, habnot⟩
  have hsa : r a (a ⊓ b) := mono _ _ inf_le_left
  have hsb : r b (a ⊓ b) := mono _ _ inf_le_right
  have hca : r (a ⊓ b)ᶜ aᶜ := mono _ _ (compl_le_compl inf_le_left)
  have hcb : r (a ⊓ b)ᶜ bᶜ := mono _ _ (compl_le_compl inf_le_right)
  refine ⟨⟨Trans.trans (Trans.trans hsa hab) hca, ?_⟩,
          ⟨Trans.trans (Trans.trans hsb hab) hcb, ?_⟩⟩
  · exact fun hc ↦ habnot (Trans.trans (Trans.trans hca hc) hsa)
  · exact fun hc ↦ habnot (Trans.trans (Trans.trans hcb hc) hsb)

/-- V3 from monotonicity and transitivity. -/
theorem chancyDisjunctionIntro_of [IsLikelihoodMono r] [IsTrans α r] :
    ChancyDisjunctionIntro r := by
  rintro a b ⟨hA, hAnot⟩
  have h1 : r (a ⊔ b) a := mono _ _ le_sup_left
  have h2 : r aᶜ (aᶜ ⊓ bᶜ) := mono _ _ inf_le_left
  refine ⟨?_, ?_⟩
  · rw [compl_sup]; exact Trans.trans (Trans.trans h1 hA) h2
  · rw [compl_sup]; exact fun hc ↦ hAnot (Trans.trans (Trans.trans h2 hc) h1)

/-- V4 from monotonicity. -/
theorem minimality_of [IsLikelihoodMono r] : Minimality r := fun _ ↦ mono _ _ bot_le

/-- V5 from monotonicity. -/
theorem maximality_of [IsLikelihoodMono r] : Maximality r := fun _ ↦ mono _ _ le_top

/-- V6 for the necessity modal `⊥ ≽ aᶜ` of the order itself, from monotonicity, transitivity,
additivity, and non-triviality. -/
theorem mustToProbably_of [IsLikelihoodMono r] [IsTrans α r] [hq : IsQualitativeAdditive r]
    [IsNontrivial r] : MustToProbably r fun a ↦ r ⊥ aᶜ := by
  intro a h0ac
  have hA0 : r a ⊥ := mono _ _ bot_le
  refine ⟨Trans.trans hA0 h0ac, ?_⟩
  intro hAcA
  have h0A : r ⊥ a := Trans.trans h0ac hAcA
  have hAtop : r a ⊤ := by rw [hq.qadd a ⊤]; simpa using h0ac
  exact IsNontrivial.bot_not_ge_top (Trans.trans h0A hAtop)

/-- V7 for the possibility modal `¬ ⊥ ≽ a` of the order itself, from monotonicity and
transitivity. -/
theorem probablyToMight_of [IsLikelihoodMono r] [IsTrans α r] : ProbablyToMight r (Possibly r) := by
  rintro a ⟨_, hAnot⟩ hempty
  exact hAnot (IsTrans.trans aᶜ ⊥ a (mono ⊥ aᶜ bot_le) hempty)

/-- V8 for the conditional read as entailment, from monotonicity and transitivity: *probably*
is monotone. -/
theorem chancyModusPonens_of [IsLikelihoodMono r] [IsTrans α r] : ChancyModusPonens r (· ≤ ·) := by
  rintro a b hab ⟨ha, hanot⟩
  have h1 : r b a := mono _ _ hab
  have h2 : r aᶜ bᶜ := mono _ _ (compl_le_compl hab)
  exact ⟨Trans.trans (Trans.trans h1 ha) h2,
    fun hc ↦ hanot (Trans.trans (Trans.trans h2 hc) h1)⟩

/-- V9 for the conditional read as entailment, the contrapositive of V8. -/
theorem chancyModusTollens_of [IsLikelihoodMono r] [IsTrans α r] : ChancyModusTollens r (· ≤ ·) :=
  fun a b hab hb ha ↦ hb (chancyModusPonens_of a b hab ha)

/-- V10 for the conditional read as entailment, from monotonicity. -/
theorem conditionalToComparative_of [IsLikelihoodMono r] : ConditionalToComparative r (· ≤ ·) :=
  fun _ _ hab ↦ mono _ _ hab

/-- V11 from transitivity and complement reversal. -/
theorem positiveFormTransfer_of [IsTrans α r] [IsComplementReversing r] :
    PositiveFormTransfer r := by
  rintro a b hba ⟨ha, hanot⟩
  have h2 : r aᶜ bᶜ := complRev _ _ hba
  refine ⟨Trans.trans (Trans.trans hba ha) h2, ?_⟩
  exact fun hc ↦ hanot (Trans.trans (Trans.trans h2 hc) hba)

/-- V12 from transitivity and complement reversal. -/
theorem complementTransfer_of [IsTrans α r] [IsComplementReversing r] : ComplementTransfer r := by
  intro a b hba ha
  exact Trans.trans (Trans.trans hba ha) (complRev _ _ hba)

end ComparativeProbability
