import Linglib.Data.Examples.Ronai2024
import Linglib.Studies.ChemlaSpector2011

/-!
# Ronai (2024): Embedded scalar diversity

This file formalizes [ronai-2024]'s two experiments on the embedded scalar implicature of
*every N was P* across 42 lexical scales: whether *Every soup was warm* suggests the strong
inference *No soup was hot*, the implicature computed in the scope of the universal, beyond the
weak inference *Not every soup was hot* that a global implicature yields. Experiment 1 is the
design of [chemla-spector-2011] and [gotzner-romoli-2018] with the scale varied, a sliding-scale
judgment of how far the sentence suggests a true control, the weak inference, the strong
inference, or a false control, and the cline of responses tracks the number of readings of the
sentence that entail the judged one. The readings are `ChemlaSpector2011.Exp1Some.reading` over a
domain of any size, `supports_iff` derives which reading entails which inference, and
`exp1_monotone` checks the cline on the rows. Only the local reading entails the strong
inference, and `strong_admitted` shows that every account but the unmodified neo-Gricean one
makes that reading available under a universal: the grammatical theory of [chierchia-2004] and
[chierchia-fox-spector-2012] computes it locally, and [sauerland-2004]'s account negates the
alternative *some N was Q*, which is not stronger than the utterance. Experiment 2 replaces the
false control by the Yes/No inference task of [van-tiel-geurts-2016], since the compatible
control of [gotzner-romoli-2018] is the negation of the strong inference itself
(`compatible_iff_not_strong`).

The paper's argument for alternative-based accounts is statistical and stays in prose. The
strong inference varies across the scales as the global implicature rates of
[van-tiel-geurts-2016] do, and the two properties of alternatives that predict global scalar
diversity, semantic distance and boundedness, predict the embedded variation in both
experiments. The same properties acting at both levels is expected when the embedded inference
is computed from the alternatives, as on the accounts above and the neo-Gricean-uncertainty
model of [potts-etal-2016], and unexplained when it is an unconstrained strengthening of lexical
meanings, as in [bergen-levy-goodman-2016]; the null result of [sun-tian-breheny-2018] for the
same predictors in a *P so not Q* naturalness task is attributed to the corrective context
those sentences need.

## Implementation notes

* A scale ⟨P, Q⟩ with `Q ⊆ P` puts each individual of the domain in one of the three cells of
  `SomeAllWorld`: neither term, the weak term only, or the strong term; the *some*/*all* case
  names the cells.
* The rows carry the condition means of Figure 1 and the per-scale strong-inference rates of
  both experiments, computed from the raw data the paper deposits.

## References

* [ronai-2024]
* [chemla-spector-2011]
* [gotzner-romoli-2018]
* [van-tiel-geurts-2016]
* [chierchia-2004]
* [chierchia-fox-spector-2012]
* [sauerland-2004]
* [potts-etal-2016]
* [bergen-levy-goodman-2016]
* [sun-tian-breheny-2018]
-/

namespace Ronai2024

open ChemlaSpector2011 Data.Examples SomeAllWorld

variable {ι : Type*}

/-! ### The inferences judged in Experiment 1 -/

/-- The second sentence of a trial (11): the true control *at least one N was P*, the weak
inference *not every N was Q*, the strong inference *no N was Q*, and the false control *not
every N was P*. -/
inductive Inference where
  | trueControl
  | weak
  | strong
  | falseControl
  deriving DecidableEq, Repr, Fintype

/-- What each inference says of a domain of individuals. The weak inference is the negation of
the utterance's only alternative on an unmodified neo-Gricean account, *every N was Q*. -/
def Inference.den : Inference → (ι → SomeAllWorld) → Prop
  | .trueControl, m => ∃ i, atLeastOne (m i)
  | .weak, m => ¬ everyAll m
  | .strong, m => ∀ i, ¬ universal (m i)
  | .falseControl, m => ¬ everySome m

instance [Fintype ι] (m : ι → SomeAllWorld) : (n : Inference) → Decidable (n.den m)
  | .trueControl => inferInstanceAs (Decidable (∃ _, _))
  | .weak => inferInstanceAs (Decidable (¬ _))
  | .strong => inferInstanceAs (Decidable (∀ _, _))
  | .falseControl => inferInstanceAs (Decidable (¬ _))

/-- The row key of an inference. -/
def Inference.key : Inference → String
  | .trueControl => "true"
  | .weak => "weak"
  | .strong => "strong"
  | .falseControl => "false"

/-- *Some N was Q*, (5): the alternative built by replacing both scalar terms, which
[sauerland-2004]'s account admits though it is not stronger than the utterance, and the
compatible control of [gotzner-romoli-2018]'s second experiment. -/
def compatible (m : ι → SomeAllWorld) : Prop := ∃ i, universal (m i)

instance [Fintype ι] (m : ι → SomeAllWorld) : Decidable (compatible m) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- Negating the alternative *some N was Q* yields the strong inference. -/
theorem compatible_iff_not_strong (m : ι → SomeAllWorld) :
    compatible m ↔ ¬ Inference.den .strong m := by
  simp [compatible, Inference.den]

/-- *Some N was Q* does not entail *every N was P*: an individual at `all` beside one at
`none`. -/
theorem compatible_not_everySome : ∃ m : Bool → SomeAllWorld, compatible m ∧ ¬ everySome m :=
  ⟨λ b => if b then .all else .none, by decide⟩

/-! ### Readings and the inferences they support (§3.4) -/

/-- A reading supports an inference when it entails it on every nonempty domain. -/
def Supports (ℓ : ReadingLabel) (n : Inference) : Prop :=
  ∀ {ι : Type} [Nonempty ι] (m : ι → SomeAllWorld), Exp1Some.reading ℓ m → n.den m

/-- The inferences each reading supports: the literal reading the true control alone, the
global reading the weak inference too, the local reading the strong inference too; no reading
supports the false control. -/
def supported : ReadingLabel → Finset Inference
  | .literal => {.trueControl}
  | .global => {.trueControl, .weak}
  | .local_ => {.trueControl, .weak, .strong}

theorem supports_iff (ℓ : ReadingLabel) (n : Inference) : Supports ℓ n ↔ n ∈ supported ℓ := by
  refine ⟨λ h => ?_, λ h ι _ m hm => ?_⟩
  · cases ℓ <;> cases n <;> first
      | decide
      | exact absurd (h (λ _ : Unit => .all) (by decide)) (by decide)
      | exact absurd (h (λ b : Bool => if b then .all else .someNotAll) (by decide)) (by decide)
      | exact absurd (h (λ _ : Unit => .someNotAll) (by decide)) (by decide)
  · cases ℓ <;> cases n <;>
      simp only [supported, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
        or_false, false_or] at h
    case literal.trueControl => exact ⟨Classical.arbitrary ι, hm _⟩
    case global.trueControl => exact ⟨Classical.arbitrary ι, hm.1 _⟩
    case global.weak => exact hm.2
    case local_.trueControl => exact ⟨Classical.arbitrary ι, hm.everySome _⟩
    case local_.weak => exact hm.not_everyAll
    case local_.strong => exact (everySomeNotAll_iff.1 hm).2

instance (ℓ : ReadingLabel) (n : Inference) : Decidable (Supports ℓ n) :=
  decidable_of_iff _ (supports_iff ℓ n).symm

/-- Only the local reading supports the strong inference. -/
theorem supports_strong_iff (ℓ : ReadingLabel) : Supports ℓ .strong ↔ ℓ = .local_ := by
  cases ℓ <;> simp [supports_iff, supported]

/-- The number of readings supporting an inference, which the sliding-scale response tracks. -/
def support (n : Inference) : ℕ := (Finset.univ.filter (Supports · n)).card

/-- Every account but the unmodified neo-Gricean one makes the local reading available under a
universal: the grammatical theory computes it in the scope of *every*, and a globalist whose
alternatives need not be stronger than the utterance reaches it because there it entails the
literal reading (`Exp1Some.local_globallyDerivable`). -/
theorem strong_admitted (t : Theory) :
    t.admits (Exp1Some.reading (ι := ι)) .local_ ↔ t ≠ .restrictedGlobalist := by
  cases t <;> simp [Theory.admits, Exp1Some.local_globallyDerivable]

/-! ### The rows -/

/-- The mean response to an inference over the 42 scales in Experiment 1 (Figure 1), in
percent. -/
def mean (n : Inference) : Option ℕ :=
  (Examples.all.find? λ r =>
    r.feature? "example" == some "11" && r.feature? "condition" == some n.key).bind
    (·.nat? "mean")

/-- Figure 1: the responses rise with the readings supporting the inference, true above weak
above strong above false, the cline of [gotzner-romoli-2018] across the 42 scales. The strong
inference above the false control is the paper's evidence that embedded implicatures are
computed; the weak inference above the strong one reflects that the global reading supports
only the former. -/
theorem exp1_monotone :
    ∃ r₀ ∈ mean .falseControl, ∃ r₁ ∈ mean .strong, ∃ r₂ ∈ mean .weak,
      ∃ r₃ ∈ mean .trueControl,
        RatingsMonotone [(r₀, support .falseControl), (r₁, support .strong),
          (r₂, support .weak), (r₃, support .trueControl)] := by
  decide +kernel

/-! ### Experiment 2 (§4) -/

/-- The compatible control is consistent with the sentence: a domain of individuals at `all`
verifies *every N was P* and *some N was Q*. -/
theorem everySome_and_compatible : ∃ m : Unit → SomeAllWorld, everySome m ∧ compatible m :=
  ⟨λ _ => .all, by decide⟩

/-- Once the strong inference is computed the compatible control is false, the local reading
excluding it, which is why Experiment 2 replaces the baseline by an inference task. -/
theorem not_compatible_of_everySomeNotAll {m : ι → SomeAllWorld} (h : everySomeNotAll m) :
    ¬ compatible m :=
  λ ⟨i, hi⟩ => (everySomeNotAll_iff.1 h).2 i hi

end Ronai2024
