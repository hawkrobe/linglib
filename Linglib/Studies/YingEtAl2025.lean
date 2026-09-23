module

public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Semantics.Attitudes.EpistemicThreshold
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Linglib.Data.Examples.YingEtAl2025

/-!
# Ying, Zhi-Xuan, Wong, Mansinghka & Tenenbaum (2025): Understanding Epistemic Language

This file formalizes the epistemic language of thought of
[ying-zhi-xuan-wong-mansinghka-tenenbaum-2025], a degree-based semantics for attitude verbs,
modal verbs and modal adjectives grounded in the probability an agent assigns to a formula.
Each expression compares that probability with a lexical threshold (`Thresholds`,
`meetsThreshold`): *believes*, *certain*, the modal verbs from *could* to *must*, and
*likely* hold when the probability clears their threshold; *uncertain* and *unlikely* when it
falls below; *knows that* is belief plus truth, *knows if* knowledge of the question, and the
*about* operators quantify over a contextually restricted domain (`knowsAbout`,
`certainAbout`, `uncertainAbout`). A modal under *believes* is lowered to a comparison with
the modal's own threshold rather than the belief threshold (`believesModal_might`).
Comparatives and superlatives compare degrees, and the strengthened superlative scales the
threshold by a multiplier (`mostStr`). The entailments among the expressions follow from the
ordering of the thresholds alone (`Thresholds.Ordered`, `must_entails_might`,
`certainAbout_believes`, `uncertainAbout_certainAbout`), and the fitted values of the paper's
lexicon respect that ordering (`fitted`, `fitted_ordered`). The modal verbs' forces in the
English fragment agree with the ordering: no possibility modal carries a higher threshold
than a necessity modal (`force_threshold_le`).

## Implementation notes

The probabilities are the agent's credences as a function of agent and proposition, as in
the threshold substrate; the Bayesian theory-of-mind inference that produces them from
observed actions is not modelled. The fitted thresholds and the literature-derived initial
values of the paper's second appendix are recorded as instances of `Thresholds`, and the
theorems are stated for any thresholds satisfying the ordering.

## References

* [ying-zhi-xuan-wong-mansinghka-tenenbaum-2025]
* [lassiter-goodman-2017]
* [hintikka-1962]
-/

@[expose] public section

namespace YingEtAl2025

open EpistemicThreshold English.Auxiliaries Modality

variable {E W X : Type*}

/-! ### Thresholds -/

/-- The probability thresholds of the epistemic lexicon and the multiplier of the
strengthened superlative. -/
structure Thresholds where
  believes : ℚ
  certain : ℚ
  uncertain : ℚ
  likely : ℚ
  unlikely : ℚ
  could : ℚ
  might : ℚ
  may : ℚ
  should : ℚ
  must : ℚ
  most : ℚ
  deriving DecidableEq, Repr

/-- The ordering of the thresholds the entailments rest on: the modal verbs form a scale from
*could* to *must*, *likely* sits between *may* and *should*, belief lies above *likely* and
below *certain*, and the reversed-polarity thresholds lie below *certain*. -/
structure Thresholds.Ordered (Θ : Thresholds) : Prop where
  could_might : Θ.could ≤ Θ.might
  might_may : Θ.might ≤ Θ.may
  may_likely : Θ.may ≤ Θ.likely
  likely_believes : Θ.likely ≤ Θ.believes
  believes_should : Θ.believes ≤ Θ.should
  should_must : Θ.should ≤ Θ.must
  must_certain : Θ.must ≤ Θ.certain
  unlikely_uncertain : Θ.unlikely ≤ Θ.uncertain
  uncertain_certain : Θ.uncertain ≤ Θ.certain
  one_le_most : 1 ≤ Θ.most

/-- The thresholds fitted against human plausibility ratings. -/
def fitted : Thresholds :=
  ⟨3/4, 19/20, 7/10, 7/10, 2/5, 1/5, 1/5, 3/10, 4/5, 19/20, 3/2⟩

/-- The initial thresholds derived from the literature, before fitting. -/
def initial : Thresholds :=
  ⟨3/4, 19/20, 1/2, 3/5, 2/5, 1/5, 1/5, 3/10, 4/5, 19/20, 3/2⟩

theorem fitted_ordered : fitted.Ordered := by
  constructor <;> norm_num [fitted]

theorem initial_ordered : initial.Ordered := by
  constructor <;> norm_num [initial]

/-! ### The epistemic expressions -/

variable (Θ : Thresholds) (Pr : E → Set W → ℚ)

/-- *A believes that φ*. -/
def believes (a : E) (φ : Set W) : Prop := meetsThreshold Pr Θ.believes a φ

/-- *A believes M*, for a modal claim `M`: the modal applied to the agent. -/
def believesModal (a : E) (M : E → Prop) : Prop := M a

/-- *A knows that φ*: belief and truth. -/
def knowsThat (a : E) (φ : Set W) (w : W) : Prop := believes Θ Pr a φ ∧ w ∈ φ

/-- *A knows if φ*: knowledge of the answer. -/
def knowsIf (a : E) (φ : Set W) (w : W) : Prop :=
  knowsThat Θ Pr a φ w ∨ knowsThat Θ Pr a φᶜ w

/-- *A knows about φ*: some relevant entity of which the agent knows φ. -/
def knowsAbout (a : E) (C : X → Prop) (φ : X → Set W) (w : W) : Prop :=
  ∃ x, C x ∧ knowsThat Θ Pr a (φ x) w

/-- *A does not know that φ*: φ holds but is not believed. -/
def notKnowsThat (a : E) (φ : Set W) (w : W) : Prop := ¬ believes Θ Pr a φ ∧ w ∈ φ

/-- *A is certain that φ*. -/
def certainThat (a : E) (φ : Set W) : Prop := meetsThreshold Pr Θ.certain a φ

/-- *A is certain about φ*: some relevant entity of which the agent is certain. -/
def certainAbout (a : E) (C : X → Prop) (φ : X → Set W) : Prop :=
  ∃ x, C x ∧ certainThat Θ Pr a (φ x)

/-- *A is uncertain if φ or ψ*: neither alternative reaches the threshold. -/
def uncertainIf (a : E) (φ ψ : Set W) : Prop :=
  failsThreshold Pr Θ.uncertain a φ ∧ failsThreshold Pr Θ.uncertain a ψ

/-- *A is uncertain about φ*: no relevant entity reaches the threshold. -/
def uncertainAbout (a : E) (C : X → Prop) (φ : X → Set W) : Prop :=
  ∀ x, C x → failsThreshold Pr Θ.uncertain a (φ x)

/-- The modal verbs and adjective, each a property of agents. -/
def could (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.could a φ
def might (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.might a φ
def may (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.may a φ
def should (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.should a φ
def must (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.must a φ
def likely (φ : Set W) (a : E) : Prop := meetsThreshold Pr Θ.likely a φ
def unlikely (φ : Set W) (a : E) : Prop := failsThreshold Pr Θ.unlikely a φ

/-- The degree of *likely*: the probability itself. -/
def degree (a : E) (φ : Set W) : ℚ := Pr a φ

/-- *φ is more likely than ψ*. -/
def more (φ ψ : Set W) (a : E) : Prop := degree Pr a ψ < degree Pr a φ

/-- *φ of o is most likely* among the relevant alternatives. -/
def mostSup (o : X) (C : X → Prop) (φ : X → Set W) (a : E) : Prop :=
  ∀ x, C x → degree Pr a (φ x) ≤ degree Pr a (φ o)

/-- The strengthened superlative: the degree reaches the multiplied threshold. -/
def mostStr (θ : ℚ) (φ : Set W) (a : E) : Prop := Θ.most * θ ≤ degree Pr a φ

/-! ### Entailments from the ordering -/

variable {Θ Pr}

/-- A higher threshold entails a lower one. -/
theorem meets_of_meets_of_le {θ₁ θ₂ : ℚ} (h : θ₁ ≤ θ₂) {a : E} {φ : Set W}
    (hm : meetsThreshold Pr θ₂ a φ) : meetsThreshold Pr θ₁ a φ :=
  h.trans hm

/-- Knowledge entails belief. -/
theorem knowsThat_believes {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) :
    believes Θ Pr a φ := h.1

/-- Knowledge is veridical. -/
theorem knowsThat_mem {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) : w ∈ φ := h.2

/-- Knowing that answers the question. -/
theorem knowsIf_of_knowsThat {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) :
    knowsIf Θ Pr a φ w := Or.inl h

/-- Belief and not knowing exclude one another. -/
theorem not_notKnowsThat_of_believes {a : E} {φ : Set W} {w : W} (h : believes Θ Pr a φ) :
    ¬ notKnowsThat Θ Pr a φ w := λ hn => hn.1 h

/-- A modal under *believes* is lowered to the modal's own threshold. -/
theorem believesModal_might (a : E) (φ : Set W) :
    believesModal (E := E) a (might Θ Pr φ) ↔ meetsThreshold Pr Θ.might a φ := Iff.rfl

/-- *must* entails *should*, *likely*, *may*, *might* and *could* under the ordering. -/
theorem must_entails_might (h : Θ.Ordered) {φ : Set W} {a : E} (hm : must Θ Pr φ a) :
    might Θ Pr φ a :=
  meets_of_meets_of_le (h.might_may.trans (h.may_likely.trans (h.likely_believes.trans
    (h.believes_should.trans h.should_must)))) hm

theorem must_entails_should (h : Θ.Ordered) {φ : Set W} {a : E} (hm : must Θ Pr φ a) :
    should Θ Pr φ a :=
  meets_of_meets_of_le h.should_must hm

theorem should_entails_likely (h : Θ.Ordered) {φ : Set W} {a : E} (hm : should Θ Pr φ a) :
    likely Θ Pr φ a :=
  meets_of_meets_of_le (h.likely_believes.trans h.believes_should) hm

theorem might_entails_could (h : Θ.Ordered) {φ : Set W} {a : E} (hm : might Θ Pr φ a) :
    could Θ Pr φ a :=
  meets_of_meets_of_le h.could_might hm

/-- Certainty entails belief. -/
theorem certainThat_believes (h : Θ.Ordered) {a : E} {φ : Set W} (hc : certainThat Θ Pr a φ) :
    believes Θ Pr a φ :=
  meets_of_meets_of_le (h.believes_should.trans (h.should_must.trans h.must_certain)) hc

/-- Certainty about supplies a believed witness. -/
theorem certainAbout_believes (h : Θ.Ordered) {a : E} {C : X → Prop} {φ : X → Set W}
    (hc : certainAbout Θ Pr a C φ) : ∃ x, C x ∧ believes Θ Pr a (φ x) :=
  let ⟨x, hC, hx⟩ := hc
  ⟨x, hC, certainThat_believes h hx⟩

/-- Uncertainty about and certainty about are incompatible. -/
theorem uncertainAbout_certainAbout (h : Θ.Ordered) {a : E} {C : X → Prop} {φ : X → Set W}
    (hu : uncertainAbout Θ Pr a C φ) (hc : certainAbout Θ Pr a C φ) : False :=
  let ⟨x, hC, hx⟩ := hc
  absurd (lt_of_le_of_lt (h.uncertain_certain.trans hx) (hu x hC)) (lt_irrefl _)

/-- The strengthened superlative entails the plain threshold reading. -/
theorem mostStr_meets (h : Θ.Ordered) {θ : ℚ} (hθ : 0 ≤ θ) {φ : Set W} {a : E}
    (hm : mostStr Θ Pr θ φ a) : meetsThreshold Pr θ a φ :=
  le_trans (le_mul_of_one_le_left hθ h.one_le_most) hm

/-- The superlative holds of a maximal alternative. -/
theorem mostSup_of_forall {o : X} {C : X → Prop} {φ : X → Set W} {a : E}
    (h : ∀ x, C x → Pr a (φ x) ≤ Pr a (φ o)) : mostSup Pr o C φ a := h

/-! ### The English modal verbs -/

/-- The modal verbs of the lexicon. -/
inductive ModalVerb where
  | could
  | might
  | may
  | should
  | must
  deriving DecidableEq, Repr, Fintype

/-- The threshold of each modal verb. -/
def ModalVerb.threshold (Θ : Thresholds) : ModalVerb → ℚ
  | .could => Θ.could
  | .might => Θ.might
  | .may => Θ.may
  | .should => Θ.should
  | .must => Θ.must

/-- The English auxiliary of each modal verb. -/
def ModalVerb.aux : ModalVerb → Auxiliary
  | .could => English.Auxiliaries.could
  | .might => English.Auxiliaries.might
  | .may => English.Auxiliaries.may
  | .should => English.Auxiliaries.should
  | .must => English.Auxiliaries.must

/-- The epistemic forces of each modal verb, read off the fragment. -/
def ModalVerb.forces (v : ModalVerb) : Finset ModalForce := v.aux.toModalItem.forcesOf .epistemic

theorem forces_might : ModalVerb.might.forces = {.possibility} := by decide

theorem forces_must : ModalVerb.must.forces = {.necessity} := by decide

theorem forces_should : ModalVerb.should.forces = {.weakNecessity} := by decide

/-- Under the ordering, a possibility modal never carries a higher threshold than a modal of
necessity or weak necessity. -/
theorem force_threshold_le (h : Θ.Ordered) {v v' : ModalVerb}
    (hv : v.forces = {.possibility}) (hv' : v'.forces ≠ {.possibility}) :
    v.threshold Θ ≤ v'.threshold Θ := by
  have hc := h.could_might; have hm := h.might_may; have hl := h.may_likely
  have hb := h.likely_believes; have hs := h.believes_should; have hu := h.should_must
  cases v <;> cases v' <;>
    first
      | exact absurd hv (by decide)
      | exact absurd (by decide) hv'
      | (simp only [ModalVerb.threshold]; linarith)

end YingEtAl2025
