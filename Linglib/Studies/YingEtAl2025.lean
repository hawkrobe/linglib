import Linglib.Fragments.English.Auxiliaries
import Linglib.Semantics.Attitudes.EpistemicThreshold
import Mathlib.Tactic.NormNum

/-!
# Ying et al. 2025: epistemic language as threshold semantics over credence

[ying-zhi-xuan-wong-mansinghka-tenenbaum-2025] ("Understanding
Epistemic Language with a Language-augmented Bayesian Theory of
Mind", TACL 13) interpret epistemic vocabulary — attitude verbs,
modal verbs, and modal adjectives — as threshold functions over agent
credence, with credence computed by Bayesian theory-of-mind inference
from observed actions. `EpistemicEntry` renders their lexical entries
(their Table 1): a credence threshold plus a factivity flag, with the
threshold values the paper's grid-search best fits against human
plausibility ratings in a Doors, Keys & Gems gridworld — the ordering
is the theoretical commitment, the specific values are empirical
fits. The Table 1 operator inventory (`knowsIf`, `uncertainIf`,
`knowsAbout`, `mostSup`, ...) and the scalar entailments
(`knows_entails_believes`, `must_entails_might`, ...) follow.

The bridge section connects the English modal fragment
(`English.Auxiliaries`) to the fitted entries: the Fragment's forms
map to entries, necessity-force modals carry strictly higher
thresholds than possibility-force modals, and the within-force scalar
ordering (must > should; may > might) captures differences binary
force cannot express. The final section records the divergence from
[herbstritt-franke-2019]'s independently fitted threshold for
*probably*.
-/

namespace YingEtAl2025

open EpistemicThreshold
open English.Auxiliaries
open Modality (ModalForce ModalFlavor ForceFlavor)

variable {E W X : Type*}

/-! ### The epistemic lexicon (Table 1) -/

/-- An epistemic lexical entry: the expression holds iff credence
    clears `θ`, with `factive` marking the additional truth
    requirement of *knows*. The lexical form is carried by the
    Fragment (`English.Auxiliaries`), not the entry. -/
structure EpistemicEntry where
  /-- Credence threshold. -/
  θ : ℚ
  /-- Truth requirement at the evaluation world (*knows* but not
      *believes*). -/
  factive : Bool := false
  deriving DecidableEq, Repr

namespace EpistemicEntry

/-! The fitted thresholds (Table 1(b)):
must = certain (0.95) > should (0.80) > believes (0.75) >
likely = uncertain (0.70) > unlikely (0.40) > may (0.30) >
might = could (0.20). `uncertain` and `unlikely` are
reversed-polarity: they hold when credence is strictly *below* the
threshold (`failsThreshold`). -/

def believes : EpistemicEntry := ⟨3/4, false⟩
def knows : EpistemicEntry := ⟨3/4, true⟩
def certain : EpistemicEntry := ⟨19/20, false⟩
def must : EpistemicEntry := ⟨19/20, false⟩
def should : EpistemicEntry := ⟨4/5, false⟩
def likely : EpistemicEntry := ⟨7/10, false⟩
def may : EpistemicEntry := ⟨3/10, false⟩
def might : EpistemicEntry := ⟨1/5, false⟩
def could : EpistemicEntry := ⟨1/5, false⟩
def uncertain : EpistemicEntry := ⟨7/10, false⟩
def unlikely : EpistemicEntry := ⟨2/5, false⟩

/-- The superlative multiplier α_most (Table 1(b)). -/
def α_most : ℚ := 3/2

/-- The threshold scale is strictly decreasing:
    must = certain > should > believes > likely = uncertain >
    unlikely > may > might = could. -/
theorem scale_sorted :
    [19/20, 4/5, 3/4, 7/10, 2/5, 3/10, (1 : ℚ)/5].IsChain (· > ·) := by
  refine .cons_cons (by norm_num) (.cons_cons (by norm_num)
    (.cons_cons (by norm_num) (.cons_cons (by norm_num)
      (.cons_cons (by norm_num) (.cons_cons (by norm_num)
        (.singleton _))))))

end EpistemicEntry

/-- Full evaluation of an entry: credence clears the threshold, and
    factive entries additionally require the complement at the
    evaluation world. -/
def holdsAt (cr : E → Set W → ℚ) (e : EpistemicEntry)
    (a : E) (φ : Set W) (w : W) : Prop :=
  meetsThreshold cr e.θ a φ ∧ (e.factive = true → w ∈ φ)

/-- A stronger entry — higher threshold, weaker factivity — entails a
    weaker one. Every pairwise entailment below is one application. -/
theorem holdsAt_mono_of_le {e₁ e₂ : EpistemicEntry}
    (hθ : e₁.θ ≤ e₂.θ) (hf : e₁.factive = true → e₂.factive = true)
    (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr e₂ a φ w → holdsAt cr e₁ a φ w :=
  fun ⟨hcr, hfact⟩ => ⟨le_trans hθ hcr, fun h₁ => hfact (hf h₁)⟩

/-- *knows* entails *believes*: same threshold, *knows* adds
    factivity. -/
theorem knows_entails_believes (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .knows a φ w → holdsAt cr .believes a φ w :=
  holdsAt_mono_of_le (le_refl (3/4 : ℚ)) (by decide) cr a φ w

/-- *knows* is veridical: knowledge entails truth. -/
theorem knows_is_veridical (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .knows a φ w → w ∈ φ :=
  fun ⟨_, h⟩ => h rfl

/-- *certain* entails *believes*. -/
theorem certain_entails_believes (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .certain a φ w → holdsAt cr .believes a φ w :=
  holdsAt_mono_of_le (by norm_num : (3 : ℚ)/4 ≤ 19/20) (by decide) cr a φ w

/-- *must* entails *should*. -/
theorem must_entails_should (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .must a φ w → holdsAt cr .should a φ w :=
  holdsAt_mono_of_le (by norm_num : (4 : ℚ)/5 ≤ 19/20) (by decide) cr a φ w

/-- *should* entails *likely*. -/
theorem should_entails_likely (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .should a φ w → holdsAt cr .likely a φ w :=
  holdsAt_mono_of_le (by norm_num : (7 : ℚ)/10 ≤ 4/5) (by decide) cr a φ w

/-- *must* entails *might*: necessity entails possibility on the
    threshold scale. -/
theorem must_entails_might (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .must a φ w → holdsAt cr .might a φ w :=
  holdsAt_mono_of_le (by norm_num : (1 : ℚ)/5 ≤ 19/20) (by decide) cr a φ w

/-- *believes* entails *may*. -/
theorem believes_entails_may (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) :
    holdsAt cr .believes a φ w → holdsAt cr .may a φ w :=
  holdsAt_mono_of_le (by norm_num : (3 : ℚ)/10 ≤ 3/4) (by decide) cr a φ w

/-! ### Structural operators (Table 1(a)) -/

/-- knows_if: the agent knows the answer to the polar question ?φ. -/
def knowsIf (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) : Prop :=
  holdsAt cr .knows a φ w ∨ holdsAt cr .knows a φᶜ w

/-- not_knows_that: φ is true but the agent does not believe it. -/
def notKnowsThat (cr : E → Set W → ℚ) (a : E) (φ : Set W) (w : W) : Prop :=
  ¬ meetsThreshold cr EpistemicEntry.believes.θ a φ ∧ w ∈ φ

/-- uncertain_if: the agent's credence in both alternatives falls
    below the *uncertain* threshold. -/
def uncertainIf (cr : E → Set W → ℚ) (a : E) (φ ψ : Set W) : Prop :=
  failsThreshold cr EpistemicEntry.uncertain.θ a φ ∧
  failsThreshold cr EpistemicEntry.uncertain.θ a ψ

/-- The strengthened superlative most_str: credence reaches α_most
    times the entry's threshold. -/
def mostStr (cr : E → Set W → ℚ) (e : EpistemicEntry) (a : E) (φ : Set W) : Prop :=
  EpistemicEntry.α_most * e.θ ≤ cr a φ

/-! ### Quantified operators (Table 1(a))

knows_about, certain_about, uncertain_about, and most_sup quantify
over a context-restricted entity domain, for sentences like "the
player knows which box has the key". -/

/-- knows_about: for some contextually relevant entity, the agent
    knows that φ holds of it. -/
def knowsAbout (cr : E → Set W → ℚ) (a : E)
    (C : X → Prop) (φ : X → Set W) (w : W) : Prop :=
  ∃ x, C x ∧ holdsAt cr .knows a (φ x) w

/-- certain_about: for some contextually relevant entity, credence in
    φ of it clears the *certain* threshold. -/
def certainAbout (cr : E → Set W → ℚ) (a : E)
    (C : X → Prop) (φ : X → Set W) : Prop :=
  ∃ x, C x ∧ meetsThreshold cr EpistemicEntry.certain.θ a (φ x)

/-- uncertain_about: for every contextually relevant entity, credence
    falls below the *uncertain* threshold — the universal dual of
    `certainAbout`'s existential. -/
def uncertainAbout (cr : E → Set W → ℚ) (a : E)
    (C : X → Prop) (φ : X → Set W) : Prop :=
  ∀ x, C x → failsThreshold cr EpistemicEntry.uncertain.θ a (φ x)

/-- most_sup: credence in φ of the object is at least credence in φ
    of every contextually relevant alternative. -/
def mostSup (cr : E → Set W → ℚ) (a : E)
    (o : X) (C : X → Prop) (φ : X → Set W) : Prop :=
  ∀ x, C x → cr a (φ x) ≤ cr a (φ o)

/-- A known witness gives knows_about. -/
theorem knowsAbout_of_holdsAt (cr : E → Set W → ℚ) (a : E)
    (C : X → Prop) (φ : X → Set W) (w : W) (x : X) (hC : C x)
    (h : holdsAt cr .knows a (φ x) w) : knowsAbout cr a C φ w :=
  ⟨x, hC, h⟩

/-- certain_about supplies a believed witness. -/
theorem certainAbout_entails_believes (cr : E → Set W → ℚ) (a : E)
    (C : X → Prop) (φ : X → Set W) (h : certainAbout cr a C φ) :
    ∃ x, C x ∧ meetsThreshold cr EpistemicEntry.believes.θ a (φ x) :=
  let ⟨x, hC, hcr⟩ := h
  ⟨x, hC, le_trans (by norm_num : (3 : ℚ)/4 ≤ 19/20) hcr⟩

/-- uncertain_about and certain_about are incompatible. -/
theorem uncertainAbout_contradicts_certainAbout (cr : E → Set W → ℚ)
    (a : E) (C : X → Prop) (φ : X → Set W)
    (h_unc : uncertainAbout cr a C φ) (h_cert : certainAbout cr a C φ) :
    False :=
  let ⟨x, hC, hcr⟩ := h_cert
  absurd (lt_of_le_of_lt (le_trans (by norm_num : (7 : ℚ)/10 ≤ 19/20) hcr)
    (h_unc x hC)) (lt_irrefl _)

/-! ### Fragment bridge: English modal auxiliaries -/

/-- Map an English modal auxiliary to its epistemic threshold entry;
    non-epistemic modals (deontic *shall*) have none. The mapping
    derives from the Fragment's `form` field. -/
def toEpistemicEntry (a : AuxEntry) : Option EpistemicEntry :=
  match a.form with
  | "must"   => some .must
  | "should" => some .should
  | "may"    => some .may
  | "might"  => some .might
  | "could"  => some .could
  | _        => none

/-- The epistemic force of a modal auxiliary, if it has an epistemic
    reading. -/
def epistemicForce (a : AuxEntry) : Option ModalForce :=
  let epMeanings := a.modalMeaning.filter (·.flavor == .epistemic)
  epMeanings.head?.map (·.force)

/-! Per-entry checks of the form → entry → threshold pipeline; these
break if the Fragment's form field or the fitted threshold changes. -/

theorem must_threshold : (toEpistemicEntry must).map (·.θ) = some (19/20 : ℚ) := rfl
theorem should_threshold : (toEpistemicEntry should).map (·.θ) = some (4/5 : ℚ) := rfl
theorem may_threshold : (toEpistemicEntry may).map (·.θ) = some (3/10 : ℚ) := rfl
theorem might_threshold : (toEpistemicEntry might).map (·.θ) = some (1/5 : ℚ) := rfl
theorem could_threshold : (toEpistemicEntry could).map (·.θ) = some (1/5 : ℚ) := rfl

/-- Non-epistemic modals have no threshold entry. -/
theorem shall_no_threshold : toEpistemicEntry shall = none := rfl

/-! ### Force–threshold consistency

Necessity-force epistemic modals carry strictly higher thresholds
than possibility-force ones — [kratzer-1981]'s algebraic force and
the fitted thresholds characterize the same items consistently. -/

theorem necessity_gt_possibility_must_might :
    EpistemicEntry.might.θ < EpistemicEntry.must.θ := by norm_num [EpistemicEntry.might, EpistemicEntry.must]

theorem necessity_gt_possibility_must_may :
    EpistemicEntry.may.θ < EpistemicEntry.must.θ := by norm_num [EpistemicEntry.may, EpistemicEntry.must]

theorem necessity_gt_possibility_should_might :
    EpistemicEntry.might.θ < EpistemicEntry.should.θ := by norm_num [EpistemicEntry.might, EpistemicEntry.should]

theorem necessity_gt_possibility_should_may :
    EpistemicEntry.may.θ < EpistemicEntry.should.θ := by norm_num [EpistemicEntry.may, EpistemicEntry.should]

theorem necessity_gt_possibility_should_could :
    EpistemicEntry.could.θ < EpistemicEntry.should.θ := by norm_num [EpistemicEntry.could, EpistemicEntry.should]

/-- The epistemic force of *must* is necessity (from the Fragment). -/
theorem must_is_necessity : epistemicForce must = some .necessity := rfl

/-- The epistemic force of *might* is possibility. -/
theorem might_is_possibility : epistemicForce might = some .possibility := rfl

/-- The epistemic force of *should* is weak necessity. -/
theorem should_is_weakNecessity : epistemicForce should = some .weakNecessity := rfl

/-- The epistemic force of *may* is possibility. -/
theorem may_is_possibility : epistemicForce may = some .possibility := rfl

/-! ### Within-force ordering

The □ > □w gap (must > should) is expressible by the three-way
`ModalForce`; the within-◇ gap (may > might) remains a purely scalar
difference. -/

/-- Strong necessity *must* outranks weak necessity *should*. -/
theorem must_gt_should : EpistemicEntry.should.θ < EpistemicEntry.must.θ := by
  norm_num [EpistemicEntry.should, EpistemicEntry.must]

/-- Among possibility modals, *may* outranks *might*. -/
theorem may_gt_might : EpistemicEntry.might.θ < EpistemicEntry.may.θ := by
  norm_num [EpistemicEntry.might, EpistemicEntry.may]

/-- *might* and *could* share a threshold. -/
theorem might_eq_could : EpistemicEntry.might.θ = EpistemicEntry.could.θ := rfl

/-! ### Divergence from Herbstritt & Franke 2019

[herbstritt-franke-2019] (Cognition 186) independently infer a
credence threshold for *probably* by Bayesian fitting against
urn-production data, reporting a posterior mean of 0.549 with 95% HDI
[0.500, 0.594] (their Table 6). The fitted threshold for *likely*
here (0.70) lies above that interval's upper bound, so the two
parameter-fitted accounts disagree at the 95%-credibility level.
Candidate explanations: lexical (*probably* ≠ *likely*), task (urn
production vs. theory-of-mind in a gridworld), or posterior
uncertainty (points vs. intervals). -/

/-- The fitted *likely* threshold exceeds the upper bound of
    [herbstritt-franke-2019]'s 95% HDI for *probably* (their
    Table 6). -/
theorem likely_above_hf_probably_hdi :
    (594 / 1000 : ℚ) < EpistemicEntry.likely.θ := by
  norm_num [EpistemicEntry.likely]

end YingEtAl2025
