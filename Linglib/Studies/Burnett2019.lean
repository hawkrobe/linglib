import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Studies.Eckert2008
import Linglib.Studies.Labov2012

/-!
# Burnett 2019: signalling games and the construction of style

A speaker choosing between *-ing* and *-in'*, or between a released and a flapped /t/, conveys
something about the persona they are projecting. This file formalizes the account on which that
inference is the equilibrium of a signalling game played by a rational speaker and listener: each
variant is compatible with the personae sharing a property in its indexical field, the listener
infers a persona from the variant, and the speaker chooses the variant that best conveys the
persona they are after.

Two kinds of variation come out of the one model. A speaker holding a persona fixed changes
variants as the context changes the prior over personae — style shifting, here the cool guy who
prefers *-in'* in the casual context and *-ing* in the careful one. And a listener holding the
variant fixed infers different personae from different speakers, since their priors differ: the
same released /t/ that makes one speaker sound like a stern leader leaves a strongly stereotyped
speaker's interpretation untouched.

The meaning function is not stipulated: it is the lift of each variant's indexical field to
persona compatibility, and `ingMeaning_eq_emMeaningMI` checks the two agree. The predictions are
exact comparisons of the listener and speaker distributions, not simulated values.

## Main definitions

* `ingField`, `ingMeaning` — the indexical fields of the two variants and the compatibility they
  induce
* `L0`, `S1`, `L1` — the literal listener, the speaker and the pragmatic listener at a prior
* `excluded` — the persona each variant rules out
* `casualWeight`, `carefulWeight`, `riceWeight`, `pelosiWeight`, `bushWeight` — the contexts

## Main results

* `prefers_iff` — the speaker prefers the variant that rules out more prior mass, so the choice
  between these two turns on the prior odds of the stern leader and the doofus
* `casual_coolGuy_prefers_apical`, `careful_coolGuy_prefers_velar` — style shifting, from the
  prior alone
* `bush_indifferent`, `rice_indifferent` — a prior that does not separate those two personae
  leaves the speaker indifferent, which is what bulletproofing amounts to
* `sternLeader_certain` — a persona only one variant can convey produces it with certainty
* `L1_eq_zero_of_incompatible` — a variant gives no posterior mass to a persona it cannot convey
* `L0_uniform_apply` — with no prior beliefs the literal listener is uniform over the extension
* `matches_labov_direction` — the predicted direction is the one [labov-2012] observed

## Implementation notes

Each context is a Rational Speech Act model over personae as states and variants as utterances, on
the measure/kernel pipeline of `Pragmatics/RSA/Basic.lean`: the speaker is the softmax of the
literal listener at rationality 6, the value the paper uses, and the pragmatic listener is the
Bayesian posterior against the same prior. Contexts are given as integer weights, since every stage
normalises and only the ratios matter. No normaliser is evaluated anywhere below: preferences are
compared with the register lemmas, which cancel them.

## References

* [burnett-2019]
* [eckert-2008]
* [labov-2012]
* [lewis-1969]
* [podesva-reynolds-callier-baptiste-2015]
-/

namespace Burnett2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal
open SocialMeaning
open SocialMeaning.EckertMontague
open Eckert2008 (INGVariant)

/-! ### Personae and variants -/

/-- Social properties (Burnett example (5)). Two bipolar dimensions:
    competence (competent/incompetent) and warmth (friendly/aloof). -/
inductive PersonaTrait where
  | competent | incompetent | friendly | aloof
  deriving DecidableEq, Repr

instance : Fintype PersonaTrait where
  elems := {.competent, .incompetent, .friendly, .aloof}
  complete := by intro x; cases x <;> simp

/-- The four personae: maximally consistent subsets (Burnett example (6)).
    Each selects one pole per dimension. -/
inductive Persona where
  | coolGuy      -- {competent, friendly}: the cool guy
  | sternLeader  -- {competent, aloof}: the stern leader
  | doofus       -- {incompetent, friendly}: the doofus
  | asshole      -- {incompetent, aloof}: the arrogant asshole
  deriving DecidableEq, Repr

instance : Fintype Persona where
  elems := {.coolGuy, .sternLeader, .doofus, .asshole}
  complete := by intro x; cases x <;> simp

-- INGVariant is imported from Studies/Eckert2008
-- Burnett's *-ing* = .velar, *-in'* = .apical

/-! ### Meaning from indexical fields -/

/-! Eckert fields (Burnett example (10)):
- [*-ing*] = {competent, aloof}
- [*-in'*] = {incompetent, friendly}

The meaning function is derived via the Montagovian Individual /
intersection semantics (Burnett footnote 14, Table 1): persona p is
compatible with variant v iff p shares at least one property with v's
Eckert field. -/

/-- The property space for Burnett's simplified example. -/
def burnettSpace : PropertySpace where
  Property := PersonaTrait
  incompatible
    | .competent, .incompetent | .incompetent, .competent => true
    | .friendly, .aloof | .aloof, .friendly => true
    | _, _ => false
  incomp_symm := by intro p q; cases p <;> cases q <;> simp
  incomp_irrefl := by intro p; cases p <;> rfl

/-- Persona membership as a `Finset`. -/
def Persona.toFinset : Persona → Finset PersonaTrait
  | .coolGuy     => {.competent, .friendly}
  | .sternLeader => {.competent, .aloof}
  | .doofus      => {.incompetent, .friendly}
  | .asshole     => {.incompetent, .aloof}

/-- Eckert fields for (ING) (Burnett example (10)). -/
def ingEckertField : INGVariant → Finset PersonaTrait
  | .velar => {.competent, .aloof}
  | .apical => {.incompetent, .friendly}

/-- The ING grounded field: both Eckert fields are consistent. -/
def ingField : GroundedField INGVariant burnettSpace where
  indexedProperties := ingEckertField
  indexed_consistent := by intro v; cases v <;> decide

/-- Meaning via the EM intersection lift: persona p is compatible with
    variant v iff p shares ≥1 property with v's Eckert field. -/
def ingMeaning : INGVariant → Persona → Bool
  | .velar,.coolGuy     => true   -- coolGuy has competent ∈ {comp, aloof}
  | .velar,.sternLeader => true   -- sternLeader has comp AND aloof
  | .velar,.asshole     => true   -- asshole has aloof ∈ {comp, aloof}
  | .velar,.doofus      => false  -- doofus has neither comp nor aloof
  | .apical,.coolGuy     => true   -- coolGuy has friendly ∈ {incomp, friendly}
  | .apical,.sternLeader => false  -- sternLeader has neither incomp nor friendly
  | .apical,.asshole     => true   -- asshole has incomp ∈ {incomp, friendly}
  | .apical,.doofus      => true   -- doofus has incomp AND friendly

/-- **Grounding theorem**: the inline meaning function equals the
    theory-layer `emMeaningMI` applied to the ING Eckert fields. -/
theorem ingMeaning_eq_emMeaningMI (v : INGVariant) (p : Persona) :
    ingMeaning v p = emMeaningMI ingField v p.toFinset := by
  cases v <;> cases p <;> decide

/-! ### The model

The literal listener conditions the persona prior on the variant's extension, the speaker is its
softmax at the paper's rationality 6 with no costs, and the pragmatic listener inverts the speaker
against the same prior. Nothing below evaluates a normaliser: preferences are compared with the
register lemmas, which cancel them. -/

instance : MeasurableSpace Persona := ⊤
instance : DiscreteMeasurableSpace Persona := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Persona := DiscreteMeasurableSpace.toMeasurableSingletonClass
instance : Nonempty Persona := ⟨.coolGuy⟩
instance : MeasurableSpace INGVariant := ⊤
instance : DiscreteMeasurableSpace INGVariant := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass INGVariant :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass
instance : Nonempty INGVariant := ⟨.velar⟩

/-- The personae a variant is compatible with. -/
def compatible (v : INGVariant) : Finset Persona := Finset.univ.filter fun p => ingMeaning v p

/-- The extension of a variant, as a set. -/
abbrev extension (v : INGVariant) : Set Persona := ↑(compatible v)

/-- The literal listener conditions the prior on the variant's extension. -/
noncomputable abbrev L0 (prior : Measure Persona) : Kernel INGVariant Persona :=
  literalListener prior fun v => (extension v).indicator 1

/-- The speaker, the softmax of the literal listener at rationality 6 (p. 435), without costs. -/
noncomputable abbrev S1 (prior : Measure Persona) : Kernel Persona INGVariant :=
  speaker 6 1 (L0 prior)

/-- The pragmatic listener inverts the speaker against the prior. -/
noncomputable abbrev L1 (prior : Measure Persona) [IsFiniteMeasure prior] :
    Kernel INGVariant Persona :=
  pragmaticListener 6 1 (L0 prior) prior

section Model

variable (prior : Measure Persona) [IsFiniteMeasure prior]

theorem L0_apply_singleton_le_one (v : INGVariant) (p : Persona) : L0 prior v {p} ≤ 1 := by
  by_cases h : p ∈ compatible v
  · exact literalListener_indicator_apply_singleton_le_one prior extension (measure_ne_top _ _)
      (Finset.mem_coe.mpr h)
  · rw [literalListener_indicator_apply_singleton_of_notMem prior extension
      (Finset.mem_coe.not.mpr h)]
    exact zero_le_one

variable {prior}

theorem L0_apply_singleton_ne_zero {v : INGVariant} {p : Persona} (hp : p ∈ compatible v)
    (h0 : prior {p} ≠ 0) : L0 prior v {p} ≠ 0 := by
  rw [literalListener_indicator_apply_singleton prior extension (Finset.mem_coe.mpr hp)]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h0

theorem S1_apply_singleton_ne_zero {v : INGVariant} {p : Persona} (hp : p ∈ compatible v)
    (h0 : prior {p} ≠ 0) : S1 prior p {v} ≠ 0 :=
  speaker_apply_singleton_ne_zero (by norm_num) (fun _ => one_ne_zero)
    (fun _ => ENNReal.one_ne_top) (fun v' => L0_apply_singleton_le_one prior v' p)
    (L0_apply_singleton_ne_zero hp h0)

theorem comp_S1_ne_zero {v : INGVariant} {p : Persona} (hp : p ∈ compatible v)
    (h0 : prior {p} ≠ 0) : (S1 prior ∘ₘ prior) {v} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ h0 (S1_apply_singleton_ne_zero hp h0)

end Model

/-! ### The extensions differ in one persona each

*-ing* is compatible with every persona but the doofus and *-in'* with every persona but the stern
leader, so the two extensions share the cool guy and the asshole and differ exactly in those two.
That is the whole of what the speaker's choice turns on. -/

theorem extension_velar : compatible .velar = {.coolGuy, .sternLeader, .asshole} := by decide

theorem extension_apical : compatible .apical = {.coolGuy, .doofus, .asshole} := by decide

private theorem measure_extension (prior : Measure Persona) (v : INGVariant) :
    prior (extension v) = ∑ p ∈ compatible v, prior {p} :=
  sum_measure_singleton.symm

private theorem mul_lt_mul_right_iff {a b c : ℝ≥0∞} (h0 : c ≠ 0) (hc : c ≠ ⊤) :
    a * c < b * c ↔ a < b := by
  refine ⟨fun h => ?_, fun h => ENNReal.mul_lt_mul_left h0 hc h⟩
  by_contra hab
  exact absurd h (not_lt.mpr (mul_le_mul' (not_lt.mp hab) le_rfl))

private theorem measure_extension_velar (prior : Measure Persona) :
    prior (extension .velar)
      = prior {(Persona.coolGuy)} + prior {(Persona.asshole)} + prior {(Persona.sternLeader)} := by
  rw [measure_extension, show compatible .velar = {.coolGuy, .asshole, .sternLeader} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, ← add_assoc]

private theorem measure_extension_apical (prior : Measure Persona) :
    prior (extension .apical)
      = prior {(Persona.coolGuy)} + prior {(Persona.asshole)} + prior {(Persona.doofus)} := by
  rw [measure_extension, show compatible .apical = {.coolGuy, .asshole, .doofus} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, ← add_assoc]

/-- The persona each variant rules out: *-ing* rules out the doofus, *-in'* the stern leader. -/
def excluded : INGVariant → Persona
  | .velar => .doofus
  | .apical => .sternLeader

/-- The extensions share the cool guy and the asshole, so one outweighs the other exactly when the
persona it keeps — the other's excluded one — outweighs the persona it rules out. -/
theorem measure_extension_lt_iff (prior : Measure Persona) [IsFiniteMeasure prior]
    {v₁ v₂ : INGVariant} (h : v₁ ≠ v₂) :
    prior (extension v₂) < prior (extension v₁) ↔ prior {excluded v₁} < prior {excluded v₂} := by
  have hfin : prior {(Persona.coolGuy)} + prior {(Persona.asshole)} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  cases v₁ <;> cases v₂
  · exact absurd rfl h
  · rw [measure_extension_apical, measure_extension_velar]
    exact ENNReal.add_lt_add_iff_left hfin
  · rw [measure_extension_velar, measure_extension_apical]
    exact ENNReal.add_lt_add_iff_left hfin
  · exact absurd rfl h

/-- **The speaker's choice.** For a persona either variant can convey, the speaker prefers the
variant that rules out more prior mass — the more informative one. Since the two variants differ
only in ruling out the doofus and the stern leader, the choice is settled by which of those two the
context finds likelier. -/
theorem prefers_iff (prior : Measure Persona) [IsFiniteMeasure prior] {p : Persona}
    {v₁ v₂ : INGVariant} (hne : v₁ ≠ v₂) (h₁ : p ∈ compatible v₁) (h₂ : p ∈ compatible v₂)
    (h0 : prior {p} ≠ 0) :
    (S1 prior p).real {v₁} < (S1 prior p).real {v₂}
      ↔ prior {excluded v₁} < prior {excluded v₂} := by
  refine Iff.trans (speaker_real_singleton_lt_iff (α := (6 : ℝ)) (by norm_num)
    (fun _ => ENNReal.one_ne_top) (fun v' => L0_apply_singleton_le_one prior v' p)
    ⟨v₁, mul_ne_zero (weight_rpow_ne_zero (by norm_num)
      (L0_apply_singleton_ne_zero h₁ h0)) one_ne_zero⟩) ?_
  simp only [mul_one]
  rw [ENNReal.rpow_lt_rpow_iff (by norm_num)]
  rw [literalListener_indicator_apply_singleton (u := v₁) (w := p) prior extension
    (Finset.mem_coe.mpr h₁)]
  rw [literalListener_indicator_apply_singleton (u := v₂) (w := p) prior extension
    (Finset.mem_coe.mpr h₂)]
  rw [mul_lt_mul_right_iff h0 (measure_ne_top _ _), ENNReal.inv_lt_inv,
    measure_extension_lt_iff prior hne]

/-! ### The contexts

A context is a prior over personae. Only the ratios matter — the literal listener, the speaker and
the posterior all normalise — so the tables' percentages are recorded as integer weights. -/

/-- The prior determined by a weighting of the personae. -/
noncomputable def priorOf (w : Persona → ℕ) : Measure Persona :=
  ∑ p, (w p : ℝ≥0∞) • Measure.dirac p

@[simp] theorem priorOf_singleton (w : Persona → ℕ) (p : Persona) : priorOf w {p} = w p :=
  Measure.sum_smul_dirac_apply_singleton (fun p => (w p : ℝ≥0∞)) p

instance (w : Persona → ℕ) : IsFiniteMeasure (priorOf w) :=
  ⟨by
    rw [priorOf, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun p _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

theorem priorOf_singleton_ne_zero {w : Persona → ℕ} {p : Persona} (h : w p ≠ 0) :
    priorOf w {p} ≠ 0 := by
  rw [priorOf_singleton]
  exact_mod_cast h

/-- At the barbecue the voters take Obama to be aloof (Table 2). -/
def casualWeight : Persona → ℕ
  | .sternLeader => 3
  | .coolGuy => 2
  | .asshole => 3
  | .doofus => 2

/-- With the journalists he is taken to be incompetent (Table 5). -/
def carefulWeight : Persona → ℕ
  | .sternLeader => 2
  | .coolGuy => 2
  | .asshole => 3
  | .doofus => 3

/-- Rice is unfamiliar, so the listener's beliefs are uniform (Table 10). -/
def riceWeight : Persona → ℕ := fun _ => 1

/-- Pelosi is taken to be inarticulate (Table 13). -/
def pelosiWeight : Persona → ℕ
  | .sternLeader => 1
  | .coolGuy => 1
  | .asshole => 9
  | .doofus => 9

/-- Bush is taken to be inarticulate and aloof, almost to certainty (Table 15). -/
def bushWeight : Persona → ℕ
  | .sternLeader => 1
  | .coolGuy => 1
  | .asshole => 97
  | .doofus => 1

/-! ### Variant choice

Every prediction about the speaker is an instance of `prefers_iff`. -/

/-- At the barbecue the stern leader outweighs the doofus, so *-in'* — which rules the stern leader
out — is the more informative variant, and a persona either variant can convey is conveyed by it.
That is Obama's cool guy, predicted to use *-in'* about 69% of the time (p. 435). -/
theorem casual_coolGuy_prefers_apical :
    (S1 (priorOf casualWeight) .coolGuy).real {.velar}
      < (S1 (priorOf casualWeight) .coolGuy).real {.apical} :=
  (prefers_iff _ (by decide) (by decide) (by decide)
    (priorOf_singleton_ne_zero (by decide))).mpr (by
      simp only [excluded, priorOf_singleton, casualWeight]
      exact_mod_cast (by norm_num : (2 : ℕ) < 3))

/-- The asshole, also conveyable either way, goes the same way at the barbecue. -/
theorem casual_asshole_prefers_apical :
    (S1 (priorOf casualWeight) .asshole).real {.velar}
      < (S1 (priorOf casualWeight) .asshole).real {.apical} :=
  (prefers_iff _ (by decide) (by decide) (by decide)
    (priorOf_singleton_ne_zero (by decide))).mpr (by
      simp only [excluded, priorOf_singleton, casualWeight]
      exact_mod_cast (by norm_num : (2 : ℕ) < 3))

/-- **Style shifting.** With the journalists the doofus outweighs the stern leader instead, so
*-ing* is now the more informative variant and the same cool guy prefers it. Neither the speaker
nor the meaning has changed: the context's prior has, and with it which variant rules more out. -/
theorem careful_coolGuy_prefers_velar :
    (S1 (priorOf carefulWeight) .coolGuy).real {.apical}
      < (S1 (priorOf carefulWeight) .coolGuy).real {.velar} :=
  (prefers_iff _ (by decide) (by decide) (by decide)
    (priorOf_singleton_ne_zero (by decide))).mpr (by
      simp only [excluded, priorOf_singleton, carefulWeight]
      exact_mod_cast (by norm_num : (2 : ℕ) < 3))

/-- **Bulletproofing.** Bush's listeners are almost certain he is inarticulate and aloof, and the
two personae the variants distinguish carry the same small weight, so neither variant rules out
more than the other and the speaker is indifferent: variant choice conveys nothing at all
(pp. 444–445). -/
theorem bush_indifferent :
    ¬ (S1 (priorOf bushWeight) .asshole).real {.velar}
        < (S1 (priorOf bushWeight) .asshole).real {.apical} ∧
      ¬ (S1 (priorOf bushWeight) .asshole).real {.apical}
        < (S1 (priorOf bushWeight) .asshole).real {.velar} := by
  constructor <;>
    · rw [prefers_iff _ (by decide) (by decide) (by decide)
        (priorOf_singleton_ne_zero (by decide))]
      simp [excluded, bushWeight]

/-- The same holds of Rice, whose listeners have no prior beliefs to speak of. -/
theorem rice_indifferent :
    ¬ (S1 (priorOf riceWeight) .coolGuy).real {.velar}
        < (S1 (priorOf riceWeight) .coolGuy).real {.apical} ∧
      ¬ (S1 (priorOf riceWeight) .coolGuy).real {.apical}
        < (S1 (priorOf riceWeight) .coolGuy).real {.velar} := by
  constructor <;>
    · rw [prefers_iff _ (by decide) (by decide) (by decide)
        (priorOf_singleton_ne_zero (by decide))]
      simp [excluded, riceWeight]

/-- The predicted direction is the observed one: the cool guy takes *-in'* at the barbecue and
*-ing* with the journalists, and Obama's rate of *-in'* falls from the casual through the careful
to the formal style ([labov-2012]). -/
theorem matches_labov_direction :
    (S1 (priorOf casualWeight) .coolGuy).real {.velar}
        < (S1 (priorOf casualWeight) .coolGuy).real {.apical} ∧
      (S1 (priorOf carefulWeight) .coolGuy).real {.apical}
        < (S1 (priorOf carefulWeight) .coolGuy).real {.velar} ∧
      Labov2012.obama_ING.casual > Labov2012.obama_ING.careful ∧
      Labov2012.obama_ING.careful > Labov2012.obama_ING.formal :=
  ⟨casual_coolGuy_prefers_apical, careful_coolGuy_prefers_velar,
    Labov2012.obama_ING_monotone.1, Labov2012.obama_ING_monotone.2⟩

/-! ### Interpretation

What the listener does with a variant is the posterior over personae. A persona only one variant
can convey produces it with certainty, while a persona either can convey splits its production
between them, so the exclusive persona wins the posterior whenever the prior does not favour the
other. That is the shape of the paper's interpretation results: a released /t/ points at the stern
leader, a flapped one at the doofus. -/

section Interpretation

/-- A persona only one variant can convey produces it with certainty. -/
theorem S1_eq_one_of_exclusive {w : Persona → ℕ} (hw : ∀ p, w p ≠ 0) {p : Persona}
    {v : INGVariant} (hp : p ∈ compatible v) (hother : ∀ v' ≠ v, p ∉ compatible v') :
    S1 (priorOf w) p {v} = 1 :=
  speaker_literalListener_indicator_eq_one (α := (6 : ℝ)) (cost := 1) (u := v) (w := p)
    (by norm_num) one_ne_zero ENNReal.one_ne_top (priorOf w) extension
    (priorOf_singleton_ne_zero (hw p)) (Finset.mem_coe.mpr hp)
    fun v' hv' => Finset.mem_coe.not.mpr (hother v' hv')

/-- The stern leader can only be conveyed by *-ing*, and the doofus only by *-in'*: each is
produced with certainty by the persona it is exclusive to. -/
theorem sternLeader_certain {w : Persona → ℕ} (hw : ∀ p, w p ≠ 0) :
    S1 (priorOf w) .sternLeader {.velar} = 1 ∧ S1 (priorOf w) .doofus {.apical} = 1 :=
  ⟨S1_eq_one_of_exclusive hw (by decide) (by decide),
    S1_eq_one_of_exclusive hw (by decide) (by decide)⟩

/-- A variant gives no posterior mass to a persona it cannot convey: hearing *-ing* rules out the
doofus and hearing *-in'* rules out the stern leader, whatever the listener believed beforehand. -/
theorem L1_eq_zero_of_incompatible {w : Persona → ℕ} (hw : ∀ p, w p ≠ 0) {p q : Persona}
    {v : INGVariant} (hp : p ∉ compatible v) (hq : q ∈ compatible v) :
    L1 (priorOf w) v {p} = 0 := by
  show ((S1 (priorOf w))†(priorOf w)) v {p} = 0
  rw [posterior_apply_singleton _ _
      (comp_S1_ne_zero hq (priorOf_singleton_ne_zero (hw q))),
    speaker_apply_singleton_eq_zero (by norm_num)
      (literalListener_indicator_apply_singleton_of_notMem (priorOf w) extension
        (Finset.mem_coe.not.mpr hp))]
  simp

/-- With no prior beliefs the literal listener spreads its mass evenly over the three personae the
variant can convey — the game-theoretic literal listener of Definition 4.1. -/
theorem L0_uniform_apply {v : INGVariant} {p : Persona} (hp : p ∈ compatible v) :
    L0 (priorOf riceWeight) v {p} = 3⁻¹ := by
  have hcard : (compatible v).card = 3 := by cases v <;> decide
  rw [literalListener_indicator_apply_singleton (u := v) (w := p) (priorOf riceWeight) extension
    (Finset.mem_coe.mpr hp), measure_extension]
  simp only [priorOf_singleton, riceWeight, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    hcard]
  norm_num

end Interpretation

end Burnett2019
