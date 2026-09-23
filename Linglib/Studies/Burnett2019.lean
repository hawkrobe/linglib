module

public import Linglib.Pragmatics.SocialMeaning.Game
public import Linglib.Studies.Eckert2008
public import Linglib.Studies.Labov2012

/-!
# Burnett (2019): Signalling games, sociolinguistic variation and the construction of style

This file formalizes the social meaning games of [burnett-2019]. A speaker choosing between
*-ing* and *-in'* conveys something about the persona they are constructing, and the paper
takes that inference to be the equilibrium of a signalling game between a rational speaker and
listener: each variant is compatible with the personae sharing a property with its indexical
field, the listener infers a persona from the variant against a prior, and the speaker chooses
the variant that best conveys the persona they are after. Two kinds of variation come out of
the one model. A speaker holding a persona fixed changes variants as the context changes the
listener's prior, style shifting, here [labov-2012]'s Obama who prefers *-in'* at a barbecue and
*-ing* with the journalists; and a listener holding the variant fixed infers different personae
from different speakers, so that a strongly stereotyped speaker such as the paper's Bush
conveys nothing by the choice.

The property space is the example's two dimensions, competence and warmth, and the four
personae of example (6) are its maximal consistent sets (`personae_eq`). The meaning of a
variant is the lift of its indexical field to persona compatibility, and every prediction is an
instance of the game's speaker preferring the more informative variant (`prefers_iff`).

## Implementation notes

The contexts are priors over personae given as integer weights, read off the paper's tables as
the text describes them, more mass on the aloof personae at the barbecue and on the incompetent
ones with the journalists. The speaker is the softmax of the literal listener at the paper's
rationality 6 with no costs, and the pragmatic listener the Bayesian posterior against the
same prior; no normaliser is evaluated, preferences being compared with the pipeline's lemmas,
which cancel them. The persona selection of Section 4.3, a softmax over the speaker's values of
the personae and the marginal rate of a variant, is not represented.

## References

* [burnett-2019]
* [eckert-2008]
* [labov-2012]
* [lewis-1969]
* [podesva-reynolds-callier-baptiste-2015]
-/

@[expose] public section

namespace Burnett2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal
open SocialMeaning
open Eckert2008 (INGVariant)

/-! ### Personae and variants -/

/-- The social properties of example (5), two poles of competence and two of warmth. -/
inductive PersonaTrait where
  | competent
  | incompetent
  | friendly
  | aloof
  deriving DecidableEq

instance : Fintype PersonaTrait :=
  ⟨{.competent, .incompetent, .friendly, .aloof}, λ x => by cases x <;> simp⟩

/-- The dimension a trait is a pole of. -/
def PersonaTrait.dimension : PersonaTrait → Dimension
  | .competent | .incompetent => .competence
  | .friendly | .aloof => .warmth

/-- The property space of the example makes the two poles of each dimension incompatible. -/
def incompatible : SimpleGraph PersonaTrait where
  Adj p q := p ≠ q ∧ p.dimension = q.dimension
  symm := ⟨λ _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨λ _ h => h.1 rfl⟩

instance : DecidableRel incompatible.Adj := λ p q => inferInstanceAs (Decidable (p ≠ q ∧ _))

/-- A persona of the example is a maximal consistent set of its properties. -/
abbrev Persona := SocialMeaning.Persona incompatible

/-- The cool guy, competent and friendly. -/
def coolGuy : Persona := ⟨{.competent, .friendly}, by decide +kernel⟩

/-- The stern leader, competent and aloof. -/
def sternLeader : Persona := ⟨{.competent, .aloof}, by decide +kernel⟩

/-- The doofus, incompetent and friendly. -/
def doofus : Persona := ⟨{.incompetent, .friendly}, by decide +kernel⟩

/-- The arrogant asshole, incompetent and aloof. -/
def asshole : Persona := ⟨{.incompetent, .aloof}, by decide +kernel⟩

/-- The four personae of example (6) are the maximal consistent sets of the property space. -/
theorem personae_eq : (Finset.univ : Finset Persona) = {coolGuy, sternLeader, doofus, asshole} := by
  decide +kernel

instance : Nonempty Persona := ⟨coolGuy⟩

/-- The indexical fields of example (10) have *-ing* index competence and aloofness and *-in'*
incompetence and friendliness. -/
def ingEckertField : IndexicalField INGVariant PersonaTrait
  | .velar => {.competent, .aloof}
  | .apical => {.incompetent, .friendly}

/-- The grounded field of (ING), both fields being consistent. -/
def ingField : GroundedField INGVariant incompatible where
  indexes := ingEckertField
  isIndepSet := by intro v; cases v <;> decide

instance : MeasurableSpace INGVariant := ⊤
instance : MeasurableSingletonClass INGVariant :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass
instance : Nonempty INGVariant := ⟨.velar⟩

/-! ### The model

The literal listener conditions the persona prior on the personae the variant meets, the
speaker is its softmax at the paper's rationality 6 with no costs, and the pragmatic listener
inverts the speaker against the same prior. -/

/-- The literal listener conditions the prior on the variant's Eckert–Montague field. -/
noncomputable abbrev L0 (prior : Measure Persona) : Kernel INGVariant Persona :=
  literalListener prior ingField.indexation

/-- The speaker, the softmax of the literal listener at rationality 6 (p. 435), without costs. -/
noncomputable abbrev S1 (prior : Measure Persona) : Kernel Persona INGVariant :=
  speaker 6 (λ _ => 1) (L0 prior)

/-- The pragmatic listener inverts the speaker against the prior. -/
noncomputable abbrev L1 (prior : Measure Persona) [IsFiniteMeasure prior] :
    Kernel INGVariant Persona :=
  pragmaticListener 6 (λ _ => 1) (L0 prior) prior

/-! ### The extensions differ in one persona each

*-ing* meets every persona but the doofus and *-in'* every persona but the stern leader, so the
two extensions share the cool guy and the asshole and differ exactly in those two. That is the
whole of what the speaker's choice turns on. -/

theorem personae_velar : ingField.personae .velar = {coolGuy, sternLeader, asshole} := by
  decide +kernel

theorem personae_apical : ingField.personae .apical = {coolGuy, doofus, asshole} := by
  decide +kernel

/-- The persona each variant rules out, the doofus for *-ing* and the stern leader for *-in'*. -/
def excluded : INGVariant → Persona
  | .velar => doofus
  | .apical => sternLeader

private theorem measure_personae_velar (prior : Measure Persona) :
    prior ↑(ingField.personae .velar)
      = prior {coolGuy} + prior {asshole} + prior {sternLeader} := by
  rw [← sum_measure_singleton,
    show ingField.personae .velar = {coolGuy, asshole, sternLeader} by decide +kernel,
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton, ← add_assoc]

private theorem measure_personae_apical (prior : Measure Persona) :
    prior ↑(ingField.personae .apical) = prior {coolGuy} + prior {asshole} + prior {doofus} := by
  rw [← sum_measure_singleton,
    show ingField.personae .apical = {coolGuy, asshole, doofus} by decide +kernel,
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton, ← add_assoc]

/-- The extensions share the cool guy and the asshole, so one outweighs the other exactly when
the persona it keeps, the other's excluded one, outweighs the persona it rules out. -/
theorem measure_personae_lt_iff (prior : Measure Persona) [IsFiniteMeasure prior]
    {v₁ v₂ : INGVariant} (h : v₁ ≠ v₂) :
    prior ↑(ingField.personae v₂) < prior ↑(ingField.personae v₁)
      ↔ prior {excluded v₁} < prior {excluded v₂} := by
  have hfin : prior {coolGuy} + prior {asshole} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  cases v₁ <;> cases v₂
  · exact absurd rfl h
  · rw [measure_personae_apical, measure_personae_velar]
    exact ENNReal.add_lt_add_iff_left hfin
  · rw [measure_personae_velar, measure_personae_apical]
    exact ENNReal.add_lt_add_iff_left hfin
  · exact absurd rfl h

/-- For a persona either variant can convey, the speaker prefers the variant that rules out
more prior mass, the more informative one. Since the two variants differ only in ruling out the
doofus and the stern leader, the choice is settled by which of those two the context finds
likelier. -/
theorem prefers_iff (prior : Measure Persona) [IsFiniteMeasure prior] {p : Persona}
    {v₁ v₂ : INGVariant} (hne : v₁ ≠ v₂) (h₁ : p ∈ ingField.personae v₁)
    (h₂ : p ∈ ingField.personae v₂) (h0 : prior {p} ≠ 0) :
    (S1 prior p).real {v₁} < (S1 prior p).real {v₂}
      ↔ prior {excluded v₁} < prior {excluded v₂} := by
  rw [ingField.speaker_indexation_real_singleton_lt_iff prior (by norm_num) one_ne_zero
    ENNReal.one_ne_top h0 h₁ h₂, measure_personae_lt_iff prior hne]

/-! ### The contexts

A context is a prior over personae, given as integer weights read off the paper's tables as
the text describes them. -/

/-- At the barbecue the voters take Obama to be aloof (Table 2), so the aloof personae carry
more mass. -/
def casualWeight (π : Persona) : ℕ := if .aloof ∈ π.1 then 3 else 2

/-- With the journalists he is taken to be incompetent (Table 5). -/
def carefulWeight (π : Persona) : ℕ := if .incompetent ∈ π.1 then 3 else 2

/-- Rice is unfamiliar, so the listener's beliefs are uniform (Table 10). -/
def riceWeight : Persona → ℕ := λ _ => 1

/-- Pelosi is taken to be inarticulate (Table 13). -/
def pelosiWeight (π : Persona) : ℕ := if .incompetent ∈ π.1 then 9 else 1

/-- Bush is taken to be inarticulate and aloof, almost to certainty (Table 15). -/
def bushWeight (π : Persona) : ℕ := if .incompetent ∈ π.1 ∧ .aloof ∈ π.1 then 97 else 1

/-! ### Variant choice

Every prediction about the speaker is an instance of `prefers_iff`. -/

/-- At the barbecue the stern leader outweighs the doofus, so *-in'*, which rules the stern
leader out, is the more informative variant, and a persona either variant can convey is conveyed
by it. That is Obama's cool guy, predicted to use *-in'* about 69% of the time (p. 435). -/
theorem casual_coolGuy_prefers_apical :
    (S1 (priorOfWeights casualWeight) coolGuy).real {.velar}
      < (S1 (priorOfWeights casualWeight) coolGuy).real {.apical} :=
  (prefers_iff _ (by decide) (by decide +kernel) (by decide +kernel)
    (priorOfWeights_singleton_ne_zero _ (by decide +kernel))).mpr (by
      simp only [excluded, priorOfWeights_singleton]
      exact_mod_cast (by decide +kernel : casualWeight doofus < casualWeight sternLeader))

/-- The asshole, also conveyable either way, goes the same way at the barbecue. -/
theorem casual_asshole_prefers_apical :
    (S1 (priorOfWeights casualWeight) asshole).real {.velar}
      < (S1 (priorOfWeights casualWeight) asshole).real {.apical} :=
  (prefers_iff _ (by decide) (by decide +kernel) (by decide +kernel)
    (priorOfWeights_singleton_ne_zero _ (by decide +kernel))).mpr (by
      simp only [excluded, priorOfWeights_singleton]
      exact_mod_cast (by decide +kernel : casualWeight doofus < casualWeight sternLeader))

/-- Style shifting arises because with the journalists the doofus outweighs the stern leader
instead, so *-ing* is now the more informative variant and the same cool guy prefers it.
Neither the speaker nor the meaning has changed, only the context's prior, and with it which
variant rules more out. -/
theorem careful_coolGuy_prefers_velar :
    (S1 (priorOfWeights carefulWeight) coolGuy).real {.apical}
      < (S1 (priorOfWeights carefulWeight) coolGuy).real {.velar} :=
  (prefers_iff _ (by decide) (by decide +kernel) (by decide +kernel)
    (priorOfWeights_singleton_ne_zero _ (by decide +kernel))).mpr (by
      simp only [excluded, priorOfWeights_singleton]
      exact_mod_cast (by decide +kernel : carefulWeight sternLeader < carefulWeight doofus))

/-- Bulletproofing arises because Bush's listeners are almost certain he is inarticulate and
aloof, and the two personae the variants distinguish carry the same small weight, so neither
variant rules out more than the other, the speaker is indifferent, and variant choice conveys
nothing at all (pp. 444–445). -/
theorem bush_indifferent :
    ¬ (S1 (priorOfWeights bushWeight) asshole).real {.velar}
        < (S1 (priorOfWeights bushWeight) asshole).real {.apical} ∧
      ¬ (S1 (priorOfWeights bushWeight) asshole).real {.apical}
        < (S1 (priorOfWeights bushWeight) asshole).real {.velar} := by
  constructor <;>
    · rw [prefers_iff _ (by decide) (by decide +kernel) (by decide +kernel)
        (priorOfWeights_singleton_ne_zero _ (by decide +kernel))]
      simp only [excluded, priorOfWeights_singleton]
      exact_mod_cast (by decide +kernel : ¬ bushWeight _ < bushWeight _)

/-- The same holds of Rice, whose listeners have no prior beliefs to speak of. -/
theorem rice_indifferent :
    ¬ (S1 (priorOfWeights riceWeight) coolGuy).real {.velar}
        < (S1 (priorOfWeights riceWeight) coolGuy).real {.apical} ∧
      ¬ (S1 (priorOfWeights riceWeight) coolGuy).real {.apical}
        < (S1 (priorOfWeights riceWeight) coolGuy).real {.velar} := by
  constructor <;>
    · rw [prefers_iff _ (by decide) (by decide +kernel) (by decide +kernel)
        (priorOfWeights_singleton_ne_zero _ (by decide +kernel))]
      simp [excluded, riceWeight]

/-- The predicted direction is the observed one, the cool guy taking *-in'* at the barbecue
and *-ing* with the journalists while Obama's rate of *-in'* falls from the casual through the
careful to the formal style ([labov-2012]). -/
theorem matches_labov_direction :
    (S1 (priorOfWeights casualWeight) coolGuy).real {.velar}
        < (S1 (priorOfWeights casualWeight) coolGuy).real {.apical} ∧
      (S1 (priorOfWeights carefulWeight) coolGuy).real {.apical}
        < (S1 (priorOfWeights carefulWeight) coolGuy).real {.velar} ∧
      Labov2012.obama_ING.casual > Labov2012.obama_ING.careful ∧
      Labov2012.obama_ING.careful > Labov2012.obama_ING.formal :=
  ⟨casual_coolGuy_prefers_apical, careful_coolGuy_prefers_velar,
    Labov2012.obama_ING_monotone.1, Labov2012.obama_ING_monotone.2⟩

/-! ### Interpretation

What the listener does with a variant is the posterior over personae. A persona only one
variant can convey produces it with certainty, while a persona either can convey splits its
production between them, so the exclusive persona wins the posterior whenever the prior does
not favour the other. That is the shape of the paper's interpretation results: a released /t/
points at the stern leader, a flapped one at the doofus. -/

/-- The stern leader can only be conveyed by *-ing* and the doofus only by *-in'*, so each is
produced with certainty by the persona it is exclusive to. -/
theorem sternLeader_certain {w : Persona → ℕ} (hw : ∀ p, w p ≠ 0) :
    S1 (priorOfWeights w) sternLeader {.velar} = 1 ∧
      S1 (priorOfWeights w) doofus {.apical} = 1 :=
  ⟨ingField.speaker_indexation_eq_one_of_exclusive _ (by norm_num) one_ne_zero ENNReal.one_ne_top
      (priorOfWeights_singleton_ne_zero _ (hw _)) (by decide +kernel) (by decide +kernel),
    ingField.speaker_indexation_eq_one_of_exclusive _ (by norm_num) one_ne_zero ENNReal.one_ne_top
      (priorOfWeights_singleton_ne_zero _ (hw _)) (by decide +kernel) (by decide +kernel)⟩

/-- A variant gives no posterior mass to a persona it cannot convey, so hearing *-ing* rules
out the doofus and hearing *-in'* rules out the stern leader, whatever the listener believed
beforehand. -/
theorem L1_eq_zero_of_excluded {w : Persona → ℕ} (hw : ∀ p, w p ≠ 0) (v : INGVariant) :
    L1 (priorOfWeights w) v {excluded v} = 0 := by
  cases v
  · exact ingField.pragmaticListener_indexation_apply_singleton_of_not_meets _ (by norm_num)
      one_ne_zero ENNReal.one_ne_top (π' := coolGuy) (by decide +kernel) (by decide +kernel)
      (priorOfWeights_singleton_ne_zero _ (hw _))
  · exact ingField.pragmaticListener_indexation_apply_singleton_of_not_meets _ (by norm_num)
      one_ne_zero ENNReal.one_ne_top (π' := coolGuy) (by decide +kernel) (by decide +kernel)
      (priorOfWeights_singleton_ne_zero _ (hw _))

/-- With no prior beliefs the literal listener spreads its mass evenly over the three personae
the variant can convey, the game-theoretic literal listener of Definition 4.1. -/
theorem L0_uniform_apply {v : INGVariant} {p : Persona} (hp : p ∈ ingField.personae v) :
    L0 (priorOfWeights riceWeight) v {p} = 3⁻¹ := by
  have hcard : (ingField.personae v).card = 3 := by cases v <;> decide +kernel
  rw [ingField.literalListener_indexation_apply_singleton _ hp, priorOfWeights_singleton,
    ← sum_measure_singleton]
  simp only [priorOfWeights_singleton, riceWeight, Nat.cast_one, Finset.sum_const, nsmul_eq_mul,
    mul_one, hcard]
  norm_num

end Burnett2019
