module

public import Linglib.Pragmatics.SocialMeaning.Game
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Henderson and McCready (2024): Signaling without Saying

This file formalizes the social meaning games for identifying dogwhistles of Chapter 4 of
[henderson-mccready-2024]. A dogwhistle sends one message to an in-group and another to an
out-group, and the book models it by loosening [burnett-2019]'s social meaning games in two
ways. A listener holds, besides a prior over personae, a likelihood of each message given each
persona, so that the literal listener is Bayes' rule over that likelihood and Burnett's
indexation is the lexicalized special case (`L0`). And the speaker's social utility for a
message toward a listener sums, over the personae, the log posterior with the speaker's and the
listener's values of the persona weighted by the posterior (`socialUtility`); the utility toward
an audience is the sum over its listeners (`groupUtility`), and the speaker is the softmax of
the utility. A message is a dogwhistle to a population when the likelihood listeners assign it
correlates with their approval of the personae it signals, so that those who hear the whistle
and approve reward it, those who hear it and disapprove punish it, and those who do not hear it
react to its innocuous reading alone.

The case study has Jill Stein choosing between *big pharma*, which savvy listeners tie to the
anti-vaxxer persona and unsavvy ones read as merely anti-corporate, and *corporate scientists*.
A savvy pro-vaxxer prefers that she disavow, an unsavvy one prefers it too but by less, and an
anti-vaxxer prefers the dogwhistle (`savvyProVax_prefers_disavowal`,
`unsavvyProVax_prefers_disavowal`, `antiVax_prefers_dogwhistle`), so a pro-vaxxer audience
calls for the disavowal and an anti-vaxxer audience for the dogwhistle, and a mixed audience
turns on its composition (`dogwhistle_optimal_iff`).

## Implementation notes

The book's percentages are recorded as integer weights, since the literal listener normalizes,
and the log of a zero posterior is zero, which is mathlib's convention and matches the book's
sum over the personae consistent with the message. The orderings of the utilities are proved
symbolically from the exact posteriors, bounding the log terms by the quadratic lower bound
on the exponential. The parameter exploration of Section 4.3 and the enriching dogwhistles of
Chapter 5 are not represented.

## References

* [henderson-mccready-2024]
* [burnett-2019]
* [henderson-mccready-2018]
-/

@[expose] public section

namespace HendersonMcCready2024

open SocialMeaning MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### Personae -/

/-- The two issues of the case study. -/
inductive Issue where
  | vaccines
  | corporations
  deriving DecidableEq

/-- The social properties, a stance on each issue. -/
inductive Trait where
  | proVax
  | antiVax
  | proCorporate
  | antiCorporate
  deriving DecidableEq

instance : Fintype Trait :=
  ⟨{.proVax, .antiVax, .proCorporate, .antiCorporate}, λ t => by cases t <;> simp⟩

/-- The issue a trait is a stance on. -/
def Trait.issue : Trait → Issue
  | .proVax | .antiVax => .vaccines
  | .proCorporate | .antiCorporate => .corporations

/-- The two stances on one issue are incompatible. -/
def incompatible : SimpleGraph Trait where
  Adj p q := p ≠ q ∧ p.issue = q.issue
  symm := ⟨λ _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨λ _ h => h.1 rfl⟩

instance : DecidableRel incompatible.Adj := λ p q => inferInstanceAs (Decidable (p ≠ q ∧ _))

/-- A persona takes a stance on each issue. -/
abbrev Persona := SocialMeaning.Persona incompatible

def proVaxProCorp : Persona := ⟨{.proVax, .proCorporate}, by decide +kernel⟩
def proVaxAntiCorp : Persona := ⟨{.proVax, .antiCorporate}, by decide +kernel⟩
def antiVaxProCorp : Persona := ⟨{.antiVax, .proCorporate}, by decide +kernel⟩
def antiVaxAntiCorp : Persona := ⟨{.antiVax, .antiCorporate}, by decide +kernel⟩

theorem personae_eq :
    (Finset.univ : Finset Persona) =
      {proVaxProCorp, proVaxAntiCorp, antiVaxProCorp, antiVaxAntiCorp} := by
  decide +kernel

/-! ### Messages, listeners and their beliefs -/

/-- The two messages are the dogwhistle and the disavowal. -/
inductive Message where
  | bigPharma
  | corporateScientists
  deriving DecidableEq, Fintype

instance : MeasurableSpace Message := ⊤
instance : MeasurableSingletonClass Message :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The three kinds of listener in the audience. -/
inductive ListenerType where
  | savvyAntiVax
  | savvyProVax
  | unsavvyProVax
  deriving DecidableEq, Fintype

/-- A listener is savvy when they know the anti-vaxxer discourse. -/
def ListenerType.Savvy : ListenerType → Prop
  | .unsavvyProVax => False
  | _ => True

instance : DecidablePred ListenerType.Savvy
  | .savvyAntiVax => inferInstanceAs (Decidable True)
  | .savvyProVax => inferInstanceAs (Decidable True)
  | .unsavvyProVax => inferInstanceAs (Decidable False)

/-- Every listener holds the same prior about Stein, probably anti-corporate, pro- or anti-vax
equally, and pro-corporate only if anti-vax, in the proportions 8 : 8 : 3 : 1. -/
def priorWeight (π : Persona) : ℕ :=
  if .antiCorporate ∈ π.1 then 8 else if .antiVax ∈ π.1 then 3 else 1

/-- A listener's likelihood of each message given each persona, in twentieths. *Corporate
scientists* all but rules out the anti-vaxxer and leans anti-corporate for everyone; *big
pharma* is impossible from a pro-vax pro-corporate speaker, and savvy listeners tie it to the
anti-vax anti-corporate persona where unsavvy ones read it as anti-corporate. -/
def likelihood (t : ListenerType) : Message → Persona → ℕ
  | .corporateScientists, π =>
    if .antiVax ∈ π.1 then 2 else if .proCorporate ∈ π.1 then 12 else 16
  | .bigPharma, π =>
    if .proVax ∈ π.1 ∧ .proCorporate ∈ π.1 then 0
    else if t.Savvy then (if .antiVax ∈ π.1 ∧ .antiCorporate ∈ π.1 then 16 else 2)
    else if .proVax ∈ π.1 then 14 else if .antiCorporate ∈ π.1 then 3 else 2

/-- A listener's approval of each persona has the pro- and anti-vaxxers reward their own
stance and punish the other, the unsavvy pro-vaxxer less invested, and everyone slightly punish
a pro-corporate speaker. -/
def approval : ListenerType → Persona → ℤ
  | .savvyAntiVax, π =>
    (if .antiVax ∈ π.1 then 100 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)
  | .savvyProVax, π =>
    (if .proVax ∈ π.1 then 100 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)
  | .unsavvyProVax, π =>
    (if .proVax ∈ π.1 then 75 else -100) + (if .proCorporate ∈ π.1 then -25 else 0)

/-- Stein is accommodating and values no persona over another. -/
def speakerValue : Persona → ℤ := λ _ => 0

/-! ### The model -/

/-- A listener's literal listener is Bayes' rule over their likelihood, Burnett's literal
listener when the likelihood is an indexation. -/
noncomputable def L0 (t : ListenerType) : Kernel Message Persona :=
  literalListener (priorOfWeights priorWeight) λ m π => (likelihood t m π : ℝ≥0∞)

/-- The posterior a listener assigns a persona on hearing a message, as a real number. -/
theorem L0_real_singleton (t : ListenerType) (m : Message) (π : Persona) :
    (L0 t m).real {π}
      = (likelihood t m π * priorWeight π : ℝ) / ∑ π', (likelihood t m π' * priorWeight π' : ℝ) :=
  literalListener_natCast_real_singleton priorWeight (likelihood t) m π

/-- The speaker's social utility of a message toward a listener sums, over the personae, the
log posterior with the speaker's and the listener's values weighted by the posterior. -/
noncomputable def socialUtility (t : ListenerType) (m : Message) : ℝ :=
  ∑ π, (Real.log ((L0 t m).real {π}) + (speakerValue π + approval t π) * (L0 t m).real {π})

/-- The utility toward an audience with the given numbers of each kind of listener. -/
noncomputable def groupUtility (audience : ListenerType → ℕ) (m : Message) : ℝ :=
  ∑ t, audience t * socialUtility t m

/-- The speaker chooses a message by the softmax of its utility toward the audience. -/
noncomputable def speaker (α : ℝ) (audience : ListenerType → ℕ) : Measure Message :=
  speakerOfScore (λ _ : Unit => λ m => ((α * groupUtility audience m : ℝ) : EReal)) ()

/-- The dogwhistle is optimal for an audience exactly when the listeners who reward it, counted
with their numbers, outweigh those who punish it, the book's condition (2). -/
theorem dogwhistle_optimal_iff (audience : ListenerType → ℕ) :
    groupUtility audience .corporateScientists < groupUtility audience .bigPharma ↔
      0 < ∑ t, audience t *
        (socialUtility t .bigPharma - socialUtility t .corporateScientists) := by
  simp only [groupUtility, mul_sub, Finset.sum_sub_distrib, sub_pos]

/-! ### The case study -/

private theorem sum_univ (f : Persona → ℝ) :
    ∑ π, f π = f proVaxProCorp + f proVaxAntiCorp + f antiVaxProCorp + f antiVaxAntiCorp := by
  rw [personae_eq, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

/-- A lower bound on a log from the quadratic lower bound on the exponential. -/
private theorem neg_lt_log {r g : ℝ} (hr : 0 < r) (hg : 0 ≤ g)
    (h : 1 < r * (1 + g + g ^ 2 / 2)) : -g < Real.log r := by
  rw [Real.lt_log_iff_exp_lt hr, Real.exp_neg, inv_lt_comm₀ (Real.exp_pos g) hr,
    inv_lt_iff_one_lt_mul₀ hr]
  exact h.trans_le (by
    rw [mul_comm r]; exact mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg hg) hr.le)

/-- A savvy pro-vaxxer hears the whistle and disapproves, so the disavowal is worth more to
Stein toward them. -/
theorem savvyProVax_prefers_disavowal :
    socialUtility .savvyProVax .bigPharma < socialUtility .savvyProVax .corporateScientists := by
  simp only [socialUtility, L0_real_singleton, sum_univ]
  simp +decide only [likelihood, approval, speakerValue, priorWeight]
  norm_num
  have h := neg_lt_log (g := 149) (by norm_num) (by norm_num)
    (r := ((2 / 27 : ℝ) * (64 / 81) * (1 / 27) * (8 / 81)) / ((8 / 75 : ℝ) * (1 / 25) * (64 / 75)))
    (by norm_num)
  rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul] at h
  · linarith
  all_goals norm_num

/-- An unsavvy pro-vaxxer does not hear the whistle and reads *big pharma* as anti-corporate,
so the disavowal is still worth more, but by less. -/
theorem unsavvyProVax_prefers_disavowal :
    socialUtility .unsavvyProVax .bigPharma
      < socialUtility .unsavvyProVax .corporateScientists := by
  simp only [socialUtility, L0_real_singleton, sum_univ]
  simp +decide only [likelihood, approval, speakerValue, priorWeight]
  norm_num
  have h := neg_lt_log (g := 11) (by norm_num) (by norm_num)
    (r := ((2 / 27 : ℝ) * (64 / 81) * (1 / 27) * (8 / 81)) / ((56 / 71 : ℝ) * (3 / 71) * (12 / 71)))
    (by norm_num)
  rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul] at h
  · linarith
  all_goals norm_num

/-- An anti-vaxxer hears the whistle and approves, so the dogwhistle is worth more. -/
theorem antiVax_prefers_dogwhistle :
    socialUtility .savvyAntiVax .corporateScientists < socialUtility .savvyAntiVax .bigPharma := by
  simp only [socialUtility, L0_real_singleton, sum_univ]
  simp +decide only [likelihood, approval, speakerValue, priorWeight]
  norm_num
  have h := neg_lt_log (g := 153) (by norm_num) (by norm_num)
    (r := ((8 / 75 : ℝ) * (1 / 25) * (64 / 75)) / ((2 / 27 : ℝ) * (64 / 81) * (1 / 27) * (8 / 81)))
    (by norm_num)
  rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul] at h
  · linarith
  all_goals norm_num

end HendersonMcCready2024
