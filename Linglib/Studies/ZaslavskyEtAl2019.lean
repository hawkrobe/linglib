import Linglib.Pragmatics.InformationTheory.ChannelCapacity

/-!
# Zaslavsky et al. (2019): Color Naming Reflects Both Perceptual Structure and Communicative Need

This file formalizes [zaslavsky-etal-2019]'s information-theoretic link between communicative
need and communicative precision in color naming. A language's color naming distribution
`p(w | c)` is a channel from colors to words (`CommChannel`), and the expected surprisal
`S(c)` of a color under a need distribution `p(c)` is its communicative imprecision
(`commPrecision`), the measure with which [gibson-etal-2017] found warm colors named more
precisely than cool ones across languages. The paper's central observation is that the need
distribution maximizing the information the lexicon conveys, the capacity-achieving prior of
[cover-thomas-2006], satisfies `p(c) ∝ exp(−S(c))`, so that `−log p(c)` is linear in `S(c)`
with slope one (`cap_linear`), which ties the asymmetry in need to the asymmetry in precision.

Two of the paper's constructions are formalized here. The artificial naming systems obtained
by clustering the color chips in perceptual space are deterministic channels (`ofPartition`),
whose surprisal under a uniform need is the log size of the color's cluster
(`commPrecision_ofPartition_uniform`), so that their warm–cool asymmetry is an asymmetry in
cluster size (`warmCoolAsymmetry_ofPartition_uniform_iff`); their capacity-achieving prior
spreads mass equally over clusters (`isCAP_clusterPrior`), attaining the capacity `log k` of a
`k`-term deterministic lexicon (`mutualInfo_clusterPrior`). The universal need distribution
inferred from the World Color Survey averages the per-language capacity-achieving priors
(`averagePrior`).

## Implementation notes

* The perceptual coordinates of the chips and the `k`-means procedure are not represented;
  a clustering enters only through its assignment of chips to terms.
* `WarmCoolAsymmetry` states the paper's empirical pattern as a property of a channel, a need
  distribution and a temperature classification; the survey data that instantiate it are not
  in the library.

## References

* [zaslavsky-etal-2019]
* [gibson-etal-2017]
* [cover-thomas-2006]
* [shannon-1948]
* [zaslavsky-kemp-regier-tishby-2018]
-/

namespace ZaslavskyEtAl2019

open Pragmatics.InformationTheory Finset Real

variable {C W : Type} [Fintype C]

/-! ### The warm–cool asymmetry -/

/-- The temperature of a color chip. -/
inductive Temperature
  | warm | cool
  deriving DecidableEq, Repr

section Asymmetry

variable [Fintype W]

/-- The warm–cool asymmetry of [gibson-etal-2017]: under the need distribution `p`, the warm
colors have lower mean expected surprisal than the cool ones. -/
def WarmCoolAsymmetry (nc : CommChannel C W) (p : C → ℝ) (temp : C → Temperature) : Prop :=
  (∑ c ∈ univ.filter (temp · = .warm), commPrecision nc p c) / (univ.filter (temp · = .warm)).card
    < (∑ c ∈ univ.filter (temp · = .cool), commPrecision nc p c)
        / (univ.filter (temp · = .cool)).card

end Asymmetry

/-! ### Hard clusterings and the cluster prior -/

variable [DecidableEq W]

/-- The chips assigned to the term `w` by the clustering `f`. -/
def cluster (f : C → W) (w : W) : Finset C := univ.filter (λ c => f c = w)

/-- The need distribution that spreads mass equally over the clusters of `f` and uniformly
within each. -/
noncomputable def clusterPrior (f : C → W) (c : C) : ℝ :=
  1 / ((univ.image f).card * (cluster f (f c)).card)

theorem clusterPrior_pos (f : C → W) (c : C) : 0 < clusterPrior f c := by
  have hk : (0 : ℝ) < (univ.image f).card := by
    exact_mod_cast card_pos.mpr ⟨f c, mem_image_of_mem f (mem_univ c)⟩
  have hcl : (0 : ℝ) < (cluster f (f c)).card := by
    exact_mod_cast card_pos.mpr ⟨c, by simp [cluster]⟩
  unfold clusterPrior
  positivity

/-- Each cluster carries mass `1 / k` under the cluster prior. -/
theorem sum_clusterPrior_cluster (f : C → W) (c : C) :
    ∑ c' ∈ cluster f (f c), clusterPrior f c' = 1 / (univ.image f).card := by
  have hcl : (0 : ℝ) < (cluster f (f c)).card := by
    exact_mod_cast card_pos.mpr ⟨c, by simp [cluster]⟩
  rw [sum_congr rfl (λ c' hc' => show clusterPrior f c' =
      1 / ((univ.image f).card * (cluster f (f c)).card) by
    simp only [cluster, mem_filter, mem_univ, true_and] at hc'
    simp only [clusterPrior, hc']), sum_const, nsmul_eq_mul]
  field_simp

/-- The cluster prior is a probability distribution. -/
theorem sum_clusterPrior [Nonempty C] (f : C → W) : ∑ c, clusterPrior f c = 1 := by
  have hk : (0 : ℝ) < (univ.image f).card := by
    exact_mod_cast card_pos.mpr (univ_nonempty.image f)
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image f) (g := f)
      (λ c _ => mem_image_of_mem f (mem_univ c)),
    sum_congr rfl (g := λ _ => 1 / ((univ.image f).card : ℝ)) (λ w hw => ?_), sum_const,
    nsmul_eq_mul]
  · field_simp
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hw
    exact sum_clusterPrior_cluster f c

/-! ### Naming systems from a hard clustering -/

variable [Fintype W]

/-- The deterministic naming channel of a hard clustering: each color is named by the term of
its cluster. -/
def ofPartition (f : C → W) : CommChannel C W where
  encode c w := if f c = w then 1 else 0
  encode_nonneg _ _ := by split_ifs <;> norm_num
  encode_sum_one _ := by simp

theorem marginalWord_ofPartition (f : C → W) (p : C → ℝ) (w : W) :
    marginalWord (ofPartition f) p w = ∑ c ∈ cluster f w, p c := by
  simp [marginalWord, ofPartition, cluster, sum_filter]

theorem posterior_ofPartition (f : C → W) (p : C → ℝ) (c : C) :
    posterior (ofPartition f) p (f c) c = p c / ∑ c' ∈ cluster f (f c), p c' := by
  unfold posterior
  rw [marginalWord_ofPartition]
  simp [ofPartition]

/-- A color's expected surprisal under a deterministic channel is the surprisal of its
posterior given its own term. -/
theorem commPrecision_ofPartition (f : C → W) (p : C → ℝ) (c : C) :
    commPrecision (ofPartition f) p c = -log (posterior (ofPartition f) p (f c) c) := by
  simp [commPrecision, ofPartition, ite_mul]

/-- Under a positive need distribution, the surprisal of a color is the log mass of its cluster
less its own log need. -/
theorem commPrecision_ofPartition_eq (f : C → W) {p : C → ℝ} (hp : ∀ c, 0 < p c) (c : C) :
    commPrecision (ofPartition f) p c = log (∑ c' ∈ cluster f (f c), p c') - log (p c) := by
  have hmass : 0 < ∑ c' ∈ cluster f (f c), p c' :=
    sum_pos (λ c' _ => hp c') ⟨c, by simp [cluster]⟩
  rw [commPrecision_ofPartition, posterior_ofPartition, log_div (hp c).ne' hmass.ne']
  ring

/-- Under a uniform need, the surprisal of a color is the log size of its cluster. -/
theorem commPrecision_ofPartition_uniform (f : C → W) (c : C) :
    commPrecision (ofPartition f) (λ _ => 1 / Fintype.card C) c = log (cluster f (f c)).card := by
  have hC : (0 : ℝ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨c⟩
  have hcl : (0 : ℝ) < (cluster f (f c)).card := by
    exact_mod_cast card_pos.mpr ⟨c, by simp [cluster]⟩
  rw [commPrecision_ofPartition_eq f (λ _ => by positivity), sum_const, nsmul_eq_mul,
    log_mul hcl.ne' (by positivity)]
  ring

/-- For a clustering system, the warm–cool asymmetry under a uniform need is an asymmetry in
mean log cluster size. -/
theorem warmCoolAsymmetry_ofPartition_uniform_iff (f : C → W) (temp : C → Temperature) :
    WarmCoolAsymmetry (ofPartition f) (λ _ => 1 / Fintype.card C) temp ↔
      (∑ c ∈ univ.filter (temp · = .warm), log (cluster f (f c)).card)
          / (univ.filter (temp · = .warm)).card
        < (∑ c ∈ univ.filter (temp · = .cool), log (cluster f (f c)).card)
          / (univ.filter (temp · = .cool)).card := by
  simp only [WarmCoolAsymmetry, commPrecision_ofPartition_uniform]

/-! ### The capacity-achieving prior of a clustering system -/

/-- The cluster prior satisfies the capacity-achieving condition `p(c) ∝ exp(−S(c))` with
normalizer the number of terms. -/
theorem clusterPrior_eq_exp (f : C → W) (c : C) :
    clusterPrior f c =
      exp (-commPrecision (ofPartition f) (clusterPrior f) c) / (univ.image f).card := by
  have hk : (0 : ℝ) < (univ.image f).card := by
    exact_mod_cast card_pos.mpr ⟨f c, mem_image_of_mem f (mem_univ c)⟩
  have hcl : (0 : ℝ) < (cluster f (f c)).card := by
    exact_mod_cast card_pos.mpr ⟨c, by simp [cluster]⟩
  rw [commPrecision_ofPartition_eq f (clusterPrior_pos f), sum_clusterPrior_cluster]
  unfold clusterPrior
  rw [one_div, log_inv, one_div, log_inv, log_mul hk.ne' hcl.ne',
    show -(-log ((univ.image f).card : ℝ)
        - -(log ((univ.image f).card : ℝ) + log ((cluster f (f c)).card : ℝ)))
      = -log ((cluster f (f c)).card : ℝ) by ring,
    exp_neg, exp_log hcl]
  field_simp

/-- The cluster prior is a capacity-achieving prior of the clustering system. -/
theorem isCAP_clusterPrior (f : C → W) [Nonempty C] :
    IsCAP (ofPartition f) (clusterPrior f) :=
  ⟨(univ.image f).card, by exact_mod_cast card_pos.mpr (univ_nonempty.image f),
    λ c _ => clusterPrior_eq_exp f c⟩

/-- A `k`-term clustering system conveys `log k` bits about color at its capacity-achieving
prior. -/
theorem mutualInfo_clusterPrior [Nonempty C] (f : C → W) :
    mutualInfo (ofPartition f) (clusterPrior f) = log (univ.image f).card :=
  mutualInfo_eq_log_Z_of_cap _ _ (by exact_mod_cast card_pos.mpr (univ_nonempty.image f))
    (λ c _ => clusterPrior_eq_exp f c) (λ c => (clusterPrior_pos f c).le) (sum_clusterPrior f)
    (clusterPrior_pos f)

/-! ### The universal need distribution -/

/-- The universal need distribution inferred from a survey: the average of the per-language
capacity-achieving priors. -/
noncomputable def averagePrior {L : ℕ} (priors : Fin L → C → ℝ) (c : C) : ℝ :=
  (∑ l, priors l c) / L

/-- The average of probability distributions is a probability distribution. -/
theorem sum_averagePrior {L : ℕ} (hL : 0 < L) (priors : Fin L → C → ℝ)
    (h : ∀ l, ∑ c, priors l c = 1) : ∑ c, averagePrior priors c = 1 := by
  simp only [averagePrior]
  rw [← sum_div, sum_comm]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast hL.ne')

end ZaslavskyEtAl2019
