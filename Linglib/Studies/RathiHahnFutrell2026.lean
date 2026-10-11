module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.MeasureTheory.MeasurableSpace.Sum

/-!
# Rathi, Hahn, and Futrell (2026): Toward an information-theoretic model of morphological fusion based on an efficient tradeoff of memory and surprisal

Rathi, Hahn and Futrell measure the informational fusion of a form as its surprisal under a
learner that has seen no form with the same features, and explain which features a language
fuses by the tradeoff of memory and surprisal. Fusing two features into one part of a word leaves
that part the entropy of the second given the first, plus what it keeps of the first, while
fusing a feature with one it is independent of hides the second from the next part. We prove both
arguments of the paper's appendix for arbitrary languages, show that the second needs joint
independence, and derive the toy languages of Tables 4 to 6 as instances. The simulated tradeoff
curves and the corpus studies rest on estimated language models and a neural learner, and are
not formalized.

## Main statements

* `entropy_fused_eq`: a part fusing `X₁` with `X₂` has the entropy `H[X₂ | X₁]` plus its mutual
  information with `X₁`, which can fall below the entropy of `X₂`.
* `condEntropy_le_condEntropy_fused`: if `X₁` is independent of `(X₂, X₃)`, a part fusing `X₁`
  with `X₂` leaves `X₃` at least the entropy `H[X₃ | X₂]` given that part.
* `VoiceTense.condEntropy_fused_lt`: a first feature independent of the second and of the third
  separately can fall below that bound.
* `VoiceTense.entropy_nonclustered_snd`: without category clustering, the second slot also
  identifies the meaning.

## Implementation notes

* Entropies are in nats. Feature values are `Bool`s, with `false` for active, present and
  perfect. Tables 4 and 5 are the toy languages at `d = 1/4`, and Table 6 at `d = 1/2`.
* A learner is any function from a data set, a lexeme and a cell to a measure on forms, and
  informational fusion is Core's `surprisal`. A form the learner rules out has informational
  fusion `∞` in the paper and the junk value `0` of `Real.log` here.
* The appendix assumes only that the first feature is independent of the second. Its step
  dropping the fused part's information about the third given the second needs the joint
  independence that the language of Table 5 has.
* The appendix says that without category clustering the second slot keeps its surprisal, but
  each slot of the nonclustered language of Table 6 identifies the meaning, so the entropy of
  both slots grows.

## References

* [N. Rathi, M. Hahn, R. Futrell, *Toward an information-theoretic model of morphological
  fusion based on an efficient tradeoff of memory and surprisal* (2026)][rathi-hahn-futrell-2026]
* [N. Rathi, M. Hahn, R. Futrell, *An information-theoretic characterization of morphological
  fusion* (2021)][rathi-hahn-futrell-2021]
* [M. Hahn, J. Degen, R. Futrell, *Modeling word and morpheme order in natural language as an
  efficient trade-off of memory and surprisal* (2021)][hahn-degen-futrell-2021]
* [S. Wu, R. Cotterell, T. O'Donnell, *Morphological irregularity correlates with frequency*
  (2019)][wu-cotterell-odonnell-2019]
* [J. Mansfield, S. Stoll, B. Bickel, *Category clustering: a probabilistic bias in the
  morphology of verbal agreement marking* (2020)][mansfield-stoll-bickel-2020]
* [T. M. Cover, J. A. Thomas, *Elements of information theory* (2006)][cover-thomas-2006]
-/

@[expose] public section

namespace RathiHahnFutrell2026

open MeasureTheory ProbabilityTheory InformationTheory Real

/-! ### Informational fusion -/

section Fusion

variable {Lex K Form : Type*} {V : K → Type*} [MeasurableSpace Form]
  (learner : Set (Lex × (∀ k, V k) × Form) → Lex → (∀ k, V k) → Measure Form)
  (L : Lex → (∀ k, V k) → Form)

/-- The fusion of the form of the lexeme `ℓ` in the cell `σ` of the language `L`, over the
categories `J`, is its surprisal under a learner trained on the words of `L` whose cells differ
from `σ` in some category of `J`. A cell gives each category `k` a value in `V k`, and a word is
a lexeme, a cell and a form. Where fusion holds out cells, [wu-cotterell-odonnell-2019]'s
irregularity holds out a lexeme. -/
noncomputable def fusion (J : Set K) (ℓ : Lex) (σ : ∀ k, V k) : ℝ :=
  surprisal (learner {w | w.2.1 ∉ J.pi (fun k ↦ {σ k}) ∧ w.2.2 = L w.1 w.2.1} ℓ σ) (L ℓ σ)

/-- Over all categories, fusion is the paper's informational fusion, which holds out the words of
the cell `σ` itself. -/
theorem fusion_univ (ℓ : Lex) (σ : ∀ k, V k) :
    fusion learner L .univ ℓ σ
      = surprisal (learner {w | w.2.1 ≠ σ ∧ w.2.2 = L w.1 w.2.1} ℓ σ) (L ℓ σ) := by
  simp [fusion, Set.univ_pi_singleton]

/-- In a language with two categories, pairwise fusion is informational fusion. -/
theorem fusion_pair_eq_fusion_univ {k₁ k₂ : K} (h : ∀ k, k = k₁ ∨ k = k₂) :
    fusion learner L {k₁, k₂} = fusion learner L .univ := by
  rw [show ({k₁, k₂} : Set K) = .univ from Set.eq_univ_of_forall h]

end Fusion

/-! ### The appendix's arguments -/

section Appendix

variable {Ω S₁ S₂ S₃ F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Fintype S₁]
  [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Fintype S₂]
  [MeasurableSpace S₃] [MeasurableSingletonClass S₃] [Fintype S₃]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Fintype F]
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {X₃ : Ω → S₃}

/-- A part fusing two features that still identifies the second once the first is known has the
entropy of the second feature given the first, plus what it keeps of the first. -/
theorem entropy_fused_eq (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) {g : S₁ → S₂ → F}
    (hg : ∀ a, (g a).Injective) :
    H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] = H[X₂ | X₁ ; μ] + I[fun ω ↦ g (X₁ ω) (X₂ ω) : X₁ ; μ] := by
  have hY : Measurable fun ω ↦ g (X₁ ω) (X₂ ω) :=
    (measurable_of_finite (Function.uncurry g)).comp (hX₁.prodMk hX₂)
  rw [mutualInfo_eq_entropy_sub_condEntropy μ hY hX₁, condEntropy_of_injective μ hX₂ hX₁ g hg]
  ring

/-- Such a part has at least the entropy of the second feature given the first, the bound of
the appendix's first argument. An agglutinative part has the entropy of the second feature. -/
theorem condEntropy_le_entropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    {g : S₁ → S₂ → F} (hg : ∀ a, (g a).Injective) :
    H[X₂ | X₁ ; μ] ≤ H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] :=
  (entropy_fused_eq hX₁ hX₂ hg).ge.trans' <| le_add_of_nonneg_right <|
    mutualInfo_nonneg μ ((measurable_of_finite (Function.uncurry g)).comp (hX₁.prodMk hX₂)) hX₁

/-- A part fusing a feature independent of the other two with the second leaves the third
feature at least its entropy given the second, the appendix's second argument. -/
theorem condEntropy_le_condEntropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hX₃ : Measurable X₃) (hind : X₁ ⟂ᵢ[μ] fun ω ↦ (X₂ ω, X₃ ω)) (g : S₁ → S₂ → F) :
    H[X₃ | X₂ ; μ] ≤ H[X₃ | fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] := by
  rw [← condEntropy_prod_eq_of_indepFun μ hX₃ hX₂ hX₁
    (hind.comp measurable_id measurable_swap).symm]
  exact condEntropy_le_condEntropy_comp μ hX₃ (hX₂.prodMk hX₁) fun p ↦ g p.2 p.1

/-- XOR with a bit independent of `D` keeps that bit's entropy given `D`. -/
theorem condEntropy_xor_eq_entropy {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) : H[fun ω ↦ xor (V ω) (D ω) | D ; μ] = H[V ; μ] := by
  rw [show (fun ω ↦ xor (V ω) (D ω)) = fun ω ↦ (fun b v ↦ xor v b) (D ω) (V ω) from rfl,
    condEntropy_of_injective μ hV hD (fun b v ↦ xor v b) fun _ _ _ ↦ Bool.xor_left_inj.mp,
    hind.condEntropy_eq_entropy hV hD]

/-- XOR with a fair bit independent of `D` is a fair bit. -/
theorem entropy_xor_eq_log_two {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) (hfair : H[V ; μ] = log 2) :
    H[fun ω ↦ xor (V ω) (D ω) ; μ] = log 2 := by
  refine le_antisymm (by simpa using entropy_le_log_card (fun ω ↦ xor (V ω) (D ω)) μ) ?_
  rw [← hfair, ← condEntropy_xor_eq_entropy hV hD hind]
  exact condEntropy_le_entropy μ (measurable_of_finite (Function.uncurry xor) |>.comp
    (hV.prodMk hD)) hD

end Appendix

/-! ### The toy languages -/

section Bits

open unitInterval

/-- The fair coin as a point of the unit interval. -/
noncomputable def half : I := ⟨2⁻¹, by norm_num, by norm_num⟩

/-- Independent bits, bit `i` being `true` with probability `p i`. -/
noncomputable def bits {n : ℕ} (p : Fin n → I) : Measure (Fin n → Bool) :=
  Measure.pi fun i ↦ Ber(true, false, p i)

variable {n : ℕ} (p : Fin n → I)

instance : IsProbabilityMeasure (bits p) := by unfold bits; infer_instance

theorem iIndepFun_bits : iIndepFun (fun i (ω : Fin n → Bool) ↦ ω i) (bits p) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

theorem entropy_bit (i : Fin n) :
    H[fun ω : Fin n → Bool ↦ ω i ; bits p] = binEntropy (p i) := by
  show Hm[(bits p).map (Function.eval i)] = _
  rw [bits, (measurePreserving_eval _ i).map_eq,
    measureEntropy_bernoulliMeasure (by decide : true ≠ false)]

/-- A sequence of bits has the product of their probabilities. -/
theorem bits_real_singleton (x : Fin n → Bool) :
    (bits p).real {x} = ∏ i, if x i then (p i : ℝ) else 1 - p i := by
  rw [← Set.univ_pi_singleton, measureReal_def, bits, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases x i <;> simp

end Bits

/-! #### Fusion lowers local surprisal, Table 4 -/

namespace VoiceTense

open unitInterval

/-- The meanings of Tables 4 and 6 when tense disagrees with voice with probability `d`. The
first bit is the voice, a fair coin, and the second says whether tense disagrees with voice. -/
noncomputable def meanings (d : I) : Measure (Fin 2 → Bool) := bits ![half, d]

/-- The voice feature, `false` for active. -/
def voice (ω : Fin 2 → Bool) : Bool := ω 0

/-- The tense feature, `false` for present. -/
def tense (ω : Fin 2 → Bool) : Bool := xor (ω 0) (ω 1)

variable (d : I)

instance : IsProbabilityMeasure (meanings d) := by unfold meanings; infer_instance

private theorem indep : (fun ω : Fin 2 → Bool ↦ ω 0) ⟂ᵢ[meanings d] fun ω ↦ ω 1 :=
  (iIndepFun_bits _).indepFun (i := 0) (j := 1) (by decide)

/-- Voice and tense agree with probability `1 - d`, as in the probabilities of Table 4. -/
theorem meanings_real (v t : Bool) :
    (meanings d).real {ω | voice ω = v ∧ tense ω = t} = (if v = t then 1 - (d : ℝ) else d) / 2 := by
  have : {ω : Fin 2 → Bool | voice ω = v ∧ tense ω = t} = {![v, xor v t]} := by
    ext ω
    refine ⟨fun ⟨hv, ht⟩ ↦ ?_, fun (h : ω = _) ↦ by simp [h, voice, tense]⟩
    subst hv ht
    ext i; fin_cases i <;> simp [voice, tense]
  rw [this, meanings, bits_real_singleton]
  cases v <;> cases t <;> simp [Fin.prod_univ_two, half] <;> ring

theorem entropy_voice : H[voice ; meanings d] = log 2 := by
  rw [show voice = fun ω : Fin 2 → Bool ↦ ω 0 from rfl, meanings, entropy_bit]
  simp [half]

theorem condEntropy_tense_voice : H[tense | voice ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) | fun ω ↦ ω 0 ; meanings d] = _
  rw [condEntropy_of_injective (meanings d) (measurable_pi_apply 1) (measurable_pi_apply 0) xor
    fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d).symm.condEntropy_eq_entropy (measurable_pi_apply 1) (measurable_pi_apply 0),
    meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (measurable_pi_apply 0) (measurable_pi_apply 1) (indep d)
    (entropy_voice d)

theorem mutualInfo_tense_voice : I[tense : voice ; meanings d] = log 2 - binEntropy d := by
  rw [mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense)
    (measurable_of_finite voice), entropy_tense, condEntropy_tense_voice]

/-- The agglutinative language `Lagg` writes each feature as its own character. -/
def agg (ω : Fin 2 → Bool) : Bool × Bool := (voice ω, tense ω)

/-- The fusional language `Lfus` writes voice and then the exclusive or of the two features. -/
def fus (ω : Fin 2 → Bool) : Bool × Bool := (voice ω, xor (voice ω) (tense ω))

theorem entropy_fus_snd : H[fun ω ↦ (fus ω).2 ; meanings d] = binEntropy d := by
  rw [show (fun ω ↦ (fus ω).2) = fun ω : Fin 2 → Bool ↦ ω 1 by
    funext ω; simp [fus, voice, tense], meanings, entropy_bit]
  rfl

/-- Fusion lowers the entropy of the second character by the mutual information of the two
features. -/
theorem entropy_agg_snd_sub_entropy_fus_snd :
    H[fun ω ↦ (agg ω).2 ; meanings d] - H[fun ω ↦ (fus ω).2 ; meanings d]
      = I[tense : voice ; meanings d] := by
  rw [show (fun ω ↦ (agg ω).2) = tense from rfl, entropy_tense, entropy_fus_snd,
    mutualInfo_tense_voice]

/-- Fusion lowers the entropy of the second character exactly when the features are
dependent. -/
theorem entropy_fus_snd_lt_iff :
    H[fun ω ↦ (fus ω).2 ; meanings d] < H[fun ω ↦ (agg ω).2 ; meanings d] ↔ (d : ℝ) ≠ 2⁻¹ := by
  rw [entropy_fus_snd, show (fun ω ↦ (agg ω).2) = tense from rfl, entropy_tense,
    binEntropy_lt_log_two]

/-- Voice, a fair coin, masks the disagreement bit, so tense carries no information about it. -/
theorem mutualInfo_disagree_tense : I[fun ω ↦ ω 1 : tense ; meanings d] = 0 := by
  rw [mutualInfo_comm _ (measurable_pi_apply 1) (measurable_of_finite tense),
    mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense) (measurable_pi_apply 1),
    show tense = fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) from rfl,
    condEntropy_xor_eq_entropy (measurable_pi_apply 0) (measurable_pi_apply 1) (indep d)]
  exact sub_eq_zero.mpr ((entropy_tense d).trans (entropy_voice d).symm)

/-- The hypotheses the appendix states for its second argument do not suffice. Take the
disagreement bit as a first feature: it is independent of voice and of tense, and voice and
tense share information, yet a part that fuses it with voice determines tense. -/
theorem condEntropy_fused_lt (h₀ : 0 < (d : ℝ)) (h₁ : (d : ℝ) < 1) (hd : (d : ℝ) ≠ 2⁻¹) :
    I[fun ω ↦ ω 1 : voice ; meanings d] = 0 ∧ I[fun ω ↦ ω 1 : tense ; meanings d] = 0 ∧
      0 < I[tense : voice ; meanings d] ∧
      H[tense | fun ω ↦ (ω 1, voice ω) ; meanings d] < H[tense | voice ; meanings d] := by
  have h0 : H[tense | fun ω ↦ (ω 1, voice ω) ; meanings d] = 0 :=
    condEntropy_comp_self _ ((measurable_pi_apply 1).prodMk (measurable_of_finite voice))
      fun p : Bool × Bool ↦ xor p.2 p.1
  refine ⟨(mutualInfo_eq_zero_iff _ (measurable_pi_apply 1) (measurable_pi_apply 0)).mpr
    (indep d).symm, mutualInfo_disagree_tense d, ?_, ?_⟩
  · rw [mutualInfo_tense_voice, sub_pos]
    exact binEntropy_lt_log_two.mpr hd
  · rw [h0, condEntropy_tense_voice]
    exact binEntropy_pos h₀ h₁

/-! #### Category clustering lowers local surprisal, Table 6 -/

/-- The language `Lclustered` of Table 6 writes the voice morpheme and then the tense morpheme,
the category clustering of [mansfield-stoll-bickel-2020]. -/
def clustered (ω : Fin 2 → Bool) : (Bool ⊕ Bool) × (Bool ⊕ Bool) :=
  (.inl (voice ω), .inr (tense ω))

/-- The language `Lnonclustered` of Table 6 writes the tense morpheme first when tense disagrees
with voice. -/
def nonclustered (ω : Fin 2 → Bool) : (Bool ⊕ Bool) × (Bool ⊕ Bool) :=
  if ω 1 then (.inr (tense ω), .inl (voice ω)) else (.inl (voice ω), .inr (tense ω))

/-- A slot that identifies the meaning has the entropy of the meaning. -/
private theorem entropy_comp_bits {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : Bool × Bool → β} (hf : f.Injective) :
    H[f ∘ fun ω : Fin 2 → Bool ↦ (ω 0, ω 1) ; meanings d] = log 2 + binEntropy d := by
  have h01 : Measurable fun ω : Fin 2 → Bool ↦ (ω 0, ω 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  rw [entropy_comp_of_injective (meanings d) h01 (measurable_of_finite f) hf,
    (indep d).entropy_pair_eq_add (measurable_pi_apply 0) (measurable_pi_apply 1),
    show (fun ω : Fin 2 → Bool ↦ ω 0) = voice from rfl, entropy_voice, meanings, entropy_bit]
  rfl

theorem entropy_clustered_fst : H[fun ω ↦ (clustered ω).1 ; meanings d] = log 2 := by
  rw [show (fun ω ↦ (clustered ω).1) = Sum.inl ∘ voice from rfl,
    entropy_comp_of_injective _ (measurable_of_finite voice) (measurable_of_finite _)
      Sum.inl_injective, entropy_voice]

/-- Without category clustering the first slot identifies the meaning, and its entropy exceeds
the clustered language's by `binEntropy d`. -/
theorem entropy_nonclustered_fst :
    H[fun ω ↦ (nonclustered ω).1 ; meanings d] = log 2 + binEntropy d := by
  rw [show (fun ω ↦ (nonclustered ω).1) = (fun p : Bool × Bool ↦
      if p.2 then (Sum.inr (xor p.1 p.2) : Bool ⊕ Bool) else .inl p.1) ∘
        fun ω : Fin 2 → Bool ↦ (ω 0, ω 1) by
    funext ω; by_cases h : ω 1 <;> simp [nonclustered, voice, tense, h]]
  exact entropy_comp_bits d (by decide)

/-- At the paper's uniform weights, dropping category clustering doubles the entropy of the
first slot. -/
theorem entropy_nonclustered_fst_half :
    H[fun ω ↦ (nonclustered ω).1 ; meanings half]
      = 2 * H[fun ω ↦ (clustered ω).1 ; meanings half] := by
  rw [entropy_nonclustered_fst, entropy_clustered_fst]
  simp [half]
  ring

/-- Category clustering lowers the entropy of the first slot whenever both orders occur. -/
theorem entropy_clustered_fst_lt (h₀ : 0 < (d : ℝ)) (h₁ : (d : ℝ) < 1) :
    H[fun ω ↦ (clustered ω).1 ; meanings d] < H[fun ω ↦ (nonclustered ω).1 ; meanings d] := by
  rw [entropy_clustered_fst, entropy_nonclustered_fst]
  linarith [binEntropy_pos h₀ h₁]

/-- The second slot of `Lclustered` is the tense morpheme. -/
theorem entropy_clustered_snd : H[fun ω ↦ (clustered ω).2 ; meanings d] = log 2 := by
  rw [show (fun ω ↦ (clustered ω).2) = Sum.inr ∘ tense from rfl,
    entropy_comp_of_injective _ (measurable_of_finite tense) (measurable_of_finite _)
      Sum.inr_injective, entropy_tense]

/-- Without category clustering the second slot identifies the meaning as well, so its entropy
also exceeds the clustered language's by `binEntropy d`. The appendix says it is unchanged. -/
theorem entropy_nonclustered_snd :
    H[fun ω ↦ (nonclustered ω).2 ; meanings d] = log 2 + binEntropy d := by
  rw [show (fun ω ↦ (nonclustered ω).2) = (fun p : Bool × Bool ↦
      if p.2 then (Sum.inl p.1 : Bool ⊕ Bool) else .inr (xor p.1 p.2)) ∘
        fun ω : Fin 2 → Bool ↦ (ω 0, ω 1) by
    funext ω; by_cases h : ω 1 <;> simp [nonclustered, voice, tense, h]]
  exact entropy_comp_bits d (by decide)

end VoiceTense

/-! #### Fusing independent features raises long-range surprisal, Table 5 -/

namespace VoiceAspectTense

open unitInterval

/-- The meanings of Table 5 when tense disagrees with aspect with probability `d`. Voice and
aspect are fair coins, and the third bit says whether tense disagrees with aspect. -/
noncomputable def meanings (d : I) : Measure (Fin 3 → Bool) := bits ![half, half, d]

/-- The voice feature, `false` for active. -/
def voice (ω : Fin 3 → Bool) : Bool := ω 0

/-- The aspect feature, `false` for perfect. -/
def aspect (ω : Fin 3 → Bool) : Bool := ω 1

/-- The tense feature, `false` for present. -/
def tense (ω : Fin 3 → Bool) : Bool := xor (ω 1) (ω 2)

/-- The agglutinative language `Lagg` writes each feature as its own character. -/
def agg (ω : Fin 3 → Bool) : Bool × Bool × Bool := (voice ω, aspect ω, tense ω)

/-- The language `Lfuse-low` fuses the independent voice and aspect in its second character. -/
def fuseLow (ω : Fin 3 → Bool) : Bool × Bool × Bool :=
  (voice ω, xor (voice ω) (aspect ω), tense ω)

/-- The language `Lfuse-high` fuses the dependent aspect and tense in its third character. -/
def fuseHigh (ω : Fin 3 → Bool) : Bool × Bool × Bool :=
  (voice ω, aspect ω, xor (aspect ω) (tense ω))

variable (d : I)

instance : IsProbabilityMeasure (meanings d) := by unfold meanings; infer_instance

private theorem indep {i j : Fin 3} (hij : i ≠ j) :
    (fun ω : Fin 3 → Bool ↦ ω i) ⟂ᵢ[meanings d] fun ω ↦ ω j :=
  (iIndepFun_bits _).indepFun hij

private theorem entropy_fair {i : Fin 3} (hi : i ≠ 2) :
    H[fun ω : Fin 3 → Bool ↦ ω i ; meanings d] = log 2 := by
  rw [meanings, entropy_bit]
  fin_cases i <;> simp_all [half]

/-- Aspect and tense agree with probability `1 - d`, as in the probabilities of Table 5. -/
theorem meanings_real (v a t : Bool) :
    (meanings d).real {ω | voice ω = v ∧ aspect ω = a ∧ tense ω = t}
      = (if a = t then 1 - (d : ℝ) else d) / 4 := by
  have : {ω : Fin 3 → Bool | voice ω = v ∧ aspect ω = a ∧ tense ω = t} = {![v, a, xor a t]} := by
    ext ω
    refine ⟨fun ⟨hv, ha, ht⟩ ↦ ?_, fun (h : ω = _) ↦ by simp [h, voice, aspect, tense]⟩
    subst hv ha ht
    ext i; fin_cases i <;> simp [voice, aspect, tense]
  rw [this, meanings, bits_real_singleton]
  cases v <;> cases a <;> cases t <;> simp [Fin.prod_univ_three, half] <;> ring

theorem condEntropy_tense_aspect : H[tense | aspect ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 3 → Bool ↦ xor (ω 1) (ω 2) | fun ω ↦ ω 1 ; meanings d] = _
  rw [condEntropy_of_injective (meanings d) (measurable_pi_apply 2) (measurable_pi_apply 1) xor
    fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d (by decide)).condEntropy_eq_entropy (measurable_pi_apply 2) (measurable_pi_apply 1),
    meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (measurable_pi_apply 1) (measurable_pi_apply 2) (indep d (by decide))
    (entropy_fair d (by decide))

/-- Fusing the dependent aspect and tense costs nothing, since the third character given the
second keeps the entropy of tense given aspect. -/
theorem condEntropy_fuseHigh :
    H[fun ω ↦ (fuseHigh ω).2.2 | fun ω ↦ (fuseHigh ω).2.1 ; meanings d]
      = H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d] := by
  rw [show (fun ω ↦ (fuseHigh ω).2.2) = fun ω : Fin 3 → Bool ↦ ω 2 by
      funext ω; simp [fuseHigh, aspect, tense]]
  show H[fun ω : Fin 3 → Bool ↦ ω 2 | fun ω ↦ ω 1 ; meanings d] = H[tense | aspect ; meanings d]
  rw [(indep d (by decide)).condEntropy_eq_entropy (measurable_pi_apply 2) (measurable_pi_apply 1),
    condEntropy_tense_aspect, meanings, entropy_bit]
  rfl

/-- Fusing voice with aspect leaves the third character at least the entropy of tense given
aspect, as the appendix's second argument says, since voice is independent of aspect and tense
together. -/
theorem condEntropy_agg_le_fuseLow :
    H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d]
      ≤ H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d] := by
  have hind : voice ⟂ᵢ[meanings d] fun ω ↦ (aspect ω, tense ω) :=
    (((iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 2 0 (by decide)
      (by decide)).symm).comp measurable_id (measurable_of_finite fun p : Bool × Bool ↦
        (p.1, xor p.1 p.2))
  exact condEntropy_le_condEntropy_fused (measurable_pi_apply 0) (measurable_pi_apply 1)
    (measurable_of_finite tense) hind xor

/-- Fusing the independent voice and aspect hides aspect from the second character, so the third
character given the second keeps the whole entropy of tense. -/
theorem condEntropy_fuseLow :
    H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d] = log 2 := by
  show H[tense | fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) ; meanings d] = _
  have hY : Measurable fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) := measurable_of_finite _
  refine le_antisymm ((condEntropy_le_entropy _ (measurable_of_finite tense) hY).trans
    (entropy_tense d).le) ?_
  -- given the disagreement bit, `(tense, xor voice aspect)` is a recoding of `(aspect, voice)`
  have h10 : Measurable fun ω : Fin 3 → Bool ↦ (ω 1, ω 0) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 0)
  have hinj : ∀ b : Bool, (fun p : Bool × Bool ↦ (xor p.1 b, xor p.2 p.1)).Injective := by
    decide
  have hrec : H[fun ω ↦ (tense ω, xor (ω 0) (ω 1)) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d]
      = H[fun ω ↦ (ω 1, ω 0) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d] :=
    condEntropy_of_injective _ h10 (measurable_pi_apply 2)
      (fun b (p : Bool × Bool) ↦ (xor p.1 b, xor p.2 p.1)) hinj
  have hpair := condEntropy_le_entropy (meanings d)
    ((measurable_of_finite tense).prodMk hY) (measurable_pi_apply 2)
  have hind : (fun ω : Fin 3 → Bool ↦ (ω 1, ω 0)) ⟂ᵢ[meanings d] fun ω ↦ ω 2 :=
    (iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 0 2 (by decide)
      (by decide)
  rw [hrec, hind.condEntropy_eq_entropy h10 (measurable_pi_apply 2),
    (indep d (by decide)).entropy_pair_eq_add (measurable_pi_apply 1) (measurable_pi_apply 0),
    entropy_fair d (by decide), entropy_fair d (by decide)] at hpair
  linarith [chain_rule (meanings d) (measurable_of_finite tense) hY,
    show H[fun ω ↦ xor (ω 0) (ω 1) ; meanings d] ≤ log 2 by
      simpa using entropy_le_log_card (fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1)) (meanings d)]

/-- Fusing the independent features costs the third character given the second the mutual
information of tense and aspect. -/
theorem condEntropy_fuseLow_sub_agg :
    H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d]
      - H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d]
      = I[tense : aspect ; meanings d] := by
  show _ - H[tense | aspect ; meanings d] = _
  rw [condEntropy_fuseLow, mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense)
    (measurable_of_finite aspect), entropy_tense]

/-- Fusing the independent features raises the surprisal of the third character given the
second exactly when aspect and tense are dependent. -/
theorem condEntropy_agg_lt_fuseLow_iff :
    H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d]
      < H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d] ↔
        (d : ℝ) ≠ 2⁻¹ := by
  rw [condEntropy_fuseLow, show (fun ω ↦ (agg ω).2.2) = tense from rfl,
    show (fun ω ↦ (agg ω).2.1) = aspect from rfl, condEntropy_tense_aspect, binEntropy_lt_log_two]

end VoiceAspectTense

end RathiHahnFutrell2026
