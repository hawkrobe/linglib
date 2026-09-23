module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.MeasureTheory.MeasurableSpace.Sum
public import Linglib.Morphology.Paradigm.Basic

/-!
# Rathi, Hahn, and Futrell (2026): Toward an information-theoretic model of morphological fusion based on an efficient tradeoff of memory and surprisal

This file formalizes Rathi, Hahn and Futrell's measure of informational fusion and their
information-theoretic account of when a language fuses features. Fusing two features into one
part of a word lowers that part's entropy by the features' mutual information, less what the
fused part still shares with the first feature, while fusing a feature with one it is
independent of hides the second from the next part. We prove both arguments of the paper's
appendix for arbitrary languages, show that the second needs its first feature independent of
the other two jointly, and derive the paper's toy languages as instances.

## Main definitions

* `LearnerModel.fusion M L p S σ`: the surprisal of the form for `σ` under a learner that has
  seen no form for the feature sets in `S`.
* `bits p`: independent bits, bit `i` being `true` with probability `p i`.
* `Table4.meanings d`, `Table5.meanings d`: the meanings of the paper's toy languages, a fair
  voice bit and further bits in which a feature disagrees with another with probability `d`.

## Main statements

* `entropy_sub_entropy_fused`: fusing `X₁` into the part expressing `X₂` lowers its entropy by
  `I[X₂ : X₁] - I[Y₂ : X₁]`, where `Y₂` is the fused part.
* `condEntropy_le_condEntropy_fused`: if `X₁` is independent of `(X₂, X₃)`, a part fusing `X₁`
  with `X₂` leaves the part expressing `X₃` at least the entropy `H[X₃ | X₂]`.
* `Table4.condEntropy_fused_lt`: a first feature independent of the second and of the third
  separately can fall below that bound.
* `Table4.entropy_agg_snd_sub_entropy_fus_snd`, `Table5.condEntropy_fuseLow_sub_agg`,
  `Table6.entropy_nonclustered_fst`: fusion saves the features' mutual information on local
  surprisal, fusing independent features costs the hidden mutual information on the next
  character, and dropping category clustering adds `binEntropy d` to the first slot.

## Implementation notes

* Entropies are in nats. Feature values are `Bool`s, with `false` for active, present and
  perfect, and the paper's tables are `d = 1/4` for Tables 4 and 5 and `d = 1/2` for Table 6,
  as `Table4.meanings_real_active_present` and `Table5.meanings_real_active_perfect_present`
  check on a row.
* The appendix assumes only that the first feature is independent of the second; its step
  dropping the fused part's information about the third given the second needs the joint
  independence that the toy language of Table 5 has.
* The corpus studies of polyexponence, suppletion and pairwise fusion rest on optimal orderings
  and a neural learner computed outside Lean.

## References

* [N. Rathi, M. Hahn, R. Futrell, *Toward an information-theoretic model of morphological
  fusion based on an efficient tradeoff of memory and surprisal* (2026)][rathi-hahn-futrell-2026]
* [N. Rathi, M. Hahn, R. Futrell, *An information-theoretic characterization of morphological
  fusion* (2021)][rathi-hahn-futrell-2021]
* [M. Hahn, J. Degen, R. Futrell, *Modeling word and morpheme order in natural language as an
  efficient trade-off of memory and surprisal* (2021)][hahn-degen-futrell-2021]
* [S. Wu, R. Cotterell, T. O'Connor, *Morphological irregularity correlates with frequency*
  (2019)][wu-cotterell-2019]
* [J. Mansfield, S. Stoll, B. Bickel, *Category clustering: a probabilistic bias in the
  morphology of verbal agreement marking* (2020)][mansfield-stoll-bickel-2020]
* [T. M. Cover, J. A. Thomas, *Elements of information theory* (2006)][cover-thomas-2006]
-/

@[expose] public section

namespace RathiHahnFutrell2026

open MeasureTheory ProbabilityTheory InformationTheory Real

section Learner

open Morphology

variable {n : ℕ} {Form : Type*}

/-! ### Informational fusion -/

/-- `holdOut L S` is the language `L` with every form for the feature sets in `S` removed, the
data set from which a learner guesses those forms. -/
def holdOut (L : ParadigmSystem n Form) (S : Finset (Fin n)) : ParadigmSystem n (Option Form) :=
  ⟨L.entries.map fun e ↦ (fun c ↦ if c ∈ S then none else some (e.1 c), e.2)⟩

/-- A learner model assigns a probability to a form at a feature set for a lexeme whose other
forms it is shown, after training on a data set. -/
structure LearnerModel (n : ℕ) (Form : Type*) where
  predict : ParadigmSystem n (Option Form) → Paradigm n (Option Form) → Fin n → Form → ℝ

/-- The probability the learner assigns to the form for `σ` in the paradigm `p` of the language
`L`, trained on `L` with the feature sets in `S` held out. -/
def LearnerModel.prob (M : LearnerModel n Form) (L : ParadigmSystem n Form) (p : Paradigm n Form)
    (S : Finset (Fin n)) (σ : Fin n) : ℝ :=
  M.predict (holdOut L S) (fun c ↦ if c ∈ S then none else some (p c)) σ (p σ)

/-- The informational fusion of the form for `σ` is its surprisal under a learner that has seen
no form for the feature sets in `S`, among them `σ`. Holding out `σ` alone is the paper's
informational fusion, which holds out a feature set where [wu-cotterell-2019]'s irregularity
holds out a lemma; holding out every feature set containing a pair of features is its pairwise
fusion. -/
noncomputable def LearnerModel.fusion (M : LearnerModel n Form) (L : ParadigmSystem n Form)
    (p : Paradigm n Form) (S : Finset (Fin n)) (σ : Fin n) : ℝ :=
  -log (M.prob L p S σ)

/-- A form's informational fusion under a learner assigning it a probability is nonnegative. -/
theorem LearnerModel.fusion_nonneg {M : LearnerModel n Form} {L : ParadigmSystem n Form}
    {p : Paradigm n Form} {S : Finset (Fin n)} {σ : Fin n} (h₀ : 0 ≤ M.prob L p S σ)
    (h₁ : M.prob L p S σ ≤ 1) : 0 ≤ M.fusion L p S σ :=
  neg_nonneg.2 (log_nonpos h₀ h₁)

end Learner

/-! ### The appendix's arguments -/

section Appendix

variable {Ω S₁ S₂ S₃ F F' : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Fintype S₁]
  [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Fintype S₂]
  [MeasurableSpace S₃] [MeasurableSingletonClass S₃] [Fintype S₃]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Fintype F]
  [MeasurableSpace F'] [MeasurableSingletonClass F'] [Fintype F']
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {X₃ : Ω → S₃}

/-- A part fusing two features that still identifies the second once the first is known has at
least the entropy of the second feature given the first. -/
theorem condEntropy_le_entropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    {g : S₁ → S₂ → F} (hg : ∀ a, (g a).Injective) :
    H[X₂ | X₁ ; μ] ≤ H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] := by
  rw [← condEntropy_of_injective μ hX₂ hX₁ g hg]
  exact condEntropy_le_entropy μ ((measurable_of_finite (Function.uncurry g)).comp
    (hX₁.prodMk hX₂)) hX₁

omit [Fintype F] in
/-- Fusion lowers the entropy of the second part by the mutual information of the two features,
less the mutual information that the fused part keeps with the first feature. -/
theorem entropy_sub_entropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) {f : S₂ → F}
    (hf : f.Injective) {g : S₁ → S₂ → F'} (hg : ∀ a, (g a).Injective) :
    H[f ∘ X₂ ; μ] - H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ]
      = I[X₂ : X₁ ; μ] - I[fun ω ↦ g (X₁ ω) (X₂ ω) : X₁ ; μ] := by
  have hY : Measurable fun ω ↦ g (X₁ ω) (X₂ ω) :=
    (measurable_of_finite (Function.uncurry g)).comp (hX₁.prodMk hX₂)
  rw [entropy_comp_of_injective μ hX₂ (measurable_of_finite f) hf,
    mutualInfo_eq_entropy_sub_condEntropy μ hX₂ hX₁,
    mutualInfo_eq_entropy_sub_condEntropy μ hY hX₁, condEntropy_of_injective μ hX₂ hX₁ g hg]
  ring

/-- Given a feature independent of the other two, conditioning on it as well as on the second
leaves the entropy of the third feature given the second. -/
theorem condEntropy_pair_eq_of_indepFun (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hX₃ : Measurable X₃) (hind : X₁ ⟂ᵢ[μ] fun ω ↦ (X₂ ω, X₃ ω)) :
    H[X₃ | fun ω ↦ (X₁ ω, X₂ ω) ; μ] = H[X₃ | X₂ ; μ] := by
  have h12 := hX₁.prodMk hX₂
  have h123 := hX₁.prodMk (hX₂.prodMk hX₃)
  have e : H[fun ω ↦ (X₃ ω, X₁ ω, X₂ ω) ; μ] = H[fun ω ↦ (X₁ ω, X₂ ω, X₃ ω) ; μ] := by
    rw [show (fun ω ↦ (X₃ ω, X₁ ω, X₂ ω)) = (fun p : S₁ × S₂ × S₃ ↦ (p.2.2, p.1, p.2.1)) ∘
      fun ω ↦ (X₁ ω, X₂ ω, X₃ ω) from rfl]
    exact entropy_comp_of_injective μ h123 (measurable_of_finite _) fun p q h ↦ by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.2.2 h.1)
  have i12 : X₁ ⟂ᵢ[μ] X₂ := hind.comp measurable_id measurable_fst
  have c1 := chain_rule μ hX₃ h12
  have c2 := chain_rule μ hX₃ hX₂
  have c3 := entropy_comm μ hX₂ hX₃
  have c4 := hind.entropy_pair_eq_add hX₁ (hX₂.prodMk hX₃)
  have c5 := i12.entropy_pair_eq_add hX₁ hX₂
  linarith

/-- A part fusing a feature independent of the other two with the second leaves the third part
at least the entropy of the third feature given the second. -/
theorem condEntropy_le_condEntropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hX₃ : Measurable X₃) (hind : X₁ ⟂ᵢ[μ] fun ω ↦ (X₂ ω, X₃ ω)) (g : S₁ → S₂ → F)
    {h : S₃ → F'} (hh : h.Injective) :
    H[X₃ | X₂ ; μ] ≤ H[h ∘ X₃ | fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] := by
  have h12 := hX₁.prodMk hX₂
  calc H[X₃ | X₂ ; μ] = H[fun ω ↦ h (X₃ ω) | fun ω ↦ (X₁ ω, X₂ ω) ; μ] := by
        rw [condEntropy_of_injective μ hX₃ h12 (fun _ ↦ h) fun _ ↦ hh,
          condEntropy_pair_eq_of_indepFun hX₁ hX₂ hX₃ hind]
    _ ≤ H[h ∘ X₃ | Function.uncurry g ∘ fun ω ↦ (X₁ ω, X₂ ω) ; μ] :=
        condEntropy_le_condEntropy_comp μ ((measurable_of_finite h).comp hX₃) h12 _

/-- A first feature independent of the second does not always meet the bound. If it is a noise
bit `N` independent of the second feature and the third is the second XOR `N`, a part fusing the
first two determines the third. -/
theorem condEntropy_fused_lt_of_xor {N X : Ω → Bool} (hN : Measurable N) (hX : Measurable X)
    (hind : N ⟂ᵢ[μ] X) (hpos : 0 < H[N ; μ]) :
    I[N : X ; μ] = 0 ∧ H[fun ω ↦ xor (X ω) (N ω) | fun ω ↦ (N ω, X ω) ; μ]
      < H[fun ω ↦ xor (X ω) (N ω) | X ; μ] := by
  refine ⟨(mutualInfo_eq_zero_iff μ hN hX).mpr hind, ?_⟩
  rw [show (fun ω ↦ xor (X ω) (N ω)) = (fun p : Bool × Bool ↦ xor p.2 p.1) ∘
      fun ω ↦ (N ω, X ω) from rfl, condEntropy_comp_self μ (hN.prodMk hX)]
  rw [show (fun p : Bool × Bool ↦ xor p.2 p.1) ∘ (fun ω ↦ (N ω, X ω))
      = fun ω ↦ xor (X ω) (N ω) from rfl,
    condEntropy_of_injective μ hN hX xor fun _ _ _ ↦ Bool.xor_right_inj.mp,
    hind.condEntropy_eq_entropy hN hX]
  exact hpos

omit [IsProbabilityMeasure μ] in
theorem entropy_le_log_two (X : Ω → Bool) : H[X ; μ] ≤ Real.log 2 := by
  simpa using entropy_le_log_card X μ

/-- XOR with a bit independent of `D` keeps that bit's entropy given `D`. -/
theorem condEntropy_xor_eq_entropy {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) : H[fun ω ↦ xor (V ω) (D ω) | D ; μ] = H[V ; μ] := by
  rw [show (fun ω ↦ xor (V ω) (D ω)) = fun ω ↦ (fun b v ↦ xor v b) (D ω) (V ω) from rfl,
    condEntropy_of_injective μ hV hD (fun b v ↦ xor v b) fun _ _ _ ↦ Bool.xor_left_inj.mp,
    hind.condEntropy_eq_entropy hV hD]

/-- XOR with a fair bit independent of `D` is a fair bit. -/
theorem entropy_xor_eq_log_two {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) (hfair : H[V ; μ] = Real.log 2) :
    H[fun ω ↦ xor (V ω) (D ω) ; μ] = Real.log 2 := by
  have hX : Measurable fun ω ↦ xor (V ω) (D ω) :=
    (measurable_of_finite (Function.uncurry xor)).comp (hV.prodMk hD)
  have h := condEntropy_le_entropy μ hX hD
  rw [condEntropy_xor_eq_entropy hV hD hind, hfair] at h
  exact le_antisymm (entropy_le_log_two _) h

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
    H[fun ω : Fin n → Bool ↦ ω i ; bits p] = Real.binEntropy (p i) := by
  show Hm[(bits p).map (Function.eval i)] = _
  rw [bits, (measurePreserving_eval _ i).map_eq,
    measureEntropy_bernoulliMeasure (by decide : true ≠ false)]

end Bits

/-! #### Fusion lowers local surprisal, Table 4 -/

namespace Table4

open Real unitInterval

/-- `meanings d` is the distribution of Table 4's meanings when tense disagrees with voice with
probability `d`. Its first bit is the voice, a fair coin, and its second says whether tense
disagrees with voice. -/
noncomputable def meanings (d : I) : Measure (Fin 2 → Bool) := bits ![half, d]

/-- The voice feature, `false` for active. -/
def voice (ω : Fin 2 → Bool) : Bool := ω 0

/-- The tense feature, `false` for present. -/
def tense (ω : Fin 2 → Bool) : Bool := xor (ω 0) (ω 1)

variable (d : I)

instance : IsProbabilityMeasure (meanings d) := by unfold meanings; infer_instance

private theorem indep : (fun ω : Fin 2 → Bool ↦ ω 0) ⟂ᵢ[meanings d] fun ω ↦ ω 1 :=
  (iIndepFun_bits _).indepFun (i := 0) (j := 1) (by decide)

private theorem m (i : Fin 2) : Measurable fun ω : Fin 2 → Bool ↦ ω i := measurable_pi_apply i

theorem entropy_voice : H[voice ; meanings d] = log 2 := by
  rw [show voice = fun ω : Fin 2 → Bool ↦ ω 0 from rfl, meanings, entropy_bit]
  simp [half, binEntropy_two_inv]

theorem condEntropy_tense_voice : H[tense | voice ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) | fun ω ↦ ω 0 ; meanings d] = _
  rw [condEntropy_of_injective _ (m 1) (m 0) xor fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d).symm.condEntropy_eq_entropy (m 1) (m 0), meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (m 0) (m 1) (indep d) (entropy_voice d)

theorem mutualInfo_tense_voice : I[tense : voice ; meanings d] = log 2 - binEntropy d := by
  show I[tense : fun ω : Fin 2 → Bool ↦ ω 0 ; meanings d] = _
  rw [mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense) (m 0),
    entropy_tense]
  exact congrArg (log 2 - ·) (condEntropy_tense_voice d)

/-- The agglutinative language `Lagg` writes each feature as its own character. -/
def agg (ω : Fin 2 → Bool) : Bool × Bool := (voice ω, tense ω)

/-- The fusional language `Lfus` writes voice and then the exclusive or of the two features. -/
def fus (ω : Fin 2 → Bool) : Bool × Bool := (voice ω, xor (voice ω) (tense ω))

/-- Fusion lowers the entropy of the second character by the mutual information of the two
features. -/
theorem entropy_agg_snd_sub_entropy_fus_snd :
    H[fun ω ↦ (agg ω).2 ; meanings d] - H[fun ω ↦ (fus ω).2 ; meanings d]
      = I[tense : voice ; meanings d] := by
  have h := entropy_sub_entropy_fused (μ := meanings d) (m 0) (measurable_of_finite tense)
    (f := id) Function.injective_id (g := xor) fun _ _ _ ↦ Bool.xor_right_inj.mp
  have hfus : (fun ω : Fin 2 → Bool ↦ xor (ω 0) (tense ω)) = fun ω ↦ ω 1 := by
    funext ω; simp [tense]
  rw [hfus, (mutualInfo_eq_zero_iff _ (m 1) (m 0)).mpr (indep d).symm, sub_zero,
    Function.id_comp] at h
  rwa [show (fun ω ↦ (fus ω).2) = fun ω : Fin 2 → Bool ↦ ω 1 by
    funext ω; simp [fus, voice, tense]]

theorem entropy_fus_snd : H[fun ω ↦ (fus ω).2 ; meanings d] = binEntropy d := by
  rw [show (fun ω ↦ (fus ω).2) = fun ω : Fin 2 → Bool ↦ ω 1 by
    funext ω; simp [fus, voice, tense], meanings, entropy_bit]
  rfl

/-- Fusion lowers the entropy of the second character exactly when the features are
dependent. -/
theorem entropy_fus_snd_lt_iff :
    H[fun ω ↦ (fus ω).2 ; meanings d] < H[fun ω ↦ (agg ω).2 ; meanings d] ↔ (d : ℝ) ≠ 2⁻¹ := by
  rw [entropy_fus_snd, show (fun ω ↦ (agg ω).2) = tense from rfl, entropy_tense,
    binEntropy_lt_log_two]

/-- At `d = 1/4`, an active present meaning has probability `3/8`, as in the first row of
Table 4. -/
theorem meanings_real_active_present :
    (meanings ⟨1 / 4, by norm_num, by norm_num⟩).real {ω | voice ω = false ∧ tense ω = false}
      = 3 / 8 := by
  have : {ω : Fin 2 → Bool | voice ω = false ∧ tense ω = false}
      = Set.univ.pi fun _ ↦ {false} := by
    ext ω
    rcases h0 : ω 0 <;> rcases h1 : ω 1 <;> simp [voice, tense, Fin.forall_fin_two, h0, h1]
  rw [this, measureReal_def, meanings, bits, Measure.pi_pi]
  simp [Fin.prod_univ_two, half]
  norm_num

/-- Voice, a fair coin, masks the disagreement bit, so tense carries no information about it. -/
theorem mutualInfo_disagree_tense : I[fun ω ↦ ω 1 : tense ; meanings d] = 0 := by
  rw [mutualInfo_comm _ (m 1) (measurable_of_finite tense),
    mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense) (m 1),
    show tense = fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) from rfl,
    condEntropy_xor_eq_entropy (m 0) (m 1) (indep d)]
  exact sub_eq_zero.mpr ((entropy_tense d).trans (entropy_voice d).symm)

/-- The hypotheses the Appendix states for its second argument do not suffice. Take the
disagreement bit as a first feature: it is independent of voice and of tense, and voice and
tense share information, yet a part that fuses it with voice determines tense. -/
theorem condEntropy_fused_lt (h₀ : 0 < (d : ℝ)) (h₁ : (d : ℝ) < 1) (hd : (d : ℝ) ≠ 2⁻¹) :
    I[fun ω ↦ ω 1 : voice ; meanings d] = 0 ∧ I[fun ω ↦ ω 1 : tense ; meanings d] = 0 ∧
      0 < I[tense : voice ; meanings d] ∧
      H[tense | fun ω ↦ (ω 1, voice ω) ; meanings d] < H[tense | voice ; meanings d] := by
  have hpos : 0 < H[fun ω : Fin 2 → Bool ↦ ω 1 ; meanings d] := by
    rw [meanings, entropy_bit]; exact binEntropy_pos h₀ h₁
  obtain ⟨hi, hlt⟩ := condEntropy_fused_lt_of_xor (m 1) (m 0) (indep d).symm hpos
  refine ⟨hi, mutualInfo_disagree_tense d, ?_, hlt⟩
  rw [mutualInfo_tense_voice, sub_pos]
  exact (binEntropy_lt_log_two).mpr hd

end Table4

/-! #### Category clustering lowers local surprisal, Table 6 -/

namespace Table6

open Real unitInterval Table4

/-- The language `Lclustered` of Table 6 writes the voice morpheme and then the tense
morpheme. -/
def clustered (ω : Fin 2 → Bool) : (Bool ⊕ Bool) × (Bool ⊕ Bool) :=
  (.inl (voice ω), .inr (tense ω))

/-- The language `Lnonclustered` of Table 6 writes the tense morpheme first when tense disagrees
with voice. -/
def nonclustered (ω : Fin 2 → Bool) : (Bool ⊕ Bool) × (Bool ⊕ Bool) :=
  if ω 1 then (.inr (tense ω), .inl (voice ω)) else (.inl (voice ω), .inr (tense ω))

variable (d : I)

theorem entropy_clustered_fst : H[fun ω ↦ (clustered ω).1 ; meanings d] = log 2 := by
  rw [show (fun ω ↦ (clustered ω).1) = Sum.inl ∘ voice from rfl,
    entropy_comp_of_injective _ (measurable_of_finite voice) (measurable_of_finite _)
      Sum.inl_injective, entropy_voice]

/-- Without category clustering the first slot identifies the whole meaning, and its entropy
exceeds the clustered language's by `binEntropy d`. -/
theorem entropy_nonclustered_fst :
    H[fun ω ↦ (nonclustered ω).1 ; meanings d] = log 2 + binEntropy d := by
  have e : (fun ω ↦ (nonclustered ω).1) = (fun p : Bool × Bool ↦
      if p.2 then (Sum.inr (xor p.1 p.2) : Bool ⊕ Bool) else .inl p.1) ∘
        fun ω : Fin 2 → Bool ↦ (ω 0, ω 1) := by
    funext ω; by_cases h : ω 1 <;> simp [nonclustered, voice, tense, h]
  have hinj : (fun p : Bool × Bool ↦
      if p.2 then (Sum.inr (xor p.1 p.2) : Bool ⊕ Bool) else .inl p.1).Injective := by
    decide
  rw [e, entropy_comp_of_injective _ ((m 0).prodMk (m 1)) (measurable_of_finite _) hinj,
    (indep d).entropy_pair_eq_add (m 0) (m 1)]
  exact congrArg₂ (· + ·) (entropy_voice d) (by rw [meanings, entropy_bit]; rfl)

/-- At the paper's uniform weights, dropping category clustering doubles the entropy of the
first slot. -/
theorem entropy_nonclustered_fst_half :
    H[fun ω ↦ (nonclustered ω).1 ; meanings half]
      = 2 * H[fun ω ↦ (clustered ω).1 ; meanings half] := by
  rw [entropy_nonclustered_fst, entropy_clustered_fst]
  simp [half, binEntropy_two_inv]
  ring

/-- Category clustering lowers the entropy of the first slot whenever both orders occur. -/
theorem entropy_clustered_fst_lt (h₀ : 0 < (d : ℝ)) (h₁ : (d : ℝ) < 1) :
    H[fun ω ↦ (clustered ω).1 ; meanings d] < H[fun ω ↦ (nonclustered ω).1 ; meanings d] := by
  rw [entropy_clustered_fst, entropy_nonclustered_fst]
  linarith [binEntropy_pos h₀ h₁]

end Table6

/-! #### Fusing independent features raises long-range surprisal, Table 5 -/

namespace Table5

open Real unitInterval

/-- `meanings d` is the distribution of Table 5's meanings when tense disagrees with aspect with
probability `d`. Voice and aspect are fair coins, and the third bit says whether tense disagrees
with aspect. -/
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

private theorem m (i : Fin 3) : Measurable fun ω : Fin 3 → Bool ↦ ω i := measurable_pi_apply i

private theorem indep {i j : Fin 3} (hij : i ≠ j) :
    (fun ω : Fin 3 → Bool ↦ ω i) ⟂ᵢ[meanings d] fun ω ↦ ω j :=
  (iIndepFun_bits _).indepFun hij

private theorem entropy_fair {i : Fin 3} (hi : i ≠ 2) :
    H[fun ω : Fin 3 → Bool ↦ ω i ; meanings d] = log 2 := by
  rw [meanings, entropy_bit]
  fin_cases i <;> simp_all [half, binEntropy_two_inv]

theorem condEntropy_tense_aspect : H[tense | aspect ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 3 → Bool ↦ xor (ω 1) (ω 2) | fun ω ↦ ω 1 ; meanings d] = _
  rw [condEntropy_of_injective _ (m 2) (m 1) xor fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d (by decide)).condEntropy_eq_entropy (m 2) (m 1), meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (m 1) (m 2) (indep d (by decide)) (entropy_fair d (by decide))

/-- Fusing the dependent aspect and tense costs nothing, since the third character given the
second keeps the entropy of tense given aspect. -/
theorem condEntropy_fuseHigh :
    H[fun ω ↦ (fuseHigh ω).2.2 | fun ω ↦ (fuseHigh ω).2.1 ; meanings d]
      = H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d] := by
  rw [show (fun ω ↦ (fuseHigh ω).2.2) = fun ω : Fin 3 → Bool ↦ ω 2 by
      funext ω; simp [fuseHigh, aspect, tense]]
  show H[fun ω : Fin 3 → Bool ↦ ω 2 | fun ω ↦ ω 1 ; meanings d] = H[tense | aspect ; meanings d]
  rw [(indep d (by decide)).condEntropy_eq_entropy (m 2) (m 1), condEntropy_tense_aspect,
    meanings, entropy_bit]
  rfl

/-- Fusing voice with aspect leaves the third character at least the entropy of tense given
aspect, as the Appendix's second argument says, since voice is independent of aspect and tense
together. -/
theorem condEntropy_agg_le_fuseLow :
    H[fun ω ↦ (agg ω).2.2 | fun ω ↦ (agg ω).2.1 ; meanings d]
      ≤ H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d] := by
  have hind : voice ⟂ᵢ[meanings d] fun ω ↦ (aspect ω, tense ω) :=
    (((iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 2 0 (by decide)
      (by decide)).symm).comp measurable_id (measurable_of_finite fun p : Bool × Bool ↦
        (p.1, xor p.1 p.2))
  exact condEntropy_le_condEntropy_fused (m 0) (m 1) (measurable_of_finite tense) hind xor
    (h := id) Function.injective_id

/-- Fusing the independent voice and aspect hides aspect from the second character, so the third
character given the second keeps the whole entropy of tense. -/
theorem condEntropy_fuseLow :
    H[fun ω ↦ (fuseLow ω).2.2 | fun ω ↦ (fuseLow ω).2.1 ; meanings d] = log 2 := by
  show H[tense | fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) ; meanings d] = _
  have hY : Measurable fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) := measurable_of_finite _
  refine le_antisymm ((condEntropy_le_entropy _ (measurable_of_finite tense) hY).trans
    (entropy_tense d).le) ?_
  -- given the disagreement bit, `(tense, xor voice aspect)` is a recoding of `(aspect, voice)`
  have h01 : Measurable fun ω : Fin 3 → Bool ↦ (ω 1, ω 0) := (m 1).prodMk (m 0)
  have hinj : ∀ b : Bool, (fun p : Bool × Bool ↦ (xor p.1 b, xor p.2 p.1)).Injective :=
    fun b p q h ↦ by
      simp only [Prod.mk.injEq] at h
      have h1 := Bool.xor_left_inj.mp h.1
      exact Prod.ext h1 (Bool.xor_left_inj.mp (h1 ▸ h.2))
  have hrec : H[fun ω ↦ (tense ω, xor (ω 0) (ω 1)) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d]
      = H[fun ω ↦ (ω 1, ω 0) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d] :=
    condEntropy_of_injective _ h01 (m 2) (fun b (p : Bool × Bool) ↦ (xor p.1 b, xor p.2 p.1))
      hinj
  have hpair :=
    condEntropy_le_entropy (meanings d) ((measurable_of_finite tense).prodMk hY) (m 2)
  have hind : (fun ω : Fin 3 → Bool ↦ (ω 1, ω 0)) ⟂ᵢ[meanings d] fun ω ↦ ω 2 :=
    (iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 0 2 (by decide)
      (by decide)
  rw [hrec, hind.condEntropy_eq_entropy h01 (m 2),
    (indep d (by decide)).entropy_pair_eq_add (m 1) (m 0), entropy_fair d (by decide),
    entropy_fair d (by decide)] at hpair
  linarith [chain_rule (meanings d) (measurable_of_finite tense) hY,
    entropy_le_log_two (μ := meanings d) fun ω ↦ xor (ω 0) (ω 1)]

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

/-- At `d = 1/4`, an active perfect present meaning has probability `3/16`, as in the first row
of Table 5. -/
theorem meanings_real_active_perfect_present :
    (meanings ⟨1 / 4, by norm_num, by norm_num⟩).real
      {ω | voice ω = false ∧ aspect ω = false ∧ tense ω = false} = 3 / 16 := by
  have : {ω : Fin 3 → Bool | voice ω = false ∧ aspect ω = false ∧ tense ω = false}
      = Set.univ.pi fun _ ↦ {false} := by
    ext ω
    rcases h0 : ω 0 <;> rcases h1 : ω 1 <;> rcases h2 : ω 2 <;>
      simp [voice, aspect, tense, Fin.forall_fin_succ, h0, h1, h2]
  rw [this, measureReal_def, meanings, bits, Measure.pi_pi]
  simp [Fin.prod_univ_three, half]
  norm_num

end Table5

end RathiHahnFutrell2026
