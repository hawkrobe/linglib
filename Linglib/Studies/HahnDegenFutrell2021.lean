module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Fragments.Japanese.Morph
public import Linglib.Fragments.Sesotho.Morph
public import Linglib.Studies.Bybee1985
public import Linglib.Data.Examples.HahnDegenFutrell2021

/-!
# Hahn, Degen, and Futrell (2021): Modeling Word and Morpheme Order in Natural Language as an Efficient Trade-Off of Memory and Surprisal

This file formalizes the theory behind Hahn, Degen and Futrell's studies of word and morpheme
order. A listener predicts each word from a memory state updated word by word, and the paper's
information locality bound says that a listener whose memory cannot hold the dependencies up to
some distance pays at least the entropy rate plus the information carried at longer distances.
We prove the bound, compare two orders of a sentence by dependency length, and check the
paper's morpheme templates against Bybee's relevance hierarchy.

## Main definitions

* `memoryState M m₀ w t`: the listener's memory state at time `t`, reached from the initial
  state `m₀` by the memory encoding function `M`.
* `IsStationary X μ`: the law of a block of the process `X` does not depend on where it starts.
* `distanceInfo w μ t`: the mutual information between words at distance `t` given the words
  between them.

## Main statements

* `information_locality_bound`: if words and memory states are jointly stationary, `0 < T`, and
  the memory entropy is at most `∑ t ∈ Icc 1 T, t * distanceInfo w μ t`, then the average
  surprisal is at least the entropy rate plus `∑' t, distanceInfo w μ (T + t + 1)`.
* `pastCondEntropy_le_condEntropy`: under the same hypotheses, the average surprisal is at least
  the conditional entropy of a word given the `T` words before it.
* `heavyNPShift_shorter`: heavy NP shift in the paper's example (2) lowers total dependency
  length.
* `japanese_forms_licensed`, `sesotho_forms_licensed`: the affixes of the paper's Japanese and
  Sesotho forms are licensed by the Fragments' templates.
* `japanese_violates_surveyed_relevance`: Bybee's survey ranks tense closer to the stem than
  mood, and the Japanese suffix order is not sorted by the relevance hierarchy.
* `sesotho_suffixes_respect_relevance`, `sesotho_prefixes_violate_relevance`: the Sesotho
  suffixes are sorted by the hierarchy and the prefixes are not, the object marker lying inside
  the tense prefixes.

## Implementation notes

* The Japanese suffix order is `Japanese.Verb.slots`, the order of the paper's text, its
  supplement and its code, with the polite suffix before the desiderative; the paper's Table 2
  lists the two the other way round. The supplement's forms attest neither order, the two
  suffixes never sharing a form there.
* The classifications of the Japanese and Sesotho slots in Bybee's inventory, `bybeeCategory?`
  and `sesothoCategory?`, are the paper's; Japanese politeness, which Bybee does not rank, is
  left out rather than compared as agreement.
* The Sesotho rows carry the paper's own segmentation: two forms have a tense prefix fused
  with the neighbouring marker, glossed as that marker.
* Time runs over `ℕ` from the initial memory state. Every quantity in the bound is an entropy of
  a finite block, so the paper's two-sided process enters through its one-sided restriction.
* The initial memory state is an arbitrary random variable, so the bound holds without the
  paper's No Mindreading assumption, as the paper remarks.
* Entropies are in nats rather than bits; the bound is homogeneous in them.
* The dependency graphs of (2) follow Universal Dependencies conventions, with the comma
  dropped.

## References

* [M. Hahn, J. Degen, R. Futrell, *Modeling Word and Morpheme Order in Natural Language as an
  Efficient Trade-Off of Memory and Surprisal* (2021)][hahn-degen-futrell-2021]
* [J. Bybee, *Morphology: A Study of the Relation between Meaning and Form* (1985)][bybee-1985]
-/

@[expose] public section

namespace HahnDegenFutrell2021

open Data.Examples DependencyGrammar Morphology
open Morphology (Word)

/-! ### Dependency locality -/

/-- The unshifted order of example (2), in which the object precedes the prepositional phrase. -/
def longObjectFirst : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "the" .DET,
      Word.mk' "extremely" .ADV, Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV,
      Word.mk' "green" .ADJ, Word.mk' "broccoli" .NOUN, Word.mk' "with" .ADP,
      Word.mk' "a" .DET, Word.mk' "fork" .NOUN]
    1 [(1, 0, .nsubj), (1, 7, .obj), (7, 2, .det), (4, 3, .advmod), (7, 4, .amod),
      (6, 5, .advmod), (7, 6, .amod), (10, 8, .case_), (10, 9, .det), (1, 10, .obl)]

/-- The shifted order of example (2), in which the prepositional phrase precedes the long
object. -/
def shifted : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "with" .ADP, Word.mk' "a" .DET,
      Word.mk' "fork" .NOUN, Word.mk' "the" .DET, Word.mk' "extremely" .ADV,
      Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV, Word.mk' "green" .ADJ,
      Word.mk' "broccoli" .NOUN]
    1 [(1, 0, .nsubj), (1, 10, .obj), (10, 5, .det), (7, 6, .advmod), (10, 7, .amod),
      (9, 8, .advmod), (10, 9, .amod), (4, 2, .case_), (4, 3, .det), (1, 4, .obl)]

/-- Heavy NP shift cuts the verb's distance to the prepositional phrase from nine to three and
raises its distance to the object from six to nine, so the total dependency length falls. -/
theorem heavyNPShift_shorter : shifted.totalLength < longObjectFirst.totalLength := by decide

/-! ### The information locality bound -/

section InformationLocality

open MeasureTheory ProbabilityTheory InformationTheory Finset Filter Topology

variable {Ω α W Mem : Type*}

/-- `block X a n` is the block of `n` consecutive values of `X` starting at time `a`. -/
def block (X : ℕ → Ω → α) (a n : ℕ) (ω : Ω) : Fin n → α := fun i ↦ X (i + a) ω

/-- A process is stationary when the law of a block does not depend on where it starts. -/
def IsStationary [MeasurableSpace Ω] [MeasurableSpace α] (X : ℕ → Ω → α) (μ : Measure Ω) :
    Prop :=
  ∀ a n, IdentDistrib (block X a n) (block X 0 n) μ μ

theorem IsStationary.fst {β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {X : ℕ → Ω → α} {Y : ℕ → Ω → β} {μ : Measure Ω}
    (hs : IsStationary (fun t ω ↦ (X t ω, Y t ω)) μ) : IsStationary X μ :=
  fun a n ↦ (hs a n).comp (u := fun (v : Fin n → α × β) i ↦ (v i).1)
    (measurable_pi_iff.mpr fun i ↦ measurable_fst.comp (measurable_pi_apply i))

/-- `memoryState M m₀ w t` is the listener's memory state when the word at time `t` arrives. It
is reached from the initial state `m₀` by the memory encoding function `M`, which updates a state
with the word just heard. -/
def memoryState (M : Mem → W → Mem) (m₀ : Ω → Mem) (w : ℕ → Ω → W) : ℕ → Ω → Mem
  | 0 => m₀
  | t + 1 => fun ω ↦ M (memoryState M m₀ w t ω) (w t ω)

variable {w : ℕ → Ω → W} {M : Mem → W → Mem} {m₀ : Ω → Mem}

/-- A memory state is a function of the initial state and the words heard since. -/
theorem exists_memoryState_eq_comp (t : ℕ) : ∃ g : (Fin t → W) × Mem → Mem,
    memoryState M m₀ w t = g ∘ fun ω ↦ (block w 0 t ω, m₀ ω) := by
  induction t with
  | zero => exact ⟨Prod.snd, rfl⟩
  | succ t ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨fun p ↦ M (g (Fin.init p.1, p.2)) (p.1 (Fin.last t)), by
      funext ω; simp only [memoryState, hg]; rfl⟩

private theorem block_succ (t : ℕ) :
    block w 0 (t + 1) = (Fin.snocEquiv fun _ ↦ W) ∘ fun ω ↦ (w t ω, block w 0 t ω) :=
  funext fun _ ↦ (Fin.snoc_init_self _).symm

variable [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]
  [MeasurableSpace Mem] [MeasurableSingletonClass Mem] [Fintype Mem] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- `pastCondEntropy w μ n` is the conditional entropy of the word at time `n` given the `n`
words before it. -/
noncomputable def pastCondEntropy (w : ℕ → Ω → W) (μ : Measure Ω) (n : ℕ) : ℝ :=
  H[w n | block w 0 n ; μ]

/-- `distanceInfo w μ t` is the paper's `I t`, the mutual information
`I[w t : w 0 | w 1, …, w (t - 1)]` between words at distance `t` given the words between them,
which is the entropy of `w t` that `w 0` removes. -/
noncomputable def distanceInfo (w : ℕ → Ω → W) (μ : Measure Ω) (t : ℕ) : ℝ :=
  H[w t | block w 1 (t - 1) ; μ] - H[w t | block w 0 t ; μ]

/-- The entropy rate `S∞` is the infimum of the conditional entropies of a word given its past,
which is their limit when the process is stationary. -/
noncomputable def entropyRate (w : ℕ → Ω → W) (μ : Measure Ω) : ℝ :=
  ⨅ n, pastCondEntropy w μ n

theorem measurable_block [MeasurableSpace α] {X : ℕ → Ω → α} (hX : ∀ t, Measurable (X t))
    (a n : ℕ) : Measurable (block X a n) :=
  measurable_pi_iff.mpr fun i ↦ hX (i + a)

theorem measurable_memoryState (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀) :
    ∀ t, Measurable (memoryState M m₀ w t)
  | 0 => hm₀
  | t + 1 => (measurable_of_finite (Function.uncurry M)).comp
      ((measurable_memoryState hw hm₀ t).prodMk (hw t))

/-- Conditioning on a further word of the past never adds entropy, so `I (t + 1)` is
nonnegative. -/
theorem distanceInfo_succ_nonneg (hw : ∀ t, Measurable (w t)) (t : ℕ) :
    0 ≤ distanceInfo w μ (t + 1) :=
  sub_nonneg.mpr <| condEntropy_le_condEntropy_comp μ (hw _) (measurable_block hw 0 _) Fin.tail

/-- The entropy of a block is the sum of the conditional entropies of its words given their
predecessors. -/
theorem entropy_block (hw : ∀ t, Measurable (w t)) (T : ℕ) :
    H[block w 0 T ; μ] = ∑ t ∈ range T, pastCondEntropy w μ t := by
  induction T with
  | zero => simp [entropy_of_subsingleton]
  | succ T ih =>
    rw [sum_range_succ, ← ih, pastCondEntropy, ← chain_rule μ (hw T) (measurable_block hw 0 T),
      block_succ, entropy_comp_of_injective μ ((hw T).prodMk (measurable_block hw 0 T))
        (measurable_of_finite _) (Fin.snocEquiv _).injective]

/-- Over a block of `T` words, a listener's summed surprisal is at least the entropy of the
block given the initial memory state. -/
theorem condEntropy_block_le_sum (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀) (T : ℕ) :
    H[block w 0 T | m₀ ; μ] ≤ ∑ t ∈ range T, H[w t | memoryState M m₀ w t ; μ] := by
  suffices h : H[fun ω ↦ (block w 0 T ω, m₀ ω) ; μ]
      ≤ H[m₀ ; μ] + ∑ t ∈ range T, H[w t | memoryState M m₀ w t ; μ] by
    linarith [chain_rule μ (measurable_block hw 0 T) hm₀]
  induction T with
  | zero =>
    have : (fun ω ↦ (block w 0 0 ω, m₀ ω)) = (fun m ↦ (Fin.elim0, m)) ∘ m₀ :=
      funext fun ω ↦ Prod.ext (Subsingleton.elim _ _) rfl
    rw [this, entropy_comp_of_injective μ hm₀ (measurable_of_finite _) (Prod.mk_right_injective _)]
    simp
  | succ T ih =>
    have hZ := (measurable_block hw 0 T).prodMk hm₀
    obtain ⟨g, hg⟩ := exists_memoryState_eq_comp (M := M) (m₀ := m₀) (w := w) T
    let e := (Equiv.prodAssoc W (Fin T → W) Mem).symm.trans
      ((Fin.snocEquiv fun _ ↦ W).prodCongr (Equiv.refl Mem))
    have hrec : (fun ω ↦ (block w 0 (T + 1) ω, m₀ ω)) = e ∘ fun ω ↦ (w T ω, block w 0 T ω, m₀ ω) :=
      funext fun ω ↦ Prod.ext (congrFun (block_succ T) ω) rfl
    rw [hrec, entropy_comp_of_injective μ ((hw T).prodMk hZ) (measurable_of_finite _) e.injective,
      chain_rule μ (hw T) hZ, sum_range_succ, hg]
    linarith [condEntropy_le_condEntropy_comp μ (hw T) hZ g]

/-- Under joint stationarity, the average surprisal does not depend on the time. -/
theorem condEntropy_memoryState_eq (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀)
    (hs : IsStationary (fun t ω ↦ (w t ω, memoryState M m₀ w t ω)) μ) (t : ℕ) :
    H[w t | memoryState M m₀ w t ; μ] = H[w 0 | m₀ ; μ] := by
  have h := (hs t 1).comp (u := fun v ↦ v 0) (measurable_pi_apply 0)
  simp only [block, Function.comp_def, Fin.val_zero, zero_add] at h
  exact h.condEntropy_eq (hw t) (measurable_memoryState hw hm₀ t) (hw 0) hm₀

section Stationary

variable (hw : ∀ t, Measurable (w t)) (hs : IsStationary w μ)
include hw hs

/-- Under stationarity, `I (t + 1)` is the drop in conditional entropy as the past grows from
`t` words to `t + 1`. -/
theorem distanceInfo_succ (t : ℕ) :
    distanceInfo w μ (t + 1) = pastCondEntropy w μ t - pastCondEntropy w μ (t + 1) :=
  congrArg (· - _) <| ((hs 1 (t + 1)).comp
    (u := fun (v : Fin (t + 1) → W) ↦ (v (Fin.last t), fun i : Fin t ↦ v i.castSucc))
    (measurable_of_finite _)).condEntropy_eq (hw _) (measurable_block hw 1 t) (hw _)
    (measurable_block hw 0 t)

theorem pastCondEntropy_antitone : Antitone (pastCondEntropy w μ) :=
  antitone_nat_of_succ_le fun t ↦ by
    linarith [distanceInfo_succ hw hs t, distanceInfo_succ_nonneg (μ := μ) hw t]

/-- The memory allowance of the bound at `T`, by summation by parts. -/
theorem sum_Icc_mul_distanceInfo (T : ℕ) :
    ∑ t ∈ Icc 1 T, t * distanceInfo w μ t
      = ∑ t ∈ range T, pastCondEntropy w μ t - T * pastCondEntropy w μ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_Icc_succ_top (by omega), ih, distanceInfo_succ hw hs, sum_range_succ]
    push_cast
    ring

/-- The entropy rate plus the information at distances beyond `T` is the conditional entropy of
a word given the `T` words before it. -/
theorem entropyRate_add_tsum (T : ℕ) :
    entropyRate w μ + ∑' t, distanceInfo w μ (T + t + 1) = pastCondEntropy w μ T := by
  have hlim : Tendsto (pastCondEntropy w μ) atTop (𝓝 (entropyRate w μ)) :=
    tendsto_atTop_ciInf (pastCondEntropy_antitone hw hs)
      ⟨0, Set.forall_mem_range.mpr fun _ ↦ condEntropy_nonneg _ _ _⟩
  have htel (n : ℕ) :
      ∑ t ∈ range n, (pastCondEntropy w μ (T + t) - pastCondEntropy w μ (T + t + 1))
        = pastCondEntropy w μ T - pastCondEntropy w μ (T + n) :=
    sum_range_sub' (fun t ↦ pastCondEntropy w μ (T + t)) n
  have hsum : HasSum (fun t ↦ distanceInfo w μ (T + t + 1))
      (pastCondEntropy w μ T - entropyRate w μ) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun t ↦ distanceInfo_succ_nonneg hw _) _).mpr ?_
    simp_rw [distanceInfo_succ hw hs, htel]
    exact tendsto_const_nhds.sub
      (hlim.comp (tendsto_atTop_mono (fun n ↦ Nat.le_add_left n T) tendsto_id))
  rw [hsum.tsum_eq]
  ring

end Stationary

variable (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀)
  (hs : IsStationary (fun t ω ↦ (w t ω, memoryState M m₀ w t ω)) μ) {T : ℕ} (hT : 0 < T)
  (hmem : H[m₀ ; μ] ≤ ∑ t ∈ Icc 1 T, t * distanceInfo w μ t)
include hw hm₀ hs hT hmem

/-- A listener whose memory entropy is at most `∑ t ∈ Icc 1 T, t * I t` does no better than one
who remembers exactly the last `T` words. -/
theorem pastCondEntropy_le_condEntropy : pastCondEntropy w μ T ≤ H[w 0 | m₀ ; μ] := by
  have hblock := condEntropy_block_le_sum (μ := μ) (M := M) hw hm₀ T
  simp_rw [condEntropy_memoryState_eq hw hm₀ hs, sum_const, card_range, nsmul_eq_mul] at hblock
  have hb := measurable_block hw 0 T
  rw [sum_Icc_mul_distanceInfo hw hs.fst, ← entropy_block hw] at hmem
  refine le_of_mul_le_mul_left ?_ (by exact_mod_cast hT : (0 : ℝ) < T)
  linarith [chain_rule μ hb hm₀, chain_rule μ hm₀ hb, entropy_comm μ hb hm₀,
    condEntropy_nonneg m₀ (block w 0 T) μ]

/-- **The information locality bound**, the paper's Theorem 1. A listener whose memory entropy
is at most `∑ t ∈ Icc 1 T, t * I t` incurs average surprisal at least the entropy rate plus the
information at distances beyond `T`. -/
theorem information_locality_bound :
    entropyRate w μ + ∑' t, distanceInfo w μ (T + t + 1) ≤ H[w 0 | m₀ ; μ] :=
  entropyRate_add_tsum hw hs.fst T ▸ pastCondEntropy_le_condEntropy hw hm₀ hs hT hmem

end InformationLocality

/-! ### The Japanese suffix template

The supplement tabulates the relative orders of the Japanese verb suffixes in attested forms,
each segmented into a stem and its suffixes. Every suffix gloss names a suffix of the Fragment,
and the suffixes of every form are licensed by its template. -/

/-- The paper's glosses of the Japanese suffixes, as suffixes of the Fragment. -/
def japaneseSuffix? : String → Option (Σ σ, Japanese.Verb.Exponent σ)
  | "CAUS" => some ⟨_, .sase⟩
  | "PASS" => some ⟨_, .rare⟩
  | "POT" => some ⟨_, .potential⟩
  | "POL" => some ⟨_, .mas⟩
  | "DESID" => some ⟨_, .tai⟩
  | "NEG" => some ⟨_, .na⟩
  | "PST" => some ⟨_, .ta⟩
  | "HORT" => some ⟨_, .yoo⟩
  | _ => none

/-- The suffixes a row's gloss line names after the stem. -/
def japaneseSuffixes (r : LinguisticExample) : List (Σ σ, Japanese.Verb.Exponent σ) :=
  r.glossLine.tail.filterMap japaneseSuffix?

/-- The supplement's Japanese forms. -/
def japaneseForms : List LinguisticExample :=
  Examples.all.filter (·.language = "nucl1643")

/-- Every gloss after the stem of each of the supplement's Japanese forms names a suffix of
the Fragment, and the suffixes of the form are licensed by `Japanese.Verb.template`. -/
theorem japanese_forms_licensed :
    ∀ r ∈ japaneseForms, (japaneseSuffixes r).length + 1 = r.glossLine.length ∧
      Japanese.Verb.Licensed (japaneseSuffixes r) := by
  decide

/-! ### The Sesotho affix template

The paper's examples (2) and its supplement's table of Sesotho forms are segmented into a stem
and its affixes; every affix gloss names an affix of the Fragment, and the affixes of every form
are licensed by its template. -/

/-- The paper's glosses of the Sesotho affixes, as affixes of the Fragment. -/
def sesothoAffix? : String → Option (Σ σ, Sesotho.Verb.Exponent σ)
  | "SM" => some ⟨_, .subject⟩
  | "SR" => some ⟨_, .relativeSubject⟩
  | "NEG" => some ⟨_, .negative⟩
  | "FUT" => some ⟨_, .future⟩
  | "PRS" => some ⟨_, .present⟩
  | "POT" => some ⟨_, .potential⟩
  | "PERS" => some ⟨_, .persistive⟩
  | "REC" => some ⟨_, .recentPast⟩
  | "OM" => some ⟨_, .object⟩
  | "RFL" => some ⟨_, .reflexive⟩
  | "RV" => some ⟨_, .reversive⟩
  | "CAUS" => some ⟨_, .causative⟩
  | "NT" => some ⟨_, .neuter⟩
  | "APPL" => some ⟨_, .applicative⟩
  | "CL" => some ⟨_, .completive⟩
  | "RC" => some ⟨_, .reciprocal⟩
  | "PASS" => some ⟨_, .passive⟩
  | "PRF" => some ⟨_, .perfect⟩
  | "IND" => some ⟨_, .indicative⟩
  | "SBJV" => some ⟨_, .subjunctive⟩
  | "IMP" => some ⟨_, .imperative⟩
  | "IMP.PL" => some ⟨_, .imperativePlural⟩
  | "WH" => some ⟨_, .interrogative⟩
  | "REL" => some ⟨_, .relative⟩
  | _ => none

/-- The affixes a row's gloss line names, in linear order. -/
def sesothoAffixes (r : LinguisticExample) : List (Σ σ, Sesotho.Verb.Exponent σ) :=
  r.glossLine.filterMap sesothoAffix?

/-- The paper's Sesotho forms. -/
def sesothoForms : List LinguisticExample :=
  Examples.all.filter (·.language = "sout2807")

/-- Every gloss but the stem's in each of the paper's Sesotho forms names an affix of the
Fragment, and the affixes of the form are licensed by `Sesotho.Verb.template`. -/
theorem sesotho_forms_licensed :
    ∀ r ∈ sesothoForms, (sesothoAffixes r).length + 1 = r.glossLine.length ∧
      Sesotho.Verb.Licensed (sesothoAffixes r) := by
  decide

/-! ### Morpheme order and the relevance hierarchy

The paper classifies its slots as it lists them. In Japanese *suru* is derivation, the
causative valence, the passive and the potential voice, the desiderative mood, and the final
inflection tense, aspect, mood and finiteness, compared here as tense; politeness has no place
in [bybee-1985]'s inventory and is left out of the comparison. In Sesotho the reversive is
derivation, the extensions valence, the passive voice, the perfect tense, the mood ending mood,
the subject and object markers agreement, the tense prefixes tense, and the interrogative and
relative markers the substrate's nonfinite class, which houses them. -/

/-- The paper's classification of the Sesotho affix positions in [bybee-1985]'s inventory. -/
def sesothoCategory? : Sesotho.Verb.Slot → Option MorphCategory
  | .subject => some (.agreement .subj)
  | .negation => some .negation
  | .tam => some .tense
  | .object => some (.agreement .obj)
  | .reversive => some .derivation
  | .extension => some .valence
  | .voice => some .voice
  | .tense => some .tense
  | .mood => some .mood
  | .interrogativeRelative => some .nonfinite

/-- The Sesotho suffix order in Bybee's vocabulary, stem-outward. -/
def sesothoSuffixCategories : List MorphCategory :=
  Sesotho.Verb.suffixes.filterMap sesothoCategory?

/-- The Sesotho prefix order in Bybee's vocabulary, stem-outward. -/
def sesothoPrefixCategories : List MorphCategory :=
  Sesotho.Verb.prefixes.reverse.filterMap sesothoCategory?

/-- The paper's classification of the Japanese suffix positions in [bybee-1985]'s inventory. -/
def bybeeCategory? : Japanese.Verb.Slot → Option MorphCategory
  | .derivation => some .derivation
  | .valence => some .valence
  | .voice => some .voice
  | .politeness => none
  | .desiderative => some .mood
  | .negation => some .negation
  | .inflection => some .tense

/-- The Japanese suffix order in Bybee's vocabulary. -/
def japaneseCategories : List MorphCategory := Japanese.Verb.slots.filterMap bybeeCategory?

/-- Sesotho's suffixes, the reversive, the extensions, the passive, the perfect, the mood
ending and the interrogative or relative marker, are sorted by the relevance hierarchy, which
on the surveyed categories is [bybee-1985]'s order, `Bybee1985.survey_order_iso_relevance`. -/
theorem sesotho_suffixes_respect_relevance : sesothoSuffixCategories.SortedLE := by decide

/-- The paper's claim for the prefixes is that subject agreement lies farther from the stem
than the tense prefixes, which holds; but the object marker lies inside them, so the prefix
order read stem-outward is not sorted by the hierarchy. -/
theorem sesotho_prefixes_violate_relevance :
    (∀ a ∈ sesothoCategory? .tam, ∀ b ∈ sesothoCategory? .subject, a < b) ∧
      ¬ sesothoPrefixCategories.SortedLE := by
  decide

/-- Japanese is sorted by the hierarchy up to its final inflection: derivation, valence, voice,
mood and negation. -/
theorem japanese_partial_relevance : japaneseCategories.dropLast.SortedLE := by decide

/-- [bybee-1985]'s survey ranks tense closer to the stem than mood,
`Bybee1985.SurveyedCloser`, yet the Japanese desiderative, a mood suffix, precedes tense, so
the suffix order is not sorted by the relevance hierarchy. The paper's "broadly in agreement"
is not agreement. -/
theorem japanese_violates_surveyed_relevance :
    Bybee1985.SurveyedCloser .tense .mood ∧ ¬ japaneseCategories.SortedLE := by
  decide

end HahnDegenFutrell2021
