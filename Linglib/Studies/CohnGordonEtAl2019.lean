import Linglib.Pragmatics.RSA.Uniform

/-!
# Cohn-Gordon, Goodman and Potts 2019: incremental Rational Speech Acts

Iterated response models compute pragmatic reasoning over complete utterances; the paper
moves the reasoning inside the utterance. Utterances are word sequences from a closed set,
an incremental semantics scores a prefix at a referent by the fraction of its complete
extensions true of the referent among those true of some referent (§2.2), a word-level
literal listener renormalizes that score (eq. 4), a word-level speaker best-responds at
each prefix (eq. 5, with probability distributed evenly over words with viable
continuations when no continuation is true), and the chain rule multiplies the word
choices into an utterance-level speaker (eq. 7). On the Figure 1 reference game the
architectures come apart: the global speaker prefers the fully informative *red dress*
for the red dress while the incremental product prefers bare *dress* (Figures 1b, 1e),
and upon hearing *red* the incremental listener already favours the red hat at 0.64 —
the anticipatory implicature (Figure 1d). The abstract two-letter game of Figure 3
separates the architectures even at equal global informativity. Any complete utterance
true of its referent is weakly informative — the literal listener assigns the referent
at least chance probability — which is the paper's certificate for greedy word-by-word
unrolling (§2.4).

With a cost of one per word and none for the STOP token (§3.1), the global speaker
prefers the bare noun in English and Spanish alike, but the incremental speaker is
indifferent between *dress* and *red dress* while preferring *vestido* to *vestido
rojo*: after *red* the English speaker is committed to the over-modified continuation,
after *vestido* the Spanish speaker may stop — Rubio-Fernández's over-modification
asymmetry between adjective–noun and noun–adjective languages. Hearing *tall* in
Sedivy's display, the incremental pragmatic listener favours the tall cup over the tall
pitcher at 0.6, since a speaker referring to the pitcher had no use for the modifier
(§3.2); the implicature cancels, since after *tall pitcher* the listener excludes every
referent but the pitcher.

## Implementation notes

* The reference game carries an utterance-level Boolean semantics, as the paper's
  incremental semantics is "defined in terms of a global semantics and the set of
  available complete utterances" (§2.2); word-conjunctive semantics is a constructor,
  since Figure 3's semantics is not compositional.
* Word-level agents are the kernel pipeline at prefix-indexed graded meanings; the
  uniform prior and the viable-extension denominator cancel in the literal listener, so
  every cell is a ratio of extension counts, which `decide` evaluates.
* Chain-rule trajectory probabilities are real-valued products of speaker masses, so the
  §3.1 comparisons are real arithmetic in the content-word cost factor, the paper's
  `e⁻¹` generalized to any factor below one.
* Kernels are noncomputable, so the greedy unroller is a per-referent table, certified
  to land in the utterance set and to be true of its target — all that §2.4's bound
  uses.

## TODO

* §4's TUNA-corpus comparison (the share of two-word optima under each architecture) is
  an experiment over corpus trials, not formalizable content.
* The general §2.4 claim that greedy unrolling always terminates in a true complete
  utterance is argued informally in the paper; here it is certified for Figure 1.

## References

* [R. Cohn-Gordon, N. D. Goodman and C. Potts, *An Incremental Iterated Response Model
  of Pragmatics* (2019)][cohn-gordon-goodman-potts-2019]
* [P. Rubio-Fernández, *How Redundant Are Redundant Color Adjectives? An Efficiency-Based
  Analysis of Color Overspecification* (2016)][rubio-fernandez-2016]
* [J. C. Sedivy, *Implicature During Real Time Conversation: A View from Language
  Processing Research* (2007)][sedivy-2007]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace CohnGordonEtAl2019

/-! ### Reference games and the incremental semantics (§2.2) -/

/-- A reference game (Figure 1a): a closed set of complete utterances over words `U`, an
utterance-level Boolean semantics, and the referents on display. -/
structure ReferenceGame (U W : Type) where
  /-- The closed set of available complete utterances. -/
  utterances : List (List U)
  /-- The global semantics `⟦·⟧`: truth of a complete utterance at a referent. -/
  sem : List U → W → Bool
  /-- The referents on display. -/
  worlds : List W

namespace ReferenceGame

variable {U W : Type}

/-- A game whose semantics is word-conjunctive, from a lexicon of word extensions. -/
def ofLexicon (applies : U → W → Bool) (utts : List (List U)) (ws : List W) :
    ReferenceGame U W :=
  ⟨utts, fun u r => u.all fun w => applies w r, ws⟩

variable [DecidableEq U] (g : ReferenceGame U W)

/-- The number of complete extensions of `pfx` true of `r`. -/
def trueExts (pfx : List U) (r : W) : ℕ :=
  (g.utterances.filter fun u => pfx.isPrefixOf u && g.sem u r).length

/-- The number of complete extensions of `pfx` true of some referent on display. -/
def viableExts (pfx : List U) : ℕ :=
  (g.utterances.filter fun u => pfx.isPrefixOf u && g.worlds.any fun r => g.sem u r).length

theorem trueExts_le_viableExts (hw : ∀ r : W, r ∈ g.worlds) (pfx : List U) (r : W) :
    g.trueExts pfx r ≤ g.viableExts pfx := by
  simp only [trueExts, viableExts, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun u _ h => by
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, List.any_eq_true.mpr ⟨r, hw r, h.2⟩⟩

/-- The incremental semantics `⟦pfx⟧(r)` (§2.2): the fraction of complete extensions of
`pfx` true of `r` among those true of some referent on display. -/
noncomputable def incSem (pfx : List U) (r : W) : ℝ≥0∞ :=
  (g.trueExts pfx r : ℝ≥0∞) / (g.viableExts pfx : ℝ≥0∞)

/-! ### The word-level pipeline (eqs. 4–6) -/

variable [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
  [Fintype W] [Nonempty W] [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-- The incremental literal listener at context `ctx` (eq. 4): the uniform prior
reweighted by `⟦ctx ++ [u]⟧`. -/
noncomputable def l0 (ctx : List U) : Kernel U W :=
  literalListener (uniformOn Set.univ) fun u => g.incSem (ctx ++ [u])

/-- The uniform prior and the viable-extension denominator cancel in the listener: each
cell is the referent's share of the true-extension counts. -/
theorem l0_apply (hw : ∀ r : W, r ∈ g.worlds) (ctx : List U) (u : U) (r : W) :
    g.l0 ctx u {r}
      = (g.trueExts (ctx ++ [u]) r : ℝ≥0∞) / (∑ r', (g.trueExts (ctx ++ [u]) r' : ℕ) : ℕ) := by
  rw [l0, literalListener_uniformOn_apply_singleton]
  push_cast
  rcases Nat.eq_zero_or_pos (g.viableExts (ctx ++ [u])) with hv | hv
  · have ht : ∀ r' : W, g.trueExts (ctx ++ [u]) r' = 0 := fun r' =>
      Nat.le_zero.mp (hv ▸ g.trueExts_le_viableExts hw _ r')
    simp [incSem, ht]
  · simp_rw [incSem, div_eq_mul_inv, ← Finset.sum_mul]
    exact ENNReal.mul_div_mul_right _ _
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hv.ne'))

omit [Fintype W] [Nonempty W] [DiscreteMeasurableSpace W] in
theorem l0_apply_le_one (ctx : List U) (u : U) (s : Set W) : g.l0 ctx u s ≤ 1 :=
  literalListener_apply_le_one _ _ u s

/-- Dead end (§2.2): no continuation of `ctx` is true of `r`. -/
def DeadEnd (ctx : List U) (r : W) : Prop :=
  ∀ u : U, g.trueExts (ctx ++ [u]) r = 0

instance (ctx : List U) (r : W) : Decidable (g.DeadEnd ctx r) :=
  inferInstanceAs (Decidable (∀ u : U, g.trueExts (ctx ++ [u]) r = 0))

/-- The word-level speaker at context `ctx` (eq. 5): the best response to the incremental
literal listener; at a dead end, probability is distributed evenly over the words with
viable continuations. -/
noncomputable def s1 (cost : U → ℝ≥0∞) (ctx : List U) : Kernel W U :=
  Kernel.ofFunOfCountable fun r =>
    if g.DeadEnd ctx r then
      uniformOn ↑(Finset.univ.filter fun u : U => 0 < g.viableExts (ctx ++ [u]))
    else speaker 1 cost (g.l0 ctx) r

omit [Nonempty W] in
theorem s1_apply {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r) (cost : U → ℝ≥0∞) :
    g.s1 cost ctx r = speaker 1 cost (g.l0 ctx) r := by
  rw [s1, Kernel.ofFunOfCountable_apply, if_neg hnd]

omit [Nonempty W] in
theorem s1_apply_deadEnd {ctx : List U} {r : W} (hd : g.DeadEnd ctx r) (cost : U → ℝ≥0∞) :
    g.s1 cost ctx r
      = uniformOn ↑(Finset.univ.filter fun u : U => 0 < g.viableExts (ctx ++ [u])) := by
  rw [s1, Kernel.ofFunOfCountable_apply, if_pos hd]

instance (cost : U → ℝ≥0∞) (ctx : List U) : IsFiniteKernel (g.s1 cost ctx) :=
  ⟨⟨1, ENNReal.one_lt_top, fun r => by
    rw [s1, Kernel.ofFunOfCountable_apply]
    split_ifs with h
    · exact prob_le_one
    · exact Kernel.ofWeights_apply_univ_le_one _ r⟩⟩

/-- The incremental pragmatic listener at context `ctx` (eq. 6): the posterior of the
word-level speaker against the uniform prior. -/
noncomputable def l1 [StandardBorelSpace W] (cost : U → ℝ≥0∞) (ctx : List U) : Kernel U W :=
  (g.s1 cost ctx)†(uniformOn (Set.univ : Set W))

instance [StandardBorelSpace W] (cost : U → ℝ≥0∞) (ctx : List U) :
    IsMarkovKernel (g.l1 cost ctx) :=
  inferInstanceAs (IsMarkovKernel ((g.s1 cost ctx)†(uniformOn (Set.univ : Set W))))

/-- The chain-rule product from context `ctx` on: the word-level speaker's remaining
choices. -/
noncomputable def s1Chain (cost : U → ℝ≥0∞) (r : W) : List U → List U → ℝ
  | _, [] => 1
  | ctx, u :: rest => (g.s1 cost ctx r).real {u} * s1Chain cost r (ctx ++ [u]) rest

/-- The utterance-level incremental speaker (eq. 7): the chain-rule product of the
word-level speaker's choices along the utterance. -/
noncomputable def s1Utt (cost : U → ℝ≥0∞) (r : W) (u : List U) : ℝ :=
  g.s1Chain cost r [] u

omit [Nonempty W] in
/-- The speaker's share in real terms: weighted listener values over their row sum. -/
theorem s1_real_singleton {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r)
    {cost : U → ℝ≥0∞} (hc : ∀ u, cost u ≠ ∞) (u : U) :
    (g.s1 cost ctx r).real {u}
      = (g.l0 ctx u {r}).toReal * (cost u).toReal
        / ∑ u', (g.l0 ctx u' {r}).toReal * (cost u').toReal := by
  have hfin : ∀ u' : U, g.l0 ctx u' {r} ^ (1 : ℝ) * cost u' ≠ ∞ := by
    intro u'
    refine ENNReal.mul_ne_top ?_ (hc u')
    rw [ENNReal.rpow_one]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (g.l0_apply_le_one ctx u' {r})
  rw [measureReal_def, s1_apply g hnd, speaker_apply_singleton, ENNReal.toReal_div,
    ENNReal.toReal_sum fun u' _ => hfin u']
  simp_rw [ENNReal.toReal_mul, ENNReal.rpow_one]

/-! ### The global model (§2.1) -/

/-- The complete utterances of the game, as a type. -/
def Complete : Type := {u : List U // u ∈ g.utterances}

instance : Fintype g.Complete :=
  Fintype.subtype g.utterances.toFinset fun _ => List.mem_toFinset

instance : MeasurableSpace g.Complete := ⊤
instance : DiscreteMeasurableSpace g.Complete := ⟨fun _ => trivial⟩
instance : DecidableEq g.Complete := Subtype.instDecidableEq

/-- The global literal listener (eq. 1): the uniform prior conditioned on the utterance's
truth. -/
noncomputable def globalL0 : Kernel g.Complete W :=
  literalListener (uniformOn Set.univ) fun u r => if g.sem u.val r then 1 else 0

/-- The global pragmatic speaker (eq. 2). -/
noncomputable def globalS1 (cost : g.Complete → ℝ≥0∞) : Kernel W g.Complete :=
  speaker 1 cost g.globalL0

/-- The multiplicative cost factor of an utterance: the product of its words' factors
(§3.1's additive log costs). -/
noncomputable def uttCost (cost : U → ℝ≥0∞) (u : List U) : ℝ≥0∞ := (u.map cost).prod

omit [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] in
theorem globalL0_apply (u : g.Complete) (r : W) :
    g.globalL0 u {r}
      = (if g.sem u.val r then 1 else 0)
        / ((Finset.univ.filter fun r' => g.sem u.val r').card : ℝ≥0∞) := by
  rw [globalL0, literalListener_uniformOn_apply_singleton]
  congr 1
  rw [Finset.sum_boole]

omit [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] in
/-- §2.4's weak informativity: a complete utterance true of a referent gives the literal
listener at least chance probability of it. -/
theorem globalL0_ge_inv_card {u : g.Complete} {r : W} (htrue : g.sem u.val r = true) :
    ((Fintype.card W : ℝ≥0∞))⁻¹ ≤ g.globalL0 u {r} := by
  rw [globalL0_apply, if_pos htrue]
  calc ((Fintype.card W : ℝ≥0∞))⁻¹
      ≤ (((Finset.univ.filter fun r' => g.sem u.val r').card : ℕ) : ℝ≥0∞)⁻¹ := by
        refine ENNReal.inv_le_inv' ?_
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    _ = 1 / _ := (one_div _).symm

omit [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] [Fintype W] [Nonempty W]
  [DiscreteMeasurableSpace W] in
theorem globalL0_apply_le_one (u : g.Complete) (s : Set W) : g.globalL0 u s ≤ 1 :=
  literalListener_apply_le_one _ _ u s

/-! ### Evaluation lemmas -/

theorem l0_apply_ne_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {u : U} {r : W}
    (ht : g.trueExts (ctx ++ [u]) r ≠ 0) : g.l0 ctx u {r} ≠ 0 := by
  rw [l0_apply g hw, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast ht, ENNReal.natCast_ne_top _⟩

theorem l0_apply_eq_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {u : U} {r : W}
    (ht : g.trueExts (ctx ++ [u]) r = 0) : g.l0 ctx u {r} = 0 := by
  rw [l0_apply g hw, ht, Nat.cast_zero, ENNReal.zero_div]

/-- The real-valued listener cell: the referent's share of the true-extension counts. -/
theorem l0_real (hw : ∀ r : W, r ∈ g.worlds) (ctx : List U) (u : U) (r : W) :
    (g.l0 ctx u {r}).toReal
      = (g.trueExts (ctx ++ [u]) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u]) r' : ℕ) := by
  rw [l0_apply g hw, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

theorem s1_weight_ne_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {u : U} {r : W}
    (ht : g.trueExts (ctx ++ [u]) r ≠ 0) {cost : U → ℝ≥0∞} (hc : cost u ≠ 0) :
    g.l0 ctx u {r} ^ (1 : ℝ) * cost u ≠ 0 :=
  mul_ne_zero (by rw [ENNReal.rpow_one]; exact g.l0_apply_ne_zero hw ht) hc

omit [Nonempty W] in
/-- Row preference of the incremental speaker compares weighted listener cells. -/
theorem s1_real_lt_iff {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r)
    {cost : U → ℝ≥0∞} (hctop : ∀ u, cost u ≠ ∞) {u₀ : U}
    (h0 : g.l0 ctx u₀ {r} ^ (1 : ℝ) * cost u₀ ≠ 0) {u u' : U} :
    (g.s1 cost ctx r).real {u} < (g.s1 cost ctx r).real {u'} ↔
      g.l0 ctx u {r} * cost u < g.l0 ctx u' {r} * cost u' := by
  rw [s1_apply g hnd, speaker_real_singleton_lt_iff zero_le_one hctop
    (fun u'' => g.l0_apply_le_one ctx u'' {r}) ⟨u₀, h0⟩]
  simp_rw [ENNReal.rpow_one]

theorem s1_apply_ne_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ≥0∞} (hc0 : ∀ u', cost u' ≠ 0)
    (hctop : ∀ u', cost u' ≠ ∞) (ht : g.trueExts (ctx ++ [u]) r ≠ 0) :
    g.s1 cost ctx r {u} ≠ 0 := by
  rw [s1_apply g hnd]
  exact speaker_apply_singleton_ne_zero zero_le_one hc0 hctop
    (fun u' => g.l0_apply_le_one ctx u' {r}) (g.l0_apply_ne_zero hw ht)

/-- A word with no true continuation is never chosen off a dead end. -/
theorem s1_apply_eq_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) (cost : U → ℝ≥0∞)
    (ht : g.trueExts (ctx ++ [u]) r = 0) : g.s1 cost ctx r {u} = 0 := by
  rw [s1_apply g hnd]
  exact speaker_apply_singleton_eq_zero one_pos (g.l0_apply_eq_zero hw ht)

/-- A referent whose only true continuation is `u` is signalled with certainty. -/
theorem s1_apply_eq_one (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ≥0∞} (hc0 : cost u ≠ 0) (hctop : cost u ≠ ∞)
    (ht : g.trueExts (ctx ++ [u]) r ≠ 0)
    (hother : ∀ u' ≠ u, g.trueExts (ctx ++ [u']) r = 0) :
    g.s1 cost ctx r {u} = 1 := by
  rw [s1_apply g hnd]
  exact speaker_apply_singleton_eq_one one_pos hc0 hctop (g.l0_apply_ne_zero hw ht)
    (g.l0_apply_le_one ctx u {r}) fun u' hu' => g.l0_apply_eq_zero hw (hother u' hu')

/-- Listener preference upon a word compares the speaker's masses: the uniform prior
cancels. -/
theorem l1_real_lt_iff [StandardBorelSpace W] {cost : U → ℝ≥0∞} {ctx : List U} {u : U}
    (hx : (g.s1 cost ctx ∘ₘ uniformOn (Set.univ : Set W)) {u} ≠ 0) {r r' : W} :
    (g.l1 cost ctx u).real {r} < (g.l1 cost ctx u).real {r'} ↔
      (g.s1 cost ctx r).real {u} < (g.s1 cost ctx r').real {u} := by
  rw [l1, ← Finset.coe_singleton, ← Finset.coe_singleton r',
    posterior_real_finset_lt_iff _ _ hx, Finset.sum_singleton, Finset.sum_singleton,
    uniformOn_univ_real_singleton, uniformOn_univ_real_singleton,
    mul_comm ((Fintype.card W : ℝ))⁻¹, mul_comm ((Fintype.card W : ℝ))⁻¹,
    mul_lt_mul_iff_left₀ (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))]

/-- Exact Bayes for the incremental listener. -/
theorem l1_real_singleton [StandardBorelSpace W] {cost : U → ℝ≥0∞} {ctx : List U} {u : U}
    (hx : (g.s1 cost ctx ∘ₘ uniformOn (Set.univ : Set W)) {u} ≠ 0) (r : W) :
    (g.l1 cost ctx u).real {r}
      = (g.s1 cost ctx r).real {u} / ∑ r', (g.s1 cost ctx r').real {u} := by
  rw [l1, posterior_real_singleton _ _ hx, Measure.comp_real_singleton]
  simp_rw [uniformOn_univ_real_singleton, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))]

/-- At no cost, the speaker's share is a double ratio of extension counts. -/
theorem s1_real_counts (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W}
    (hnd : ¬ g.DeadEnd ctx r) (u : U) :
    (g.s1 1 ctx r).real {u}
      = ((g.trueExts (ctx ++ [u]) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u]) r' : ℕ))
        / ∑ u', ((g.trueExts (ctx ++ [u']) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u']) r' : ℕ)) := by
  rw [s1_real_singleton g (cost := 1) hnd fun _ => ENNReal.one_ne_top]
  simp_rw [Pi.one_apply, ENNReal.toReal_one, mul_one, l0_real g hw]

end ReferenceGame

private theorem natCast_div_lt {a b c d : ℕ} (hd : d ≠ 0) (hab : a * d < c * b) :
    (a : ℝ≥0∞) / (b : ℕ) < (c : ℝ≥0∞) / (d : ℕ) := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness), ENNReal.toReal_div,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast,
    div_lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hb)
      (by exact_mod_cast Nat.pos_of_ne_zero hd)]
  exact_mod_cast hab

/-! ### Figure 1: the reference game -/

/-- The words of Figure 1a. -/
inductive Word
  | red | dress | object
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.red⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ => trivial⟩

/-- The referents of Figure 1a: the red dress R1, the blue dress R2, the red hat R3. -/
inductive Referent
  | redDress | blueDress | redHat
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.redDress⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ => trivial⟩

/-- Figure 1a: three utterances with word-conjunctive semantics over three referents. -/
def figureOne : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r => match u, r with
      | .red, .redDress | .red, .redHat | .dress, .redDress | .dress, .blueDress
      | .object, _ => true
      | _, _ => false)
    [[.dress], [.red, .dress], [.red, .object]]
    [.redDress, .blueDress, .redHat]

private theorem fig1_hw : ∀ r : Referent, r ∈ figureOne.worlds := by decide

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Word → M) :
    ∑ u, f u = f .red + (f .dress + f .object) := by
  rw [show (Finset.univ : Finset Word) = {.red, .dress, .object} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Figure 1c, R1 row: the speaker leads with *red*, keeping both red referents viable,
while *dress* dilutes the listener over the two dresses. -/
theorem adj_first_for_target :
    (figureOne.s1 1 [] .redDress).real {Word.dress}
      < (figureOne.s1 1 [] .redDress).real {Word.red} := by
  rw [figureOne.s1_real_lt_iff (cost := 1) (by decide) (fun _ => ENNReal.one_ne_top)
    (figureOne.s1_weight_ne_zero (u := Word.dress) fig1_hw (by decide) one_ne_zero)]
  simp only [Pi.one_apply, mul_one]
  rw [figureOne.l0_apply fig1_hw, figureOne.l0_apply fig1_hw]
  exact natCast_div_lt (by decide) (by decide)

/-- Figure 1c, R1 row after *red*: the speaker completes with *dress*, unique to R1. -/
theorem noun_after_adj :
    (figureOne.s1 1 [.red] .redDress).real {Word.object}
      < (figureOne.s1 1 [.red] .redDress).real {Word.dress} := by
  rw [figureOne.s1_real_lt_iff (cost := 1) (by decide) (fun _ => ENNReal.one_ne_top)
    (figureOne.s1_weight_ne_zero (u := Word.dress) fig1_hw (by decide) one_ne_zero)]
  simp only [Pi.one_apply, mul_one]
  rw [figureOne.l0_apply fig1_hw, figureOne.l0_apply fig1_hw]
  exact natCast_div_lt (by decide) (by decide)

/-- Figure 1c, R2 row: the blue dress forces *dress* as the first word. -/
theorem noun_only_for_r2 : figureOne.s1 1 [] .blueDress {Word.dress} = 1 :=
  figureOne.s1_apply_eq_one fig1_hw (by decide) one_ne_zero ENNReal.one_ne_top (by decide)
    (by decide)

/-- Figure 1c, R3 row: the red hat forces *red* as the first word. -/
theorem adj_only_for_r3 : figureOne.s1 1 [] .redHat {Word.red} = 1 :=
  figureOne.s1_apply_eq_one fig1_hw (by decide) one_ne_zero ENNReal.one_ne_top (by decide)
    (by decide)

/-- Figure 1c, R2 row after *red* — the §2.2 dead end: no continuation is true of the blue
dress, and probability distributes evenly over the words with viable continuations. -/
theorem uniform_after_red_for_r2 :
    (figureOne.s1 1 [.red] .blueDress).real {Word.dress} = 1 / 2 ∧
    (figureOne.s1 1 [.red] .blueDress).real {Word.object} = 1 / 2 ∧
    (figureOne.s1 1 [.red] .blueDress).real {Word.red} = 0 := by
  have h := figureOne.s1_apply_deadEnd (ctx := [.red]) (r := .blueDress) (by decide) 1
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [measureReal_def, h, uniformOn_finset_apply_singleton] <;>
    · rw [show (Finset.univ.filter fun u : Word =>
          0 < figureOne.viableExts ([Word.red] ++ [u])) = {Word.dress, Word.object} from by
          decide]
      norm_num [show ({Word.dress, Word.object} : Finset Word).card = 2 from rfl,
        show (Word.red = Word.dress ∨ Word.red = Word.object) = False from by simp]

/-! ### Figure 1d: the anticipatory implicature -/

/-- The four speaker cells behind Figures 1c–1e, at no cost, in closed form. -/
theorem s1_figureOne_values :
    (figureOne.s1 1 [] .redDress).real {Word.red} = 4 / 7 ∧
    (figureOne.s1 1 [] .redDress).real {Word.dress} = 3 / 7 ∧
    (figureOne.s1 1 [.red] .redDress).real {Word.dress} = 2 / 3 ∧
    (figureOne.s1 1 [] .redHat).real {Word.red} = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red] .redDress = 2 from rfl,
      show ∑ r', figureOne.trueExts [Word.red] r' = 3 from rfl,
      show figureOne.trueExts [Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.dress] r' = 2 from rfl,
      show figureOne.trueExts [Word.object] .redDress = 0 from rfl]
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red] .redDress = 2 from rfl,
      show ∑ r', figureOne.trueExts [Word.red] r' = 3 from rfl,
      show figureOne.trueExts [Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.dress] r' = 2 from rfl,
      show figureOne.trueExts [Word.object] .redDress = 0 from rfl]
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red, Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.red, Word.dress] r' = 1 from rfl,
      show figureOne.trueExts [Word.red, Word.object] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.red, Word.object] r' = 2 from rfl,
      show figureOne.trueExts [Word.red, Word.red] .redDress = 0 from rfl]
  · rw [measureReal_def, adj_only_for_r3, ENNReal.toReal_one]

private theorem red_marginal_ne_zero :
    (figureOne.s1 1 [] ∘ₘ uniformOn (Set.univ : Set Referent)) {Word.red} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (w := Referent.redHat)
    (uniformOn_univ_singleton_ne_zero _)
    (by rw [adj_only_for_r3]; exact one_ne_zero)

/-- Figure 1d — the anticipatory implicature: upon hearing *red*, the incremental listener
favours the red hat over the red dress, since *red* is the hat's only opening while the
dress's speaker had alternatives. -/
theorem listener_anticipation :
    (figureOne.l1 1 [] .red).real {Referent.redDress}
      < (figureOne.l1 1 [] .red).real {Referent.redHat} := by
  rw [figureOne.l1_real_lt_iff red_marginal_ne_zero]
  rw [s1_figureOne_values.1, measureReal_def, adj_only_for_r3, ENNReal.toReal_one]
  norm_num

private theorem r2_never_opens_red : (figureOne.s1 1 [] .blueDress).real {Word.red} = 0 := by
  rw [figureOne.s1_real_counts fig1_hw (by decide)]
  norm_num [show figureOne.trueExts [Word.red] .blueDress = 0 from rfl]

/-- Figure 1d, exactly: `L1(R3 | red) = 1 / (4/7 + 0 + 1) = 7/11 ≈ 0.64` — the paper's
0.64. -/
theorem listener_anticipation_value :
    (figureOne.l1 1 [] .red).real {Referent.redHat} = 7 / 11 := by
  rw [figureOne.l1_real_singleton red_marginal_ne_zero,
    show (Finset.univ : Finset Referent) = {.redDress, .blueDress, .redHat} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    s1_figureOne_values.1, r2_never_opens_red, measureReal_def, adj_only_for_r3,
    ENNReal.toReal_one]
  norm_num

/-! ### Figure 1e: the chain-rule wedge -/

/-- Figure 1e, R1 row: the chain-rule utterance-level speaker (eq. 7) prefers bare *dress*
(3/7) to *red dress* (4/7 · 2/3 = 8/21) — the architectural wedge against Figure 1b, where
the global speaker prefers *red dress*. -/
theorem incremental_prefers_bare_noun :
    figureOne.s1Utt 1 .redDress [.red, .dress] < figureOne.s1Utt 1 .redDress [.dress] := by
  obtain ⟨h1, h2, h3, -⟩ := s1_figureOne_values
  simp only [ReferenceGame.s1Utt, ReferenceGame.s1Chain, List.nil_append, mul_one]
  rw [h1, h2, h3]
  norm_num

/-! ### The global model on Figure 1 (§2.1, Figure 1b) -/

private theorem fig1_mem_dress : [Word.dress] ∈ figureOne.utterances := by decide
private theorem fig1_mem_redDress : [Word.red, Word.dress] ∈ figureOne.utterances := by decide

/-- Figure 1b: the global pragmatic speaker prefers *red dress* (1/2) to bare *dress*
(1/4) for the red dress — the preference the chain rule reverses. -/
theorem global_prefers_red_dress :
    (figureOne.globalS1 1 .redDress).real {⟨[.dress], fig1_mem_dress⟩}
      < (figureOne.globalS1 1 .redDress).real {⟨[.red, .dress], fig1_mem_redDress⟩} := by
  have key : ∀ (u : figureOne.Complete),
      figureOne.globalL0 u {Referent.redDress}
        = (if figureOne.sem u.val .redDress then 1 else 0)
          / ((Finset.univ.filter fun r' => figureOne.sem u.val r').card : ℝ≥0∞) :=
    fun u => figureOne.globalL0_apply u .redDress
  refine (speaker_real_singleton_lt_iff (cost := 1) zero_le_one
    (fun _ => ENNReal.one_ne_top) (fun u => figureOne.globalL0_apply_le_one u _)
    ⟨⟨[.red, .dress], fig1_mem_redDress⟩, by
      rw [ENNReal.rpow_one, Pi.one_apply, mul_one, key]
      norm_num [show figureOne.sem [Word.red, Word.dress] .redDress = true from rfl,
        show (Finset.univ.filter fun r' =>
          figureOne.sem [Word.red, Word.dress] r').card = 1 from rfl]⟩).mpr ?_
  simp only [ENNReal.rpow_one, Pi.one_apply, mul_one, key]
  rw [show figureOne.sem [Word.dress] .redDress = true from rfl,
    show figureOne.sem [Word.red, Word.dress] .redDress = true from rfl,
    show (Finset.univ.filter fun r' => figureOne.sem [Word.dress] r').card = 2 from rfl,
    show (Finset.univ.filter fun r' => figureOne.sem [Word.red, Word.dress] r').card = 1
      from rfl, Nat.cast_one, Nat.cast_ofNat, div_one]
  exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top

/-! ### §2.4: greedy unrolling and weak informativity -/

/-- The greedy unrolling of Figure 1 (§2.3): the word-by-word argmax trajectory per
referent. -/
def greedyUnroll : Referent → List Word
  | .redDress => [.red, .dress]
  | .blueDress => [.dress]
  | .redHat => [.red, .object]

/-- Greedy unrolling lands in the utterance set. -/
theorem greedyUnroll_complete (r : Referent) : greedyUnroll r ∈ figureOne.utterances := by
  cases r <;> decide

/-- Greedy unrolling produces a true utterance. -/
theorem greedyUnroll_true (r : Referent) : figureOne.sem (greedyUnroll r) r = true := by
  cases r <;> decide

/-- §2.4's weak informativity for Figure 1: the global literal listener gives the target of
each greedy output at least chance probability. -/
theorem greedyUnroll_weakly_informative (r : Referent) :
    ((Fintype.card Referent : ℝ≥0∞))⁻¹
      ≤ figureOne.globalL0 ⟨greedyUnroll r, greedyUnroll_complete r⟩ {r} :=
  figureOne.globalL0_ge_inv_card (greedyUnroll_true r)

/-! ### Figure 3: the abstract two-letter game

Four utterances AA, AB, BA, BB over two worlds; every pair is true except (AB, W1). The
global speaker is indifferent among W1's three true utterances, while the chain rule
prefers AA: choosing A first costs informativity (AB is false of W1), but the second
letter is then forced, and 2/5 · 1 beats 3/5 · 1/2. -/

/-- The two letters. -/
inductive Letter
  | A | B
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Letter := ⟨.A⟩
instance : MeasurableSpace Letter := ⊤
instance : DiscreteMeasurableSpace Letter := ⟨fun _ => trivial⟩

/-- The two worlds. -/
inductive AbstractWorld
  | W1 | W2
  deriving DecidableEq, Fintype, Repr

instance : Nonempty AbstractWorld := ⟨.W1⟩
instance : MeasurableSpace AbstractWorld := ⊤
instance : DiscreteMeasurableSpace AbstractWorld := ⟨fun _ => trivial⟩

/-- Figure 3's game: the semantics is a table, not word-conjunctive. -/
def figureThree : ReferenceGame Letter AbstractWorld where
  utterances := [[.A, .A], [.A, .B], [.B, .A], [.B, .B]]
  sem u r := !(decide (u = [.A, .B]) && decide (r = .W1))
  worlds := [.W1, .W2]

private theorem fig3_hw : ∀ r : AbstractWorld, r ∈ figureThree.worlds := by decide

private theorem sum_letter {M : Type*} [AddCommMonoid M] (f : Letter → M) :
    ∑ u, f u = f .A + f .B := by
  rw [show (Finset.univ : Finset Letter) = {.A, .B} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Figure 3, red: the chain rule strictly prefers AA (0.4) to BA (0.3) for W1. -/
theorem figureThree_incremental_prefers_AA :
    figureThree.s1Utt 1 .W1 [.B, .A] < figureThree.s1Utt 1 .W1 [.A, .A] := by
  simp only [ReferenceGame.s1Utt, ReferenceGame.s1Chain, List.nil_append, mul_one]
  rw [figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter]
  norm_num [show figureThree.trueExts [Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.B] .W1 = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A] r' = 3 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B] r' = 4 from by decide,
    show figureThree.trueExts [Letter.A, Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.A, Letter.B] .W1 = 0 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A, Letter.A] r' = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A, Letter.B] r' = 1 from by decide,
    show figureThree.trueExts [Letter.B, Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.B, Letter.B] .W1 = 1 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B, Letter.A] r' = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B, Letter.B] r' = 2 from by decide]

private theorem fig3_mem_AA : [Letter.A, Letter.A] ∈ figureThree.utterances := by decide
private theorem fig3_mem_BA : [Letter.B, Letter.A] ∈ figureThree.utterances := by decide

/-- Figure 3, green: the global speaker is indifferent between AA and BA for W1 — both are
true and equally informative, so only the chain rule separates them. -/
theorem figureThree_global_indifferent :
    figureThree.globalS1 1 .W1 {⟨[.A, .A], fig3_mem_AA⟩}
      = figureThree.globalS1 1 .W1 {⟨[.B, .A], fig3_mem_BA⟩} := by
  have key : ∀ (u : figureThree.Complete), figureThree.sem u.val .W1 = true →
      (Finset.univ.filter fun r' => figureThree.sem u.val r').card = 2 →
      figureThree.globalL0 u {AbstractWorld.W1} = 1 / 2 := by
    intro u htrue hcard
    rw [figureThree.globalL0_apply, htrue, hcard, if_pos rfl, Nat.cast_ofNat]
  rw [ReferenceGame.globalS1, speaker_apply_singleton, speaker_apply_singleton,
    key ⟨[.A, .A], fig3_mem_AA⟩ (by decide) (by decide),
    key ⟨[.B, .A], fig3_mem_BA⟩ (by decide) (by decide)]
  simp only [Pi.one_apply]

/-! ### §3.1: over-modification and the STOP token

English: a red dress R1 and a blue hat R2, utterances *dress*, *red dress*, *hat*,
*blue hat*, each closed by STOP. Every content word carries the same cost factor `κ` and
STOP is free. The incremental speaker is indifferent between *dress* and *red dress* at
every `κ`: the first choice weighs *dress* and *red* equally, and each continuation is
then forced. Spanish puts the noun first, so *vestido* alone opens R1's utterances; the
choice between STOP and *rojo* is then cost-driven, and any dispreference for longer
utterances (`κ < 1`) yields the paper's preference for the bare noun — at `κ = e⁻¹`,
0.73 against 0.27. -/

namespace English

/-- English words: adjective before noun, plus the STOP token. -/
inductive Word
  | dress | red | hat | blue | stop
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.dress⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ => trivial⟩

/-- The two referents: a red dress and a blue hat. -/
inductive Referent
  | redDress | blueHat
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.redDress⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ => trivial⟩

/-- The English game: adjective–noun order, STOP-terminated. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r => match u, r with
      | .dress, .redDress | .red, .redDress | .hat, .blueHat | .blue, .blueHat
      | .stop, _ => true
      | _, _ => false)
    [[.dress, .stop], [.red, .dress, .stop], [.hat, .stop], [.blue, .hat, .stop]]
    [.redDress, .blueHat]

/-- STOP is semantically inert: appending it changes no utterance's truth value. -/
theorem sem_append_stop (u : List Word) (r : Referent) :
    game.sem (u ++ [.stop]) r = game.sem u r := by
  simp only [game, ReferenceGame.ofLexicon, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]

/-- Every complete utterance is STOP-terminated. -/
theorem utterances_stop_terminated :
    ∀ u ∈ game.utterances, u.getLast? = some Word.stop := by decide

/-- The §3.1 cost: a common factor `κ` per content word, none for STOP. -/
noncomputable def cost (κ : ℝ≥0∞) : Word → ℝ≥0∞ := fun u => if u = .stop then 1 else κ

private theorem hw : ∀ r : Referent, r ∈ game.worlds := by decide

private theorem step1 {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞) (u : Word)
    (hu : u = .dress ∨ u = .red) : (game.s1 (cost κ) [] .redDress).real {u} = 1 / 2 := by
  rw [game.s1_real_singleton (by decide) fun u' => by
    unfold cost; split <;> simp [hκtop]]
  rw [show (Finset.univ : Finset Word) = {.dress, .red, .hat, .blue, .stop} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have hd : (game.l0 [] .dress {Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.dress] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.dress] r' = 1 from by decide]
  have hr : (game.l0 [] .red {Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.red] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.red] r' = 1 from by decide]
  have hz : ∀ u' ∈ [Word.hat, Word.blue, Word.stop],
      (game.l0 [] u' {Referent.redDress}).toReal = 0 := by
    intro u' hu'
    fin_cases hu' <;>
      · rw [game.l0_apply_eq_zero hw (by decide), ENNReal.toReal_zero]
  have hκ : (κ.toReal) ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hκ0, hκtop⟩
  have hc : ∀ u' : Word, u' ≠ .stop → (cost κ u').toReal = κ.toReal := fun u' hu' => by
    rw [cost, if_neg hu']
  rcases hu with rfl | rfl <;>
    · rw [hd, hr, hz .hat (by decide), hz .blue (by decide), hz .stop (by decide),
        hc .dress (by decide), hc .red (by decide)]
      rw [div_eq_div_iff (by positivity) two_ne_zero]
      ring

private theorem forced_dress_after_red {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞) :
    game.s1 (cost κ) [.red] .redDress {Word.dress} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by simp [cost, hκ0]) (by simp [cost, hκtop])
    (by decide) (by decide)

private theorem forced_stop_after_dress {κ : ℝ≥0∞} :
    game.s1 (cost κ) [.dress] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by simp [cost]) (by simp [cost])
    (by decide) (by decide)

private theorem forced_stop_after_red_dress {κ : ℝ≥0∞} :
    game.s1 (cost κ) [.red, .dress] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by simp [cost]) (by simp [cost])
    (by decide) (by decide)

/-- §3.1, English: the incremental speaker is *indifferent* between bare *dress* and
over-modified *red dress* at every content-word cost — the paper's 0.5/0.5. The first
word decides on informativity alone, where *dress* and *red* tie, and after *red* the
over-modifying *dress* is forced. -/
theorem incremental_indifferent {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞) :
    game.s1Utt (cost κ) .redDress [.dress, .stop]
      = game.s1Utt (cost κ) .redDress [.red, .dress, .stop] := by
  simp only [ReferenceGame.s1Utt, ReferenceGame.s1Chain, List.nil_append,
    List.cons_append, mul_one]
  rw [step1 hκ0 hκtop .dress (Or.inl rfl), step1 hκ0 hκtop .red (Or.inr rfl),
    measureReal_def, forced_stop_after_dress, measureReal_def, forced_dress_after_red hκ0
      hκtop, measureReal_def, forced_stop_after_red_dress]
  norm_num

private theorem mem_dress : [Word.dress, Word.stop] ∈ game.utterances := by decide
private theorem mem_redDress : [Word.red, Word.dress, Word.stop] ∈ game.utterances := by
  decide

/-- §3.1, English, globally: both utterances identify the red dress, so with any
dispreference for length the global speaker prefers bare *dress* — the paper's 0.73
against 0.27 at `κ = e⁻¹`, and the contrast with the incremental speaker's
indifference. -/
theorem global_prefers_bare_noun {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκlt : κ < 1) :
    (game.globalS1 (fun u => ReferenceGame.uttCost (cost κ) u.val) .redDress).real
        {⟨[.red, .dress, .stop], mem_redDress⟩}
      < (game.globalS1 (fun u => ReferenceGame.uttCost (cost κ) u.val) .redDress).real
        {⟨[.dress, .stop], mem_dress⟩} := by
  have hκtop : κ ≠ ∞ := (hκlt.trans ENNReal.one_lt_top).ne
  have hL : ∀ u : game.Complete, game.sem u.val .redDress = true →
      (Finset.univ.filter fun r' => game.sem u.val r').card = 1 →
      game.globalL0 u {Referent.redDress} = 1 := by
    intro u htrue hcard
    rw [game.globalL0_apply, htrue, hcard, if_pos rfl, Nat.cast_one, div_one]
  have hc1 : ReferenceGame.uttCost (cost κ) [Word.dress, Word.stop] = κ := by
    simp [ReferenceGame.uttCost, cost]
  have hc2 : ReferenceGame.uttCost (cost κ) [Word.red, Word.dress, Word.stop] = κ * κ := by
    simp [ReferenceGame.uttCost, cost]
  have hctop : ∀ u : game.Complete, ReferenceGame.uttCost (cost κ) u.val ≠ ∞ := by
    rintro ⟨u, hu⟩
    simp only [game, ReferenceGame.ofLexicon, List.mem_cons, List.not_mem_nil, or_false]
      at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [ReferenceGame.uttCost, cost, ENNReal.mul_eq_top, hκtop]
  refine (speaker_real_singleton_lt_iff (cost := fun u : game.Complete =>
    ReferenceGame.uttCost (cost κ) u.val) zero_le_one hctop (fun u => game.globalL0_apply_le_one u _)
    ⟨⟨[.dress, .stop], mem_dress⟩, by
      rw [ENNReal.rpow_one, hL _ (by decide) (by decide), one_mul, hc1]
      exact hκ0⟩).mpr ?_
  simp only [ENNReal.rpow_one]
  rw [hL _ (by decide) (by decide), hL _ (by decide) (by decide), one_mul, one_mul, hc1, hc2]
  calc κ * κ < 1 * κ := ENNReal.mul_lt_mul_left hκ0 hκtop hκlt
    _ = κ := one_mul κ

end English

namespace Spanish

/-- Spanish words: noun before adjective, plus the STOP token. -/
inductive Word
  | vestido | rojo | sombrero | azul | stop
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.vestido⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ => trivial⟩

/-- The Spanish game over the same referents: noun–adjective order, STOP-terminated. -/
def game : ReferenceGame Word English.Referent :=
  .ofLexicon
    (fun u r => match u, r with
      | .vestido, .redDress | .rojo, .redDress | .sombrero, .blueHat
      | .azul, .blueHat | .stop, _ => true
      | _, _ => false)
    [[.vestido, .stop], [.vestido, .rojo, .stop], [.sombrero, .stop],
      [.sombrero, .azul, .stop]]
    [.redDress, .blueHat]

/-- The §3.1 cost, as in English. -/
noncomputable def cost (κ : ℝ≥0∞) : Word → ℝ≥0∞ := fun u => if u = .stop then 1 else κ

private theorem hw : ∀ r : English.Referent, r ∈ game.worlds := by decide

private theorem forced_vestido {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞) :
    game.s1 (cost κ) [] .redDress {Word.vestido} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by simp [cost, hκ0]) (by simp [cost, hκtop])
    (by decide) (by decide)

private theorem forced_stop_after_rojo {κ : ℝ≥0∞} :
    game.s1 (cost κ) [.vestido, .rojo] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by simp [cost]) (by simp [cost])
    (by decide) (by decide)

private theorem step2 {κ : ℝ≥0∞} (hκtop : κ ≠ ∞) :
    (game.s1 (cost κ) [.vestido] .redDress).real {Word.stop} = 1 / (1 + κ.toReal) ∧
    (game.s1 (cost κ) [.vestido] .redDress).real {Word.rojo} = κ.toReal / (1 + κ.toReal) := by
  have hs : (game.l0 [.vestido] .stop {English.Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.vestido, Word.stop] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.vestido, Word.stop] r' = 1 from by decide]
  have hr : (game.l0 [.vestido] .rojo {English.Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.vestido, Word.rojo] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.vestido, Word.rojo] r' = 1 from by decide]
  have hz : ∀ u' ∈ [Word.vestido, Word.sombrero, Word.azul],
      (game.l0 [.vestido] u' {English.Referent.redDress}).toReal = 0 := by
    intro u' hu'
    fin_cases hu' <;>
      · rw [game.l0_apply_eq_zero hw (by decide), ENNReal.toReal_zero]
  have hcs : (cost κ .stop).toReal = 1 := by simp [cost]
  have hcr : (cost κ .rojo).toReal = κ.toReal := by simp [cost]
  have hpos : (0 : ℝ) < 1 + κ.toReal := lt_add_of_lt_of_nonneg one_pos ENNReal.toReal_nonneg
  constructor <;>
    · rw [game.s1_real_singleton (by decide) fun u' => by
        unfold cost; split <;> simp [hκtop]]
      rw [show (Finset.univ : Finset Word) = {.vestido, .rojo, .sombrero, .azul, .stop} from
        by decide]
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton, hs, hr, hz .vestido (by decide), hz .sombrero (by decide),
        hz .azul (by decide), hcs, hcr]
      rw [div_eq_div_iff (by positivity) hpos.ne']
      ring

/-- §3.1, Spanish: with any dispreference for longer utterances (`κ < 1`), the incremental
speaker prefers bare *vestido* to *vestido rojo* — at `κ = e⁻¹` the paper's 0.73 against
0.27. The noun alone already settles the referent, so the second step is a pure cost
choice between STOP and *rojo*. -/
theorem incremental_prefers_bare_noun {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκlt : κ < 1) :
    game.s1Utt (cost κ) .redDress [.vestido, .rojo, .stop]
      < game.s1Utt (cost κ) .redDress [.vestido, .stop] := by
  have hκtop : κ ≠ ∞ := (hκlt.trans ENNReal.one_lt_top).ne
  obtain ⟨hstop, hrojo⟩ := step2 (κ := κ) hκtop
  have hpos : (0 : ℝ) < 1 + κ.toReal :=
    lt_add_of_lt_of_nonneg one_pos ENNReal.toReal_nonneg
  simp only [ReferenceGame.s1Utt, ReferenceGame.s1Chain, List.nil_append,
    List.cons_append, mul_one]
  rw [measureReal_def (μ := game.s1 (cost κ) [] .redDress), forced_vestido hκ0 hκtop,
    measureReal_def (μ := game.s1 (cost κ) [.vestido, .rojo] .redDress),
    forced_stop_after_rojo, hstop, hrojo]
  simp only [ENNReal.toReal_one, one_mul, mul_one]
  rw [div_lt_div_iff_of_pos_right hpos]
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_lt_toReal hκtop ENNReal.one_ne_top).mpr hκlt

end Spanish

/-! ### §3.2: the anticipatory implicature in Sedivy's display

A tall cup, a short cup, a tall pitcher and a key; utterances *tall cup*, *short cup*,
*tall pitcher*, *cup*, *pitcher*, *key*. Upon hearing *tall* the incremental pragmatic
listener favours the tall cup at 3/5 against the tall pitcher at 2/5: a speaker meaning the
pitcher had *pitcher* alone, so *tall* was a third of her choices, while the cup's speaker,
whose bare *cup* is ambiguous with the short cup, uses *tall* half the time. The §3.1 cost
places a common factor on every content word, which cancels within each row, so the
scene is evaluated at unit cost. The implicature cancels: were the next word *pitcher*,
the listener who has updated on *tall* excludes every referent but the pitcher. -/

namespace Sedivy

/-- The scene's words: the two scalar adjectives and three category nouns. -/
inductive Word
  | tall | short | cup | pitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.tall⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ => trivial⟩

/-- The four objects on display. -/
inductive Referent
  | tallCup | shortCup | tallPitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.tallCup⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ => trivial⟩

/-- Sedivy's display as a reference game: six utterances, word-conjunctive semantics. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r => match u, r with
      | .tall, .tallCup | .tall, .tallPitcher | .short, .shortCup | .cup, .tallCup
      | .cup, .shortCup | .pitcher, .tallPitcher | .key, .key => true
      | _, _ => false)
    [[.tall, .cup], [.short, .cup], [.tall, .pitcher], [.cup], [.pitcher], [.key]]
    [.tallCup, .shortCup, .tallPitcher, .key]

private theorem hw : ∀ r : Referent, r ∈ game.worlds := by decide

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Word → M) :
    ∑ u, f u = f .tall + (f .short + (f .cup + (f .pitcher + f .key))) := by
  rw [show (Finset.univ : Finset Word) = {.tall, .short, .cup, .pitcher, .key} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

/-- The speaker's use of *tall* as a first word: half the time for the tall cup, a third of
the time for the tall pitcher, never for the others. -/
theorem s1_tall_values :
    (game.s1 1 [] .tallCup).real {Word.tall} = 1 / 2 ∧
    (game.s1 1 [] .tallPitcher).real {Word.tall} = 1 / 3 ∧
    (game.s1 1 [] .shortCup).real {Word.tall} = 0 ∧
    (game.s1 1 [] .key).real {Word.tall} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [game.s1_real_counts hw (by decide), sum_word]
      norm_num [show game.trueExts [Word.tall] .tallCup = 1 from by decide,
        show game.trueExts [Word.tall] .tallPitcher = 1 from by decide,
        show game.trueExts [Word.tall] .shortCup = 0 from by decide,
        show game.trueExts [Word.tall] .key = 0 from by decide,
        show ∑ r', game.trueExts [Word.tall] r' = 2 from by decide,
        show game.trueExts [Word.short] .tallCup = 0 from by decide,
        show game.trueExts [Word.short] .tallPitcher = 0 from by decide,
        show game.trueExts [Word.cup] .tallCup = 1 from by decide,
        show game.trueExts [Word.cup] .tallPitcher = 0 from by decide,
        show ∑ r', game.trueExts [Word.cup] r' = 2 from by decide,
        show game.trueExts [Word.pitcher] .tallCup = 0 from by decide,
        show game.trueExts [Word.pitcher] .tallPitcher = 1 from by decide,
        show ∑ r', game.trueExts [Word.pitcher] r' = 1 from by decide,
        show game.trueExts [Word.key] .tallCup = 0 from by decide,
        show game.trueExts [Word.key] .tallPitcher = 0 from by decide]

private theorem tall_marginal_ne_zero :
    (game.s1 1 [] ∘ₘ uniformOn (Set.univ : Set Referent)) {Word.tall} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (w := Referent.tallCup)
    (uniformOn_univ_singleton_ne_zero _)
    (game.s1_apply_ne_zero hw (by decide) (fun _ => one_ne_zero)
      (fun _ => ENNReal.one_ne_top) (by decide))

/-- §3.2: upon hearing *tall*, the incremental listener favours the tall cup over the tall
pitcher — the anticipatory contrastive inference. -/
theorem listener_prefers_tall_cup :
    (game.l1 1 [] .tall).real {Referent.tallPitcher}
      < (game.l1 1 [] .tall).real {Referent.tallCup} := by
  rw [game.l1_real_lt_iff tall_marginal_ne_zero, s1_tall_values.1, s1_tall_values.2.1]
  norm_num

/-- §3.2, exactly: 3/5 for the tall cup and 2/5 for the pitcher — the paper's 0.6 and 0.4. -/
theorem listener_tall_values :
    (game.l1 1 [] .tall).real {Referent.tallCup} = 3 / 5 ∧
    (game.l1 1 [] .tall).real {Referent.tallPitcher} = 2 / 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := s1_tall_values
  have hsum : ∑ r', (game.s1 1 [] r').real {Word.tall} = 5 / 6 := by
    rw [show (Finset.univ : Finset Referent) = {.tallCup, .shortCup, .tallPitcher, .key}
      from by decide]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton, h1, h2, h3, h4]
    norm_num
  constructor <;>
    · rw [game.l1_real_singleton tall_marginal_ne_zero, hsum]
      first | rw [h1] | rw [h2]
      norm_num

/-- The listener who has heard *tall*, hearing *pitcher* next: the posterior of the
word-level speaker at context *tall* against the updated prior. -/
noncomputable def afterTallPitcher : Measure Referent :=
  ((game.s1 1 [.tall])†(game.l1 1 [] .tall)) .pitcher

/-- The implicature cancels: after *tall pitcher* every referent but the pitcher is
excluded. The tall cup's speaker never continues *tall* with *pitcher*, and the other two
referents already had no posterior mass. -/
theorem afterTallPitcher_eq_one : afterTallPitcher {Referent.tallPitcher} = 1 := by
  have hcup : game.s1 1 [.tall] .tallCup {Word.pitcher} = 0 :=
    game.s1_apply_eq_zero hw (by decide) 1 (by decide)
  have hpit : game.s1 1 [.tall] .tallPitcher {Word.pitcher} = 1 :=
    game.s1_apply_eq_one hw (by decide) one_ne_zero ENNReal.one_ne_top (by decide) (by decide)
  have hprior : ∀ r, r = Referent.shortCup ∨ r = .key → game.l1 1 [] .tall {r} = 0 := by
    rintro r (rfl | rfl) <;>
      · rw [ReferenceGame.l1, posterior_apply_singleton _ _ tall_marginal_ne_zero,
          game.s1_apply_eq_zero hw (by decide) 1 (by decide), mul_zero, ENNReal.zero_div]
  have hpos : game.l1 1 [] .tall {Referent.tallPitcher} ≠ 0 := by
    rw [ReferenceGame.l1, posterior_apply_singleton _ _ tall_marginal_ne_zero, ne_eq,
      ENNReal.div_eq_zero_iff, not_or]
    exact ⟨mul_ne_zero (uniformOn_univ_singleton_ne_zero _)
      (game.s1_apply_ne_zero hw (by decide) (fun _ => one_ne_zero)
        (fun _ => ENNReal.one_ne_top) (by decide)), measure_ne_top _ _⟩
  have hx : (game.s1 1 [.tall] ∘ₘ game.l1 1 [] .tall) {Word.pitcher} ≠ 0 :=
    comp_apply_singleton_ne_zero _ _ hpos (hpit ▸ one_ne_zero)
  rw [afterTallPitcher, posterior_apply_singleton _ _ hx, Measure.comp_apply_singleton,
    show (Finset.univ : Finset Referent) = {.tallCup, .shortCup, .tallPitcher, .key}
      from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, hcup, hpit, hprior .shortCup (Or.inl rfl),
    hprior .key (Or.inr rfl), mul_zero, zero_mul, zero_mul, mul_one, zero_add, add_zero,
    zero_add]
  exact ENNReal.div_self hpos (measure_ne_top _ _)

end Sedivy

end CohnGordonEtAl2019
