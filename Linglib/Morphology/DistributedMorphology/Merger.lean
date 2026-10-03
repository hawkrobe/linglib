module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Mathlib.Logic.Relation

/-!
# Synthetic and analytic realization: Merger over a containment hierarchy

[bobaljik-2012] ch. 3 treats the synthetic/analytic distinction as structural. A grade is realized
synthetically when Merger has bundled its heads into the root's complex word, and periphrastically
otherwise. `MergerStep` is one application of Merger, which adjoins a head to the merged region
without skipping an intervening head, and the book's generalizations about periphrasis become
theorems about the regions Merger reaches and the structure realization sees.

* The regions reachable from the bare root are exactly the initial segments of the hierarchy,
  coordinatized by `Synthesis.wordTop`.
* Merged regions are downward closed, so synthesis is downward closed in grades. This is the
  Synthetic Superlative Generalization: no language has *long – more long – longest*.
* Rules see only the root's word, so distinct root forms at two grades force Merger past the lower
  one. This is the Root Suppletion Generalization: no *good – more bett*.

## Main declarations

* `MergerStep`, `MergerReachable`, `mergerReachable_iff_exists_region`
* `Synthesis`, `MergerReachable.mem_of_le`, `Synthesis.syntheticAt_of_le`
* `realizeIn`, `isContiguous_realizeIn`, `min_lt_wordTop_of_realizeIn_ne`, `rsg`

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology (Paradigm IsContiguous)
open Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### Merger as successive-cyclic head bundling -/

/-- One application of Merger adjoins head `h` to the merged region `R`. Every head strictly
between the root and `h` must already be merged, since Merger cannot skip intervening heads, which
[bobaljik-2012] takes from the definition of Morphological Merger. For head movement the condition
is successive cyclicity. -/
def MergerStep [NeZero n] (R S : Finset (Fin n)) : Prop :=
  ∃ h : Fin n, 0 < h ∧ h ∉ R ∧ (∀ k : Fin n, 0 < k → k < h → k ∈ R) ∧ S = insert h R

/-- The merged regions reachable from the bare root (empty region) by
successive applications of Merger. -/
def MergerReachable [NeZero n] (R : Finset (Fin n)) : Prop :=
  Relation.ReflTransGen MergerStep ∅ R

theorem mergerReachable_Ioc [NeZero n] (t : Fin n) :
    MergerReachable (Finset.Ioc 0 t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  induction t using Fin.induction with
  | zero => rw [Finset.Ioc_self]; exact .refl
  | succ i ih =>
    refine ih.tail ⟨i.succ, i.succ_pos, ?_, ?_, ?_⟩
    · simp only [Finset.mem_Ioc, not_and, not_le]
      exact fun _ ↦ Fin.castSucc_lt_succ
    · exact fun k hk0 hkh ↦ Finset.mem_Ioc.mpr ⟨hk0, Fin.le_castSucc_iff.mpr hkh⟩
    · ext k
      simp only [Finset.mem_insert, Finset.mem_Ioc, Fin.ext_iff, Fin.lt_def,
        Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_zero]
      omega

/-- The regions reachable by successive Merger are exactly the initial
segments of the hierarchy, since the no-skipping condition forces every head
below a merged head to be merged. -/
theorem mergerReachable_iff [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ t : Fin n, R = Finset.Ioc 0 t := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ht ▸ mergerReachable_Ioc t⟩
  induction h with
  | refl => exact ⟨0, (Finset.Ioc_self 0).symm⟩
  | tail _ hstep ih =>
    obtain ⟨t, rfl⟩ := ih
    obtain ⟨h, hpos, hnot, hskip, rfl⟩ := hstep
    have hth : t < h := by
      rcases lt_or_ge t h with h' | h'
      · exact h'
      · exact absurd (Finset.mem_Ioc.mpr ⟨hpos, h'⟩) hnot
    refine ⟨h, ?_⟩
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro (rfl | ⟨hk0, hkt⟩)
      · exact ⟨hpos, le_rfl⟩
      · exact ⟨hk0, le_trans hkt hth.le⟩
    · rintro ⟨hk0, hkh⟩
      rcases eq_or_lt_of_le hkh with rfl | hkh'
      · exact Or.inl rfl
      · exact Or.inr ⟨hk0, (Finset.mem_Ioc.mp (hskip k hk0 hkh')).2⟩

/-- Merged regions are downward closed in heads, so if the superlative head has merged, so has the
comparative head below it. This is the core of the Synthetic Superlative Generalization of
[bobaljik-2012] ch. 3. -/
theorem MergerReachable.mem_of_le [NeZero n] {R : Finset (Fin n)}
    (hR : MergerReachable R) {h k : Fin n} (hk0 : 0 < k) (hkh : k ≤ h)
    (hh : h ∈ R) : k ∈ R := by
  obtain ⟨t, rfl⟩ := mergerReachable_iff.mp hR
  exact Finset.mem_Ioc.mpr ⟨hk0, le_trans hkh (Finset.mem_Ioc.mp hh).2⟩

/-! ### The synthetic extent -/

/-- The synthetic extent of a lexeme's paradigm. Heads `1..wordTop` are realized word-internally
with the root, and grades above `wordTop` are periphrastic. By `mergerReachable_iff_exists_region`
the regions successive-cyclic Merger builds are exactly those of this form. -/
structure Synthesis (n : ℕ) where
  /-- The highest head merged into the root's word. -/
  wordTop : Fin n
  deriving DecidableEq, Repr

/-- The merged region of the lexeme's word, heads `1..wordTop`. -/
def Synthesis.region [NeZero n] (s : Synthesis n) : Finset (Fin n) :=
  Finset.Ioc 0 s.wordTop

/-- A region is Merger-reachable iff it is the region of some synthetic extent. -/
theorem mergerReachable_iff_exists_region [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ s : Synthesis n, R = s.region :=
  mergerReachable_iff.trans
    ⟨fun ⟨t, ht⟩ ↦ ⟨⟨t⟩, ht⟩, fun ⟨s, hs⟩ ↦ ⟨s.wordTop, hs⟩⟩

theorem Synthesis.mergerReachable_region [NeZero n] (s : Synthesis n) :
    MergerReachable s.region :=
  mergerReachable_Ioc s.wordTop

/-- Grade `g` is realized synthetically when all its heads are word-internal. -/
def Synthesis.SyntheticAt (s : Synthesis n) (g : Fin n) : Prop :=
  g ≤ s.wordTop

instance (s : Synthesis n) (g : Fin n) : Decidable (s.SyntheticAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Syntheticity is containment of the grade's heads in the merged
region. -/
theorem Synthesis.syntheticAt_iff_region [NeZero n] {s : Synthesis n} {g : Fin n} :
    s.SyntheticAt g ↔ Finset.Ioc 0 g ⊆ s.region := by
  refine ⟨fun h ↦ Finset.Ioc_subset_Ioc le_rfl h, fun hsub ↦ ?_⟩
  rcases eq_or_ne g 0 with rfl | hg
  · exact Fin.zero_le _
  · exact (Finset.mem_Ioc.mp
      (hsub (Finset.mem_Ioc.mpr ⟨(Fin.pos_iff_ne_zero' g).mpr hg, le_rfl⟩))).2

/-- Synthesis is downward closed, so a synthetic superlative entails a synthetic comparative. This
is the Synthetic Superlative Generalization of [bobaljik-2012] ch. 3, the grade-level shadow of
`MergerReachable.mem_of_le`. -/
theorem Synthesis.syntheticAt_of_le {s : Synthesis n} {g g' : Fin n}
    (h : s.SyntheticAt g) (h' : g' ≤ g) : s.SyntheticAt g' :=
  le_trans h' h

/-! ### Word-internal realization -/

/-- Realization within the lexeme's synthetic extent. At grade `g` rules see only the root's word,
which reaches head `min g wordTop`, so suppletion cannot be conditioned by material outside the
word ([bobaljik-2012]'s locality condition (90)). A periphrastic grade thus embeds the highest
synthetic form, as the Greek superlative *o cheiró-ter-os* embeds the comparative. A superlative
that embeds the positive instead, as Russian *samyj plox-oj* does (§3.3.3), is `realize`
precomposed with a choice of word extent for each grade. -/
def realizeIn (s : Synthesis n) (v : List (SpanRule n F)) : Paradigm n (Option F) :=
  fun g ↦ realize v (min g s.wordTop)

/-- At a synthetic grade, word-internal realization is realization. -/
theorem realizeIn_eq_realize_of_le {s : Synthesis n} {v : List (SpanRule n F)}
    {g : Fin n} (h : g ≤ s.wordTop) : realizeIn s v g = realize v g :=
  congrArg (realize v) (min_eq_left h)

/-- At a periphrastic grade, the root's word realizes as at `wordTop`, the highest grade whose
structure is word-internal. -/
theorem realizeIn_eq_realize_wordTop_of_le {s : Synthesis n}
    {v : List (SpanRule n F)} {g : Fin n} (h : s.wordTop ≤ g) :
    realizeIn s v g = realize v s.wordTop :=
  congrArg (realize v) (min_eq_right h)

/-- Word-internal realization is contiguous, since it is `realize` precomposed with the monotone
regrading `min · wordTop`. -/
theorem isContiguous_realizeIn {s : Synthesis n} {v : List (SpanRule n F)}
    (hAH : Antihomophonous v) : IsContiguous (realizeIn s v) :=
  (isContiguous_realize hAH).comp_monotone fun _ _ h ↦ min_le_min_right _ h

/-- A lexeme with no Merger at all (`wordTop = 0`, fully periphrastic
paradigm) realizes the same root form at every grade. -/
theorem realizeIn_const_of_wordTop_eq_zero {s : Synthesis n}
    {v : List (SpanRule n F)} (h : (s.wordTop : ℕ) = 0) (g g' : Fin n) :
    realizeIn s v g = realizeIn s v g' := by
  have hle : ∀ x : Fin n, s.wordTop ≤ x := fun x ↦ by
    rw [Fin.le_def, h]; exact Nat.zero_le _
  rw [realizeIn_eq_realize_wordTop_of_le (hle g),
    realizeIn_eq_realize_wordTop_of_le (hle g')]

/-- Distinct root forms at two grades force Merger past their lower grade, so root suppletion at a
grade requires that grade's word to be synthetic. This is the general form of the Root Suppletion
Generalization of [bobaljik-2012] ch. 3; above `wordTop` the word realizes constantly
(`realizeIn_eq_realize_wordTop_of_le`). -/
theorem min_lt_wordTop_of_realizeIn_ne {s : Synthesis n}
    {v : List (SpanRule n F)} {g g' : Fin n}
    (h : realizeIn s v g ≠ realizeIn s v g') : min g g' < s.wordTop := by
  by_contra hle
  push Not at hle
  rw [realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_left g g')),
    realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_right g g'))] at h
  exact h rfl

/-- Root suppletion is limited to synthetic comparatives, the Root Suppletion Generalization of
[bobaljik-2012] ch. 3. A lexeme showing distinct root forms at two grades has undergone Merger at
least once, so its comparative is synthetic, which excludes *good – more bett*. -/
theorem rsg {s : Synthesis 3} {v : List (SpanRule 3 F)} {g g' : Fin 3}
    (h : realizeIn s v g ≠ realizeIn s v g') : s.SyntheticAt 1 := by
  have hlt := min_lt_wordTop_of_realizeIn_ne h
  rw [Fin.lt_def] at hlt
  rw [Synthesis.SyntheticAt, Fin.le_def, Fin.val_one]
  omega

end DistributedMorphology
