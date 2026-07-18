import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Morphology.DM.DomainLocality
import Mathlib.Logic.Relation

/-!
# Synthetic and analytic realization: Merger over a containment hierarchy
[bobaljik-2012]

[bobaljik-2012] ch. 3 treats the synthetic/analytic distinction as
structural: a grade is realized synthetically when Merger has bundled
its heads into the root's complex word, periphrastically otherwise.
`MergerStep` models one application of Merger — adjoin a head to the
merged region, skipping no intervening head (part of Marantz's
definition; equivalently, successive-cyclic head movement) — and the
book's generalizations are theorems about the reachable regions:

* **Initial segments** (`mergerReachable_iff_exists_region`): the
  regions reachable from the bare root are exactly the initial
  segments of the hierarchy, coordinatized by `Synthesis.wordTop`.
* **SSG** (`MergerReachable.mem_of_le`,
  `Synthesis.syntheticAt_of_le`): no morphological superlative
  without a morphological comparative — merged regions are downward
  closed in heads, so synthesis is downward closed in grades. No
  language has `long – more long – longest`.
* **RSG** (`min_lt_wordTop_of_realizeIn_ne`, specialized as `rsg`):
  root suppletion is limited to synthetic comparatives. Items can
  only be conditioned by word-internal structure (`realizeIn`), so
  distinct root forms at two grades force Merger past their lower
  grade — no `*good – more bett`.

The merged region also induces a two-block domain partition of the
grades (`Synthesis.domainPartition`) — [bobaljik-2012]'s structural
adjacency as one source of `Morphology/DM/DomainLocality.lean`'s
domain-relativized contiguity, alongside the accessibility-domain
refinements of [moskal-2015] and [smith-moskal-xu-kang-bobaljik-2019].

## Main declarations

* `MergerStep`, `MergerReachable` — Merger as successive-cyclic head
  bundling; the reachable merged regions
* `Synthesis n` — how far up the hierarchy the lexeme's word extends
* `realizeIn` — realization seeing only word-internal structure
* `MergerReachable.mem_of_le`, `Synthesis.syntheticAt_of_le` (SSG),
  `min_lt_wordTop_of_realizeIn_ne` (RSG), `isContiguous_realizeIn`,
  `Synthesis.domainPartition`
-/

namespace Morphology.DM

open Morphology.Containment

variable {n : ℕ} {F : Type*}

/-! ### Merger as successive-cyclic head bundling -/

/-- One application of Merger: adjoin head `h` to the merged region
`R`. The side condition that every head strictly between the root and
`h` is already merged is [bobaljik-2012]'s "Merger cannot skip
intervening heads" (part of Marantz's definition of Morphological
Merger; equivalently, successive-cyclic head movement). -/
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
      exact λ _ => Fin.castSucc_lt_succ
    · exact λ k hk0 hkh =>
        Finset.mem_Ioc.mpr ⟨hk0, Fin.le_castSucc_iff.mpr hkh⟩
    · ext k
      simp only [Finset.mem_insert, Finset.mem_Ioc, Fin.ext_iff, Fin.lt_def,
        Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_zero]
      omega

/-- The regions reachable by successive Merger are exactly the initial
segments of the hierarchy: the no-skipping condition forces every head
below a merged head to be merged. -/
theorem mergerReachable_iff [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ t : Fin n, R = Finset.Ioc 0 t := by
  refine ⟨λ h => ?_, λ ⟨t, ht⟩ => ht ▸ mergerReachable_Ioc t⟩
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

/-- **SSG core** ([bobaljik-2012] ch. 3): merged regions are downward
closed in heads — if the superlative head has merged, so has the
comparative head below it. -/
theorem MergerReachable.mem_of_le [NeZero n] {R : Finset (Fin n)}
    (hR : MergerReachable R) {h k : Fin n} (hk0 : 0 < k) (hkh : k ≤ h)
    (hh : h ∈ R) : k ∈ R := by
  obtain ⟨t, rfl⟩ := mergerReachable_iff.mp hR
  exact Finset.mem_Ioc.mpr ⟨hk0, le_trans hkh (Finset.mem_Ioc.mp hh).2⟩

/-! ### The synthetic extent -/

/-- The synthetic extent of a lexeme's paradigm: heads `1..wordTop` are
realized word-internally with the root (Merger applied); grades above
`wordTop` are periphrastic. `wordTop` coordinatizes the merged region:
by `mergerReachable_iff_exists_region`, the regions successive-cyclic
Merger can build are exactly those of this form. -/
structure Synthesis (n : ℕ) where
  /-- The highest head merged into the root's word. -/
  wordTop : Fin n
  deriving DecidableEq, Repr

/-- The merged region of the lexeme's word: heads `1..wordTop`. -/
def Synthesis.region [NeZero n] (s : Synthesis n) : Finset (Fin n) :=
  Finset.Ioc 0 s.wordTop

/-- Merged regions and synthetic extents are in coordinatizing
correspondence: a region is Merger-reachable iff it is `s.region` for
some `Synthesis s`. -/
theorem mergerReachable_iff_exists_region [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ s : Synthesis n, R = s.region :=
  mergerReachable_iff.trans
    ⟨λ ⟨t, ht⟩ => ⟨⟨t⟩, ht⟩, λ ⟨s, hs⟩ => ⟨s.wordTop, hs⟩⟩

theorem Synthesis.mergerReachable_region [NeZero n] (s : Synthesis n) :
    MergerReachable s.region :=
  mergerReachable_Ioc s.wordTop

/-- Grade `g` is realized synthetically: all its heads are
word-internal. -/
def Synthesis.SyntheticAt (s : Synthesis n) (g : Fin n) : Prop :=
  g ≤ s.wordTop

instance (s : Synthesis n) (g : Fin n) : Decidable (s.SyntheticAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Syntheticity is containment of the grade's heads in the merged
region. -/
theorem Synthesis.syntheticAt_iff_region [NeZero n] {s : Synthesis n} {g : Fin n} :
    s.SyntheticAt g ↔ Finset.Ioc 0 g ⊆ s.region := by
  refine ⟨λ h => Finset.Ioc_subset_Ioc le_rfl h, λ hsub => ?_⟩
  rcases eq_or_ne g 0 with rfl | hg
  · exact Fin.zero_le _
  · exact (Finset.mem_Ioc.mp
      (hsub (Finset.mem_Ioc.mpr ⟨(Fin.pos_iff_ne_zero' g).mpr hg, le_rfl⟩))).2

/-- **SSG** ([bobaljik-2012] ch. 3): synthesis is downward closed — a
synthetic superlative entails a synthetic comparative. The grade-level
shadow of `MergerReachable.mem_of_le`. -/
theorem Synthesis.syntheticAt_of_le {s : Synthesis n} {g g' : Fin n}
    (h : s.SyntheticAt g) (h' : g' ≤ g) : s.SyntheticAt g' :=
  le_trans h' h

/-! ### Word-internal realization -/

/-- Realization restricted to word-internal structure: at grade `g`,
rules see only the merged region — suppletion cannot be conditioned by
periphrastic material outside the word ([bobaljik-2012]'s locality
condition (90) applied through Merger). Models the
comparative-embedding periphrasis type (Greek, the book's (107a–b));
the positive-embedding type (Russian, (107c–d)) needs a per-grade
embedding choice rather than a single `wordTop`. -/
def realizeIn (s : Synthesis n) (v : List (SpanRule n F)) : Paradigm n (Option F) :=
  λ g => realize v (min g s.wordTop)

/-- At a synthetic grade, word-internal realization is realization. -/
theorem realizeIn_eq_realize_of_le {s : Synthesis n} {v : List (SpanRule n F)}
    {g : Fin n} (h : g ≤ s.wordTop) : realizeIn s v g = realize v g := by
  unfold realizeIn
  rw [min_eq_left h]

/-- At a periphrastic grade, the root word realizes as at `wordTop` —
the highest grade whose structure is word-internal. -/
theorem realizeIn_eq_realize_wordTop_of_le {s : Synthesis n}
    {v : List (SpanRule n F)} {g : Fin n} (h : s.wordTop ≤ g) :
    realizeIn s v g = realize v s.wordTop := by
  unfold realizeIn
  rw [min_eq_right h]

/-- Word-internal realization is still contiguous: `realizeIn` is
`realize` precomposed with the monotone regrading `min · wordTop`. -/
theorem isContiguous_realizeIn {s : Synthesis n} {v : List (SpanRule n F)}
    (hAH : Antihomophonous v) : IsContiguous (realizeIn s v) :=
  (isContiguous_realize hAH).comp_monotone (λ _ _ h => min_le_min_right _ h)

/-- A lexeme with no Merger at all (`wordTop = 0`, fully periphrastic
paradigm) realizes the same root form at every grade. -/
theorem realizeIn_const_of_wordTop_eq_zero {s : Synthesis n}
    {v : List (SpanRule n F)} (h : (s.wordTop : ℕ) = 0) (g g' : Fin n) :
    realizeIn s v g = realizeIn s v g' := by
  have hle : ∀ x : Fin n, s.wordTop ≤ x := λ x => by
    rw [Fin.le_def, h]; exact Nat.zero_le _
  rw [realizeIn_eq_realize_wordTop_of_le (hle g),
    realizeIn_eq_realize_wordTop_of_le (hle g')]

/-- **RSG, general form** ([bobaljik-2012] ch. 3): distinct root forms
at two grades force Merger past their lower grade — root suppletion at
a grade requires that grade's word to be synthetic. Contrapositively:
above `wordTop` the word realizes constantly (`
realizeIn_eq_realize_wordTop_of_le`). -/
theorem min_lt_wordTop_of_realizeIn_ne {s : Synthesis n}
    {v : List (SpanRule n F)} {g g' : Fin n}
    (h : realizeIn s v g ≠ realizeIn s v g') : min g g' < s.wordTop := by
  by_contra hle
  push Not at hle
  rw [realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_left g g')),
    realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_right g g'))] at h
  exact h rfl

/-- **RSG** ([bobaljik-2012] ch. 3): root suppletion is limited to
synthetic comparatives — a lexeme showing distinct root forms at two
grades has undergone Merger at least once, so its comparative is
synthetic. Excludes `*good – more bett`. -/
theorem rsg {s : Synthesis 3} {v : List (SpanRule 3 F)} {g g' : Fin 3}
    (h : realizeIn s v g ≠ realizeIn s v g') : s.SyntheticAt 1 := by
  have hlt := min_lt_wordTop_of_realizeIn_ne h
  rw [Fin.lt_def] at hlt
  rw [Synthesis.SyntheticAt, Fin.le_def, Fin.val_one]
  omega

/-! ### The induced domain partition -/

open Morphology.DomainLocality in
/-- The two-block domain partition induced by Merger: word-internal
grades vs periphrastic ones — [bobaljik-2012]'s structural adjacency
as a source of domain partitions for
`Morphology/DM/DomainLocality.lean`. -/
def Synthesis.domainPartition (s : Synthesis n) : DomainPartition n Bool :=
  λ g => decide (s.SyntheticAt g)

open Morphology.DomainLocality in
theorem Synthesis.sameDomain_domainPartition_iff {s : Synthesis n} {i j : Fin n} :
    SameDomain s.domainPartition i j ↔ (s.SyntheticAt i ↔ s.SyntheticAt j) := by
  simp [SameDomain, domainPartition, decide_eq_decide]

end Morphology.DM
