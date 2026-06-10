import Linglib.Morphology.Containment.Vocabulary

/-!
# Synthetic and analytic realization: Merger over a containment hierarchy
[bobaljik-2012]

[bobaljik-2012] ch. 3 treats the synthetic/analytic distinction as
structural: a grade is realized synthetically when Merger has bundled
its heads into the root's complex word, periphrastically otherwise.
Because Merger cannot skip intervening heads (part of Marantz's
definition; equivalently, successive-cyclic head movement), the merged
region is an initial segment of the hierarchy — recorded here as
`Synthesis.wordTop`. Two of the book's generalizations then fall out:

* **SSG** (`Synthesis.syntheticAt_of_le`): no morphological superlative
  without a morphological comparative — synthesis is downward closed.
  The empirical content lives in the modeling choice (merged region =
  initial segment); the theorem is its one-line consequence.
* **RSG** (`rsg`): root suppletion is limited to synthetic
  comparatives. Items can only be conditioned by word-internal
  structure, so a lexeme whose comparative is periphrastic
  (`wordTop = 0`) realizes the same root form at every grade
  (`realizeIn_const_of_wordTop_eq_zero`) — no `*good – more bett`.

## Main declarations

* `Synthesis n` — how far up the hierarchy the lexeme's word extends
* `realizeIn` — realization seeing only word-internal structure
* `Synthesis.syntheticAt_of_le` (SSG), `rsg`,
  `isContiguous_realizeIn`
-/

namespace Morphology.Containment

variable {n : ℕ} {F : Type*}

/-- The synthetic extent of a lexeme's paradigm: heads `1..wordTop` are
realized word-internally with the root (Merger applied); grades above
`wordTop` are periphrastic. That the merged region is an initial
segment encodes [bobaljik-2012]'s "Merger cannot skip intervening
heads". -/
structure Synthesis (n : ℕ) where
  /-- The highest head merged into the root's word. -/
  wordTop : Fin n
  deriving DecidableEq, Repr

/-- Grade `g` is realized synthetically: all its heads are
word-internal. -/
def Synthesis.SyntheticAt (s : Synthesis n) (g : Fin n) : Prop :=
  g ≤ s.wordTop

instance (s : Synthesis n) (g : Fin n) : Decidable (s.SyntheticAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **SSG core** ([bobaljik-2012] ch. 3): synthesis is downward closed —
a synthetic superlative entails a synthetic comparative. No language
has `long – more long – longest`. -/
theorem Synthesis.syntheticAt_of_le {s : Synthesis n} {g g' : Fin n}
    (h : s.SyntheticAt g) (h' : g' ≤ g) : s.SyntheticAt g' :=
  le_trans h' h

/-- Realization restricted to word-internal structure: at grade `g`,
items see only the merged region — suppletion cannot be conditioned by
periphrastic material outside the word ([bobaljik-2012]'s locality
condition (90) applied through Merger). -/
def realizeIn (s : Synthesis n) (v : List (Item n F)) : Pattern n (Option F) :=
  λ g => realize v (min g s.wordTop)

/-- Word-internal realization is still contiguous: `realizeIn` is
`realize` precomposed with the monotone regrading `min · wordTop`. -/
theorem isContiguous_realizeIn {s : Synthesis n} {v : List (Item n F)}
    (hAH : Antihomophonous v) : IsContiguous (realizeIn s v) :=
  (isContiguous_realize hAH).comp_monotone (λ _ _ h => min_le_min_right _ h)

/-- A lexeme with no Merger at all (`wordTop = 0`, fully periphrastic
paradigm) realizes the same root form at every grade. -/
theorem realizeIn_const_of_wordTop_eq_zero {s : Synthesis n}
    {v : List (Item n F)} (h : (s.wordTop : ℕ) = 0) (g g' : Fin n) :
    realizeIn s v g = realizeIn s v g' := by
  have hbot : ∀ x : Fin n, min x s.wordTop = s.wordTop := λ x =>
    min_eq_right (by rw [Fin.le_def, h]; exact Nat.zero_le _)
  unfold realizeIn
  rw [hbot, hbot]

/-- **RSG** ([bobaljik-2012] ch. 3): root suppletion is limited to
synthetic comparatives. Contrapositively: a lexeme showing distinct
root forms at two grades must have undergone Merger at least once —
its comparative is synthetic. Excludes `*good – more bett`. -/
theorem rsg {s : Synthesis 3} {v : List (Item 3 F)} {g g' : Fin 3}
    (h : realizeIn s v g ≠ realizeIn s v g') : s.SyntheticAt 1 := by
  by_contra hsyn
  refine h (realizeIn_const_of_wordTop_eq_zero ?_ g g')
  unfold Synthesis.SyntheticAt at hsyn
  rw [Fin.le_def] at hsyn
  simp only [Fin.val_one] at hsyn
  omega

end Morphology.Containment
