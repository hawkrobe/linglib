import Linglib.Phonology.ItemSpecificity.Defs

/-!
# UseListed
[zuraw-2000]

The whole-word retrieval theory: an item with high token frequency may
be **stored as a fully-formed surface representation**, bypassing the
generative grammar entirely. The grammar is only consulted for items
below a frequency threshold.

The interface to `ItemSpecificity.HasTokenFreq` is the same as
`IndexedConstraints` — a single threshold partitions the lexicon — but
the *interpretation* differs sharply:

- Indexed constraints: both strata go through the grammar; only the
  ranking differs.
- UseListed: the high-frequency stratum **does not** go through the
  grammar; the surface form is stored as-is.

## Empirical signature

UseListed predicts that high-frequency items will faithfully realize
their stored surface form, which may diverge arbitrarily from the
grammar's output. Crucially, **novel items cannot be listed**, so any
UseListed prediction must be tested on the productivity gradient: novel
items pattern with the *grammar*, not with the high-frequency lexicon.

The Breiss-Katsuda-Kawahara compounds (Figure 7 of
[breiss-katsuda-kawahara-2026]) test this directly: novel
compounds show the same compound-frequency-conditioned nasalisation
gradient as familiar compounds, contra UseListed.
-/

namespace Constraints.ItemSpecificity.UseListed

open Constraints.ItemSpecificity

-- ============================================================================
-- § 1: Listed-vs-computed gate
-- ============================================================================

/-- An item is "listed" iff its log-frequency reaches the threshold.
    Listed items bypass the grammar; computed items go through it.

    Implemented as an alias of `ItemSpecificity.isAboveThreshold`, the
    shared threshold predicate also used by `Indexed.isCore`; the two
    differ only in semantics (storage gate vs. stratum membership). -/
abbrev isListed {α : Type} [HasTokenFreq α] (threshold : ℝ) (a : α) : Prop :=
  isAboveThreshold threshold a

/-- The UseListed dispatch: returns the listed surface form for items
    above threshold, otherwise the grammar's output. Parametric in both
    the listed-form retrieval function and the grammar function — this
    file fixes only the dispatch logic, not either component. -/
noncomputable def dispatch {α β : Type} [HasTokenFreq α] (threshold : ℝ)
    (listedForm : α → β) (grammarForm : α → β) (a : α) : β :=
  if tokenLogFreq a ≥ threshold then listedForm a else grammarForm a

-- ============================================================================
-- § 2: Novel-item invariance (the discriminating prediction)
-- ============================================================================

/-- For any item below the listing threshold, the UseListed dispatch
    returns exactly the grammar's prediction — independent of the
    listed-form lookup table. This is the formal version of "novel
    items can't be listed, so they pattern with the grammar".

    Empirical content: if a study presents *novel* (frequency-zero)
    items and finds they pattern with the high-frequency listed
    distribution, UseListed is refuted. -/
theorem dispatch_novel_eq_grammar
    {α β : Type} [HasTokenFreq α] (threshold : ℝ)
    (listedForm grammarForm : α → β) (a : α)
    (hnovel : tokenLogFreq a < threshold) :
    dispatch threshold listedForm grammarForm a = grammarForm a := by
  unfold dispatch
  simp [not_le.mpr hnovel]

end Constraints.ItemSpecificity.UseListed
