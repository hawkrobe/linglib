import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Fragments.English.NumeralModifiers

/-!
# Claus & Walch 2024: Numeral modification and framing effects

Three German framing experiments on numeral modification
([claus-walch-2024]). Experiment 1 shows that enforcing a precise reading
with *genau* 'exactly' does not preclude framing effects — a standard
framing effect obtains for both risky-choice framing (the Mandel-variant
deadly-disease scenario, sure-option choices) and attribute framing (a
financial-allocation approval task) — challenging the lower-bound-reading
and alignment-assumption accounts. Experiments 2 and 3 juxtapose the two
upper-bound modifiers *bis zu* 'up to' and *höchstens* 'at most' in a
2×2 (MODIFIER × FRAME) design on the same two scenarios: *up to* patterns
standardly (more sure-option choices / approvals under the positive frame),
*at most* patterns in reverse, with a significant MODIFIER × FRAME
interaction in both experiments and no main effects.

Both modifiers set an upper bound; they contrast in evaluative contexts, (5)
in the paper, and following [blok-2015] the paper ties the contrast to the
kind of modifier: the superlative *at most*, but not the directional
*up to*, makes the complement set salient. It takes the interaction to show
that valence appraisal (operationalized as goal conduciveness) plays a
crucial role in the emergence of framing effects.

The Lean content: the choice/approval proportions of Tables 1–4 as exact
rationals, the direction claims the paper draws from them, and the Fragment
side of the account — in `English.NumeralModifiers` *at most* and *up to*
have the same readings and the same class, and differ in the kind of
construction, superlative against directional.

## Main results

* `exp1_rcf_standard` / `exp1_af_standard` — Experiment 1's standard
  framing effects under *genau* (Tables 1–2)
* `exp2_upTo_standard` / `exp2_atMost_reversed` — Experiment 2's
  opposite-direction pattern (Table 3)
* `exp3_upTo_standard` / `exp3_atMost_reversed` — the Experiment 3
  replication for attribute framing (Table 4)
* `upper_bound_shared_kind_differs` — the Fragment: same readings and class,
  superlative against directional

## References

* [B. Claus, M. C. Walch, *Numeral modification and framing effects:
  exactly and at most vs up to* (2024)][claus-walch-2024]
* [D. Blok, *The semantics and pragmatics of directional numeral
  modifiers* (2015)][blok-2015]
-/

namespace ClausWalch2024

/-! ### Experiment 1: *genau* 'exactly' (Tables 1–2)

Proportion of sure-option choices (risky-choice framing, Table 1) and of
approvals (attribute framing, Table 2), positive vs negative frame. -/

/-- Table 1, positive frame: sure-option choices under *genau*. -/
def exp1RcfPos : ℚ := 519 / 1000
/-- Table 1, negative frame. -/
def exp1RcfNeg : ℚ := 346 / 1000
/-- Table 2, positive frame: approvals under *genau*. -/
def exp1AfPos : ℚ := 923 / 1000
/-- Table 2, negative frame. -/
def exp1AfNeg : ℚ := 654 / 1000

/-- Experiment 1, risky-choice framing: a standard framing effect under a
forced precise reading (the paper's significant FRAME main effect). -/
theorem exp1_rcf_standard : exp1RcfNeg < exp1RcfPos := by
  norm_num [exp1RcfPos, exp1RcfNeg]

/-- Experiment 1, attribute framing: likewise standard. -/
theorem exp1_af_standard : exp1AfNeg < exp1AfPos := by
  norm_num [exp1AfPos, exp1AfNeg]

/-! ### Experiment 2: *bis zu* vs *höchstens*, risky-choice framing (Table 3) -/

/-- Table 3, *bis zu* 'up to', positive frame. -/
def exp2UpToPos : ℚ := 592 / 1000
/-- Table 3, *bis zu* 'up to', negative frame. -/
def exp2UpToNeg : ℚ := 449 / 1000
/-- Table 3, *höchstens* 'at most', positive frame. -/
def exp2AtMostPos : ℚ := 423 / 1000
/-- Table 3, *höchstens* 'at most', negative frame. -/
def exp2AtMostNeg : ℚ := 558 / 1000

/-- Experiment 2: *up to* patterns standardly — more sure-option choices
under the positive frame. -/
theorem exp2_upTo_standard : exp2UpToNeg < exp2UpToPos := by
  norm_num [exp2UpToPos, exp2UpToNeg]

/-- Experiment 2: *at most* patterns in reverse — more sure-option choices
under the negative frame (the direction behind the paper's significant
MODIFIER × FRAME interaction). -/
theorem exp2_atMost_reversed : exp2AtMostPos < exp2AtMostNeg := by
  norm_num [exp2AtMostPos, exp2AtMostNeg]

/-! ### Experiment 3: the attribute-framing replication (Table 4) -/

/-- Table 4, *bis zu* 'up to', positive frame. -/
def exp3UpToPos : ℚ := 889 / 1000
/-- Table 4, *bis zu* 'up to', negative frame. -/
def exp3UpToNeg : ℚ := 689 / 1000
/-- Table 4, *höchstens* 'at most', positive frame. -/
def exp3AtMostPos : ℚ := 673 / 1000
/-- Table 4, *höchstens* 'at most', negative frame. -/
def exp3AtMostNeg : ℚ := 714 / 1000

/-- Experiment 3: *up to* standard, as in Experiment 2. -/
theorem exp3_upTo_standard : exp3UpToNeg < exp3UpToPos := by
  norm_num [exp3UpToPos, exp3UpToNeg]

/-- Experiment 3: *at most* reversed, replicating the interaction for
attribute framing. -/
theorem exp3_atMost_reversed : exp3AtMostPos < exp3AtMostNeg := by
  norm_num [exp3AtMostPos, exp3AtMostNeg]

/-! ### The Fragment side: shared upper bound, different kind

The paper's premise: *at most* and *up to* both set an upper bound, so
*at most 200* and *up to 200* convey that 200 is the maximum, yet they
contrast sharply in evaluative contexts ((5)). Following [blok-2015] the
paper locates the difference in the kind of modifier, the superlative making
the complement set salient where the directional does not, and the opposite
framing directions above track that split. -/

open English.NumeralModifiers Semantics in
/-- *At most* and *up to* have the same readings, each an upper bound true of
no amount above the number, and the same class; *at most* is a superlative
and *up to* a directional modifier. -/
theorem upper_bound_shared_kind_differs :
    ⟦NumeralModifier.atMost⟧ = ⟦NumeralModifier.upTo⟧ ∧
      (∀ r ∈ ⟦NumeralModifier.upTo⟧, ∀ m n, n ∈ r m → n ≤ m) ∧
      NumeralModifier.atMost.modifierClass = NumeralModifier.upTo.modifierClass ∧
      NumeralModifier.atMost.kind = some .superlative ∧
      NumeralModifier.upTo.kind = some .directional :=
  ⟨rfl, fun _ hr _ _ h ↦ by obtain rfl : _ = _ := hr; exact h, rfl, rfl, rfl⟩

end ClausWalch2024
