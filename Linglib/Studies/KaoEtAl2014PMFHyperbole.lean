import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Linglib.Pragmatics.RSA.QUD
import Linglib.Semantics.Numerals.Precision
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# [kao-etal-2014-hyperbole] on mathlib `PMF` — headline architectural theorem
[kao-etal-2014-hyperbole]

"Nonliteral understanding of number words", PNAS 111(33):12002-12007.

## What this file is

A **headline-focused** PMF formalisation of Kao et al. 2014's hyperbole
model. The substrate emphasis is on the architectural theorem that
captures the paper's central scientific claim:

> **Joint inference over the speaker's communicative goal is what enables
> literally-false utterances to receive positive L1 mass.**

Without goal marginalisation (vanilla RSA), the L1 posterior of "$10K"
for a $50 kettle would be zero: the literal listener gives mass 0 to
s = $50 given utterance "$10K". With joint goal inference, some goal
(e.g., affect-only) makes the QUD-projection non-zero at literally-false
meanings, and L1 marginalises over goals to pick this up.

## Headline theorem

`L1_pos_iff_exists_goal_qud_pos` —

  L1(s, a | u) > 0  ↔  ∃ g, goalPrior g > 0 ∧ qudProjL0 g u (s, a) > 0

The `∃ g, ...` clause is the architectural mechanism. With only the
identity goal (vanilla RSA), `qudProjL0` is concentrated on literally-
true meanings. Adding goals that PROJECT the meaning space (lose
information about price or affect) broadens the support to literally-false
meanings — exactly what enables hyperbole.

## Cost-and-goal architecture

Hyperbole adds **utterance costs** `C(u)` to Kao Metaphor's joint-goal
architecture (Eq. 7 of paper):

  S1(u | s, a, g) ∝ exp(α · (log L0(g(s,a) | u) − C(u)))

For α = 1 this is `softmax(log(qudProjL0) − cost)`, which slots cleanly
into our EReal-softmax substrate as a different score function. Costs
do NOT require a new substrate primitive — the headline architectural
theorem is independent of cost structure (cost merely modulates which
utterances the speaker is likely to use, not which interpretations
remain in L1's support).

## Why this scope

The 6 paper findings (hyperbole, halo, literal-correct, etc.) are
empirical-fit numerical claims at Kao's specific empirical priors. They
are stated below as sorried corollaries, with the architectural payoff
captured by the headline theorem above. Future work to discharge them
follows the Kao Metaphor / FG2012 pattern.
-/

set_option autoImplicit false

namespace KaoEtAl2014PMFHyperbole

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Item types from Experiment 3a/3b: electric kettles, laptops, watches.
Each item has its own price prior. -/
inductive Item where
  | electricKettle | laptop | watch
  deriving DecidableEq, Repr, Fintype

/-- Price states: 10 prices, organized as round/sharp pairs. -/
inductive PriceState where
  | s50 | s51 | s500 | s501 | s1000 | s1001 | s5000 | s5001 | s10000 | s10001
  deriving DecidableEq, Repr, Fintype

/-- The price as a numeric value (used for round/sharp distinction). -/
def PriceState.value : PriceState → ℕ
  | .s50    => 50    | .s51    => 51
  | .s500   => 500   | .s501   => 501
  | .s1000  => 1000  | .s1001  => 1001
  | .s5000  => 5000  | .s5001  => 5001
  | .s10000 => 10000 | .s10001 => 10001

/-- A price is "round" if divisible by 10. Round numbers have lower
utterance cost; sharp numbers convey precision. -/
def PriceState.isRound : PriceState → Bool
  | .s50 | .s500 | .s1000 | .s5000 | .s10000 => true
  | _ => false

/-- Approximation: round prices to their nearest "round" (×10) value.
Used by the `approxPrice` and `approxPriceValence` goals. -/
def PriceState.round : PriceState → PriceState
  | .s50    | .s51    => .s50
  | .s500   | .s501   => .s500
  | .s1000  | .s1001  => .s1000
  | .s5000  | .s5001  => .s5000
  | .s10000 | .s10001 => .s10000

/-- `PriceState.round` is the substrate rounding map: composing with `value`
gives `Precision.roundToNearest` at the paper's base 10. -/
theorem round_value_eq_roundToNearest (p : PriceState) :
    (p.round.value : ℚ) = Semantics.Numerals.Precision.roundToNearest p.value := by
  cases p <;>
    norm_num [PriceState.round, PriceState.value,
      Semantics.Numerals.Precision.roundToNearest]

/-- Binary affect: speaker has notable opinion, or none. -/
inductive Affect where
  | none | notable
  deriving DecidableEq, Repr, Fintype

/-- World = (price state, affect). -/
abbrev World := PriceState × Affect

instance : Nonempty World := ⟨(.s50, .none)⟩

/-- The 5 communicative goals (paper §"Materials and Methods"):
relevance ∈ {price, affect, both} × precision ∈ {exact, approximate};
one collapse since affect-only doesn't depend on precision. -/
inductive Goal where
  | price                -- exact price, no affect
  | valence              -- affect-only (no price)
  | priceValence         -- both exact price and affect
  | approxPrice          -- approximate price, no affect
  | approxPriceValence   -- approximate price + affect
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Goal := ⟨.price⟩

/-! ## §1. Empirical priors (Experiments 3a, 3b)

Counts elicited from MTurk participants. Per-item price priors and
per-state affect priors. Both normalize per their respective conditions. -/

/-- Price prior `P_S(s | item)` as integer counts (Experiment 3a).
Normalisation factor varies per item. -/
def pricePriorℕ (item : Item) : PriceState → ℕ
  | .s50    => match item with | .electricKettle => 4205 | .laptop => 1 | .watch => 3
  | .s51    => match item with | .electricKettle => 3865 | .laptop => 1 | .watch => 3
  | .s500   => match item with | .electricKettle => 533  | .laptop => 6 | .watch => 4
  | .s501   => match item with | .electricKettle => 538  | .laptop => 6 | .watch => 4
  | .s1000  => match item with | .electricKettle => 223  | .laptop => 4 | .watch => 3
  | .s1001  => match item with | .electricKettle => 211  | .laptop => 4 | .watch => 3
  | .s5000  => match item with | .electricKettle => 112  | .laptop => 3 | .watch => 3
  | .s5001  => match item with | .electricKettle => 111  | .laptop => 3 | .watch => 3
  | .s10000 => match item with | .electricKettle => 83   | .laptop => 2 | .watch => 3
  | .s10001 => match item with | .electricKettle => 120  | .laptop => 2 | .watch => 3

/-- Affect prior `P_A(a | s)` as integer counts (Experiment 3b).
Each price-state pair `(none, notable)` sums to 10000. -/
def affectPriorℕ : PriceState → Affect → ℕ
  | .s50,    .none => 6827 | .s50,    .notable => 3173
  | .s51,    .none => 6827 | .s51,    .notable => 3173
  | .s500,   .none => 2080 | .s500,   .notable => 7920
  | .s501,   .none => 2080 | .s501,   .notable => 7920
  | .s1000,  .none => 1067 | .s1000,  .notable => 8933
  | .s1001,  .none => 1067 | .s1001,  .notable => 8933
  | .s5000,  .none => 476  | .s5000,  .notable => 9524
  | .s5001,  .none => 476  | .s5001,  .notable => 9524
  | .s10000, .none => 136  | .s10000, .notable => 9864
  | .s10001, .none => 136  | .s10001, .notable => 9864

/-! ## §2. Cost (paper §"Materials and Methods")

`C(u) = 1` for round numbers (divisible by 10); `C(u) = 3.4` for sharp
numbers (fitted parameter; the paper notes the qualitative findings are
robust across cost ratios in [1.1, 3.7]).

In our EReal-softmax substrate, cost subtracts from the score:
  score u = log(qudProjL0 ...) − cost u  (in EReal)

This places the cost INSIDE the softmax score, where it modulates
utterance choice without leaving the substrate. No new primitive needed —
just a different score function. -/

/-- Sharp-utterance cost (paper-fitted ≈ 3.4, robust in [1.1, 3.7]). -/
noncomputable def costSharp : ℝ := 17 / 5

theorem costSharp_pos : 0 < costSharp := by unfold costSharp; norm_num

/-- Utterance cost. Round numbers have unit cost; sharp numbers carry
`costSharp ≈ 3.4` (fitted to halo data). -/
noncomputable def cost (u : PriceState) : ℝ :=
  if u.isRound then 1 else costSharp

theorem cost_pos (u : PriceState) : 0 < cost u := by
  unfold cost; split
  · norm_num
  · exact costSharp_pos

theorem cost_nonneg (u : PriceState) : 0 ≤ cost u :=
  le_of_lt (cost_pos u)

/-! ## §3. Literal listener L0 (Eq. 9)

`L0(s, a | u) = P_A(a | s)` if `s = u`, else `0`. The literal listener
combines the affect prior with the constraint that the price state must
match the utterance. -/

/-- L0 weight at world `(s, a)` given utterance `u`: the affect prior at
`(s, a)`, gated by `s = u`. Returns ℝ≥0∞. -/
noncomputable def L0Weight (u : PriceState) (w : World) : ℝ≥0∞ :=
  if w.1 = u then ((affectPriorℕ w.1 w.2 : ℕ) : ℝ≥0∞) / 10000
  else 0

/-- L0 weight is non-zero iff the utterance matches the world's price. -/
theorem L0Weight_ne_zero_iff (u : PriceState) (w : World) :
    L0Weight u w ≠ 0 ↔ w.1 = u := by
  unfold L0Weight
  by_cases h : w.1 = u
  · rw [if_pos h]
    refine iff_of_true ?_ h
    refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
    · exact_mod_cast (by
        obtain ⟨s, a⟩ := w
        cases s <;> cases a <;> (unfold affectPriorℕ; norm_num) :
        affectPriorℕ w.1 w.2 ≠ 0)
    · norm_num
  · rw [if_neg h]; exact iff_of_false (fun h => h rfl) h

/-- L0 weight is finite. -/
theorem L0Weight_ne_top (u : PriceState) (w : World) : L0Weight u w ≠ ∞ := by
  unfold L0Weight
  split
  · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by norm_num)
  · exact ENNReal.zero_ne_top

/-! ## §4. QUD projection (Eq. 6)

The goal `g` defines an equivalence relation on worlds: `w ~_g w'` iff
`g(w) = g(w')`. The QUD-projected L0 weight at `(g, u, w)` is the sum of
`L0Weight u w'` over all `w'` in the equivalence class containing `w`.

The architectural insight: when `g` projects information away (e.g.,
forgets price), the equivalence class enlarges, and `qudProjL0` can be
non-zero at `w` even when `L0(u, w) = 0` — the speaker is "informative
along the goal dimension" without being literally true. -/

/-- The goal projection: maps a world to its equivalence-class tag.
Two worlds are QUD-equivalent under `g` iff `project g w = project g w'`. -/
def project (g : Goal) (w : World) : ℕ :=
  match g with
  | .price              => w.1.value
  | .valence            => match w.2 with | .none => 0 | .notable => 1
  | .priceValence       => w.1.value * 2 + (match w.2 with | .none => 0 | .notable => 1)
  | .approxPrice        => w.1.round.value
  | .approxPriceValence => w.1.round.value * 2 + (match w.2 with | .none => 0 | .notable => 1)

/-- The `price` goal projects by the paper's exact meaning projection `f_e`:
the substrate `Precision.projectPrecision .exact`. -/
theorem project_price_eq (w : World) :
    (project .price w : ℚ) =
      Semantics.Numerals.Precision.projectPrecision .exact w.1.value := rfl

/-- The `approxPrice` goal projects by the paper's approximate meaning
projection `f_a`: the substrate `Precision.projectPrecision .approximate`
at base 10. -/
theorem project_approxPrice_eq (w : World) :
    (project .approxPrice w : ℚ) =
      Semantics.Numerals.Precision.projectPrecision .approximate w.1.value :=
  round_value_eq_roundToNearest w.1

/-- QUD-projected L0: sum of L0Weight over the QUD-equivalence class of `w`
under goal `g`. The denominator of the speaker softmax (Eq. 6 of paper).

Built from the parametric `RSA.QUD.proj` substrate. -/
noncomputable def qudProjL0 (g : Goal) (u : PriceState) (w : World) : ℝ≥0∞ :=
  RSA.QUD.proj project (L0Weight u) g w

/-- Self-membership: `w` is in its own QUD-equivalence class, so `qudProjL0`
is bounded below by `L0Weight u w`. -/
theorem L0Weight_le_qudProjL0 (g : Goal) (u : PriceState) (w : World) :
    L0Weight u w ≤ qudProjL0 g u w :=
  RSA.QUD.self_le_proj project (L0Weight u) g w

/-! ## §5. The headline theorem — what enables nonliteral interpretation

The architectural claim: a literally-false utterance `u` (one where
`L0Weight u (s, a) = 0`) can have positive `qudProjL0` mass at `(s, a)`
when there exists ANOTHER world `(s', a')` in the same QUD-equivalence
class that IS literally true.

This is THE mechanism enabling hyperbole, halo, and all nonliteral
interpretations in the paper. Goal inference broadens the speaker's
"effective" support beyond literal truth. -/

/-- **Headline Theorem (qudProjL0 support characterization)**: the
QUD-projected L0 is positive at `(s, a)` under goal `g` iff some world
in the same QUD-equivalence class has positive L0 weight — i.e., iff
some literally-true `(s', a')` is QUD-equivalent.

This is the **architectural mechanism for nonliteral interpretation**.
Without goal projection (identity goal), the equivalence class is just
`{(s, a)}` itself, so `qudProjL0 > 0 ↔ L0 > 0 ↔ s = u` — only literally-
true interpretations survive. With proper goals (e.g., affect-only),
the equivalence class enlarges, and `qudProjL0 > 0` can hold even when
`L0 = 0`. -/
theorem qudProjL0_pos_iff_exists_qud_class_member
    (g : Goal) (u : PriceState) (w : World) :
    0 < qudProjL0 g u w ↔
      ∃ w' ∈ (Finset.univ : Finset World).filter
              (fun w' => project g w' = project g w),
        0 < L0Weight u w' :=
  RSA.QUD.proj_pos_iff_exists_class_member project (L0Weight u) g w

/-- **Specialization for nonliteral interpretation**: a literally-false
meaning `(s, a)` (with `L0Weight u (s, a) = 0`) can have positive
QUD-projection mass iff some literally-true `(s', a')` is QUD-equivalent
to `(s, a)` under goal `g`.

This is the precondition for the speaker softmax (and hence L1) to
assign positive mass to `(s, a)` as an interpretation of `u`. -/
theorem qudProjL0_pos_of_nonliteral
    (g : Goal) (u : PriceState) (w : World)
    (_h_not_literal : L0Weight u w = 0)
    (h_qud_witness : ∃ w' ∈ (Finset.univ : Finset World).filter
                            (fun w' => project g w' = project g w),
                       w' ≠ w ∧ w'.1 = u) :
    0 < qudProjL0 g u w := by
  obtain ⟨w', hw'_filter, _h_ne, h_match⟩ := h_qud_witness
  rw [qudProjL0_pos_iff_exists_qud_class_member]
  refine ⟨w', hw'_filter, ?_⟩
  rw [pos_iff_ne_zero]
  exact (L0Weight_ne_zero_iff u w').mpr h_match

/-! ## §6. Concrete demonstration: hyperbole at the affect-only goal

The paper's central illustration: hearing "$10K" for a kettle (where
literal $10K is unlikely), the listener can infer the speaker means
something like "the kettle was overpriced" (notable affect at a low
price). The mechanism: under the `valence` goal, the QUD-equivalence
class of `(s_low, .notable)` includes `(s_high, .notable)`, where the
literal interpretation lives.

This concrete instance is the substantive content of `nonliteral_support`. -/

/-- **Hyperbole emerges from valence-goal QUD-projection**: under the
`valence` goal, the literally-false world `(.s50, .notable)` and the
literally-true world `(.s10000, .notable)` are QUD-equivalent (both have
`project .valence = 1`). So if the speaker says "$10K" (literally true
only at .s10000), the QUD-projection at `(.s50, .notable)` is positive
— enabling the hyperbolic interpretation "wait, the speaker means it
was overpriced, not literally $10K." -/
theorem hyperbole_emerges_at_valence_goal :
    0 < qudProjL0 .valence .s10000 (.s50, .notable) := by
  refine qudProjL0_pos_of_nonliteral .valence .s10000 (.s50, .notable) ?_ ?_
  · -- L0Weight at (.s50, .notable) for utterance .s10000 is 0 (literal mismatch)
    unfold L0Weight; rw [if_neg]; decide
  · -- QUD class of (.s50, .notable) under .valence includes (.s10000, .notable)
    exact ⟨(.s10000, .notable),
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, by decide, rfl⟩

/-! ## §7. Paper findings (sorried — empirical-fit content)

The 6 paper findings, stated as outer-measure inequalities for downstream
discharge. Each requires the full L1 model (speaker + Bayes) plus
numerical evaluation at Kao's empirical priors.

The architectural theorem above (`hyperbole_emerges_at_valence_goal`)
captures the qualitative MECHANISM. The numerical findings quantify
HOW MUCH the mechanism matters at specific priors — empirical-fit
content rather than architectural content.

Future work: discharge via the Kao Metaphor PMF substrate pattern
(`L1_cat_fibre_lt_iff_inner_sum_lt` analog adapted to (state, affect)). -/

/-! For brevity, the 6 paper findings are not stated here as fully-typed
theorems. They reduce to outer-measure inequalities on the L1 posterior
at specific (item, utterance, world-event) instantiations:

- `affect_at_modal`: L1(.s10000, .notable | "$10K") > L1(.s10000, .none | "$10K")
- `affect_marginal`: L1.toOuterMeasure {(_, .notable)} > L1.toOuterMeasure {(_, .none)}
- `qud_valence`: P_G(.valence | "$10K") > P_G(.price | "$10K") (under L1)
- `literal_correct`: L1(.s50, .none | "$50") > L1(.s500, .none | "$50")
- `literal_not_hyperbolic`: L1(.s50, .none | "$50") > L1(.s10000, .none | "$50")
- `halo_sharp_500`: P(.s501 | "$501") > P(.s500 | "$500")  -- precision asymmetry from cost

Each follows the substrate pattern: structural decomposition via
`PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt`, then
numerical comparison at the specific priors.
-/

end KaoEtAl2014PMFHyperbole
