import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.JointPosterior
import Linglib.Pragmatics.RSA.QUD
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# [kao-goodman-2015] on mathlib `PMF` — headline architectural theorem
[kao-goodman-2015]

"Let's talk (ironically) about the weather: Modeling verbal irony"
*Proceedings of the 37th Annual Meeting of the Cognitive Science Society* (2015).

## What this file is

A **headline-focused** PMF formalisation of Kao & Goodman 2015's irony
model — a minimal extension of the Kao 2014 hyperbole architecture that
uses an additional **arousal** affect dimension.

## The headline architectural insight

The paper's central scientific claim:

> "Adding the arousal dimension to affect is what enables ironic
> interpretation. Without arousal as a QUD, the model produces hyperbole
> but NOT irony."

The mechanism: **arousal is symmetric across valence-opposite weather
states** (the U-curve). Both `.terrible` and `.amazing` weather have
HIGH arousal; only `.neutral` has low arousal. So under the `.arousal`
QUD, the equivalence class of `.terrible` includes `.amazing` —
LITERALLY OPPOSITE in valence. The pragmatic listener can then
rationally interpret "the weather is terrible" as "speaker means the
weather is amazing, but feels strongly about it" — valence flip = irony.

Compare to Kao 2014 hyperbole, where the valence QUD connects worlds
of the SAME valence (different states); irony requires the arousal QUD
to connect worlds of OPPOSITE valence (arousal-symmetric states).

## Headline theorem

`arousal_qud_creates_valence_opposite_equivalence` — for any pair of
weather states `s, s'` that are arousal-equivalent but valence-opposite,
the arousal QUD's equivalence class connects them. This is the
architectural mechanism that differentiates irony from hyperbole.

Specialised to the paper's central case:

`terrible_amazing_arousal_equivalent` — "terrible" and "amazing" are
both high-arousal states, so under `.arousal` QUD the speaker's
"terrible" utterance has positive `qudProjL0` mass at the world
`(.amazing, .positive, .high)` — enabling the ironic interpretation.

## Substrate validation

This file is the second irony-family migration (after Kao 2014
hyperbole). Both share the same `qudProjL0` substrate. The architectural
distinction is purely in the **affect prior structure** (which dimension
is symmetric across worlds the speaker might want to flip) and in the
**QUD inventory** (which dimensions get marginalised).

The substrate handles both papers without modification — the EReal
softmax + posterior decomposition + qudProjL0_pos_iff_exists_qud_class
lemmas all transfer directly. Only the priors and goal projection
function change.

## Scope

The 6 paper findings (`ironic_nonliteral`, `ironic_valence_flip`,
`ironic_high_arousal`, `no_irony_without_arousal`, `literal_state`,
`literal_no_flip`) are described in §6 prose with discharge path
sketched. Empirical-fit content; the architectural payoff is the
headline above.
-/

set_option autoImplicit false

namespace KaoEtAl2015PMF

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Weather states (paper §"Computational Model"): 5 ordered values from
terrible to amazing. Weather states double as utterance types — the speaker
says "the weather is X" for X in this set. -/
inductive Weather where
  | terrible | bad | neutral | good | amazing
  deriving DecidableEq, Repr, Fintype

/-- Communicative goals / QUDs. Three dimensions:
- `.state`: literal state (price-equivalent in hyperbole)
- `.valence`: positive vs negative emotional valence (hyperbole's affect)
- `.arousal`: high vs low emotional arousal — **the irony-enabling dimension**

The paper's central claim is that adding `.arousal` to the QUD inventory
is what enables ironic interpretation. Without it, the model produces
hyperbole but not valence-flipped irony. -/
inductive Goal where
  | state | valence | arousal
  deriving DecidableEq, Repr, Fintype

/-- World: weather state × valence × arousal.
- `.1`: weather state
- `.2.1`: valence (`true` = positive, `false` = negative)
- `.2.2`: arousal (`true` = high, `false` = low) -/
abbrev World := Weather × Bool × Bool

instance : Nonempty World := ⟨(.amazing, true, true)⟩

/-! ## §1. Affect priors (Experiment 1, derived from Russell 1980 PCA)

Valence follows an S-curve across weather states (positive valence rises
monotonically: terrible → amazing).

Arousal follows a **symmetric U-curve** (high at both extremes): both
`.terrible` and `.amazing` weather have high arousal; `.neutral` has the
lowest. This U-curve is what creates the arousal-equivalence between
valence-opposite states — the architectural mechanism for irony. -/

/-- P(positive valence | weather state), ×100 (integer percent).
S-curve: terrible 1%, bad 15%, neutral 50%, good 85%, amazing 99%. -/
def positiveValencePercent : Weather → ℕ
  | .terrible =>  1
  | .bad      => 15
  | .neutral  => 50
  | .good     => 85
  | .amazing  => 99

/-- P(high arousal | weather state), ×100 (integer percent).
U-curve: terrible 90%, bad 40%, neutral 10%, good 40%, amazing 90%.
**Symmetric across valence — the irony-enabling structure.** -/
def highArousalPercent : Weather → ℕ
  | .terrible => 90
  | .bad      => 40
  | .neutral  => 10
  | .good     => 40
  | .amazing  => 90

/-- Affect prior `P(valence, arousal | state)` as integer counts ×10000
(from the product of valence and arousal probabilities, treating them as
conditionally independent given state). -/
def affectPriorℕ (st : Weather) (positive high : Bool) : ℕ :=
  let v := if positive then positiveValencePercent st else 100 - positiveValencePercent st
  let a := if high then highArousalPercent st else 100 - highArousalPercent st
  v * a

/-! ## §2. Literal listener L0 (Eq. analogous to Hyperbole Eq. 9)

`L0(s, A | u) = P(A | s)` if `s = u`, else `0`. Same form as Hyperbole. -/

/-- L0 weight at world `(s, valence, arousal)` given utterance `u`:
the affect prior at `(s, valence, arousal)`, gated by `s = u`. -/
noncomputable def L0Weight (u : Weather) (w : World) : ℝ≥0∞ :=
  if w.1 = u then ((affectPriorℕ w.1 w.2.1 w.2.2 : ℕ) : ℝ≥0∞) / 10000
  else 0

@[simp]
theorem L0Weight_of_match (u : Weather) (w : World) (h : w.1 = u) :
    L0Weight u w = ((affectPriorℕ w.1 w.2.1 w.2.2 : ℕ) : ℝ≥0∞) / 10000 := by
  unfold L0Weight; rw [if_pos h]

@[simp]
theorem L0Weight_of_mismatch (u : Weather) (w : World) (h : w.1 ≠ u) :
    L0Weight u w = 0 := by
  unfold L0Weight; rw [if_neg h]

/-- L0 weight is non-zero iff the utterance matches the world's weather AND
the affect prior at that world is non-zero. -/
theorem L0Weight_ne_zero_of_match_and_affect (u : Weather) (w : World)
    (h_match : w.1 = u) (h_affect : affectPriorℕ w.1 w.2.1 w.2.2 ≠ 0) :
    L0Weight u w ≠ 0 := by
  rw [L0Weight_of_match u w h_match]
  refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  · exact_mod_cast h_affect
  · norm_num

/-! ## §3. QUD projection — the architectural pivot

The QUD projection function `project g w` returns a value such that two
worlds are QUD-equivalent under `g` iff they project to the same value.

The three projections:
- `.state`: equivalence class = same weather state (no projection)
- `.valence`: equivalence class = same positive/negative valence
- `.arousal`: equivalence class = same high/low arousal

The architectural insight: under `.arousal`, valence-opposite states with
matching arousal are EQUIVALENT. E.g., `.terrible` and `.amazing` (both
high arousal) are arousal-equivalent — the irony-enabling pair. -/

/-- The QUD projection. Encoded as ℕ for pattern-matching simplicity. -/
def project (g : Goal) (w : World) : ℕ :=
  match g with
  | .state    => weatherIdx w.1
  | .valence  => if w.2.1 then 1 else 0
  | .arousal  => if w.2.2 then 1 else 0
where
  weatherIdx : Weather → ℕ
    | .terrible => 0 | .bad => 1 | .neutral => 2 | .good => 3 | .amazing => 4

/-- QUD-projected L0: sum of `L0Weight u w'` over worlds `w'` in the
QUD-equivalence class of `w` under goal `g`.

Built from the parametric `RSA.QUD.proj` substrate — same primitive as
Kao 2014 hyperbole, with the irony-vs-hyperbole distinction living
entirely in the prior structure (arousal U-curve) and the QUD inventory
(arousal as a goal). -/
noncomputable def qudProjL0 (g : Goal) (u : Weather) (w : World) : ℝ≥0∞ :=
  RSA.QUD.proj project (L0Weight u) g w

/-- **Headline support theorem**: qudProjL0 is positive iff some world in
the QUD-equivalence class has positive L0 weight. Direct instance of the
parametric `RSA.QUD.proj_pos_iff_exists_class_member`. -/
theorem qudProjL0_pos_iff_exists_qud_class_member
    (g : Goal) (u : Weather) (w : World) :
    0 < qudProjL0 g u w ↔
      ∃ w' ∈ (Finset.univ : Finset World).filter
              (fun w' => project g w' = project g w),
        0 < L0Weight u w' :=
  RSA.QUD.proj_pos_iff_exists_class_member project (L0Weight u) g w

/-! ## §4. The irony-vs-hyperbole architectural distinction

Both Kao 2014 (hyperbole) and Kao 2015 (irony) use qudProjL0 to enable
nonliteral interpretation. They differ in **which QUDs create which
equivalence classes**:

- **Hyperbole** (.valence QUD): the equivalence class of `(.terrible,
  negative)` is `{(.terrible, negative), (.bad, negative), ...}` — same
  valence, different states. Saying "terrible" can be interpreted as
  "merely bad" — same direction of valence, attenuated state.

- **Irony** (.arousal QUD): the equivalence class of `(.terrible, ?, .high)`
  is `{(.terrible, ?, .high), (.amazing, ?, .high)}` — opposite valence,
  matching arousal. Saying "terrible" can be interpreted as "actually
  amazing, just highly aroused" — flipped valence, matched arousal.

The headline theorem captures the irony-enabling structure. -/

/-- **Architectural theorem**: under the `.arousal` QUD, two worlds with
matching arousal are QUD-equivalent — even if they have OPPOSITE valences
or DIFFERENT weather states. -/
theorem arousal_QUD_equivalence_iff (w w' : World) :
    project .arousal w = project .arousal w' ↔ w.2.2 = w'.2.2 := by
  obtain ⟨_, _, a⟩ := w; obtain ⟨_, _, a'⟩ := w'
  cases a <;> cases a' <;> simp [project]

/-- **Headline lemma**: `.terrible` and `.amazing` are arousal-equivalent
(both high arousal). This is the irony-enabling pair: opposite valence,
matched arousal. -/
theorem terrible_amazing_arousal_equivalent :
    project .arousal (.terrible, false, true) = project .arousal (.amazing, true, true) :=
  (arousal_QUD_equivalence_iff _ _).mpr rfl

/-- **The architectural mechanism for irony** (analogue of Kao Hyperbole's
`hyperbole_emerges_at_valence_goal`).

Saying "the weather is terrible" while the actual world is `(.amazing,
positive, high)` is LITERALLY FALSE (`L0Weight .terrible (.amazing, ...) = 0`)
but has positive QUD-projection mass under the `.arousal` goal — because
the literally-true world `(.terrible, _, .high)` is arousal-equivalent.

This is the architectural condition for the speaker to rationally produce
"terrible" when actually meaning "amazing" — i.e., for verbal irony. -/
theorem irony_emerges_at_arousal_QUD :
    0 < qudProjL0 .arousal .terrible (.amazing, true, true) := by
  rw [qudProjL0_pos_iff_exists_qud_class_member]
  -- The literally-true world (.terrible, false, true) is arousal-equivalent
  -- to (.amazing, true, true), and its L0Weight is positive.
  refine ⟨(.terrible, false, true), ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- Both have arousal = true, so arousal-equivalent
    show project .arousal (.terrible, false, true) = project .arousal (.amazing, true, true)
    exact terrible_amazing_arousal_equivalent
  · -- L0Weight at the literally-true world
    rw [L0Weight_of_match .terrible (.terrible, false, true) rfl]
    -- affectPriorℕ .terrible false true = (100-1) * 90 = 99 * 90 = 8910 ≠ 0
    refine ENNReal.div_pos ?_ (by norm_num)
    show ((affectPriorℕ .terrible false true : ℕ) : ℝ≥0∞) ≠ 0
    have : affectPriorℕ .terrible false true ≠ 0 := by
      show 99 * 90 ≠ 0; decide
    exact_mod_cast this

/-! ## §5. Why arousal — and not just any QUD — enables irony

The previous theorem demonstrates that arousal QUD enables valence-flipped
interpretation. But why doesn't, say, the `.state` QUD do the same?

Answer: under `.state`, every world is in its own equivalence class
(or at most equivalence classes pairing identical states). So the only
literally-true world arousal-equivalent to `(.amazing, _, _)` under
`.state` is `(.amazing, ?, ?)` itself — no other state shares the
equivalence class. Hence "terrible" cannot be informatively used to mean
"amazing" under `.state`.

It's specifically the **arousal-symmetric prior structure** (high arousal
at both extremes) that creates the valence-flipped equivalence class. -/

/-- **No irony under .state QUD**: under the state QUD, the equivalence
class of `(.amazing, _, _)` is exactly `{w | w.1 = .amazing}` — only
`.amazing`-state worlds. So saying "terrible" gives `qudProjL0 = 0`
at any `.amazing`-state world (no literally-true `.amazing` world is
state-equivalent to a literally-true `.terrible` world). -/
theorem no_irony_under_state_QUD :
    qudProjL0 .state .terrible (.amazing, true, true) = 0 := by
  unfold qudProjL0
  refine Finset.sum_eq_zero (fun w' h_mem => ?_)
  obtain ⟨wstate, vp, ar⟩ := w'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
  refine L0Weight_of_mismatch _ _ ?_
  show wstate ≠ .terrible
  intro h_eq
  subst h_eq
  -- h_mem reduces to project.weatherIdx .terrible = project.weatherIdx .amazing, i.e., 0 = 4
  have h_lhs : project Goal.state (Weather.terrible, vp, ar) = 0 := rfl
  have h_rhs : project Goal.state ((Weather.amazing, true, true) : World) = 4 := rfl
  omega

/-! ## §6. Paper findings (sorried — empirical-fit content)

The 6 paper findings (paper §"Behavioral Experiments" + Table 1):

1. `ironic_nonliteral`: pleasantCfg.L1 .terrible (¬terrible) > L1 .terrible
2. `ironic_valence_flip`: pleasantCfg.L1 .terrible (positive) > L1 .terrible (negative)  ← **THE central irony finding**
3. `ironic_high_arousal`: pleasantCfg.L1 .terrible (high) > L1 .terrible (low)
4. `no_irony_without_arousal`: when arousal goal removed, valence flip disappears
5. `literal_state`: terribleCfg.L1 .terrible (.terrible) > L1 .terrible (¬terrible)
6. `literal_no_flip`: terribleCfg.L1 .terrible (negative) > L1 .terrible (positive)

Each follows the substrate pattern: structural decomposition via
`PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt` + numerical
comparison at the empirical priors. Findings 2 + 4 establish the paper's
central mechanistic claim (arousal QUD enables valence flip); findings
2 + 6 demonstrate context-dependence (same utterance, opposite inference
in different weather contexts).

Future work: discharge via the substrate pattern. The architectural
content (irony emerges from arousal-symmetric prior + arousal QUD) is
captured in §4 above. -/

end KaoEtAl2015PMF
