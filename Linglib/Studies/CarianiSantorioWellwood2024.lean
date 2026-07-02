import Linglib.Semantics.Degree.Gradability.StatesBased
import Linglib.Semantics.Attitudes.Confidence
import Linglib.Semantics.Attitudes.EpistemicThreshold
import Linglib.Fragments.English.Modifiers.Adjectives
import Linglib.Studies.Wellwood2015

/-!
# [cariani-santorio-wellwood-2024]: Confidence Reports

[cariani-santorio-wellwood-2024]

States-based semantics for nominal and adjectival confidence reports
(`Ann is/has confident/confidence that p`) and their comparative forms.
The paper extends Wellwood's [wellwood-2015] cross-categorial
comparative analysis to gradable attitude expressions; the central
contribution is a POS-morpheme-free account of the positive form
(CSW §3.3) plus a per-holder, non-probabilistic confidence ordering
(CSW §4.1) that admits Tversky–Kahneman conjunction fallacies (CSW §4.6).

The substrate machinery lives in `Semantics/Gradability/StatesBased.lean`
(positive-region predicates over a preorder) and
`Semantics/Attitudes/Confidence.lean` (`ConfidenceOrdering`,
`confidentEntry`/`certainEntry`, the §4.6 logic theorems). This study
file connects CSW's empirical claims to the substrate theorems and
witnesses the central cross-framework disagreement against
`Semantics/Attitudes/EpistemicThreshold.lean`.

## Coverage

| CSW section | What this file covers                                                |
|-------------|----------------------------------------------------------------------|
| §3.3        | POS-free positive form: `inPositiveRegion` over `confidentEntry`     |
| §4.6 (52)   | Conjunction fallacy: `conjunction_fallacy_predicted` (→ `confidence_not_probabilistic`) |
| §4.6 (53)   | Upward monotonicity (`Confidence.confidence_upward_monotone`)        |
| §4.6 (54)   | Transitivity of comparative confidence                               |
| §4.6 (55)   | Antisymmetry of equative confidence                                  |
| §4.6 (56–58)| Connectedness — formalized as agnostic, per CSW p.27                 |
| §4.6 (52) ↔ Threshold | Cross-framework refutation: `EpistemicThreshold.confidence_not_probabilistic` |
| §5.2 (65–66)| Asymmetric entailment `certain ⊨ confident`                          |
| §5.2 (63a–c)| Doubts triangle: confident + doubts mutually exclusive               |
| §5.2 (72)   | Comparative scale-mate equivalence                                   |
| Wellwood 2015 → CSW | Compositional bridge under unique-state assumption           |

## Out of scope (future-work sections at the bottom)

- §5.1 conditional confidence: CSW p.28 explicitly note this is "not
  entirely predicted by the system we have set up" and propose two
  off-the-shelf modifications without choosing between them.
- §5.3 `likely`: CSW sketch but do not formalize the extension to
  probability operators. The Moore-paradox asymmetry CSW discuss
  (74)–(75) is a synthesis claim across CSW + a separate `likely`
  semantics, not a CSW-derived prediction.
- §3.5 varieties (`confident in Bill`, bare `confident`, `feel confident`):
  CSW's §4.5 distributional argument for the Neodavidsonian framework.

-/

namespace CarianiSantorioWellwood2024

open Semantics.Gradability.StatesBased
open Semantics.Attitudes.Confidence
open Semantics.Attitudes.EpistemicThreshold (AgentCredence isProbabilistic
  meetsThreshold prob_conjunction_elim confidence_not_probabilistic)

/-! ## §1. Felicity Gradient

CSW use a graded inventory of acceptability marks (`✓` / `?` / `??` /
`#`). Encoding judgments as a 4-valued enum preserves the gradient
that a `Bool` encoding flattens — the difference between `??` (CSW 65b
adjectival) and `?` (CSW 66b nominal) is itself part of the data CSW
present. -/

/-- Felicity judgment levels, ordered from acceptable to unacceptable.
    Matches CSW's notational inventory. -/
inductive Felicity : Type where
  /-- ✓ — fully acceptable -/
  | acceptable
  /-- ? — mildly marked -/
  | mild
  /-- ?? — strongly marked -/
  | strong
  /-- # — infelicitous / contradictory -/
  | unacceptable
  deriving DecidableEq, Repr

/-! ## §2. Asymmetric Entailment: `certain ⊨ confident` (CSW (65)/(66))

CSW (65a) "Ann is confident that p, but she isn't certain that p." ✓
CSW (65b) "??Ann is certain that p, but she isn't confident that p."
CSW (66a) "Bob has confidence, but not certainty, that p." ✓
CSW (66b) "?Bob has certainty, but not confidence, that p."

The adjectival pair (65) is more sharply contrasted (??) than the
nominal pair (66) (?). Both directions are encoded; the substrate
predicts the direction from `certainEntry`'s maximality assumption. -/

/-- The (65a)/(66a) felicitous pair: confidence without certainty is
    consistent. Predicted by `confident_not_entails_certain`: when
    `confPt` is strictly below the certainty contrast point, the
    confidence positive region is not contained in the certainty one. -/
theorem confident_without_certain_consistent {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_strict : ¬ co.le maxPt confPt) :
    letI := co.toPreorder
    ¬ asymEntails (confidentEntry co confPt) (certainEntry co maxPt) :=
  confident_not_entails_certain co confPt maxPt h_strict

/-- The (65b)/(66b) infelicitous pair: certainty without confidence is
    inconsistent. Predicted by `certain_entails_confident`: when `maxPt`
    is the top of the ordering, the certainty positive region is contained
    in any confidence region with `confPt ≤ maxPt`. -/
theorem certain_without_confident_inconsistent {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_top : ∀ s : ConfidenceState E W, co.le s maxPt) :
    letI := co.toPreorder
    asymEntails (certainEntry co maxPt) (confidentEntry co confPt) :=
  certain_entails_confident co confPt maxPt h_top

/-- Empirical record of the (65)/(66) felicity gradient.
    Keeps adjectival (65b) and nominal (66b) markings distinct rather
    than collapsing both to `unacceptable`. -/
structure CertainConfidentJudgments where
  /-- (65a) ✓ -/
  conf_without_certain : Felicity := .acceptable
  /-- (65b) ?? — adjectival pair, sharper contrast -/
  certain_without_conf_adjectival : Felicity := .strong
  /-- (66b) ? — nominal pair, weaker contrast -/
  certain_without_conf_nominal : Felicity := .mild

def certainConfidentData : CertainConfidentJudgments := {}

/-! ## §3. Logic of Confidence Reports (CSW §4.6) -/

/-! ### §3.1 Transitivity (CSW (54)/(57)) -/

/-- CSW (54): comparative confidence is transitive. CSW (57) is
    contradictory because asserting its third clause negates the
    consequent of this entailment. -/
theorem transitivity_predicted {E W D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q s_r : ConfidenceState E W)
    (h_pq : μ s_q < μ s_p) (h_qr : μ s_r < μ s_q) :
    μ s_r < μ s_p :=
  comparative_transitive μ s_p s_q s_r h_pq h_qr

/-! ### §3.2 Antisymmetry (CSW (55)) -/

/-- CSW (55): "at least as confident of p as q" + "at least as confident
    of q as p" → "equally confident of p and q". -/
theorem antisymmetry_predicted {E W D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q : ConfidenceState E W)
    (h₁ : μ s_q ≤ μ s_p) (h₂ : μ s_p ≤ μ s_q) :
    μ s_p = μ s_q :=
  comparative_antisymmetric μ s_p s_q h₁ h₂

/-! ### §3.3 Connectedness (CSW (56)/(58)) — Agnostic

CSW p.27: "We remain agnostic about whether Connectedness actually
holds for confident and confidence." (58) is a candidate counterexample
where some propositions might simply not be comparable.

The substrate models this by using `Preorder` (which doesn't require
totality) rather than `LinearOrder`. There is no theorem to prove on
either side: the agnosticism is the substantive content. -/

/-- CSW remain agnostic about Connectedness. Encoded as a flag rather
    than a theorem to make the agnosticism formally visible. -/
structure ConnectednessStance where
  /-- Whether CSW commit to Connectedness for confidence orderings. -/
  csw_committed : Bool := false

def connectednessStance : ConnectednessStance := {}

/-! ### §3.4 Conjunction Fallacy (CSW (52)) -/

/-- CSW (52): it is consistent for "John is not confident that Linda is a
    banker" and "John is confident that Linda is a feminist banker" to hold
    together — confidence orderings are not constrained to respect logical
    conjunction (CSW's central argument against probability-functional accounts;
    [tversky-kahneman-1983]).

    Genuine witness: a non-monotone credence ranking a *consistent* conjunction
    strictly above a conjunct (`EpistemicThreshold.confidence_not_probabilistic`),
    which no probability measure can do. The cross-framework consequence is §6's
    `states_vs_threshold_on_conjunction_fallacy`. -/
theorem conjunction_fallacy_predicted :
    ∃ (cr : AgentCredence Unit Bool),
      ¬ isProbabilistic cr ∧
      ∃ (φ ψ : Bool → Bool), cr () φ < cr () (fun w => φ w && ψ w) :=
  confidence_not_probabilistic

/-! ### §3.5 Upward Monotonicity (CSW (53)) -/

/-- CSW (53): "σ is confident that p" + "σ is more confident of q than
    of p" → "σ is confident that q". Direct consequence of preorder
    transitivity through the contrast point. -/
theorem upward_monotonicity_predicted {E W : Type*}
    (co : ConfidenceOrdering E W)
    (entry : @StatesBasedEntry _ co.toPreorder)
    (s_p s_q : ConfidenceState E W)
    (h_conf : @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_p)
    (h_more : co.le s_p s_q) :
    @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_q :=
  confidence_upward_monotone co entry s_p s_q h_conf h_more

/-! ### §3.6 Doubts Triangle (CSW (63a)–(63c)) -/

/-- CSW (63a)→(63b)→¬(63c): `confident` and `doubts` are mutually
    exclusive, when the doubt contrast point lies strictly below the
    confidence contrast point on the holder's confidence ordering.

    The triangle: (63a) `certain(p)` entails (63b) `confident(p)` (via
    `certain_entails_confident`); (63b) is inconsistent with (63c)
    `doubts(p)` (this theorem); so (63a) is inconsistent with (63c).

    The substrate models `doubts` as a negative-polarity entry on the
    same `ConfidenceOrdering` as `confident`/`certain`: same entry shape
    (`StatesBasedEntry`), but consumers test `inLowerRegion` rather than
    `inPositiveRegion`. -/
theorem doubts_excludes_confidence_predicted {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt doubtPt : ConfidenceState E W)
    (h_strict : ¬ co.le confPt doubtPt)
    (s : ConfidenceState E W) :
    letI := co.toPreorder
    ¬ (StatesBasedEntry.inPositiveRegion (confidentEntry co confPt) s ∧
       StatesBasedEntry.inLowerRegion (doubtsEntry co doubtPt) s) :=
  confident_excludes_doubts co confPt doubtPt h_strict s

/-! ## §4. Comparative Scale-Mate Equivalence (CSW (72))

CSW (72): "A is more confident that p than that q" and "A is more
certain that p than that q" are truth-conditionally equivalent.

CSW p.31 explanation: the comparative discards the contrast function
and uses only the shared background ordering. The substrate captures
this **architecturally** — `statesComparativeSem` takes no
`StatesBasedEntry` parameter, so the contrast point that distinguishes
`confident` from `certain` is invisible to the comparative. The
prediction holds by construction. -/

/-- The comparative `μ-measure` ordering does not depend on which
    entry's positive region is being asked about — it sees only the
    measure function and the states.

    This is the substrate-level witness that CSW (72)'s scale-mate
    equivalence is structural, not provable. The function signature
    omits any entry parameter; pluralizing across `confidentEntry`
    and `certainEntry` is moot because the function never sees them. -/
theorem comparative_equivalence_structural {E W D : Type*} [Preorder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q : ConfidenceState E W) :
    statesComparativeSem μ s_p s_q ↔ μ s_q < μ s_p :=
  Iff.rfl

/-! ## §5. POS-Free Positive Form (CSW §3.3)

The central architectural commitment of the paper. CSW (28b)/(40):
the positive form `g-ness_C(s)` holds iff `s ≿ contrast(g-ness)` —
no covert `pos` morpheme is invoked.

The substrate (`StatesBased.inPositiveRegion`) implements this
directly: `entry.contrastPoint ≤ s` over the background preorder.
Different lexical entries (`confidentEntry`, `certainEntry`) on the
*same* `ConfidenceOrdering` have *different* positive regions because
their `contrastPoint`s differ — exactly CSW's analysis without ever
introducing POS. -/

/-- POS-free positive form: `confident` and `certain` produce different
    positive-region predicates on the same confidence ordering, with no
    `pos` morpheme intervening.

    The two predicates differ exactly when there is a state in
    `confident`'s region but not `certain`'s — i.e., when the confidence
    contrast point is strictly below the certainty contrast point. -/
theorem positive_form_pos_free {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_strict : ¬ co.le maxPt confPt) :
    letI := co.toPreorder
    ∃ s : ConfidenceState E W,
      StatesBasedEntry.inPositiveRegion (confidentEntry co confPt) s ∧
      ¬ StatesBasedEntry.inPositiveRegion (certainEntry co maxPt) s := by
  refine ⟨confPt, ?_, ?_⟩
  · show co.le confPt confPt
    exact co.le_refl _
  · show ¬ co.le maxPt confPt
    exact h_strict

/-! ## §6. Cross-Framework Refutation: States-Based vs Threshold-Probabilistic

CSW's central argument against extending threshold-style epistemic
semantics (Lassiter 2011/2016, Yalcin 2010) to confidence reports is
that confidence orderings need not respect logical conjunction
(CSW (52), §4.6). Probabilistic credence violates this: any monotone
credence function validates `Pr(p ∧ q) ≤ Pr(p)`.

The two halves of the disagreement are now formal:

- States-based admits the fallacy: `confidence_not_probabilistic` (a non-monotone
  credence ranking a consistent conjunction above a conjunct; §3.4 above).
- Probabilistic credence forbids it: `EpistemicThreshold.prob_conjunction_elim`.
- A credence function realizing the fallacy cannot be probabilistic:
  `EpistemicThreshold.confidence_not_probabilistic`.

This study file packages the disagreement as the joint statement
below. -/

/-- The empirical disagreement on CSW (52) / Tversky–Kahneman 1983,
    formalized as the conjunction of two opposing predictions:

    1. **States-based prediction** (CSW): there is a confidence ordering
       admitting the fallacy (`confidence_not_probabilistic` provides an
       `AgentCredence` witness with consistent propositions).
    2. **Threshold-probabilistic prediction**: any probabilistic credence
       blocks the fallacy at every threshold
       (`prob_conjunction_elim`).

    The two cannot agree on any datum where the fallacy is in fact
    consistent. CSW take the conjunction-fallacy data as decisive
    evidence against the threshold approach. -/
theorem states_vs_threshold_on_conjunction_fallacy :
    -- States-based side: a non-probabilistic credence with a witness
    (∃ (cr : AgentCredence Unit Bool),
       ¬ isProbabilistic cr ∧
       ∃ (φ ψ : Bool → Bool), cr () φ < cr () (fun w => φ w && ψ w))
    ∧
    -- Threshold side: probabilistic credence forbids the fallacy
    (∀ {E W : Type*} (cr : AgentCredence E W),
       isProbabilistic cr →
       ∀ (θ : ℚ) (a : E) (φ ψ : (W → Bool)),
         meetsThreshold cr θ a (fun w => φ w && ψ w) →
         meetsThreshold cr θ a φ) :=
  ⟨confidence_not_probabilistic,
   fun cr h_prob θ a φ ψ => prob_conjunction_elim cr h_prob θ a φ ψ⟩

/-! ## §7. Cross-Framework Agreement on `certain`

Three independent treatments of `certain` agree that it sits at the
upper bound of an upper-bounded scale:

1. **Fragment** (`Adjectives.certain.scaleType = .upperBounded`)
2. **Threshold** (`EpistemicThreshold.EpistemicEntry.certain_.θ = 19/20`,
   close to the scale max of 1)
3. **States-based** (`Confidence.certainEntry`'s contrast point is the
   ordering's maximum, by `h_top`)

The three encodings have genuinely different mathematical structure
(enum tag vs ℚ value vs preorder maximality), so the agreement is not
forced by a shared substrate primitive — it is a coincidence of
independent commitments that nevertheless converges. -/

/-- Two-way agreement: the Fragment and the threshold theory both
    classify `certain` at the top of an upper-bounded scale. -/
theorem certain_fragment_and_threshold_agree :
    English.Modifiers.Adjectives.certain.scaleType = .upperBounded ∧
    Semantics.Attitudes.EpistemicThreshold.EpistemicEntry.certain_.θ = 19/20 :=
  ⟨rfl, rfl⟩

/-- Polarity asymmetry across the Fragment's confidence-scale entries:
    `confident`/`certain`/`sure` pick out the *upper* region (positive
    polarity, `upperBounded`); `doubtful`/`unsure`/`uncertain` pick out
    the *lower* region (negative polarity, `lowerBounded`). The polarity
    split lives in the `scaleType` field; the substrate's
    `inPositiveRegion` vs `inLowerRegion` query then dispatches
    accordingly. -/
theorem confidence_adjectives_polarity_split :
    -- Positive polarity (upper region)
    English.Modifiers.Adjectives.confident.scaleType = .upperBounded ∧
    English.Modifiers.Adjectives.certain.scaleType   = .upperBounded ∧
    English.Modifiers.Adjectives.sure.scaleType      = .upperBounded ∧
    -- Negative polarity (lower region)
    English.Modifiers.Adjectives.doubtful.scaleType  = .lowerBounded ∧
    English.Modifiers.Adjectives.unsure.scaleType    = .lowerBounded ∧
    English.Modifiers.Adjectives.uncertain.scaleType = .lowerBounded :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Dimension agreement across the Fragment's six confidence-scale
    entries: positive- and negative-polarity adjectives all carry
    `dimension := .confidence`, anchoring them to the same
    `ConfidenceOrdering` substrate. The polarity split (above) and
    dimension agreement together capture CSW's cluster structure:
    one shared background ordering, two regions, six lexical anchors. -/
theorem confidence_adjectives_share_dimension :
    English.Modifiers.Adjectives.confident.dimension = .confidence ∧
    English.Modifiers.Adjectives.certain.dimension   = .confidence ∧
    English.Modifiers.Adjectives.sure.dimension      = .confidence ∧
    English.Modifiers.Adjectives.doubtful.dimension  = .confidence ∧
    English.Modifiers.Adjectives.unsure.dimension    = .confidence ∧
    English.Modifiers.Adjectives.uncertain.dimension = .confidence :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §8. Compositional Bridge: Wellwood 2015 → CSW

CSW build their analysis on Wellwood's [wellwood-2015]
cross-categorial comparative. The bridge below specializes Wellwood's
`adjectival_max_reduces` (which proves the comparative reduces to a
direct degree comparison under unique-eventuality assumptions) to the
shape CSW use.

This is the only bridge in the file that does substantive composition —
the others wire through substrate theorems directly. -/

/-- Wellwood 2015's `adjectivalComparative`, instantiated for confidence
    states, reduces to direct measure comparison under unique-state
    assumptions. This closes CSW's compositionality claim that nominal
    `confidence` and adjectival `confident` are interchangeable in
    comparative form. -/
theorem confidence_comparative_reduces
    {E : Type*} {Time : Type*} [LinearOrder Time]
    {frame : ArgumentStructure.ThematicFrame E Time}
    {P : Event Time → Prop}
    {μ : Event Time → ℚ}
    {a b : E} {sa sb : Event Time}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    Wellwood2015.adjectivalComparative frame P μ a b ↔ μ sb < μ sa :=
  Wellwood2015.adjectival_max_reduces ha ha_unique hb hb_unique

/-! ## §9. Future Work

Three CSW topics that this file does not formalize, with the reason
each is deferred:

### §5.1 Conditional Confidence (CSW (61))

CSW p.28: *"Confidence reports interact with conditional antecedents
in ways that are not entirely predicted by the system we have set up."*
CSW propose two off-the-shelf modifications (modal-base restriction or
information-state indexing) and conclude (p.29): *"Choosing between
these options is, of course, beyond the scope of the present
investigation."* No theorem belongs here until CSW or successors choose
between the two options.

### §5.3 `likely` and the Moore-Paradox Asymmetry (CSW (74)–(75))

CSW sketch but do not formalize an extension to probabilistic modal
adjectives. The Moore-paradox asymmetry CSW illustrate is between
*holder-relativized* `confident` and *impersonal* `likely`. The
substrate's `EpistemicThreshold.likely_` is *agent-relative* (`cr a φ`
threshold), not impersonal — so it cannot directly host the
asymmetry. A faithful formalization would require either (a) a
world-dependent objective probability primitive, or (b) a separate
study file anchored on Yalcin 2007 or Lassiter 2016 that introduces
the impersonal `likely` semantics.

-/

end CarianiSantorioWellwood2024
