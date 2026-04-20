import Linglib.Theories.Phonology.Process.Alternation
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Theories.Phonology.Subregular.OCP
import Linglib.Theories.Learning.TolerancePrinciple
import Linglib.Core.Constraint.OT.ERC
import Linglib.Core.Computability.Subregular.Tier

/-!
# Belth (2026): A Learning-Based Account of Phonological Tiers @cite{belth-2026}

D2L (Distant-to-Local) is an iterative learner that constructs phonological
tiers as a *byproduct* of trying to express alternations as adjacent
dependencies. Given underlying-form / surface-form pairs, D2L starts by
projecting all segments and tries to predict the alternating segment from
its linear neighbours. When the resulting rule fails Yang's Tolerance
Principle @cite{yang-2016}, D2L deletes the offending segments from the
tier and tries again, until either a tolerated rule is found or no further
deletion helps.

The output of D2L is a tier-based alternation rule, modelled here by the
canonical `Phonology.Alternation.TierRule` schema (in
`Theories/Phonology/Alternation.lean`). For Latin -alis / -aris allomorphy
(@cite{belth-2026} §5.3, rule 54), the rule D2L converges to is

  `Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`,

i.e. dissimilation of the underspecified affix-initial liquid `/L/` from
the immediately preceding `[+cons]` tier segment. @cite{belth-2026}
reports 0.97 accuracy on a 121-word Perseus dataset; the residual ~3%
errors are *tolerated* by Yang's Tolerance Principle (4 ≤ 121/ln 121),
so D2L converges to this rule rather than memorizing the lexicon.

This study formalizes:

- the rule (`latinDissimRule`) and its predictions on six worked
  examples (Belth ex. 5/53): *navalis*, *popularis*, *pluvalis*,
  *floralis*, *legalis*, *lunaris*;
- the genuine empirical limit: *lunaris* surfaces with `[r]`, but the
  `[+cons]`-tier rule predicts `[l]` (the immediately preceding tier
  segment is the nasal `/n/`, which is `[−lat]`, so `Disagree` outputs
  `[+lat]`). This is one of the ~3% errors the Tolerance Principle
  tolerates;
- a Tolerance-Principle certificate
  (`latinDissimRule_tolerated_on_examples`) showing the 1-of-6 exception
  count on this corpus is well under Yang's threshold;
- a Subregular bridge (`consTier_apply_eq_tierProject`) grounding the
  consonant tier in the @cite{lambert-2022}/@cite{heinz-rawal-tabor-2011}
  TSL formalism;
- an OCP-on-tier OT constraint (`latinOCP`, via
  `Phonology.Constraints.mkOCPOnTier`) and an OT tableau bridge: each
  empirical contrast becomes a winner-loser pair, `tableauERC` extracts
  the Elementary Ranking Condition (@cite{merchant-riggle-2016}), and
  the OT analysis is shown to track the rule-based analysis exactly,
  including the same lunaris failure (the lunaris ERC is contradictory
  on the two-constraint inventory ⟨OCP, *r⟩, which is the OT-side
  analogue of the rule's underextension).

D2L's Turkish (Belth §5.1) and Finnish (§5.2) rules are sketched in §10
below. They require multi-feature dependencies and explicit Elsewhere
defaults; both extensions are admittable on demand.

**On verification scope.** D2L itself — the *learning* algorithm — is not
run inside Lean. Belth's empirical claim is that, given a corpus, D2L
*converges* to specific rules. Verifying that claim end-to-end would
require running D2L on naturalistic datasets (CHILDES, MorphoChallenge,
Perseus), which is out of scope for a Lean formalization. We instead
formalize the *learned rules* and verify their predictions on
representative examples, plus the Tolerance Principle inequality that
licenses convergence.
-/

namespace Phenomena.PhonologicalAlternation.Studies.Belth2026

open Core
open Phonology.Alternation

-- ============================================================================
-- § 1: A Minimal Latin Alphabet
-- ============================================================================

/-- A minimal Latin segment alphabet sufficient for the -alis / -aris
    contrast. The unspecified affix-initial liquid is `L`; surface
    allomorphs are `l` and `r`. -/
inductive LatSeg where
  | a | e | i | o | u   -- vowels
  | l | r               -- liquids (surface)
  | L                   -- /L/, the unspecified affix-initial liquid
  | n | v | s | g | f | p | b   -- consonants from the worked examples
  deriving DecidableEq, Repr

namespace LatSeg

/-- `[+cons]` per @cite{cser-2010}'s feature inventory: every non-vowel
    is consonantal, *except* the orthographic ⟨v⟩, which @cite{belth-2026}
    treats as the glide `[w]` (`[−cons]`). This is the choice that lets
    `pluv-aLis` surface as `[r]` (the tier-preceding consonant of `pluv-`
    is `/l/`, not `/v/`). `L` is `[+cons]` — the underspecified `/L/`
    projects onto the consonant tier even though its `[lat]` value is
    not yet fixed. -/
def IsCons : LatSeg → Prop
  | .a | .e | .i | .o | .u | .v => False
  | _ => True

instance : DecidablePred IsCons := fun seg => by
  cases seg <;> unfold IsCons <;> infer_instance

/-- `[+lat]` per @cite{cser-2010}: only `l` is lateral, and `L` is
    *underspecified* for `[lat]`. Returning `Option Bool` rather than
    `Bool` here avoids the older "junk default" pattern where `L` had
    to fake some concrete value — `none` is the honest answer. -/
def isLat : LatSeg → Option Bool
  | .l => some true
  | .L => none
  | _ => some false

/-- The consonantal tier (Belth's learned tier for Latin, rule 54).
    Every `[+cons]` segment projects. -/
def consTier : Tier LatSeg LatSeg := Tier.byClass IsCons

end LatSeg

-- ============================================================================
-- § 2: The Learned Rule
-- ============================================================================

/-- The rule D2L learns under the `[+cons]` tier (@cite{belth-2026}
    rule 54): `Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`. -/
def latinDissimRule : TierRule LatSeg where
  tier := LatSeg.consTier
  side := .left
  targetIsContext := LatSeg.IsCons
  relation := .disagree
  featureValue := LatSeg.isLat
  default := none

-- ============================================================================
-- § 3: Worked Examples (@cite{belth-2026} §5.3, ex. 5 / 53)
-- ============================================================================

/-- Underlying form of *navalis* 'naval': /nav-aLis/. -/
def navalis_ur : List LatSeg := [.n, .a, .v, .a, .L, .i, .s]

/-- Underlying form of *popularis* 'popular': /popul-aLis/. -/
def popularis_ur : List LatSeg := [.p, .o, .p, .u, .l, .a, .L, .i, .s]

/-- Underlying form of *pluvalis* 'rainy': /pluv-aLis/. With `/v/` off
    the consonant tier (treated as `[w]`, `[−cons]`), the tier-preceding
    consonant in `pluv-a` is `/l/`. -/
def pluvalis_ur : List LatSeg := [.p, .l, .u, .v, .a, .L, .i, .s]

/-- Underlying form of *floralis* 'floral': /flor-aLis/. -/
def floralis_ur : List LatSeg := [.f, .l, .o, .r, .a, .L, .i, .s]

/-- Underlying form of *legalis* 'legal': /leg-aLis/. -/
def legalis_ur : List LatSeg := [.l, .e, .g, .a, .L, .i, .s]

/-- Underlying form of *lunaris* 'lunar': /lun-aLis/. The empirical
    counterexample: surface is `[r]`, but the rule predicts `[l]`
    because the immediately preceding `[+cons]` segment in `/lun-a/` is
    the nasal `/n/` (`[−lat]`), and `Disagree` outputs `[+lat]`. -/
def lunaris_ur : List LatSeg := [.l, .u, .n, .a, .L, .i, .s]

/-- The position of `L` in each underlying form. -/
def navalis_lPos    : Nat := 4
def popularis_lPos  : Nat := 6
def pluvalis_lPos   : Nat := 5
def floralis_lPos   : Nat := 5
def legalis_lPos    : Nat := 4
def lunaris_lPos    : Nat := 4

/-- Surface value predicted by the learned rule: `some true` = surfaces
    as `l`, `some false` = surfaces as `r`, `none` = the rule has no
    opinion. -/
def predicted (ur : List LatSeg) (lPos : Nat) : Option Bool :=
  latinDissimRule.applyAt (ur.take lPos)

-- ============================================================================
-- § 4: Stimulus-Contrast Theorems
-- ============================================================================

/-- *navalis*: `/v/` is `[−cons]` (a glide), so the tier-preceding
    consonant of `/nav-a/` is `/n/` (`[−lat]`). Disagree outputs
    `[+lat]` = `l`. ✓ -/
theorem navalis_predicts_l :
    predicted navalis_ur navalis_lPos = some true := by decide

/-- *popularis*: tier-preceding consonant is `/l/` (`[+lat]`). Disagree
    outputs `[−lat]` = `r`. ✓ -/
theorem popularis_predicts_r :
    predicted popularis_ur popularis_lPos = some false := by decide

/-- *pluvalis*: with `/v/` off the consonant tier, tier-preceding
    consonant of `/pluv-a/` is `/l/` (`[+lat]`). Disagree outputs
    `[−lat]` = `r`. ✓ -/
theorem pluvalis_predicts_r :
    predicted pluvalis_ur pluvalis_lPos = some false := by decide

/-- *floralis*: tier-preceding consonant is `/r/` (`[−lat]`). The
    intervening `/r/` blocks the dissimilation that *popularis*'s
    preceding `/l/` would have triggered — exactly the long-distance
    pattern Belth's tier-projection is designed to capture. ✓ -/
theorem floralis_predicts_l :
    predicted floralis_ur floralis_lPos = some true := by decide

/-- *legalis*: tier-preceding consonant is `/g/` (`[−lat]`). The
    stem-initial `/l/` is hidden from `/L/` by the intervening `/g/`
    on the consonant tier. ✓ -/
theorem legalis_predicts_l :
    predicted legalis_ur legalis_lPos = some true := by decide

/-- *navalis* (l) vs *popularis* (r) is the minimal-pair contrast: both
    have a consonant immediately before the affix on the surface, but
    only `/l/` triggers dissimilation. -/
theorem navalis_popularis_minimal_pair :
    predicted navalis_ur navalis_lPos ≠
    predicted popularis_ur popularis_lPos := by decide

-- ============================================================================
-- § 5: The Empirical Limit — *lunaris*
-- ============================================================================

/-- *lunaris*: the rule predicts `[l]` (the last `[+cons]` segment in
    `/lun-a/` is the nasal `/n/`, which is `[−lat]`, so Disagree
    outputs `[+lat]`). This is the wrong prediction — the surface form
    is `[r]`. @cite{belth-2026} reports this as one of the ~3% of
    errors the Tolerance Principle tolerates; D2L does not refine the
    tier further on this dataset. -/
theorem lunaris_predicts_l_INCORRECT :
    predicted lunaris_ur lunaris_lPos = some true := by decide

-- ============================================================================
-- § 6: Per-Datum Coverage Rollup
-- ============================================================================

/-- Witness pairs `(underlying-form-prefix, expected-surface-lat-value)`
    for each worked example. -/
def latinData : List (List LatSeg × Bool) :=
  [(navalis_ur.take navalis_lPos,     true),    -- *navalis*   — l
   (popularis_ur.take popularis_lPos, false),   -- *popularis* — r
   (pluvalis_ur.take pluvalis_lPos,   false),   -- *pluvalis*  — r
   (floralis_ur.take floralis_lPos,   true),    -- *floralis*  — l
   (legalis_ur.take legalis_lPos,     true),    -- *legalis*   — l
   (lunaris_ur.take lunaris_lPos,     false)]   -- *lunaris*   — r

/-- The learned rule misses exactly one datum out of six (*lunaris*) —
    a 5/6 ≈ 83% match on this minimal corpus, the same single-error
    rate Belth reports at the corpus scale (~3%). -/
theorem latinDissimRule_misses_lunaris :
    (latinData.filter (fun (pre, expected) =>
       !(latinDissimRule.applyAt pre == some expected))).length = 1 := by
  decide

-- ============================================================================
-- § 7: Tolerance Principle Certificate (@cite{yang-2016})
-- ============================================================================

/-! Yang's Tolerance Principle is the productivity gate inside D2L: a
rule with `n` items in scope and `e` exceptions is *tolerated* iff
`e ≤ n / ln n`. For our six worked examples with one exception
(*lunaris*), `1 ≤ 6 / ln 6 ≈ 3.35` — the rule is comfortably under the
threshold, matching @cite{belth-2026}'s 4-of-121 (~3%) result on the
full Perseus corpus. -/

open Theories.Learning.TolerancePrinciple in
/-- The threshold inequality for the six-example demo: 1 exception ≤ 6/ln 6. -/
theorem tolerates_six_one : tolerates 6 1 := by
  unfold tolerates threshold
  push_cast
  have hpos : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hle : Real.log (6 : ℝ) ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  linarith

open Theories.Learning.TolerancePrinciple in
/-- The learned rule passes Yang's Tolerance Principle on the worked
    examples: its exception count (1, *lunaris*) fits under the threshold
    `latinData.length / ln latinData.length`. This is the productivity
    certificate that licenses D2L's convergence to `latinDissimRule`
    rather than memorizing each form. -/
theorem latinDissimRule_tolerated_on_examples :
    tolerates latinData.length
      (latinData.filter (fun (pre, expected) =>
         !(latinDissimRule.applyAt pre == some expected))).length := by
  show tolerates 6 1
  exact tolerates_six_one

-- ============================================================================
-- § 8: Subregular Bridge (@cite{lambert-2022}, @cite{heinz-rawal-tabor-2011})
-- ============================================================================

/-- The consonant tier projection equals the canonical
    `tierProject` from the TSL formalism in `Core/Computability/Subregular/`.
    By construction both reduce to `List.filter` on the `[+cons]` predicate,
    so the autosegmental and language-theoretic tiers coincide. This
    grounds Belth's tier in the TSL_k subregular hierarchy. -/
theorem consTier_apply_eq_tierProject (xs : List LatSeg) :
    LatSeg.consTier.apply xs =
      Core.Computability.Subregular.tierProject LatSeg.IsCons xs :=
  rfl

/-- The TSL_2 grammar witnessing the Latin allomorphy pattern as a
    tier-based subregular language: project to the `[+cons]` tier, then
    forbid adjacent identical symbols. Lambert's @cite{lambert-2022}
    TSL_k schema, instantiated with `IsCons` as the tier predicate and
    the OCP forbidden 2-factor `[some x, some x]`. -/
def latinTSLGrammar : Core.Computability.Subregular.TSLGrammar 2 LatSeg :=
  Phonology.Subregular.TSLGrammar.ocp LatSeg.IsCons

-- ============================================================================
-- § 9: OCP-on-Tier Bridge and OT Tableau (@cite{goldsmith-1976})
-- ============================================================================

/-- Belth's tier-based dissimilation has a natural OCP twin: surface
    forms produced by the rule should not contain adjacent `[+lat]`
    segments on the consonant tier. We expose this connection via
    `Phonology.Constraints.mkOCPOnTier`, which already accepts a generic
    `Core.Tier`. A tier-adjacent pair of identical liquids contributes
    one violation. -/
def latinOCP : Core.Constraint.OT.NamedConstraint (List LatSeg) :=
  Phonology.Constraints.mkOCPOnTier "OCP/[+cons]" LatSeg.consTier id

/-- The OCP constraint is a markedness constraint by construction. -/
theorem latinOCP_is_markedness :
    latinOCP.family = Core.Constraint.OT.ConstraintFamily.markedness :=
  Phonology.Constraints.mkOCPOnTier_is_markedness _ _ _

/-- The OCP-on-tier evaluation of `latinOCP` on a candidate is zero iff
    that candidate is in `latinTSLGrammar.lang`. Specialization of
    `Phonology.Subregular.mkOCPOnTier_zero_iff_in_ocp_lang` to the Latin
    grammar. The two perspectives — markedness constraint with zero
    violations and TSL_2 grammar membership — coincide. -/
theorem latinOCP_zero_iff_in_TSL (c : List LatSeg) :
    latinOCP.eval c = 0 ↔ c ∈ latinTSLGrammar.lang :=
  Phonology.Subregular.mkOCPOnTier_zero_iff_in_ocp_lang
    "OCP/[+cons]" LatSeg.IsCons id c

/-! The OT analysis uses a minimal two-constraint inventory:

  1. `latinOCP` (markedness): no adjacent laterals on the `[+cons]` tier.
  2. `latinStarR` (markedness): the default-`[l]` preference, penalizing
     each surface `[r]`.

  On this inventory, *popularis* and *pluvalis* each force OCP ≫ \*r;
  *navalis*, *floralis*, *legalis* are vacuously satisfied. *lunaris*
  is unrankable — its ERC is contradictory (no W, one L), recapitulating
  the rule's empirical limit. -/

open Core.Constraint.OT

/-- Substitute `val` for every `L` in a candidate string. The two
    surface candidates for an underlying form are `substL .l ur` and
    `substL .r ur`. -/
def substL (val : LatSeg) : List LatSeg → List LatSeg :=
  List.map (fun seg => if seg = LatSeg.L then val else seg)

/-- Markedness constraint penalizing each surface `[r]`: the
    default-`[l]` preference. -/
def latinStarR : NamedConstraint (List LatSeg) :=
  mkMarkGrad "*r" (fun c => (c.filter (· = LatSeg.r)).length)

/-- The Latin ranking implied by allomorphy: OCP/[+cons] dominates \*r. -/
def latinRanking : List (NamedConstraint (List LatSeg)) :=
  [latinOCP, latinStarR]

/-- The two surface candidates for an underlying form. -/
def latCands (ur : List LatSeg) : List (List LatSeg) :=
  [substL .l ur, substL .r ur]

-- ---- TSL_2 membership witnesses (the empirical payoff of the bridge) ------

/-- Membership in `latinTSLGrammar.lang` is decidable: the bridge to the
    integer-valued OCP score (`latinOCP_zero_iff_in_TSL`) transports the
    `Decidable (c.eval = 0)` instance to language membership. -/
instance (c : List LatSeg) : Decidable (c ∈ latinTSLGrammar.lang) :=
  decidable_of_iff _ (latinOCP_zero_iff_in_TSL c)

/-- The empirically expected TSL_2 membership table for the Belth Latin
    inventory: each row pairs a candidate with whether the OCP-on-tier
    grammar should admit it. *pluvalis* and *floralis* are the
    discriminating cases (one candidate excluded for tier-adjacent
    identicals); *navalis* admits both (no adjacency); *lunaris* admits
    both (the OCP-on-tier grammar's empirical limit — the dissimilation
    rule fires even though only one tier-lateral is adjacent). -/
def latinTSLExpected : List (List LatSeg × Bool) :=
  [(substL .r pluvalis_ur, true), (substL .l pluvalis_ur, false),
   (substL .l floralis_ur, true), (substL .r floralis_ur, false),
   (substL .l navalis_ur,  true), (substL .r navalis_ur,  true),
   (substL .l lunaris_ur,  true), (substL .r lunaris_ur,  true)]

/-- The OCP-on-tier TSL_2 grammar agrees with the expected membership table
    on every row of `latinTSLExpected`: the empirical payoff of the
    `latinOCP_zero_iff_in_TSL` bridge in one shot. -/
theorem latinTSL_correct :
    ∀ p ∈ latinTSLExpected, (p.1 ∈ latinTSLGrammar.lang) = p.2 := by decide

/-- *popularis*: OCP fires once on `[p,o,p,u,l,a,l,i,s]` (the tier-adjacent
    `(l, l)`). Only \*r-once on the [r]-candidate — but OCP outranks, so
    [r] wins. -/
theorem popularis_optimal_is_r :
    substL .r popularis_ur ∈
      (mkTableau (latCands popularis_ur) latinRanking).optimal := by decide

theorem popularis_loser_is_l :
    substL .l popularis_ur ∉
      (mkTableau (latCands popularis_ur) latinRanking).optimal := by decide

/-- *pluvalis*: same OCP-ranking-decides pattern as *popularis* (the
    consonant tier of `/pluv-a/` is `[p, l]`, so substituting `L → l`
    creates a tier-adjacent `(l, l)`). -/
theorem pluvalis_optimal_is_r :
    substL .r pluvalis_ur ∈
      (mkTableau (latCands pluvalis_ur) latinRanking).optimal := by decide

/-- *navalis*, *floralis*, *legalis*: the [l]-candidate has OCP=0 (no
    tier-adjacent laterals) and \*r=0; the [r]-candidate has \*r=1.
    \*r breaks the tie in favour of [l]. -/
theorem navalis_optimal_is_l :
    substL .l navalis_ur ∈
      (mkTableau (latCands navalis_ur) latinRanking).optimal := by decide

theorem floralis_optimal_is_l :
    substL .l floralis_ur ∈
      (mkTableau (latCands floralis_ur) latinRanking).optimal := by decide

theorem legalis_optimal_is_l :
    substL .l legalis_ur ∈
      (mkTableau (latCands legalis_ur) latinRanking).optimal := by decide

/-- *lunaris*: the OT analysis selects [l], not the empirical [r] —
    the same error the rule makes (§5). Both candidates have OCP=0
    on the consonant tier (the intervening `/n/` separates the laterals
    in `/lun-a-l-is/` so they are *not* tier-adjacent), so \*r picks the
    [l]-candidate. -/
theorem lunaris_optimal_is_l_INCORRECT :
    substL .l lunaris_ur ∈
      (mkTableau (latCands lunaris_ur) latinRanking).optimal := by decide

-- ---- ERC analysis ----------------------------------------------------------

/-- The ERC induced by *popularis* (winner [r], loser [l]): OCP prefers
    the winner (W on constraint 0); \*r prefers the loser (L on constraint
    1). The full vector is ⟨W, L⟩ = `simpleERC 0 1`. -/
def popularisERC : ERC 2 :=
  tableauERC (mkTableau (latCands popularis_ur) latinRanking)
    (substL .r popularis_ur) (substL .l popularis_ur)

/-- The ERC induced by *pluvalis*: same shape as popularis. -/
def pluvalisERC : ERC 2 :=
  tableauERC (mkTableau (latCands pluvalis_ur) latinRanking)
    (substL .r pluvalis_ur) (substL .l pluvalis_ur)

/-- The ERC induced by *navalis* (winner [l], loser [r]): OCP indifferent,
    \*r prefers the winner. ⟨e, W⟩ — trivial (no L). -/
def navalisERC : ERC 2 :=
  tableauERC (mkTableau (latCands navalis_ur) latinRanking)
    (substL .l navalis_ur) (substL .r navalis_ur)

/-- The ERC induced by *floralis*. -/
def floralisERC : ERC 2 :=
  tableauERC (mkTableau (latCands floralis_ur) latinRanking)
    (substL .l floralis_ur) (substL .r floralis_ur)

/-- The ERC induced by *legalis*. -/
def legalisERC : ERC 2 :=
  tableauERC (mkTableau (latCands legalis_ur) latinRanking)
    (substL .l legalis_ur) (substL .r legalis_ur)

/-- The ERC induced by *lunaris* (taking the empirical [r] as the winner):
    OCP indifferent (no laterals are tier-adjacent on either candidate),
    \*r prefers the loser [l]. ⟨e, L⟩ — **contradictory** (no W, one L).
    No ranking on the inventory ⟨OCP, \*r⟩ can satisfy this; the OT
    formulation thus reproduces exactly the rule's empirical limit. -/
def lunarisERC : ERC 2 :=
  tableauERC (mkTableau (latCands lunaris_ur) latinRanking)
    (substL .r lunaris_ur) (substL .l lunaris_ur)

theorem popularisERC_is_simple :
    popularisERC = simpleERC (n := 2) 0 1 := by decide

theorem pluvalisERC_is_simple :
    pluvalisERC = simpleERC (n := 2) 0 1 := by decide

theorem navalisERC_isTrivial : navalisERC.isTrivial := by decide
theorem floralisERC_isTrivial : floralisERC.isTrivial := by decide
theorem legalisERC_isTrivial : legalisERC.isTrivial := by decide

theorem lunarisERC_isContradictory : lunarisERC.isContradictory := by decide

/-- The five non-lunaris contrasts form a **consistent** ERC set: the
    identity ranking (OCP at position 0, \*r at position 1) satisfies
    every word's ranking requirements. Two informative ERCs (popularis,
    pluvalis) both reduce to `simpleERC 0 1`; the other three are
    trivial. -/
theorem latinERCSet_consistent_without_lunaris :
    ERCSet.consistent
      [popularisERC, pluvalisERC, navalisERC, floralisERC, legalisERC] :=
  ⟨Ranking.id 2, by decide⟩

/-- Bridge to the dominance characterisation: under any ranking
    satisfying the empirical ERC set (sans lunaris), OCP dominates \*r. -/
theorem latin_OCP_dominates_starR (r : Ranking 2)
    (hr : ERCSet.satisfiedBy r
      [popularisERC, pluvalisERC, navalisERC, floralisERC, legalisERC]) :
    dominates r 0 1 := by
  have hpop : popularisERC.satisfiedBy r :=
    hr popularisERC (List.mem_cons.mpr (Or.inl rfl))
  have : (simpleERC (n := 2) 0 1).satisfiedBy r := by
    rw [← popularisERC_is_simple]; exact hpop
  exact (simpleERC_satisfiedBy_iff (by decide) r).mp this

-- ============================================================================
-- § 10: D2L's Other Learned Rules (documentation only)
-- ============================================================================

/- ### Turkish (@cite{belth-2026} §5.1)

D2L converges to two rules on Turkish CHILDES + MorphoChallenge data:

- (a) `Agree([?back], {back, round}) / [−cons] __ ∘ proj(·, [−cons])`
  — vowel harmony: an unspecified vowel takes its `[back]` value (and
  `[round]` value, if also unspecified) from the immediately
  tier-preceding vowel on the vocalic tier.
- (b) `Agree([?voice], {voice}) / [*] __`
  — voicing assimilation: the projection component is the *trivial*
  identity tier (every segment projects). This is the strict-locality
  case captured generically by
  `Phonology.Alternation.TierRule.id_tier_left_is_strict_local`.

D2L's reported test accuracy on the two corpora exceeds 0.98, beating
@cite{hayes-wilson-2008} generative phonotactic learners and LSTM
baselines (Belth Table 5).

### Finnish (@cite{belth-2026} §5.2)

- (a) `Agree([?back], {back}) / [−cons] __ ∘ proj(·, [−cons] ∖ {i, e})`
  — backness harmony skipping the neutral vowels `{i, e}`. D2L learns
  that the neutral vowels must be deleted from the tier, matching the
  descriptive analysis in @cite{ringen-heinamaki-1999}.
- (b) `Elsewhere [−back]` — the default-value rule for stems containing
  only neutral vowels. In our schema, this corresponds to
  `default := some false` on the corresponding `TierRule`.

These rules instantiate the same `TierRule` schema used above for
Latin, with two extensions deferred:

  1. *Multi-feature dependencies* — Turkish back/round harmony agrees
     on the *combined* `[back, round]` feature set, requiring a
     generalisation of `featureValue : α → Option Bool` to `α → List
     (Option Bool)` plus a parasitic condition (round only spreads if
     back agrees).
  2. *Default values* — already supported by the `default` field on
     `TierRule`; only the multi-feature wrinkle blocks a full Finnish
     formalization here.

Both extensions are admittable on demand. The Latin case above
suffices to demonstrate the schema, the empirical-limit pattern
(*lunaris*), the Tolerance Principle bridge, and the OCP-tier OT bridge.
-/

end Phenomena.PhonologicalAlternation.Studies.Belth2026
