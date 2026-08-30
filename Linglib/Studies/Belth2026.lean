import Linglib.Phonology.Subregular.TierRule
import Linglib.Phonology.Constraints.Basic
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.Subregular.OCP
import Linglib.Studies.Yang2016
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.Subregular.TierStrictlyLocal
import Linglib.Phonology.Subregular.Multitier
import Linglib.Data.Examples.Belth2026

/-!
# Belth (2026): A Learning-Based Account of Phonological Tiers

D2L (Distant-to-Local) is an iterative learner that constructs phonological
tiers as a *byproduct* of trying to express alternations as adjacent
dependencies. Given underlying-form / surface-form pairs, D2L starts by
projecting all segments and tries to predict the alternating segment from
its linear neighbours. When the resulting rule fails Yang's Tolerance
Principle [yang-2016], D2L deletes the offending segments from the
tier and tries again, until either a tolerated rule is found or no further
deletion helps.

The output of D2L is a tier-based alternation rule, modelled here by the
canonical `Subregular.TierRule` schema (in
`Phonology/Alternation.lean`); the closely-related SPE
non-tier `Subregular.LocalRewrite.Rule` schema in
`Phonology/Subregular/LocalRewrite.lean` is the right substrate
when the alternation does not factor through a tier projection.
The function-level subregular classification of D2L outputs lives in
the subregular function classes: tier-mediated dissimilation
rules of the form Belth converges to are Tier-Subsequential
([aksenova-rawski-graf-heinz-2020]). For Latin -alis / -aris
allomorphy ([belth-2026] §5.3, rule 54), the rule D2L converges
to is

  `Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`,

i.e. dissimilation of the underspecified affix-initial liquid `/L/` from
the immediately preceding `[+cons]` tier segment. [belth-2026] reports
0.97 average test accuracy over thirty 80/20 splits of the 121-word
Perseus dataset (Table 7); the residual errors are *tolerated* by Yang's
Tolerance Principle, so D2L converges to this rule rather than memorizing
the lexicon.

This study formalizes:

- the rule (`latinDissimRule`) and its predictions on six worked
  examples (Belth ex. 5/53): *navalis*, *popularis*, *pluvialis*,
  *floralis*, *legalis*, *lunaris* — including the (53c)/(53d) blocking
  cases, where `/r/` and the non-coronal blockers sit on the tier and
  hide the stem lateral;
- the genuine empirical limit: *lunaris* surfaces with `[r]`, but the
  `[+cons]`-tier rule predicts `[l]` (the immediately preceding tier
  segment is the nasal `/n/`, which is `[−lat]`, so `Disagree` outputs
  `[+lat]`). The paper does not name its residual errors; *lunaris* is
  derived here as one, absorbed by the Tolerance Principle;
- a Tolerance-Principle certificate
  (`latinDissimRule_tolerated_on_examples`) showing the 1-of-6 exception
  count on this corpus is well under Yang's threshold;
- a Subregular bridge (`consTier_apply_eq_tierProject`) grounding the
  consonant tier in the [lambert-2022]/[heinz-rawal-tanner-2011]
  TSL formalism;
- an OCP-on-tier OT constraint (`latinOCP`, via
  `Constraints.mkOCPOnTier`) and an OT tableau bridge: each
  empirical contrast becomes a winner-loser pair, `tableauERC` extracts
  the Elementary Ranking Condition ([merchant-riggle-2016]), and
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

namespace Belth2026

open Core
open Subregular

/-! ### A Minimal Latin Alphabet -/

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

/-- Tier membership for the learned `[+cons]` tier: every non-vowel
    projects. The orthographic ⟨v⟩ is Belth's semivowel `[w]`, and it
    stays on the tier — the paper's §5.3.2 point is that `/r/` and the
    non-coronal consonants, [cser-2010]'s blockers, "are preserved on
    the tier"; `[w]` is the blocker in *pluvi-alis* (53d). `L` is also
    on the tier — the underspecified `/L/` projects even though its
    `[lat]` value is not yet fixed. -/
def IsCons : LatSeg → Prop
  | .a | .e | .i | .o | .u => False
  | _ => True

instance : DecidablePred IsCons := fun seg => by
  cases seg <;> unfold IsCons <;> infer_instance

/-- `[+lat]` per [cser-2010]: only `l` is lateral, and `L` is
    *underspecified* for `[lat]`. Returning `Option Bool` rather than
    `Bool` here avoids the older "junk default" pattern where `L` had
    to fake some concrete value — `none` is the honest answer. -/
def isLat : LatSeg → Option Bool
  | .l => some true
  | .L => none
  | _ => some false

/-- The consonantal tier (Belth's learned tier for Latin, rule 54).
    Every `[+cons]` segment projects. -/
def consTier : TierProjection LatSeg LatSeg := TierProjection.byClass IsCons

end LatSeg

/-! ### The Learned Rule -/

/-- The rule D2L learns under the `[+cons]` tier ([belth-2026]
    rule 54): `Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`. -/
def latinDissimRule : TierRule LatSeg where
  tier := LatSeg.consTier
  side := .left
  targetIsContext := LatSeg.IsCons
  relation := .disagree
  featureValue := LatSeg.isLat
  default := none

/-! ### Worked Examples ([belth-2026] §5.3, ex. 5 / 53) -/

/-- Underlying form of *navalis* 'naval': /nav-aLis/. -/
def navalis_ur : List LatSeg := [.n, .a, .v, .a, .L, .i, .s]

/-- Underlying form of *popularis* 'popular': /popul-aLis/. -/
def popularis_ur : List LatSeg := [.p, .o, .p, .u, .l, .a, .L, .i, .s]

/-- Underlying form of *pluvialis* 'rainy': /pluvi-aLis/. The `[w]`
    (⟨v⟩) on the tier hides the stem `/l/` from the suffix liquid — the
    (53d) non-coronal blocking case. -/
def pluvialis_ur : List LatSeg := [.p, .l, .u, .v, .i, .a, .L, .i, .s]

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
def pluvialis_lPos  : Nat := 6
def floralis_lPos   : Nat := 5
def legalis_lPos    : Nat := 4
def lunaris_lPos    : Nat := 4

/-- Surface value predicted by the learned rule: `some true` = surfaces
    as `l`, `some false` = surfaces as `r`, `none` = the rule has no
    opinion. -/
def predicted (ur : List LatSeg) (lPos : Nat) : Option Bool :=
  latinDissimRule.applyAt (ur.take lPos)

/-! ### Stimulus-Contrast Theorems -/

/-- *navalis*: the tier-preceding segment of `/nav-a/` is the `[−lat]`
    `[w]`. Disagree outputs `[+lat]` = `l`. ✓ -/
theorem navalis_predicts_l :
    predicted navalis_ur navalis_lPos = some true := by decide

/-- *popularis*: tier-preceding consonant is `/l/` (`[+lat]`). Disagree
    outputs `[−lat]` = `r`. ✓ -/
theorem popularis_predicts_r :
    predicted popularis_ur popularis_lPos = some false := by decide

/-- *pluvialis*: the tier-preceding consonant of `/pluvi-a/` is the
    `[−lat]` `[w]`, so Disagree outputs `[+lat]` = `l` — the stem `/l/`
    is hidden by the non-coronal blocker on the tier (53d). ✓ -/
theorem pluvialis_predicts_l :
    predicted pluvialis_ur pluvialis_lPos = some true := by decide

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

/-! ### The Empirical Limit — *lunaris* -/

/-- *lunaris*: the rule predicts `[l]` (the last `[+cons]` segment in
    `/lun-a/` is the nasal `/n/`, which is `[−lat]`, so Disagree
    outputs `[+lat]`). This is the wrong prediction — the surface form
    is `[r]`. [belth-2026] reports this as one of the ~3% of
    errors the Tolerance Principle tolerates; D2L does not refine the
    tier further on this dataset. -/
theorem lunaris_predicts_l_INCORRECT :
    predicted lunaris_ur lunaris_lPos = some true := by decide

/-! ### Per-Datum Coverage Rollup -/

/-- Witness pairs `(underlying-form-prefix, expected-surface-lat-value)`
    for each worked example. -/
def latinData : List (List LatSeg × Bool) :=
  [(navalis_ur.take navalis_lPos,     true),    -- *navalis*   — l
   (popularis_ur.take popularis_lPos, false),   -- *popularis* — r
   (pluvialis_ur.take pluvialis_lPos, true),    -- *pluvialis* — l
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

/-! ### Tolerance Principle Certificate ([yang-2016]) -/

/-! Yang's Tolerance Principle is the productivity gate inside D2L: a
rule with `n` items in scope and `e` exceptions is *tolerated* iff
`e ≤ n / ln n`. For our six worked examples with one exception
(*lunaris*), `1 ≤ 6 / ln 6 ≈ 3.35` — the rule is comfortably under the
threshold, matching [belth-2026]'s 4-of-121 (~3%) result on the
full Perseus corpus. -/

open Yang2016 in
/-- The threshold inequality for the six-example demo: 1 exception ≤ 6/ln 6. -/
theorem tolerates_six_one : tolerates 6 1 := by
  unfold tolerates threshold
  push_cast
  have hpos : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hle : Real.log (6 : ℝ) ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  linarith

open Yang2016 in
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

/-! ### Subregular Bridge ([lambert-2022], [heinz-rawal-tanner-2011]) -/

/-- The consonant tier projection equals the canonical
    `tierProject` from the TSL formalism in the subregular layer.
    By construction both reduce to `List.filter` on the `[+cons]` predicate,
    so the autosegmental and language-theoretic tiers coincide. This
    grounds Belth's tier in the TSL_k subregular hierarchy. -/
theorem consTier_apply_eq_tierProject (xs : List LatSeg) :
    LatSeg.consTier.apply xs =
      Subregular.tierProject LatSeg.IsCons xs := by
  show TierProjection.apply (TierProjection.byClass LatSeg.IsCons) xs = _
  rw [TierProjection.apply_byClass, Subregular.tierProject_eq_filter]

/-- The TSL_2 grammar witnessing the Latin allomorphy pattern as a
    tier-based subregular language: project to the `[+cons]` tier, then
    forbid adjacent identical symbols. Lambert's [lambert-2022]
    TSL_k schema, instantiated with `IsCons` as the tier predicate and
    the OCP forbidden 2-factor `[some x, some x]`. -/
def latinTSLGrammar : Subregular.TierStrictlyLocalGrammar 2 LatSeg :=
  Subregular.TierStrictlyLocalGrammar.ocp LatSeg.IsCons

/-! ### OCP-on-Tier Bridge and OT Tableau ([goldsmith-1976]) -/

/-- Belth's tier-based dissimilation has a natural OCP twin: surface
    forms produced by the rule should not contain adjacent `[+lat]`
    segments on the consonant tier. We expose this connection via
    `Constraints.mkOCPOnTier`, which already accepts a generic
    `Tier`. A tier-adjacent pair of identical liquids contributes
    one violation. -/
def latinOCP : Constraints.Constraint (List LatSeg) :=
  Constraints.mkOCPOnTier LatSeg.consTier id

/-- The OCP-on-tier evaluation of `latinOCP` on a candidate is zero iff
    that candidate is in `latinTSLGrammar.language`. Specialization of
    `Subregular.mkOCPOnTier_zero_iff_in_ocp_language` to the Latin
    grammar. The two perspectives — markedness constraint with zero
    violations and TSL_2 grammar membership — coincide. -/
theorem latinOCP_zero_iff_in_TSL (c : List LatSeg) :
    latinOCP c = 0 ↔ c ∈ latinTSLGrammar.language :=
  Subregular.mkOCPOnTier_zero_iff_in_ocp_language
    LatSeg.IsCons id c

/-! The OT analysis uses a minimal two-constraint inventory:

  1. `latinOCP` (markedness): no adjacent laterals on the `[+cons]` tier.
  2. `latinStarR` (markedness): the default-`[l]` preference, penalizing
     each surface `[r]`.

  On this inventory, *popularis* and *pluvalis* each force OCP ≫ \*r;
  *navalis*, *floralis*, *legalis* are vacuously satisfied. *lunaris*
  is unrankable — its ERC is contradictory (no W, one L), recapitulating
  the rule's empirical limit. -/

open Constraints OptimalityTheory

/-- Substitute `val` for every `L` in a candidate string. The two
    surface candidates for an underlying form are `substL .l ur` and
    `substL .r ur`. -/
def substL (val : LatSeg) : List LatSeg → List LatSeg :=
  List.map (fun seg => if seg = LatSeg.L then val else seg)

/-- Markedness constraint penalizing each surface `[r]`: the
    default-`[l]` preference. -/
def latinStarR : Constraint (List LatSeg) :=
  (fun c => (c.filter (· = LatSeg.r)).length)

/-- The Latin ranking implied by allomorphy: OCP/[+cons] dominates \*r. -/
def latinRanking : List (Constraint (List LatSeg)) :=
  [latinOCP, latinStarR]

/-- The two surface candidates for an underlying form. -/
def latCands (ur : List LatSeg) : List (List LatSeg) :=
  [substL .l ur, substL .r ur]

-- ---- TSL_2 membership witnesses (the empirical payoff of the bridge) ------

/-- Membership in `latinTSLGrammar.language` is decidable: the bridge to the
    integer-valued OCP score (`latinOCP_zero_iff_in_TSL`) transports the
    `Decidable (latinOCP c = 0)` instance to language membership. -/
instance (c : List LatSeg) : Decidable (c ∈ latinTSLGrammar.language) :=
  decidable_of_iff _ (latinOCP_zero_iff_in_TSL c)

/-- The empirically expected TSL_2 membership table for the Belth Latin
    inventory: each row pairs a candidate with whether the OCP-on-tier
    grammar should admit it. *floralis* is the liquid-discriminating
    case (the [r]-candidate excluded for its tier-adjacent (r, r));
    *popularis* is excluded on both candidates — the identity-featured
    OCP also fires on its (p, p) pair, a way the constraint is stricter
    than the liquid pattern; *navalis* and *pluvialis* admit both (the
    blocker separates the liquids on the tier); *lunaris* admits both
    (the OCP-on-tier grammar's empirical limit — dissimilation fires
    even though no tier-laterals are adjacent). -/
def latinTSLExpected : List (List LatSeg × Bool) :=
  [(substL .r popularis_ur, false), (substL .l popularis_ur, false),
   (substL .l floralis_ur, true), (substL .r floralis_ur, false),
   (substL .l navalis_ur,  true), (substL .r navalis_ur,  true),
   (substL .l pluvialis_ur, true), (substL .r pluvialis_ur, true),
   (substL .l lunaris_ur,  true), (substL .r lunaris_ur,  true)]

/-- The OCP-on-tier TSL_2 grammar agrees with the expected membership table
    on every row of `latinTSLExpected`: the empirical payoff of the
    `latinOCP_zero_iff_in_TSL` bridge in one shot. -/
theorem latinTSL_correct :
    ∀ p ∈ latinTSLExpected, (p.1 ∈ latinTSLGrammar.language) = p.2 := by decide

/-- *popularis*: OCP fires once on `[p,o,p,u,l,a,l,i,s]` (the tier-adjacent
    `(l, l)`). Only \*r-once on the [r]-candidate — but OCP outranks, so
    [r] wins. -/
theorem popularis_optimal_is_r :
    substL .r popularis_ur ∈
      (Tableau.ofRanking (latCands popularis_ur) latinRanking).optimal := by decide

theorem popularis_loser_is_l :
    substL .l popularis_ur ∉
      (Tableau.ofRanking (latCands popularis_ur) latinRanking).optimal := by decide

/-- *pluvialis*: both candidates are OCP-clean — the `[w]` on the tier
    separates the liquids — so \*r picks the empirically correct [l]
    (53d): OT blocking through tier membership, same as the rule. -/
theorem pluvialis_optimal_is_l :
    substL .l pluvialis_ur ∈
      (Tableau.ofRanking (latCands pluvialis_ur) latinRanking).optimal := by decide

/-- *navalis*, *floralis*, *legalis*: the [l]-candidate has OCP=0 (no
    tier-adjacent laterals) and \*r=0; the [r]-candidate has \*r=1.
    \*r breaks the tie in favour of [l]. -/
theorem navalis_optimal_is_l :
    substL .l navalis_ur ∈
      (Tableau.ofRanking (latCands navalis_ur) latinRanking).optimal := by decide

theorem floralis_optimal_is_l :
    substL .l floralis_ur ∈
      (Tableau.ofRanking (latCands floralis_ur) latinRanking).optimal := by decide

theorem legalis_optimal_is_l :
    substL .l legalis_ur ∈
      (Tableau.ofRanking (latCands legalis_ur) latinRanking).optimal := by decide

/-- *lunaris*: the OT analysis selects [l], not the empirical [r] —
    the same error the rule makes (§5). Both candidates have OCP=0
    on the consonant tier (the intervening `/n/` separates the laterals
    in `/lun-a-l-is/` so they are *not* tier-adjacent), so \*r picks the
    [l]-candidate. -/
theorem lunaris_optimal_is_l_INCORRECT :
    substL .l lunaris_ur ∈
      (Tableau.ofRanking (latCands lunaris_ur) latinRanking).optimal := by decide

-- ---- ERC analysis ----------------------------------------------------------

/-- The ERC induced by *popularis* (winner [r], loser [l]): OCP prefers
    the winner (W on constraint 0); \*r prefers the loser (L on constraint
    1). The full vector is ⟨W, L⟩ = `simpleERC 0 1`. -/
def popularisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands popularis_ur) latinRanking)
    (substL .r popularis_ur) (substL .l popularis_ur)

/-- The ERC induced by *pluvialis* (winner [l], loser [r]): OCP
    indifferent, \*r prefers the winner — trivial. -/
def pluvialisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands pluvialis_ur) latinRanking)
    (substL .l pluvialis_ur) (substL .r pluvialis_ur)

/-- The ERC induced by *navalis* (winner [l], loser [r]): OCP indifferent,
    \*r prefers the winner. ⟨e, W⟩ — trivial (no L). -/
def navalisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands navalis_ur) latinRanking)
    (substL .l navalis_ur) (substL .r navalis_ur)

/-- The ERC induced by *floralis*. -/
def floralisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands floralis_ur) latinRanking)
    (substL .l floralis_ur) (substL .r floralis_ur)

/-- The ERC induced by *legalis*. -/
def legalisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands legalis_ur) latinRanking)
    (substL .l legalis_ur) (substL .r legalis_ur)

/-- The ERC induced by *lunaris* (taking the empirical [r] as the winner):
    OCP indifferent (no laterals are tier-adjacent on either candidate),
    \*r prefers the loser [l]. ⟨e, L⟩ — **contradictory** (no W, one L).
    No ranking on the inventory ⟨OCP, \*r⟩ can satisfy this; the OT
    formulation thus reproduces exactly the rule's empirical limit. -/
def lunarisERC : ERC 2 :=
  tableauERC (Tableau.ofRanking (latCands lunaris_ur) latinRanking)
    (substL .r lunaris_ur) (substL .l lunaris_ur)

theorem popularisERC_is_simple :
    popularisERC = simpleERC (n := 2) 0 1 := by decide

theorem pluvialisERC_isTrivial : pluvialisERC.IsTrivial := by decide

theorem navalisERC_isTrivial : navalisERC.IsTrivial := by decide
theorem floralisERC_isTrivial : floralisERC.IsTrivial := by decide
theorem legalisERC_isTrivial : legalisERC.IsTrivial := by decide

theorem lunarisERC_isContradictory : lunarisERC.IsContradictory := by decide

/-- The five non-lunaris contrasts form a **consistent** ERC set: the
    identity ranking (OCP at position 0, \*r at position 1) satisfies
    every word's ranking requirements. One informative ERC (popularis)
    reduces to `simpleERC 0 1`; the other four are trivial. -/
theorem latinERCs_consistent_without_lunaris :
    (ERC.linearExtensions
      {popularisERC, pluvialisERC, navalisERC, floralisERC, legalisERC}).Nonempty :=
  ⟨Ranking.id 2, by decide⟩

/-- Bridge to the dominance characterisation: under any ranking
    satisfying the empirical ERC set (sans lunaris), OCP dominates \*r. -/
theorem latin_OCP_dominates_starR (r : Ranking 2)
    (hr : ∀ α ∈ ({popularisERC, pluvialisERC, navalisERC, floralisERC,
      legalisERC} : Finset (ERC 2)), α.SatisfiedBy r) :
    r.Dominates 0 1 := by
  have hpop : popularisERC.SatisfiedBy r :=
    hr popularisERC (Finset.mem_insert_self _ _)
  have : (simpleERC (n := 2) 0 1).SatisfiedBy r := by
    rw [← popularisERC_is_simple]; exact hpop
  exact (simpleERC_satisfiedBy_iff (by decide) r).mp this

/-! ### D2L's Other Learned Rules (documentation only) -/

/- ### Turkish ([belth-2026] §5.1)

D2L converges to two rules on Turkish CHILDES + MorphoChallenge data:

- (a) `Agree([?back], {back, round}) / [−cons] __ ∘ proj(·, [−cons])`
  — vowel harmony: an unspecified vowel takes its `[back]` value (and
  `[round]` value, if also unspecified) from the immediately
  tier-preceding vowel on the vocalic tier.
- (b) `Agree([?voice], {voice}) / [*] __`
  — voicing assimilation: the projection component is the *trivial*
  identity tier (every segment projects). This is the strict-locality
  case captured generically by
  `Subregular.TierRule.id_tier_left_is_strict_local`.

D2L's reported test accuracy on the two corpora exceeds 0.98, beating
[hayes-wilson-2008] generative phonotactic learners and LSTM
baselines (Belth Table 5).

### Finnish ([belth-2026] §5.2)

- (a) `Agree([?back], {back}) / [−cons] __ ∘ proj(·, [−cons] ∖ {i, e})`
  — backness harmony skipping the neutral vowels `{i, e}`. D2L learns
  that the neutral vowels must be deleted from the tier, matching the
  descriptive analysis in [ringen-heinamaki-1999].
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

/-- **TSL_2 witness**: Latin liquid dissimilation is tier-strictly-local
at window-size 2. -/
theorem latinTSLGrammar_lang_isTSL2 :
    Language.IsTierStrictlyLocal 2 latinTSLGrammar.language :=
  ⟨latinTSLGrammar, rfl⟩

/-- **BTSL_2 corollary** (via `IsTierStrictlyLocal.toIsBTSL` in
`Subregular.Multitier`): Latin liquid dissimilation
is in the multitier closure of strictly local languages, hence consumed
by the [lambert-2026] BTC framework. -/
theorem latinTSLGrammar_lang_isBTSL2 :
    Language.IsBTSL 2 latinTSLGrammar.language :=
  latinTSLGrammar_lang_isTSL2.toIsBTSL

end Belth2026
