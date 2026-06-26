import Linglib.Features.WordOrder
import Linglib.Typology.Coordination
import Linglib.Syntax.Tree.Cat
import Linglib.Fragments.English.WordOrder
import Mathlib.Data.Finset.Basic

/-!
# Category mismatches in coordination [bruening-alkhalaf-2020]

Bruening, Benjamin & Eman Al Khalaf. 2020. Category mismatches in coordination
revisited. *Linguistic Inquiry* 51(1). 1–36.

In selection-violating coordination the *linearly closest* conjunct to the
selecting head must satisfy c-selection (§3.1): the first conjunct in VO
complement position, the last conjunct when the coordination precedes its
selector (subject position, OV complements, postpositions). The two rival
percolation mechanisms — linear closeness (B&AK) and structural prominence (the
bottom-up accounts of [munn-1993], [zhang-2010]) — are the two modes of a single
`predictOrder`; they agree postverbally but diverge preverbally, the
configuration that empirically distinguishes them.

Only two genuine category mismatches survive in selection-violating coordination
(§3.2): CP↔NP and non-*ly* Adverb↔Adjective, both mirroring displacement and
ellipsis. We derive this enumeration structurally from a distributional map
rather than stipulating it. Apparent mismatches in predication and modification
(§2) are not violations but supercategory selection (`Pred`, `Mod`).

## Main definitions

* `FeaturePercolation` — which conjunct's features reach the selecting head:
  `linear` (B&AK) vs `structural` (bottom-up).
* `predictOrder` — conjunct-order prediction from percolation mode and verb
  position; `linearClosenessPrediction` / `bottomUpPrediction` are its partial
  applications.
* `coordExtension` — extended distributional compatibility per `Cat`.
* `Supercategory` — the `Pred` / `Mod` supercategory features over `Cat`.

## Main results

* `percolation_diverges_preverbal` — the two accounts disagree preverbally.
* `subject_position_distinguishes`, `ov_predictions_diverge` — the
  English-subject and OV configurations that adjudicate them.
* `coordExtension_exhaustive` — only CP and AdvP extend, deriving the two
  permitted violations rather than stipulating them.

## References

[bruening-alkhalaf-2020]; the cross-linguistic OV test is [schwarzer-2026].
-/

namespace BrueningAlKhalaf2020

open Typology.Coordination (CoordSymmetry)
open Syntax (Cat)
open Syntax.Cat (NP VP AdjP AdvP PP)
open WordOrder

/-! ### Shared types for selection-violating coordination -/

/-- Preferred order of conjuncts in DP-CP selection-violating coordination. -/
inductive ConjunctOrder where
  /-- DP conjunct precedes CP conjunct. -/
  | dpFirst
  /-- CP conjunct precedes DP conjunct. -/
  | cpFirst
  deriving DecidableEq, Repr

-- `VerbPosition` and the `OVOrder → Option VerbPosition` projection
-- live in `WordOrder` substrate; consumed via `open` above.

/-! ### Feature percolation and the directionality principle -/

/-- How selectional features percolate through &P to the selecting head.

    The competing analyses of selection-violating coordination disagree on a
    single parameter: which conjunct's categorial features are visible to the
    selecting head. This parameter determines conjunct-order preferences as a
    function of surface position. -/
inductive FeaturePercolation where
  /-- Features percolate from the structurally prominent (spec) position.
      The first conjunct always determines &P's categorial features, regardless
      of surface position relative to the verb.
      Analyses: [munn-1993], [zhang-2010]. -/
  | structural
  /-- Features percolate from the linearly closest conjunct to the selecting
      head. Which conjunct is closest depends on surface position relative to
      the verb. Analysis: [bruening-alkhalaf-2020]. -/
  | linear
  deriving DecidableEq, Repr

/-- Derive conjunct order preference from feature percolation mechanism.

    The core principle: the conjunct whose features percolate to &P must satisfy
    c-selection (= must be the DP). The percolation mechanism determines *which*
    conjunct that is:

    - **Structural**: spec (= first conjunct) → always DP-first
    - **Linear**: closest to V → DP-first postverbally, CP-first preverbally -/
def predictOrder (fp : FeaturePercolation) (pos : VerbPosition) : ConjunctOrder :=
  match fp with
  | .structural => .dpFirst
  | .linear => match pos with
    | .postverbal => .dpFirst
    | .preverbal  => .cpFirst

/-- Structural percolation is position-invariant: the structurally prominent
    conjunct is always first, regardless of surface order. -/
theorem structural_position_invariant (pos₁ pos₂ : VerbPosition) :
    predictOrder .structural pos₁ = predictOrder .structural pos₂ := rfl

/-- Linear percolation is position-dependent: preverbal and postverbal yield
    different predictions. -/
theorem linear_position_dependent :
    predictOrder .linear .preverbal ≠ predictOrder .linear .postverbal := by decide

/-- The two percolation mechanisms agree in postverbal position: both predict
    DP-first when V precedes the coordination. -/
theorem percolation_agrees_postverbal :
    predictOrder .structural .postverbal = predictOrder .linear .postverbal := rfl

/-- The two percolation mechanisms diverge in preverbal position: structural
    predicts DP-first, linear predicts CP-first. This is the configuration that
    empirically distinguishes the accounts. -/
theorem percolation_diverges_preverbal :
    predictOrder .structural .preverbal ≠ predictOrder .linear .preverbal := by decide

/-- **Linear closeness prediction** (B&AK's core claim, §3.1): the linearly
    closest conjunct to the selecting head must satisfy c-selection.

    In VO complement position: V [&P X and Y] → X is closest → DP-first.
    In OV complement position: [&P X and Y] V → Y is closest → CP-first
    (so DP is last, verb-adjacent).

    This also applies to English subject position (preverbal even in VO) and
    postpositions (selecting head follows coordination).

    Derived from `predictOrder` with linear percolation. -/
def linearClosenessPrediction : VerbPosition → ConjunctOrder :=
  predictOrder .linear

/-- **Bottom-up prediction** (competitor account, §3.1): asymmetric &P structure
    makes the first conjunct structurally more prominent. The selected DP must
    be first, regardless of surface position relative to the verb.

    Analyses: [munn-1993], [zhang-2010].

    Derived from `predictOrder` with structural percolation. -/
def bottomUpPrediction : VerbPosition → ConjunctOrder :=
  predictOrder .structural

/-! ### Permitted selection violations -/

/-- B&AK identify exactly two category mismatches that are permitted in
    selection-violating coordination (§3.2).

    These parallel the categories that allow displacement and ellipsis:
    1. CP↔NP: CPs can appear in NP positions (also seen in topicalization,
       pseudoclefts, "do so" replacement)
    2. Non-*ly* Adv↔Adj: manner adverbs without *-ly* can appear in adjective
       positions (also seen in prenominal modification) -/
inductive SelectionViolationType where
  /-- CP appearing in an NP-selecting position. -/
  | cpAsNp
  /-- Non-*ly* adverb appearing in an adjective position. -/
  | advAsAdj
  deriving DecidableEq, Repr

/-- The exhaustive list of permitted violations, justified structurally by
    `coordExtension_exhaustive`: only CP and AdvP have non-empty extensions.
    See `violation_from_extension` and `extension_to_violation` for the
    bidirectional correspondence. -/
def permittedViolations : List SelectionViolationType :=
  [.cpAsNp, .advAsAdj]

theorem exactly_two_violations : permittedViolations.length = 2 := rfl

/-! ### English VO complement position -/

/-- English is VO: complements follow the selecting verb. -/
theorem english_is_vo : English.wordOrder.ovOrder = .vo := rfl

/-- English complement position maps to postverbal. -/
theorem english_complement_postverbal :
    OVOrder.verbPosition English.wordOrder.ovOrder = some .postverbal := rfl

/-- B&AK predict DP-first in English complement position: the first conjunct is
    closest to V.

      You can depend on [NP my assistant] and [CP that he will
      be on time]. ✓

    [bruening-alkhalaf-2020]'s (3a), from [sag-etal-1985] (1985:165). -/
theorem bak_english_complement :
    linearClosenessPrediction .postverbal = .dpFirst := rfl

/-- Bottom-up also predicts DP-first for English VO complements. Both accounts
    agree for this configuration. -/
theorem accounts_agree_complement :
    linearClosenessPrediction .postverbal = bottomUpPrediction .postverbal := rfl

/-! ### English subject position: the distinguishing case

B&AK's strongest within-English evidence for closeness over first-conjunct
prominence (§3.1, their (41)):

  (41a)  [CP That he was late all the time] and
         [NP his constant harassment of coworkers]
         resulted in his being dismissed.                          ✓

  (41b) *[NP His constant harassment of coworkers] and
         [CP that he was late all the time]
         resulted in his being dismissed.                          ✗

When coordination is in subject position, it precedes the verb even in English
VO. The last conjunct is closest to V. B&AK predict the NP must be last
(closest), giving CP-first order. Bottom-up accounts predict DP-first
regardless — wrong for this configuration.
-/

/-- B&AK predict CP-first in subject position: the last conjunct is closest to
    V, so the DP must be last. -/
theorem bak_subject_cpFirst :
    linearClosenessPrediction .preverbal = .cpFirst := rfl

/-- Bottom-up predicts DP-first even in subject position. -/
theorem bottomUp_subject_dpFirst :
    bottomUpPrediction .preverbal = .dpFirst := rfl

/-- Subject position distinguishes the two accounts within a single language
    (English). B&AK argue this is decisive evidence for closeness over
    structural prominence. -/
theorem subject_position_distinguishes :
    linearClosenessPrediction .preverbal ≠ bottomUpPrediction .preverbal := by
  decide

/-! ### Cross-linguistic predictions -/

/-- For OV languages, B&AK predict CP-first: complements precede V, so the last
    conjunct is closest. The DP must be last → CP-first. -/
theorem bak_predicts_cpFirst_ov :
    (OVOrder.verbPosition .ov).map linearClosenessPrediction = some .cpFirst := rfl

/-- For VO languages, B&AK predict DP-first. -/
theorem bak_predicts_dpFirst_vo :
    (OVOrder.verbPosition .vo).map linearClosenessPrediction = some .dpFirst := rfl

/-- OV is the cross-linguistic test case. Bottom-up and B&AK diverge on OV
    complement order.

    [schwarzer-2026] tests this with German and finds DP-first (~77%),
    supporting bottom-up over B&AK for OV complement position. -/
theorem ov_predictions_diverge :
    (OVOrder.verbPosition .ov).map linearClosenessPrediction ≠
    (OVOrder.verbPosition .ov).map bottomUpPrediction := by
  decide

/-! ### Supercategories -/

/-- B&AK's supercategory features unify apparent category mismatches that are
    not true selection violations.

    **Pred**: NP, VP, AP, PP can all serve as predicates. A verb like *become*
    selects the supercategory Pred — specifically NP and AP, *not* PP (§2,
    their (1), (34)); selection is finer-grained than the supercategory that
    coordination cares about.

    **Mod**: AP, AdvP can both modify. Prenominal position selects Mod, not
    specifically Adj. -/
inductive Supercategory where
  /-- Predicative: NP, VP, AP, PP can all serve as predicates. -/
  | pred
  /-- Modifier: AP, AdvP can both serve as (prenominal) modifiers. -/
  | mod
  deriving DecidableEq, Repr

/-- Categories belonging to each supercategory, grounded in the `Cat` category
    system from `Syntax`. `Pred` is the full predicative supercategory (B&AK's
    (84): `Pred:{NP,AP}` and friends); `Mod` is restricted here to the
    prenominal modifier categories. The inclusion order on `Finset Cat` gives
    the lattice structure. -/
def Supercategory.cats : Supercategory → Finset Cat
  | .pred => {NP, VP, AdjP, PP}
  | .mod  => {AdjP, AdvP}

/-- AP belongs to both supercategories. -/
theorem adjp_in_pred : AdjP ∈ Supercategory.cats .pred := by decide

theorem adjp_in_mod : AdjP ∈ Supercategory.cats .mod := by decide

/-- Pred and Mod overlap at exactly AP. -/
theorem supercats_overlap :
    Supercategory.cats .pred ∩ Supercategory.cats .mod = {AdjP} := by decide

/-- Extended distributional compatibility for coordination (§3.2). Categories
    that `c` can appear as in non-coordination contexts (displacement, ellipsis),
    beyond its native category.

    - CP → NP: CPs can be topicalized, pseudoclefted, and pro-form replaced —
      NP-like distributional properties
    - AdvP → AdjP: non-*ly* adverbs appear prenominally — AdjP-like
      distributional properties (only with a non-*ly* adverb conjoined to an
      AP in prenominal position, AP last; this coarse map drops those
      conditions)

    All other categories have no extended compatibility. Combined with
    `Supercategory.cats`, this derives B&AK's "exactly two permitted violations"
    (§3.2). -/
def coordExtension : Cat → Finset Cat
  | .CP        => {NP}
  | .proj .ADV => {AdjP}
  | _          => ∅

/-- CP extends to NP positions. -/
theorem cp_extends_np : NP ∈ coordExtension .CP :=
  Finset.mem_singleton.mpr rfl

/-- AdvP extends to AdjP positions. -/
theorem advp_extends_adjp : AdjP ∈ coordExtension (.proj .ADV) :=
  Finset.mem_singleton.mpr rfl

/-- Only CP and AdvP have non-empty coordination extensions. This structurally
    derives B&AK's "exactly two permitted violations" (§3.2) from distributional
    profiles rather than stipulating them as a list. -/
theorem coordExtension_exhaustive (c : Cat) :
    coordExtension c ≠ ∅ → c = .CP ∨ c = AdvP := by
  cases c with
  | CP => intro _; exact Or.inl rfl
  | S => intro h; exact absurd rfl h
  | head _ => intro h; exact absurd rfl h
  | proj u =>
    cases u <;> intro h <;>
      first | exact Or.inr rfl | exact absurd rfl h

/-- Map each violation type to its source and target categories. The source
    category can appear in a position selecting the target via coordination. -/
def SelectionViolationType.cats : SelectionViolationType → Cat × Cat
  | .cpAsNp   => (.CP, NP)
  | .advAsAdj => (AdvP, AdjP)

/-- Each permitted violation corresponds to a non-empty `coordExtension`: the
    target category appears in the extension of the source. -/
theorem violation_from_extension (v : SelectionViolationType) :
    v.cats.2 ∈ coordExtension v.cats.1 := by
  cases v <;> exact Finset.mem_singleton.mpr rfl

/-- Every non-empty `coordExtension` corresponds to a permitted violation. This,
    together with `violation_from_extension`, establishes a bijection between
    `SelectionViolationType` and non-empty extensions, proving the enumeration
    is not stipulated but derived from distributional profiles. -/
theorem extension_to_violation (c : Cat) (h : coordExtension c ≠ ∅) :
    ∃ v : SelectionViolationType, v.cats.1 = c := by
  rcases coordExtension_exhaustive c h with rfl | rfl
  · exact ⟨.cpAsNp, rfl⟩
  · exact ⟨.advAsAdj, rfl⟩

/-! ### Structural assumptions and coordination symmetry

B&AK's derivation (§4.3) builds the *syntax* left-to-right rather than bottom-up,
with feature checking at &P using the linearly closest conjunct. They accept
asymmetric &P structure — the same assumption as the bottom-up accounts — and
disagree only about the *mechanism* deriving predictions from it: linear
closeness (B&AK) vs structural prominence (bottom-up). Both accept
`CoordSymmetry.asymmetric`, but only the bottom-up account's predictions
*require* it.
-/

/-- Coordination structure as adopted by both B&AK and the bottom-up accounts is
    asymmetric: the first conjunct (specifier) is structurally more prominent
    than the second (§4.3, their (82)–(83)).

    Under [marcolli-chomsky-berwick-2025] nonplanar Merge, `merge x y` and
    `merge y x` are strictly equal (Merge is commutative on the syntactic-object
    carrier), so this asymmetry can no longer be grounded in Merge structure; it
    survives only as a stipulation on the Coord head, or as a consequence of
    Externalization (LCA / head directionality). The stipulation is load-bearing
    only for the bottom-up alternatives; B&AK's own closeness mechanism is
    linear-order-side and does not require it. -/
def mergeCoordSymmetry : CoordSymmetry := .asymmetric

/-- Despite assuming asymmetric structure, B&AK's closeness prediction is
    position-dependent: preverbal and postverbal yield different orders. -/
theorem closeness_is_position_dependent :
    linearClosenessPrediction .preverbal ≠
    linearClosenessPrediction .postverbal := by decide

/-- Bottom-up accounts derive position-invariant predictions from the same
    asymmetric structure: always DP-first. -/
theorem bottomUp_is_position_invariant :
    bottomUpPrediction .preverbal = bottomUpPrediction .postverbal := rfl

/-- Structural percolation presupposes asymmetric coordination: there must be a
    structurally prominent (spec) position for features to percolate from. Linear
    percolation requires no particular structural assumption — closeness is
    defined over surface strings, not tree structure. -/
def FeaturePercolation.requiredSymmetry : FeaturePercolation → Option CoordSymmetry
  | .structural => some .asymmetric
  | .linear => none

/-- Both accounts adopt asymmetric structure, but only the bottom-up account's
    predictions *require* it. B&AK's closeness mechanism would make the same
    predictions under symmetric structure. -/
theorem structural_requires_asymmetric :
    FeaturePercolation.requiredSymmetry .structural = some mergeCoordSymmetry ∧
    FeaturePercolation.requiredSymmetry .linear = none :=
  ⟨rfl, rfl⟩

/-! ### Postposition data

B&AK extend the closeness analysis to postpositions (§3.1, their (43)). When the
selecting head is a postposition (e.g. *notwithstanding*), the coordination
precedes it, so the last conjunct is closest and must satisfy selection (= be
the NP), giving CP-first order — as in subject position and OV complements.
Formally the postposition case reduces to `VerbPosition.preverbal`
(cf. `bak_subject_cpFirst`).
-/

end BrueningAlKhalaf2020
