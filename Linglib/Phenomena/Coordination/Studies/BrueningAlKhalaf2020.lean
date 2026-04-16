import Linglib.Phenomena.WordOrder.Typology
import Linglib.Core.Coordination
import Linglib.Core.Tree
import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Mathlib.Data.Finset.Basic

/-!
# @cite{bruening-alkhalaf-2020} — Category Mismatches in Coordination Revisited

Bruening, Benjamin & Eman Al Khalaf. 2020. Category mismatches in
coordination revisited. *Linguistic Inquiry* 51(1). 1–36.

## The Directionality Effect (§3.1)

The linearly closest conjunct to the selecting head must satisfy
c-selection. In VO languages (English complement position), this is
the first conjunct. In OV languages, or when coordination precedes
the verb (English subject position, postpositions), this is the last
conjunct.

## Two Permitted Violations (§3.2)

Only two genuine category mismatches occur in selection-violating
coordination: CP↔NP and non-*ly* Adverb↔Adjective. Both parallel
displacement and ellipsis patterns.

## Supercategories (§2)

Apparent category mismatches in predication and modification are not
true violations but supercategory selection. *become* selects Pred
(AP, VP, PP); prenominal position selects Mod (AP, AdvP).

## Left-to-Right Derivation (§4)

PF and LF are built left-to-right simultaneously. Feature checking
at &P proceeds linearly, explaining why the closest conjunct must
satisfy selection.

## Connection to @cite{schwarzer-2026}

@cite{schwarzer-2026} tests the cross-linguistic prediction using German
OV: B&AK predict CP-first for OV complements, but Schwarzer finds
DP-first (~77%), supporting bottom-up accounts instead.
-/

namespace BrueningAlKhalaf2020

open Core.Coordination
open Core.Tree (Cat)
open Core.Tree.Cat (NP VP AdjP AdvP PP)
open Phenomena.WordOrder.Typology

-- ============================================================================
-- § 1: Shared Types for Selection-Violating Coordination
-- ============================================================================

/-- Preferred order of conjuncts in DP-CP selection-violating coordination. -/
inductive ConjunctOrder where
  /-- DP conjunct precedes CP conjunct. -/
  | dpFirst
  /-- CP conjunct precedes DP conjunct. -/
  | cpFirst
  deriving DecidableEq, Repr, BEq

/-- Surface position of the coordination relative to the selecting verb. -/
inductive VerbPosition where
  /-- Coordination precedes verb (OV complements, VO subjects). -/
  | preverbal
  /-- Coordination follows verb (VO complements). -/
  | postverbal
  deriving DecidableEq, Repr, BEq

/-- Derive verb position from typological OV order.
    OV: complements precede verb → preverbal.
    VO: complements follow verb → postverbal.
    No dominant order: indeterminate. -/
def OVOrder.toVerbPosition : OVOrder → Option VerbPosition
  | .ov => some .preverbal
  | .vo => some .postverbal
  | .noDominant => none

-- ============================================================================
-- § 2: Feature Percolation & The Directionality Principle (§3.1)
-- ============================================================================

/-- How selectional features percolate through &P to the selecting head.

    The competing analyses of selection-violating coordination disagree
    on a single parameter: which conjunct's categorical features are
    visible to the selecting head. This parameter determines conjunct
    order preferences as a function of surface position. -/
inductive FeaturePercolation where
  /-- Features percolate from the structurally prominent (spec) position.
      The first conjunct always determines &P's categorical features,
      regardless of surface position relative to the verb.
      Analyses: @cite{sag-etal-1985}, @cite{munn-1993}, @cite{peterson-2004},
      @cite{zhang-2010}. -/
  | structural
  /-- Features percolate from the linearly closest conjunct to the
      selecting head. Which conjunct is closest depends on surface
      position relative to the verb.
      Analysis: @cite{bruening-alkhalaf-2020}. -/
  | linear
  deriving DecidableEq, Repr, BEq

/-- Derive conjunct order preference from feature percolation mechanism.

    The core principle: the conjunct whose features percolate to &P must
    satisfy c-selection (= must be the DP). The percolation mechanism
    determines *which* conjunct that is:

    - **Structural**: spec (= first conjunct) → always DP-first
    - **Linear**: closest to V → DP-first postverbally, CP-first preverbally -/
def predictOrder (fp : FeaturePercolation) (pos : VerbPosition) : ConjunctOrder :=
  match fp with
  | .structural => .dpFirst
  | .linear => match pos with
    | .postverbal => .dpFirst
    | .preverbal  => .cpFirst

/-- Structural percolation is position-invariant: the structurally
    prominent conjunct is always first, regardless of surface order. -/
theorem structural_position_invariant (pos₁ pos₂ : VerbPosition) :
    predictOrder .structural pos₁ = predictOrder .structural pos₂ := rfl

/-- Linear percolation is position-dependent: preverbal and postverbal
    yield different predictions. -/
theorem linear_position_dependent :
    predictOrder .linear .preverbal ≠ predictOrder .linear .postverbal := by decide

/-- The two percolation mechanisms agree in postverbal position:
    both predict DP-first when V precedes the coordination. -/
theorem percolation_agrees_postverbal :
    predictOrder .structural .postverbal = predictOrder .linear .postverbal := rfl

/-- The two percolation mechanisms diverge in preverbal position:
    structural predicts DP-first, linear predicts CP-first. This is
    the configuration that empirically distinguishes the accounts. -/
theorem percolation_diverges_preverbal :
    predictOrder .structural .preverbal ≠ predictOrder .linear .preverbal := by decide

/-- **Linear closeness prediction** (B&AK's core claim, §3.1):
    the linearly closest conjunct to the selecting head must satisfy
    c-selection.

    In VO complement position: V [&P X and Y] → X is closest → DP-first.
    In OV complement position: [&P X and Y] V → Y is closest → CP-first
    (so DP is last, verb-adjacent).

    This also applies to English subject position (preverbal even in VO)
    and postpositions (selecting head follows coordination).

    Derived from `predictOrder` with linear percolation. -/
def linearClosenessPrediction : VerbPosition → ConjunctOrder :=
  predictOrder .linear

/-- **Bottom-up prediction** (competitor account, §3.1):
    asymmetric &P structure makes the first conjunct structurally more
    prominent. The selected DP must be first, regardless of surface
    position relative to the verb.

    Analyses: @cite{sag-etal-1985}, @cite{munn-1993}, @cite{peterson-2004},
    @cite{zhang-2010}.

    Derived from `predictOrder` with structural percolation. -/
def bottomUpPrediction : VerbPosition → ConjunctOrder :=
  predictOrder .structural

-- ============================================================================
-- § 3: Permitted Selection Violations (§3.2)
-- ============================================================================

/-- B&AK identify exactly two category mismatches that are permitted in
    selection-violating coordination (§3.2).

    These parallel the categories that allow displacement and ellipsis:
    1. CP↔NP: CPs can appear in NP positions (also seen in topicalization,
       pseudoclefts, "do so" replacement)
    2. Non-*ly* Adv↔Adj: manner adverbs without *-ly* can appear in
       adjective positions (also seen in prenominal modification) -/
inductive SelectionViolationType where
  /-- CP appearing in an NP-selecting position. -/
  | cpAsNp
  /-- Non-*ly* adverb appearing in an adjective position. -/
  | advAsAdj
  deriving DecidableEq, Repr

/-- The exhaustive list of permitted violations, justified structurally
    by `coordExtension_exhaustive` (§ 7): only CP and AdvP have
    non-empty extensions. See `violation_from_extension` and
    `extension_to_violation` (§ 7) for the bidirectional correspondence. -/
def permittedViolations : List SelectionViolationType :=
  [.cpAsNp, .advAsAdj]

theorem exactly_two_violations : permittedViolations.length = 2 := rfl

-- ============================================================================
-- § 4: English VO Complement Position
-- ============================================================================

/-- English is VO: complements follow the selecting verb. -/
theorem english_is_vo : english.ovOrder = .vo := rfl

/-- English complement position maps to postverbal. -/
theorem english_complement_postverbal :
    OVOrder.toVerbPosition english.ovOrder = some .postverbal := rfl

/-- B&AK predict DP-first in English complement position: the first
    conjunct is closest to V.

      You can depend on [DP my assistant] and [CP that he will
      be on time]. ✓

    @cite{sag-etal-1985} ex. (3a), @cite{bruening-alkhalaf-2020} §3.1. -/
theorem bak_english_complement :
    linearClosenessPrediction .postverbal = .dpFirst := rfl

/-- Bottom-up also predicts DP-first for English VO complements.
    Both accounts agree for this configuration. -/
theorem accounts_agree_complement :
    linearClosenessPrediction .postverbal = bottomUpPrediction .postverbal := rfl

-- ============================================================================
-- § 5: English Subject Position — The Distinguishing Case (§3.1)
-- ============================================================================

/-!
B&AK's strongest within-English evidence for closeness over first-conjunct
(§3.1, examples (41a/b)):

  (41a) [CP That he had been gambling with public funds] and
        [DP the fact that he had been keeping a mistress]
        resulted in his being dismissed.                          ✓

  (41b) *[DP The fact that he had been keeping a mistress] and
         [CP that he had been gambling with public funds]
         resulted in his being dismissed.                         ✗

When coordination is in subject position, it precedes the verb even in
English VO. The LAST conjunct is closest to V. B&AK predict the DP must
be last (closest), giving CP-first order. Bottom-up accounts predict
DP-first regardless — wrong for this configuration.
-/

/-- B&AK predict CP-first in subject position: the last conjunct is
    closest to V, so the DP must be last. -/
theorem bak_subject_cpfirst :
    linearClosenessPrediction .preverbal = .cpFirst := rfl

/-- Bottom-up predicts DP-first even in subject position. -/
theorem bottomUp_subject_dpfirst :
    bottomUpPrediction .preverbal = .dpFirst := rfl

/-- Subject position distinguishes the two accounts within a single
    language (English). B&AK argue this is decisive evidence for
    closeness over structural prominence. -/
theorem subject_position_distinguishes :
    linearClosenessPrediction .preverbal ≠ bottomUpPrediction .preverbal := by
  decide

-- ============================================================================
-- § 6: Cross-Linguistic Predictions
-- ============================================================================

/-- For OV languages, B&AK predict CP-first: complements precede V,
    so the last conjunct is closest. The DP must be last → CP-first. -/
theorem bak_predicts_cpfirst_ov :
    (OVOrder.toVerbPosition .ov).map linearClosenessPrediction = some .cpFirst := rfl

/-- For VO languages, B&AK predict DP-first. -/
theorem bak_predicts_dpfirst_vo :
    (OVOrder.toVerbPosition .vo).map linearClosenessPrediction = some .dpFirst := rfl

/-- OV is the cross-linguistic test case. Bottom-up and B&AK diverge
    on OV complement order.

    @cite{schwarzer-2026} tests this with German and finds DP-first (~77%),
    supporting bottom-up over B&AK for OV complement position. -/
theorem ov_predictions_diverge :
    (OVOrder.toVerbPosition .ov).map linearClosenessPrediction ≠
    (OVOrder.toVerbPosition .ov).map bottomUpPrediction := by
  decide

-- ============================================================================
-- § 7: Supercategories (§2)
-- ============================================================================

/-- B&AK's supercategory features unify apparent category mismatches
    that are not true selection violations.

    **Pred**: AP, VP, PP can all serve as predicates. Verbs like
    *become* select Pred, not a specific lexical category.

    **Mod**: AP, AdvP can both modify. Prenominal position selects
    Mod, not specifically Adj. -/
inductive Supercategory where
  /-- Predicative: AP, VP, PP can all serve as predicates. -/
  | pred
  /-- Modifier: AP, AdvP can both serve as modifiers. -/
  | mod
  deriving DecidableEq, Repr

/-- Categories belonging to each supercategory, grounded in the `Cat`
    category system from `Core.Tree`. The inclusion order on `Finset Cat`
    gives the lattice structure: `Supercategory.cats .pred` and
    `Supercategory.cats .mod` are elements ordered by ⊆. -/
def Supercategory.cats : Supercategory → Finset Cat
  | .pred => {VP, AdjP, PP}
  | .mod  => {AdjP, AdvP}

/-- AP belongs to both supercategories. -/
theorem adjp_in_pred : AdjP ∈ Supercategory.cats .pred :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem adjp_in_mod : AdjP ∈ Supercategory.cats .mod :=
  Finset.mem_insert_self _ _

/-- Pred and Mod overlap at exactly AP. -/
theorem supercats_overlap :
    Supercategory.cats .pred ∩ Supercategory.cats .mod = {AdjP} := by
  ext x
  simp only [Supercategory.cats, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | rfl | rfl
    · rcases h2 with h | h <;> exact absurd h (by decide)
    · rfl
    · rcases h2 with h | h <;> exact absurd h (by decide)
  · rintro rfl; exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩

/-- Extended distributional compatibility for coordination (§3.2).
    Categories that `c` can appear as in non-coordination contexts
    (displacement, ellipsis), beyond its native category.

    - CP → NP: CPs can be topicalized, pseudoclefted, and pro-form
      replaced — NP-like distributional properties
    - AdvP → AdjP: non-*ly* adverbs appear prenominally — AdjP-like
      distributional properties

    All other categories have no extended compatibility. Combined
    with `Supercategory.cats`, this derives B&AK's "exactly two
    permitted violations" (§3.2). -/
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

/-- Only CP and AdvP have non-empty coordination extensions.
    This structurally derives B&AK's "exactly two permitted
    violations" (§3.2) from distributional profiles rather than
    stipulating them as a list. -/
theorem coordExtension_exhaustive (c : Cat) :
    coordExtension c ≠ ∅ → c = .CP ∨ c = AdvP := by
  cases c with
  | CP => intro _; exact Or.inl rfl
  | S => intro h; exact absurd rfl h
  | head _ => intro h; exact absurd rfl h
  | proj u =>
    cases u <;> intro h <;>
      first | exact Or.inr rfl | exact absurd rfl h

/-- Map each violation type to its source and target categories.
    The source category can appear in a position selecting the target
    via coordination. -/
def SelectionViolationType.cats : SelectionViolationType → Cat × Cat
  | .cpAsNp   => (.CP, NP)
  | .advAsAdj => (AdvP, AdjP)

/-- Each permitted violation corresponds to a non-empty `coordExtension`:
    the target category appears in the extension of the source. -/
theorem violation_from_extension (v : SelectionViolationType) :
    v.cats.2 ∈ coordExtension v.cats.1 := by
  cases v <;> exact Finset.mem_singleton.mpr rfl

/-- Every non-empty `coordExtension` corresponds to a permitted violation.
    This, together with `violation_from_extension`, establishes a
    bijection between `SelectionViolationType` and non-empty extensions,
    proving the enumeration is not stipulated but derived from
    distributional profiles. -/
theorem extension_to_violation (c : Cat) (h : coordExtension c ≠ ∅) :
    ∃ v : SelectionViolationType, v.cats.1 = c := by
  rcases coordExtension_exhaustive c h with rfl | rfl
  · exact ⟨.cpAsNp, rfl⟩
  · exact ⟨.advAsAdj, rfl⟩

-- ============================================================================
-- § 8: Structural Assumptions & CoordSymmetry (§4)
-- ============================================================================

/-!
B&AK's derivation model (§4) builds structure left-to-right, with PF and
LF computed simultaneously. Feature checking at &P uses the linearly
closest conjunct. The model posits null syntactic heads (null N dominating
CP, null Adv head) to mediate the two permitted violations.

Crucially, B&AK accept asymmetric &P structure — the same assumption as
bottom-up accounts. The disagreement is about the **mechanism**: closeness
(B&AK) vs structural prominence (bottom-up). Both theories accept
`CoordSymmetry.asymmetric`, but derive different predictions from it:

- B&AK: closeness → predictions depend on surface position
- Bottom-up: structural prominence → predictions are position-invariant
-/

/-- Coordination structure under Minimalist Merge is asymmetric:
    Merge distinguishes its children (`merge_distinguishes_children`),
    so the first conjunct (specifier) is structurally more prominent
    than the second (complement).

    Both B&AK and bottom-up accounts accept this (§4). The disagreement
    is about the mechanism (closeness vs structural prominence), not
    the structure itself. -/
def mergeCoordSymmetry : CoordSymmetry := .asymmetric

/-- Despite assuming asymmetric structure, B&AK's closeness prediction
    is position-DEPENDENT: preverbal and postverbal yield different
    orders. -/
theorem closeness_is_position_dependent :
    linearClosenessPrediction .preverbal ≠
    linearClosenessPrediction .postverbal := by decide

/-- Bottom-up accounts derive position-INVARIANT predictions from the
    same asymmetric structure: always DP-first. -/
theorem bottomUp_is_position_invariant :
    bottomUpPrediction .preverbal = bottomUpPrediction .postverbal := rfl

/-- Structural percolation presupposes asymmetric coordination: there
    must be a structurally prominent (spec) position for features to
    percolate from. Linear percolation requires no particular structural
    assumption — closeness is defined over surface strings, not tree
    structure. -/
def FeaturePercolation.requiredSymmetry : FeaturePercolation → Option CoordSymmetry
  | .structural => some .asymmetric
  | .linear => none

/-- Both accounts adopt asymmetric structure, but only the bottom-up
    account's predictions *require* it. B&AK's closeness mechanism
    would make the same predictions under symmetric structure. -/
theorem structural_requires_asymmetric :
    FeaturePercolation.requiredSymmetry .structural = some mergeCoordSymmetry ∧
    FeaturePercolation.requiredSymmetry .linear = none :=
  ⟨rfl, rfl⟩

/-- Merge produces structurally asymmetric objects: the two children
    of `merge x y` are distinguished (x is the specifier, y is the
    complement). When x ≠ y, swapping them produces a different
    syntactic object.

    This is the structural foundation of `CoordSymmetry.asymmetric`:
    if coordination is External Merge, then the first conjunct is
    always structurally distinguished from the second. -/
theorem merge_distinguishes_children
    (x y : Minimalism.SyntacticObject) (h : x ≠ y) :
    Minimalism.merge x y ≠ Minimalism.merge y x :=
  fun heq => h (Minimalism.SyntacticObject.node.inj heq).1

/-- Merge's asymmetry satisfies structural percolation's presupposition. -/
theorem merge_satisfies_structural_presupposition :
    FeaturePercolation.requiredSymmetry .structural = some mergeCoordSymmetry := rfl

/-- The full Merge → prediction chain:

    1. Merge distinguishes children (`merge_distinguishes_children`)
    2. Therefore coordination via Merge is asymmetric (`mergeCoordSymmetry`)
    3. Structural percolation's presupposition is met
       (`merge_satisfies_structural_presupposition`)
    4. `predictOrder .structural` yields position-invariant DP-first

    This grounds the bottom-up prediction in Minimalist architecture
    rather than stipulating `CoordSymmetry.asymmetric`. -/
theorem merge_grounds_prediction (pos : VerbPosition) :
    mergeCoordSymmetry = .asymmetric ∧
    FeaturePercolation.requiredSymmetry .structural = some mergeCoordSymmetry ∧
    predictOrder .structural pos = .dpFirst :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Postposition Data (§3.1)
-- ============================================================================

/-!
B&AK extend the closeness analysis to postpositions (§3.1, examples
(43a/b)). When the selecting head is a postposition (e.g., *notwithstanding*),
the coordination precedes it. The LAST conjunct is closest, so it must
satisfy selection (= be DP). This gives CP-first order, just as in
subject position and OV complements.

Formally, the postposition case reduces to `VerbPosition.preverbal`:
coordination precedes the selecting head, making it structurally
identical to subject position (cf. `bak_subject_cpfirst`).
-/

end BrueningAlKhalaf2020
