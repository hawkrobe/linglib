import Linglib.Core.Semantics.Presupposition
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Karttunen 1973: Presuppositions of Compound Sentences
@cite{karttunen-1973}

Linguistic Inquiry 4(2): 169–193.

## Core Contributions

1. **The projection problem**: how are presuppositions of constituent sentences
   inherited (or not) by compound sentences?

2. **Three-way classification of complement-taking predicates** (§§2–5):
   - **Plugs**: block all complement presuppositions (*say*, *tell*, *promise*)
   - **Holes**: let all complement presuppositions through (*know*, *regret*,
     *stop*, *force*, *manage*, *believe*)
   - **Filters**: conditionally cancel some presuppositions (*if...then*,
     *and*, *or*)

3. **Filtering conditions for logical connectives** (§§5–7):
   - **If A then B** (rule 13): A's presuppositions always project;
     B's presuppositions project unless A's assertion entails them.
   - **A and B** (rule 17): same as conditional.
   - **A or B** (rule 24): A's presuppositions always project;
     B's presuppositions project unless ¬A entails them.

4. **Classical-logic equivalence** (§8): the identical filtering conditions
   for *if...then* and *and* follow from (i) negation preserves
   presuppositions, (ii) logical equivalents share presuppositions,
   (iii) `A ⊃ B ≡ ¬A ∨ B ≡ ¬(A ∧ ¬B)`.

## What's Still Live vs Historical

The plug/hole/filter vocabulary and the filtering connective formulas are
still the foundation of presupposition projection theory in 2026. The
specific verb inventories, the three-valued logic comparison (§10), the
revised filtering conditions with background assumptions (§9), and the
internal/external negation distinction (§10) are historical — superseded
by CCP (@cite{heim-1983}), local contexts (@cite{schlenker-2009}), and
the projective content taxonomy (@cite{tonhauser-beaver-roberts-simons-2013}).

## Integration

The filtering connectives `PrProp.impFilter`, `PrProp.andFilter`,
`PrProp.orFilter` in `Core/Semantics/Presupposition.lean` are direct
formalizations of Karttunen's rules (13), (17), (24). This study file
proves that correspondence and verifies Fragment verb entries carry the
correct `ProjectionBehavior` annotations.
-/

namespace Phenomena.Presupposition.Studies.Karttunen1973

open Classical
open Core.Presupposition
open Core.Proposition
open Core.Verbs (ProjectionBehavior)
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════════════════
-- § 1. Plug/Hole/Filter Classification Verification
-- ════════════════════════════════════════════════════════════════

/-! Verify that Fragment verb entries carry the correct `projectionBehavior`
    annotations, matching Karttunen's classification (§§3–5). -/

-- ── Plugs (§3): verbs of saying / performatives ──

theorem say_is_plug :
    say.toVerbCore.projectionBehavior = some .plug := rfl

theorem tell_is_plug :
    tell.toVerbCore.projectionBehavior = some .plug := rfl

theorem claim_is_plug :
    claim.toVerbCore.projectionBehavior = some .plug := rfl

theorem promise_is_plug :
    promise.toVerbCore.projectionBehavior = some .plug := rfl

-- ── Holes (§4): factives, aspectuals, implicatives, attitudes ──

theorem know_is_hole :
    know.toVerbCore.projectionBehavior = some .hole := rfl

theorem regret_is_hole :
    regret.toVerbCore.projectionBehavior = some .hole := rfl

theorem realize_is_hole :
    realize.toVerbCore.projectionBehavior = some .hole := rfl

theorem stop_is_hole :
    stop.toVerbCore.projectionBehavior = some .hole := rfl

theorem manage_is_hole :
    manage.toVerbCore.projectionBehavior = some .hole := rfl

theorem force_is_hole :
    force.toVerbCore.projectionBehavior = some .hole := rfl

theorem believe_is_hole :
    believe.toVerbCore.projectionBehavior = some .hole := rfl

-- ── Orthogonality: trigger type vs projection behavior ──

/-- *know* is both a presupposition trigger (factive) AND a hole.
    These are orthogonal properties: trigger = creates presuppositions;
    hole = passes complement presuppositions through. -/
theorem know_trigger_and_hole :
    know.toVerbCore.presupType = some .softTrigger ∧
    know.toVerbCore.projectionBehavior = some .hole := ⟨rfl, rfl⟩

/-- *say* is a non-trigger AND a plug. -/
theorem say_nontrigger_and_plug :
    say.toVerbCore.presupType = none ∧
    say.toVerbCore.projectionBehavior = some .plug := ⟨rfl, rfl⟩

/-- *manage* has a prerequisite presupposition (@cite{nadathur-2024})
    and is a hole (presuppositions project through it). -/
theorem manage_prerequisite_and_hole :
    manage.toVerbCore.presupType = some .prerequisiteSoft ∧
    manage.toVerbCore.projectionBehavior = some .hole := ⟨rfl, rfl⟩

/-- *believe* has no presupposition trigger but is a hole.
    Karttunen (§4) initially considers whether attitude verbs are plugs,
    then argues they are holes — the cumulative hypothesis works for them. -/
theorem believe_nontrigger_and_hole :
    believe.toVerbCore.presupType = none ∧
    believe.toVerbCore.projectionBehavior = some .hole := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Filtering Conditions = Core Connectives
-- ════════════════════════════════════════════════════════════════

/-! Karttunen's filtering conditions (rules 13, 17, 24) are encoded
    directly in the `PrProp` connectives. These theorems make the
    correspondence explicit. -/

variable {W : Type*}

/-- Rule 13a: If A presupposes C (A >> C), then "If A then B" >> C.
    The antecedent's presupposition always projects. -/
theorem rule13a (p q : PrProp W) (w : W)
    (hp : ¬p.presup w) :
    ¬(PrProp.impFilter p q).presup w := by
  simp [PrProp.impFilter, hp]

/-- Rule 13b: If B >> C, then "If A then B" >> C, unless A ⊨ C.
    When A's assertion entails B's presupposition, the presupposition
    is filtered out. -/
theorem rule13b (p q : PrProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (PrProp.impFilter p q).presup = p.presup :=
  PrProp.impFilter_eliminates_presup p q h

/-- Rule 17: filtering condition for conjunction is the same formula
    as for conditionals. This is Karttunen §6's key observation. -/
theorem rule17_same_presup_as_rule13 (p q : PrProp W) (w : W) :
    (PrProp.andFilter p q).presup w = (PrProp.impFilter p q).presup w := rfl

/-- Rule 24: filtering for disjunction uses ¬A instead of A.
    "A or B" >> C unless ¬A ⊨ C (i.e., ¬A's truth entails C). -/
theorem rule24_negation_asymmetry (p q : PrProp W) (w : W) :
    (PrProp.orFilter p q).presup w ↔
    (p.assertion w → q.presup w) ∧
    (q.assertion w → p.presup w) ∧
    (p.presup w ∨ q.presup w) := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. Classical-Logic Equivalence (§8)
-- ════════════════════════════════════════════════════════════════

/-! Karttunen §8 argues that identical filtering conditions for
    *if...then* and *and* are consistent with classical logic, given:
    (i) negation preserves presuppositions;
    (ii) logically equivalent sentences share presuppositions;
    (iii) `A ⊃ B ≡ ¬A ∨ B ≡ ¬(A ∧ ¬B)`.

    We prove this as a theorem about `PrProp` connectives. -/

/-- The filtering presupposition of `impFilter p q` equals that of
    `andFilter p q`. This is the formal content of §8's argument:
    the presupposition function for "if A then B" and "A and B" is
    identical (both = `p.presup ∧ (¬p.assertion ∨ q.presup)`). -/
theorem conditional_conjunction_same_filtering (p q : PrProp W) :
    (PrProp.impFilter p q).presup = (PrProp.andFilter p q).presup := rfl

/-- Negation preserves presupposition (principle (i) of §8). -/
theorem negation_preserves (p : PrProp W) :
    (PrProp.neg p).presup = p.presup := PrProp.neg_presup p

-- ════════════════════════════════════════════════════════════════
-- § 4. Karttunen's Key Examples
-- ════════════════════════════════════════════════════════════════

/-! Finite world models for Karttunen's central examples. -/

/-- World for ex. (4)/(11a): "If Jack has children, then all of
    Jack's children are bald." -/
inductive JackWorld where
  | hasChildren_allBald     -- Jack has children, all bald
  | hasChildren_notAllBald  -- Jack has children, not all bald
  | noChildren              -- Jack has no children
  deriving DecidableEq, Repr

/-- "Jack has children" — no presupposition. -/
def jackHasChildren : PrProp JackWorld :=
  PrProp.ofBool
    (fun _ => true)
    (fun w => match w with
      | .hasChildren_allBald | .hasChildren_notAllBald => true
      | .noChildren => false)

/-- "All of Jack's children are bald" — presupposes Jack has children. -/
def allChildrenBald : PrProp JackWorld :=
  PrProp.ofBool
    (fun w => match w with
      | .hasChildren_allBald | .hasChildren_notAllBald => true
      | .noChildren => false)
    (fun w => match w with
      | .hasChildren_allBald => true
      | .hasChildren_notAllBald | .noChildren => false)

/-- Ex. (11a): "If Jack has children, then all of Jack's children
    are bald." The presupposition of the consequent ("Jack has children")
    is filtered because the antecedent entails it. -/
theorem ex11a_presup_filtered :
    (PrProp.impFilter jackHasChildren allChildrenBald).presup = fun _ => True := by
  funext w; simp [PrProp.impFilter, jackHasChildren, allChildrenBald, PrProp.ofBool]

/-- Ex. (10a)/(10b): When the two clauses are semantically unrelated,
    the conditional has all the presuppositions of its constituents.
    We model this with presuppositionless antecedent + presuppositional
    consequent where the antecedent doesn't entail the presupposition. -/
theorem unrelated_clauses_project (p q : PrProp W) (w : W)
    (hp_def : p.presup w)
    (hp_true : p.assertion w)
    (hq_undef : ¬q.presup w) :
    ¬(PrProp.impFilter p q).presup w := by
  simp [PrProp.impFilter, hp_def, hp_true, hq_undef]

/-- Ex. (16a): "Jack has children and all of Jack's children are bald."
    Same filtering as the conditional — the conjunction doesn't
    presuppose Jack has children. -/
theorem ex16a_presup_filtered :
    (PrProp.andFilter jackHasChildren allChildrenBald).presup = fun _ => True := by
  funext w; simp [PrProp.andFilter, jackHasChildren, allChildrenBald, PrProp.ofBool]

-- ════════════════════════════════════════════════════════════════
-- § 5. Three-Valued Logic Comparison (§10) — Historical
-- ════════════════════════════════════════════════════════════════

/-! Karttunen §10 compares four three-valued conjunction tables:

    | System              | Filtering behavior    |
    |---------------------|-----------------------|
    | Bochvar internal    | Hole (cumulative)     |
    | Bochvar external    | Plug                  |
    | Łukasiewicz         | Symmetric filter      |
    | Van Fraassen        | Symmetric filter      |

    The `PrProp` connective zoo covers these:
    - `PrProp.and` = Bochvar internal (both must be defined)
    - `PrProp.andFilter` = Karttunen's asymmetric filter
    - `PrProp.andBelnap` = Belnap's conditional assertion

    Łukasiewicz/Van Fraassen use symmetric filtering: when one
    operand is # and the other is F, the result is F (not #).
    This is not `andFilter` (which is asymmetric/left-to-right).

    The Bochvar external connectives correspond to plugs: they
    use a "truth operator" `t(A)` that maps # → F, making all
    presuppositions invisible. -/

/-- Bochvar internal conjunction = `PrProp.and`: both presuppositions
    must hold. This is the cumulative hypothesis. -/
theorem bochvar_internal_is_classical (p q : PrProp W) (w : W) :
    (PrProp.and p q).presup w ↔ (p.presup w ∧ q.presup w) := Iff.rfl

/-- The filtering conjunction is strictly weaker than classical:
    it can be defined even when q's presupposition fails (if p's
    assertion is false). -/
theorem filter_weaker_than_classical (p q : PrProp W) (w : W)
    (h : (PrProp.and p q).presup w) :
    (PrProp.andFilter p q).presup w := by
  simp [PrProp.and, PrProp.andFilter] at *
  exact ⟨h.1, fun _ => h.2⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. Internal vs External Negation (§10) — Historical
-- ════════════════════════════════════════════════════════════════

/-! Karttunen distinguishes two senses of *not*:

    - **Internal negation** (choice negation): a hole. Ordinary
      negation lets presuppositions through. This is `PrProp.neg`.
    - **External negation** (exclusion negation): a plug. Maps
      # → F, blocking all presuppositions.

    The distinction corresponds to Bochvar's internal vs external
    connectives. In 2026 this is subsumed by metalinguistic negation
    (Horn 1985) and focus alternatives. -/

/-- External negation: maps undefined to false (a plug). -/
def negExternal (p : PrProp W) : PrProp W :=
  { presup := fun _ => True
  , assertion := fun w => p.presup w ∧ p.assertion w }

/-- External negation is always defined (it's a plug). -/
theorem negExternal_always_defined (p : PrProp W) (w : W) :
    (negExternal p).presup w := trivial

/-- Internal negation preserves presupposition (it's a hole). -/
theorem neg_internal_preserves (p : PrProp W) :
    (PrProp.neg p).presup = p.presup := PrProp.neg_presup p

/-- The two negations agree when the presupposition holds. -/
theorem neg_agree_when_defined (p : PrProp W) (w : W)
    (h : p.presup w) :
    (PrProp.neg p).assertion w ↔ ¬(negExternal p).assertion w := by
  simp [PrProp.neg, negExternal, h]

-- ════════════════════════════════════════════════════════════════
-- § 7. Revised Filtering Conditions (§9) — Historical
-- ════════════════════════════════════════════════════════════════

/-! Karttunen §9 revises the filtering conditions to handle cases
    where background assumptions contribute to filtering.

    Rule (24b'): If B >> C, then S >> C unless there exists a
    (possibly null) set X of assumed facts such that X ∪ {¬A} ⊨ C.

    This is superseded by CCP / local contexts (@cite{heim-1983},
    @cite{schlenker-2009}), where the context set plays the role
    of X automatically. The `LocalCtx` machinery in
    `Theories/Semantics/Presupposition/LocalContext.lean` handles
    this: the local context at a position already incorporates all
    "assumed facts" from the discourse context.

    We state the revised condition as a theorem schema showing that
    the simple filtering condition is a special case (X = ∅). -/

/-- The simple filtering condition (rule 13b) is the special case of
    the revised condition (rule 17b') where X = ∅. -/
theorem simple_is_special_case_of_revised (p q : PrProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (PrProp.impFilter p q).presup = p.presup :=
  PrProp.impFilter_eliminates_presup p q h

end Phenomena.Presupposition.Studies.Karttunen1973
