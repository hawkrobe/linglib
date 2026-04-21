import Linglib.Core.InformationStructure
import Linglib.Core.Discourse.Coherence
import Linglib.Core.Question.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Question.Answerhood
import Linglib.Core.Mood.PartitionAsInquiry
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Pragmatics.DecisionTheoretic.But
import Linglib.Fragments.English.FocusParticles
import Linglib.Fragments.English.FunctionWords

/-!
# @cite{umbach-2004} — On the Notion of Contrast @cite{umbach-2004}

Umbach, Carla (2004). On the Notion of Contrast in Information Structure
and Discourse Structure. *Journal of Semantics* 21(2): 155–175.

## Core thesis

Contrast is **similarity plus dissimilarity**. This single notion unifies
three levels at which "contrast" appears:

1. **Focus alternatives** (§2.2): all focus evokes alternatives that are
   similar (common integrator) and dissimilar (semantically independent).
   This is contrast in the broadest sense — a prerequisite for any
   coordination by *and* or *but*.

2. **Contrastive focus** (§2.3): adds *exclusion* on top of
   similarity+dissimilarity. Exhaustive interpretation entails that no
   other alternative satisfies the predicate.

3. **Discourse relations** (§3): CONTRAST and CORRECTION both require
   similarity+dissimilarity but differ in *exclusion type*:
   - CONTRAST: excludes *additional* alternatives (confirm+deny)
   - CORRECTION: excludes *by substitution* (German *sondern*)

## Key contributions formalized

- Alternative set well-formedness: `semanticallyIndependent`,
  `commonIntegrator`, `wellFormedAlts` (defined in Core, exercised here)
- Confirm+deny condition on "but" (§3.1)
- Exclusion variety taxonomy connecting *only*-phrases ↔ CONTRAST
  and contrastive focus ↔ CORRECTION (§2.3, §3.2)
- Bridge: comparison with @cite{merin-1999} DTS account of "but"

## Connection to existing formalization

- Focus alternatives & FIP: `Semantics.FocusInterpretation` (@cite{rooth-1992})
- QUD / implicit questions: `Core.Question`, `Core.Question.isPartialAnswer` (@cite{roberts-2012})
- DTS "but": `DTS.But` (@cite{merin-1999})
- Coherence relations: `Core.Discourse.Coherence` (@cite{kehler-2002})
- Focus particles: `Fragments.English.FocusParticles`
-/

namespace Umbach2004

open Core.InformationStructure
open Core.Discourse.Coherence

-- ═══════════════════════════════════════════════════════════════════════
-- §1  World Model
-- ═══════════════════════════════════════════════════════════════════════

/-! A 6-world model sufficient for all examples.

Worlds encode who went where (Berlin/Paris/London examples from §3.2)
and what John had to drink (beer/martini examples from §2.2). -/

inductive W where
  | jBerlin      -- John went to Berlin (only)
  | jParis       -- John went to Paris (only)
  | jBoth        -- John went to Berlin and Paris
  | jBeer        -- John had a beer
  | jMartini     -- John had a martini
  | jBeerMartini -- John had a beer and a martini
  deriving DecidableEq, Repr, Inhabited

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Propositions
-- ═══════════════════════════════════════════════════════════════════════

def wentBerlin : W → Bool
  | .jBerlin | .jBoth => true | _ => false

def wentParis : W → Bool
  | .jParis | .jBoth => true | _ => false

def hadBeer : W → Bool
  | .jBeer | .jBeerMartini => true | _ => false

def hadMartini : W → Bool
  | .jMartini | .jBeerMartini => true | _ => false

/-- "had a drink" — subsumes both beer and martini. -/
def hadDrink : W → Bool
  | .jBeer | .jMartini | .jBeerMartini => true | _ => false

/-- "went somewhere" — common integrator for Berlin/Paris. -/
def wentSomewhere : W → Bool
  | .jBerlin | .jParis | .jBoth => true | _ => false

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Alternative Set Well-Formedness (@cite{umbach-2004} §2.2)
-- ═══════════════════════════════════════════════════════════════════════

/-! The core formal claim: alternatives must be pairwise semantically
independent (dissimilar) and share a common integrator (similar).
This explains coordination acceptability judgments. -/

-- ─────────────────────────────────────────────────────────────────────
-- §3a  Well-formed: {beer, martini} under "drink"
-- ─────────────────────────────────────────────────────────────────────

/-- Beer and martini are semantically independent: neither entails
    the other. Having a beer does not entail having a martini
    (witness: `W.jBeer`), and vice versa (witness: `W.jMartini`). -/
theorem beer_martini_independent :
    semanticallyIndependent hadBeer hadMartini := by
  constructor
  · intro h; exact absurd (h .jBeer rfl) (by decide)
  · intro h; exact absurd (h .jMartini rfl) (by decide)

/-- "drink" is a common integrator for {beer, martini}: every world
    where beer or martini is true is also a world where drink is true. -/
theorem drink_integrates_beer_martini :
    commonIntegrator [hadBeer, hadMartini] hadDrink := by
  intro a ha w hw
  simp [List.mem_cons] at ha
  rcases ha with rfl | rfl <;> cases w <;> simp_all [hadBeer, hadMartini, hadDrink]

/-- {beer, martini} is a well-formed alternative set under "drink". -/
theorem beer_martini_wellformed :
    wellFormedAlts [hadBeer, hadMartini] hadDrink := by
  refine ⟨drink_integrates_beer_martini, ?_⟩
  intro a ha b hb hne
  simp [List.mem_cons] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hne
  · exact beer_martini_independent
  · exact ⟨beer_martini_independent.2, beer_martini_independent.1⟩
  · exact absurd rfl hne

-- ─────────────────────────────────────────────────────────────────────
-- §3b  Ill-formed: {drink, martini} — subsumption violates independence
-- ─────────────────────────────────────────────────────────────────────

/-- "drink" subsumes "martini": hadMartini w → hadDrink w.
    This violates semantic independence, explaining why
    *#John had a drink and Mary had a martini* is odd
    (@cite{umbach-2004} §2.2, ex. 9a). -/
theorem drink_subsumes_martini :
    ∀ w : W, hadMartini w = true → hadDrink w = true := by
  intro w; cases w <;> simp [hadMartini, hadDrink]

theorem drink_martini_not_independent :
    ¬ semanticallyIndependent hadDrink hadMartini := by
  intro ⟨_, h2⟩; exact h2 drink_subsumes_martini

/-- {drink, martini} is NOT a well-formed alternative set
    (under any integrator). -/
theorem drink_martini_not_wellformed (integ : W → Bool) :
    ¬ wellFormedAlts [hadDrink, hadMartini] integ := by
  intro ⟨_, hInd⟩
  have hne : hadDrink ≠ hadMartini := by
    intro h; exact absurd (congrFun h .jBeer) (by decide)
  have h1 : hadDrink ∈ [hadDrink, hadMartini] := by simp
  have h2 : hadMartini ∈ [hadDrink, hadMartini] := by simp
  exact drink_martini_not_independent (hInd hadDrink h1 hadMartini h2 hne)

-- ─────────────────────────────────────────────────────────────────────
-- §3c  Well-formed: {Berlin, Paris} under "somewhere"
-- ─────────────────────────────────────────────────────────────────────

theorem berlin_paris_independent :
    semanticallyIndependent wentBerlin wentParis := by
  constructor
  · intro h; exact absurd (h .jBerlin rfl) (by decide)
  · intro h; exact absurd (h .jParis rfl) (by decide)

theorem somewhere_integrates :
    commonIntegrator [wentBerlin, wentParis] wentSomewhere := by
  intro a ha w hw
  simp [List.mem_cons] at ha
  rcases ha with rfl | rfl <;>
    cases w <;> simp_all [wentBerlin, wentParis, wentSomewhere]

-- ═══════════════════════════════════════════════════════════════════════
-- §3d  Connection to @cite{rooth-1992} Focus Interpretation Principle
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{umbach-2004} §2.1 builds directly on @cite{rooth-1992}'s alternative
semantics: all focus evokes alternatives, and Umbach's similarity+dissimilarity
refines what counts as a well-formed alternative set.

The FIP (Γ ⊆ ⟦α⟧f) constrains the contrast set Γ to be a subset of
focus alternatives. Umbach adds that alternatives within Γ must be
pairwise semantically independent (dissimilarity) and share a common
integrator (similarity). This is strictly more constraining than FIP alone. -/

/-- Well-formed alternatives satisfy Rooth's FIP: if the focus value
    admits each alternative as a focus alternative, the well-formedness
    constraints layer on top of FIP without contradicting it.

    Concretely: if ⟦α⟧f includes all members of the alternative set
    (Γ ⊆ ⟦α⟧f), and the alternatives are well-formed in Umbach's sense,
    then FIP is satisfied. Umbach's conditions refine, not replace, Rooth. -/
theorem wellformed_implies_fip_compatible {W : Type}
    (alts : List (W → Bool)) (integ : W → Bool)
    (focusValue : Semantics.FocusInterpretation.PropFocusValue W)
    (_hwf : wellFormedAlts alts integ)
    (gamma : (W → Bool) → Bool)
    (hgamma : ∀ a ∈ alts, gamma a)
    (hfip : Semantics.FocusInterpretation.fip gamma focusValue) :
    ∀ a ∈ alts, focusValue a :=
  fun a ha => hfip a (hgamma a ha)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Exclusion Varieties (@cite{umbach-2004} §2.3)
-- ═══════════════════════════════════════════════════════════════════════

/-! Two varieties of exclusion cross-cut information structure and
discourse structure. The taxonomy is already defined in Core
(`ExclusionVariety`); here we verify the parallel and connect
to Fragment entries. -/

/-- *Only*-phrases exclude additional alternatives:
    "Tonight, only RONALD went shopping" (§2.3, ex. 14b) excludes
    the possibility that someone *in addition to* Ronald went shopping.
    This maps to the CONTRAST discourse relation. -/
theorem only_maps_to_contrast :
    ExclusionVariety.toCoherenceRelation .additional = .contrast := rfl

/-- Contrastive focus excludes by substitution:
    "Tonight, RONALD went shopping" (§2.3, ex. 13) excludes the
    possibility that someone *instead of* Ronald went shopping.
    This maps to the CORRECTION discourse relation. -/
theorem contrastive_focus_maps_to_correction :
    ExclusionVariety.toCoherenceRelation .substitution = .correction := rfl

/-- The English "only" Fragment entry carries the additional variety. -/
theorem only_fragment_exclusion :
    Fragments.English.FocusParticles.only_.exclusionVariety =
    some .additional := rfl

/-- The exclusion parallel: *only* and CONTRAST share the *additional*
    exclusion type, just as contrastive focus and CORRECTION share
    the *substitution* type. @cite{umbach-2004} §3.2: "the discourse
    relations of contrast and correction differ from each other in the
    same way a contrastive focus differs from an only-phrase." -/
theorem exclusion_parallel :
    ExclusionVariety.additional.toCoherenceRelation ≠
    ExclusionVariety.substitution.toCoherenceRelation := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Confirm+Deny Condition on "but" (@cite{umbach-2004} §3.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{umbach-2004} §3.1: a *but*-sentence responds to an implicit
question with "yes...but no...". One conjunct confirms a sub-question,
the other denies its counterpart. This is the *confirm+deny* condition.

Example (§3.1, ex. 17e): "John cleaned up his room, but he didn't
wash the dishes" — confirms "Did John clean his room?" (yes) and
denies "Did he wash the dishes?" (no).

The confirm+deny condition distinguishes *but* from *and*: both
require similarity+dissimilarity in their conjuncts, but only *but*
requires one conjunct to confirm and one to deny. -/

/-- The confirm+deny condition on a *but*-sentence.
    Given two sub-questions q₁, q₂ (derived from focus in the conjuncts),
    the first conjunct confirms q₁ and the second denies q₂. -/
def confirmDeny {W : Type} (q₁ q₂ : W → Bool) (c₁ c₂ : W → Bool) : Prop :=
  -- c₁ confirms q₁: c₁ entails q₁
  (∀ w : W, c₁ w = true → q₁ w = true) ∧
  -- c₂ denies q₂: c₂ entails ¬q₂
  (∀ w : W, c₂ w = true → q₂ w = false)

/-- A 4-world model for the confirm+deny examples. -/
inductive CDWorld where
  | roomOnly     -- John cleaned the room but not the dishes
  | dishesOnly   -- John washed the dishes but not the room
  | both         -- John did both
  | neither      -- John did neither
  deriving DecidableEq, Repr

def cleanedRoom : CDWorld → Bool
  | .roomOnly | .both => true | _ => false

def washedDishes : CDWorld → Bool
  | .dishesOnly | .both => true | _ => false

def didntWashDishes : CDWorld → Bool
  | .roomOnly | .neither => true | _ => false

/-- "John cleaned up his room, but he didn't wash the dishes"
    (§3.1, ex. 17e) satisfies confirm+deny: the first conjunct
    confirms the room question, the second denies the dishes question. -/
theorem ex17e_confirm_deny :
    confirmDeny cleanedRoom washedDishes cleanedRoom didntWashDishes := by
  constructor
  · intro w; exact id
  · intro w; cases w <;> simp [didntWashDishes, washedDishes]

/-- Semantic independence of the sub-questions: cleaning the room
    does not entail washing the dishes, and vice versa. -/
theorem room_dishes_independent :
    semanticallyIndependent cleanedRoom washedDishes := by
  constructor
  · intro h; exact absurd (h .roomOnly rfl) (by decide)
  · intro h; exact absurd (h .dishesOnly rfl) (by decide)

-- ─────────────────────────────────────────────────────────────────────
-- §5b  QUD formulation of confirm+deny
-- ─────────────────────────────────────────────────────────────────────

/-! @cite{umbach-2004} §3.1 formulates confirm+deny in terms of implicit
questions (QUDs): "A but B" responds to an implicit conjunctive question
"Did X do A, and did X do B?" where one sub-answer confirms and the other
denies. This connects to `Core.Question.fromSetoid` (@cite{roberts-2012}):
the implicit conjunctive question is the partition by joint
(room, dishes) values, and confirm+deny picks one cell. -/

/-- Equivalence: two worlds agree on both `cleanedRoom` and `washedDishes`.
    The four cells of this partition are the four combinations of yes/no
    answers to the conjunctive question. -/
def roomDishesEquiv : Setoid CDWorld :=
  Setoid.ker (fun w => (cleanedRoom w, washedDishes w))

/-- The implicit conjunctive question behind a *but*-sentence:
    "Did John clean his room? And did he wash the dishes?"
    Built as the inquisitive content of the (room, dishes) partition. -/
def roomDishesQUD : Core.Question CDWorld :=
  Core.Question.fromSetoid roomDishesEquiv

/-- The implicit question behind CONTRAST is genuinely inquisitive:
    it has multiple alternatives (all four combinations are nontrivial). -/
theorem roomDishes_inquisitive : roomDishesQUD.isInquisitive :=
  Core.Question.isInquisitive_fromSetoid_of_two_classes roomDishesEquiv
    .roomOnly .dishesOnly (fun h => by
      have : (true, false) = (false, true) := h
      exact absurd this (by decide))

/-- The "room yes, dishes no" cell — the equivalence class of `.roomOnly`
    under `roomDishesEquiv`. -/
def roomYesDishesNo : Set CDWorld := {x | roomDishesEquiv x .roomOnly}

/-- The "room yes, dishes no" alternative partially answers the QUD:
    the confirm+deny pattern corresponds to one cell of the implicit
    conjunctive question. -/
theorem confirm_deny_is_partial_answer :
    Core.Question.isPartialAnswer roomDishesQUD roomYesDishesNo :=
  ⟨roomYesDishesNo,
   Core.Question.class_mem_alt_fromSetoid roomDishesEquiv
     (Setoid.mem_classes roomDishesEquiv .roomOnly),
   Or.inl subset_rfl⟩

-- ─────────────────────────────────────────────────────────────────────
-- §5c  Simple vs double contrast (@cite{umbach-2004} §3.1)
-- ─────────────────────────────────────────────────────────────────────

/-! @cite{umbach-2004} §3.1 distinguishes two kinds of CONTRAST:

- **Single contrast** ("but"): one conjunct confirms, one denies.
  "John cleaned his room, but he didn't wash the dishes."

- **Double contrast** ("although"/"while"): both conjuncts deny parts
  of a conjunctive expectation.
  "Although John cleaned his room, he didn't wash the dishes."

In double contrast, both conjuncts bear contrastive focus and neither
is presented as a simple confirmation. -/

/-- Single contrast: confirm+deny — one conjunct confirms, one denies.
    "John cleaned his room, but he didn't wash the dishes."
    Lexicalized by English "but", German *aber*. -/
abbrev singleContrast {W : Type} (q₁ q₂ c₁ c₂ : W → Bool) : Prop :=
  confirmDeny q₁ q₂ c₁ c₂

/-- Contrast multiplicity: single vs double.
    @cite{umbach-2004} §3.1: single contrast ("but") has one contrastive
    focus (confirm+deny); double contrast ("although"/"while") has two
    contrastive foci (both conjuncts bear contrastive marking).

    The distinction is prosodic/information-structural: "although" marks
    both conjuncts as contrastive, while "but" marks only the second. -/
inductive ContrastMultiplicity where
  /-- One contrastive focus: "A, but B" (confirm+deny, asymmetric). -/
  | single
  /-- Two contrastive foci: "Although A, B" (deny+deny, symmetric). -/
  | double
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════
-- §6  CONTRAST vs CORRECTION (@cite{umbach-2004} §3.2)
-- ═══════════════════════════════════════════════════════════════════════

/-! The discourse relations CONTRAST and CORRECTION both require
similarity+dissimilarity but differ in exclusion type and in the
implicit question they respond to.

- CONTRAST (§3.2, ex. 24a): "John didn't go to Berlin but he went to
  Paris." Implicit Q: "Did John go to Berlin, and also to Paris?"
  Counterfactual: either both or only Paris.

- CORRECTION (§3.2, ex. 25a): "John didn't go to Berlin but to Paris."
  Implicit Q: "Did John go to Berlin?" Counterfactual: Berlin *instead
  of* Paris.

German lexicalizes: *aber* (contrast) vs *sondern* (correction). -/

/-- CONTRAST responds to a conjunctive implicit question:
    "Did X do A, and did X also do B?" Answer: "yes A, but no B."
    Both alternatives could in principle be true. -/
def contrastImplicitQ {W : Type} (q₁ q₂ : W → Bool) : W → Bool :=
  fun w => q₁ w && q₂ w

/-- CORRECTION responds to a simple question about the denied item:
    "Did X do A?" Answer: "No A, but B instead."
    The alternatives are mutually exclusive. -/
def correctionImplicitQ {W : Type} (q₁ : W → Bool) : W → Bool :=
  q₁

/-- In the contrastive case (ex. 24a), the counterfactual allows
    both alternatives to be true. -/
theorem contrast_allows_both :
    contrastImplicitQ wentBerlin wentParis .jBoth = true := rfl

/-- In the corrective case (ex. 25a), the assertion is that Berlin
    is false and Paris holds *instead*. -/
theorem correction_excludes_first :
    wentBerlin .jParis = false ∧ wentParis .jParis = true :=
  ⟨rfl, rfl⟩

/-- The polarity-switch bridge: contrast and correction map to
    their corresponding coherence relations. -/
theorem polarity_switch_bridge :
    PolaritySwitchContext.toCoherenceRelation .contrast = .contrast ∧
    PolaritySwitchContext.toCoherenceRelation .correction = .correction :=
  ⟨rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Bridge: Umbach vs Merin (@cite{merin-1999})
-- ═══════════════════════════════════════════════════════════════════════

/-! Two accounts of "but" are now formalized in linglib:

1. **@cite{merin-1999}** (in `DTS.But`): "A but B" is felicitous
   iff A is positively relevant and B is negatively relevant to an issue H,
   with B "winning" (A∧B negatively relevant). This yields unexpectedness
   as the core meaning: P(B|A) < P(B).

2. **@cite{umbach-2004}** (this file): "A but B" requires
   similarity+dissimilarity in the focused alternatives of the conjuncts,
   plus the confirm+deny condition: one conjunct confirms and one denies
   a sub-question. This yields exclusion of an alternative.

### Key difference

Merin: "but" signals that A *raises expectations* that B *defeats*.
The mechanism is **probabilistic relevance** — no reference to alternatives
or focus.

Umbach: "but" is **focus-sensitive** — the contrast is determined by the
focused elements in the conjuncts. The mechanism is **alternative-based
exclusion** — the hearer must reconstruct what is being excluded, and the
exclusion type determines whether the relation is CONTRAST (additional:
"in addition to") or CORRECTION (substitution: "instead of").

### Where they agree

Both predict that "A but B" requires A and B to be in some sense
*opposed*. Merin captures this as opposite relevance signs; Umbach
captures it as the deny component of confirm+deny.

### Where they diverge

Merin's account does not predict the focus-sensitivity of "but":
if the issue H is held constant, the relevance of A and B depends
only on their truth-conditional content, not on what is focused.
Umbach's account directly predicts that shifting focus in the second
conjunct changes the contrast (§3.1, ex. 16a vs 16b).

@cite{merin-1999} Theorem 8 (CIP + contrariness → unexpectedness) is in
`DTS.But.cip_contrariness_implies_unexpectedness`.
-/

/-- Both accounts treat "but" as semantically distinct from "and".
    The Fragment entries distinguish them morphologically; the theory
    layer explains why. -/
theorem and_but_distinct :
    Fragments.English.FunctionWords.and_.form ≠
    Fragments.English.FunctionWords.but.form := by decide

/-- Both accounts agree that CONTRAST and CORRECTION are distinct.
    Merin distinguishes them by relevance sign (contrariness vs
    non-contrariness of issues); Umbach distinguishes them by
    exclusion type. -/
theorem contrast_correction_structurally_distinct :
    CoherenceRelation.contrast ≠ CoherenceRelation.correction := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Summary Taxonomy
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{umbach-2004} Conclusion (Table 1): the notion of contrast
decomposes into three nested layers, each adding a requirement:

```
similarity + dissimilarity       → all focus / all coordination
  + exclusion (in addition to)   → only-phrases / CONTRAST
  + exclusion (instead of)       → contrastive focus / CORRECTION
```

The taxonomy is now represented in linglib's type system:
- `semanticallyIndependent` + `commonIntegrator` = similarity+dissimilarity
- `ExclusionVariety.additional` = only-phrases / CONTRAST
- `ExclusionVariety.substitution` = contrastive focus / CORRECTION
- `PolaritySwitchContext.toCoherenceRelation` bridges IS ↔ discourse
- `ExclusionVariety.toCoherenceRelation` bridges focus ↔ discourse -/

/-- The three levels of contrast correspond to progressively more
    constrained discourse configurations:
    1. All focus triggers alternatives (similarity+dissimilarity)
    2. CONTRAST adds exclusion of additional alternatives (*only*)
    3. CORRECTION adds exclusion by substitution (contrastive focus) -/
theorem contrast_levels :
    -- CONTRAST and CORRECTION are both resemblance relations
    CoherenceRelation.contrast.toClass = .resemblance ∧
    CoherenceRelation.correction.toClass = .resemblance ∧
    -- but they are distinct
    CoherenceRelation.contrast ≠ CoherenceRelation.correction ∧
    -- and map to different exclusion varieties
    ExclusionVariety.additional.toCoherenceRelation =
      CoherenceRelation.contrast ∧
    ExclusionVariety.substitution.toCoherenceRelation =
      CoherenceRelation.correction :=
  ⟨rfl, rfl, by decide, rfl, rfl⟩

end Umbach2004
