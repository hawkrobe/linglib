import Linglib.Theories.Semantics.Exhaustification.PresuppositionalExhaustification
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding
import Linglib.Theories.Semantics.Presupposition.Accommodation
import Linglib.Phenomena.Modality.FreeChoice

/-!
# @cite{delpinal-bassi-sauerland-2024} — Free Choice and Presuppositional Exhaustification
@cite{delpinal-bassi-sauerland-2024} @cite{bassi-delpinal-sauerland-2021}

"Free choice and presuppositional exhaustification"
Semantics & Pragmatics 17, Article 3: 1–52.

## Core Contribution

**pex^{IE+II}** (presuppositional exhaustification) derives free choice by
splitting the output of exhaustification into assertive and presuppositional
components:

- **asserts**: the prejacent φ
- **presupposes**: negation of IE alternatives + homogeneity over II alternatives

This structural split solves embedded FC puzzles that flat exh cannot:
1. **§2**: Basic FC, double prohibition, negative FC (from local pex)
2. **§3**: Presupposed FC under negative factives ("Noah is unaware...")
3. **§4**: Filtering FC in disjunction ("Either Maria can't... or she can...")
4. **§5**: FC under universal, existential, and non-monotonic quantifiers

## Architecture

The core operator `pexIEII` is defined in
`Theories/Semantics/Exhaustification/PresuppositionalExhaustification.lean`.
This file connects pex to empirical free choice data and formalizes the
embedding puzzles from §3–§5.
-/

set_option autoImplicit false

namespace DelPinalBassiSauerland2024

open Core.Presupposition (PrProp)
open Core.CommonGround (ContextSet)
open Exhaustification.Presuppositional
open Exhaustification.FreeChoice
open Exhaustification
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.BeliefEmbedding
open Semantics.Presupposition.Accommodation

-- ============================================================================
-- §1. Bridge: pex Predicts FC Data
-- ============================================================================

/-!
## Bridge to Phenomena

pex predicts that free choice is a pragmatic inference (derived by the
covert operator pex), not a semantic entailment. This matches the empirical
data in `Phenomena.Modality.FreeChoice`.
-/

/-- FC is pragmatic (not semantic), matching empirical data -/
theorem fc_is_pragmatic :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

/-- FC is captured pragmatically -/
theorem fc_is_captured :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

-- ============================================================================
-- §2. Presupposed FC Under Negative Factives (§3)
-- ============================================================================

/-!
## §3: The "Unaware" Puzzle

Consider: "Noah is unaware that he may have tea or cake"

**Intuition**: This presupposes that Noah may have tea AND may have cake
(FC is presupposed, not asserted).

### Analysis with pex

1. pex applies locally to ◇(t∨c), producing:
   - assertion: ◇(t∨c)
   - presupposition: ¬◇(t∧c) ∧ (◇t ↔ ◇c)

2. "Unaware" is a negative factive:
   - presupposes: its complement (the full pex output holds)
   - asserts: the subject doesn't believe it

3. The factive presupposes that pex *holds* — both assertion and
   presupposition. The homogeneity presupposition (◇t ↔ ◇c) combined
   with ◇(t∨c) entails ◇t ∧ ◇c. FC is presupposed!

### Why flat exh fails

With flat exh: exh(◇(t∨c)) = ◇(t∨c) ∧ ◇t ∧ ◇c ∧ ¬◇(t∧c)
Under "unaware": presupposes the flat conjunction, asserts ¬Bel(flat)

The problem: the subject might fail to believe the conjunction for trivial
reasons (not believing ¬◇(t∧c)), losing the FC presupposition.
With pex, the FC-relevant content (homogeneity) is already presuppositional,
so it projects independently.
-/

/-- Key theorem (§3): FC is presupposed under a negative factive.

    When pex(◇(p∨q)) is embedded under "unaware", the overall sentence
    *presupposes* ◇p ∧ ◇q (free choice as presupposition).

    Uses `PrProp.negFactive` from `Core.Semantics.Presupposition`. -/
theorem fc_presupposed_under_neg_factive
    (believes : (FCWorld → Prop) → FCWorld → Prop) :
    ∀ w, (PrProp.negFactive pexFC believes).presup w → permA w ∧ permB w :=
  fun w hpresup => pex_fc w hpresup

/-- The assertion of the negative factive embedding is about belief, not FC. -/
theorem neg_factive_asserts_nonbelief
    (believes : (FCWorld → Prop) → FCWorld → Prop) :
    ∀ w, (PrProp.negFactive pexFC believes).assertion w ↔
         ¬(believes fcPrejacent w) :=
  fun _ => Iff.rfl

-- ============================================================================
-- §3. Filtering FC (§4)
-- ============================================================================

/-!
## §4: Filtering FC in Disjunction

Consider: "Either Maria can't study linguistics, or she can study syntax
or semantics"

**Intuition**: FC inference arises — Maria can study syntax AND semantics.

### Analysis with pex

The second disjunct contains pex(◇(syn ∨ sem)):
  - assertion: ◇(syn ∨ sem)
  - presupposition: ◇syn ↔ ◇sem (homogeneity)

In disjunction "A ∨ B", the presupposition of B is *filtered* by ¬A
(@cite{karttunen-1973}). Here:
  - A = ¬◇ling
  - ¬A = ◇ling (Maria CAN study linguistics)
  - Under ◇ling, the presupposition ◇syn ↔ ◇sem is informative

The homogeneity presupposition projects (after filtering), and combined
with ◇(syn ∨ sem), derives FC.

### Why flat exh fails

With flat exh in the second disjunct: ◇(syn∨sem) ∧ ◇syn ∧ ◇sem ∧ ¬◇(syn∧sem)
The FC content is asserted, not presupposed. In disjunction, only
*presuppositions* project — assertions do not. So the FC inference is
trapped inside the second disjunct and doesn't become part of the overall
meaning.
-/

/-- When the first disjunct is false, Karttunen filtering recovers full
    satisfaction of the second disjunct.
    Uses `PrProp.disjFilterLeft` from `Core.Semantics.Presupposition`. -/
theorem filtering_recovers_pex {World : Type*}
    (firstDisjunct : World → Prop) (sp : PrProp World)
    (w : World) (hFirst : ¬firstDisjunct w)
    (hFiltered : (PrProp.disjFilterLeft firstDisjunct sp).holds w) :
    sp.holds w :=
  PrProp.disjFilterLeft_recovers firstDisjunct sp w hFirst hFiltered

/-- Corollary: filtering FC for the concrete FCWorld case.
    When filtered pex holds and the first disjunct is false, FC follows. -/
theorem filtering_fc (firstDisjunct : FCWorld → Prop) (w : FCWorld)
    (hFirst : ¬firstDisjunct w)
    (hFiltered : (PrProp.disjFilterLeft firstDisjunct pexFC).holds w) :
    permA w ∧ permB w :=
  pex_fc w (filtering_recovers_pex firstDisjunct pexFC w hFirst hFiltered)

-- ============================================================================
-- §4. Structural Comparison: pex vs exh
-- ============================================================================

/-!
## Why pex Solves Puzzles That exh Cannot

The fundamental difference is **at-issue structure**:

| | exh^{IE+II}(φ) | pex^{IE+II}(φ) |
|---|---|---|
| **Asserts** | φ ∧ ¬IE ∧ II | φ |
| **Presupposes** | nothing | ¬IE ∧ homog(II) |

This matters for embedding:

1. **Under negation**: Negation targets assertions, not presuppositions.
   - ¬exh(φ) = ¬(φ ∧ ¬IE ∧ II) — FC lost under negation
   - ¬pex(φ) = ¬φ with presup intact — double prohibition

2. **Under factives**: Factives presuppose their complement.
   - aware(exh(φ)) presupposes the flat conjunction — muddled
   - aware(pex(φ)) presupposes φ + homogeneity — clean FC projection

3. **In disjunctions**: Only presuppositions project/filter.
   - A ∨ exh(φ): FC trapped in assertion, doesn't project
   - A ∨ pex(φ): homogeneity presupposition projects, FC derives
-/

/-- Key structural fact: pex and exh agree on what they entail (both derive FC),
    but disagree on at-issue structure (assert vs presuppose). -/
theorem both_derive_fc :
    (∀ w, pexFC.holds w → permA w ∧ permB w) ∧
    (∀ w, exhIEII fcALT fcPrejacent w → permA w ∧ permB w) :=
  ⟨pex_fc, free_choice⟩

/-- pex's presupposition projects through negation (by construction). -/
theorem presup_projects_through_negation :
    pexFC.neg.presup = pexFC.presup := rfl

-- ============================================================================
-- §5. Negative FC and Presupposed Negative FC (§2.2, §3.3)
-- ============================================================================

/-!
## Negative FC

The duality isomorphism (PresuppositionalExhaustification.lean §7b) gives
negative FC from the same `FCWorld` computation. Here we verify the
embedded predictions.

### §3.3: Presupposed negative FC under negative factives

"Noah is unaware that Olivia is not required to take Logic and Algebra"

Presupposes: ¬□L ∧ ¬□A (negative FC). The solution parallels §3.2:
pex applies locally, the negative factive presupposes the full pex output,
and the homogeneity ¬□L ↔ ¬□A combined with ¬□(L∧A) entails ¬□L ∧ ¬□A.
-/

/-- Presupposed negative FC: under a negative factive, pex presupposes
    ¬□L ∧ ¬□A (negative free choice). -/
theorem negative_fc_presupposed_under_neg_factive
    (believes : (FCWorld → Prop) → FCWorld → Prop) :
    ∀ w, (PrProp.negFactive pexFC believes).presup w → notReqA w ∧ notReqB w :=
  fun w hpresup => pex_negative_fc w hpresup

/-- Filtering negative FC: when the first disjunct is false, the filtered
    presupposition of the second disjunct recovers negative FC. -/
theorem filtering_negative_fc (firstDisjunct : FCWorld → Prop) (w : FCWorld)
    (hFirst : ¬firstDisjunct w)
    (hFiltered : (PrProp.disjFilterLeft firstDisjunct pexFC).holds w) :
    notReqA w ∧ notReqB w :=
  pex_negative_fc w (filtering_recovers_pex firstDisjunct pexFC w hFirst hFiltered)

-- ============================================================================
-- §6. FC Under Quantifiers (§5.1)
-- ============================================================================

/-!
## §5.1: Universal, Existential, and Negative-Existential FC

@cite{chemla-2009b} shows that ∀◇∨-sentences have universal FC readings
and ¬∃□∧-sentences have universal negative FC readings.

### Analysis with embedded pex

The LFs with embedded pex^{IE+II}:
- ∀x ∈ S[pex^{IE+II}[◇[Cx ∨ ICx]]]
- ¬∃x ∈ S[pex^{IE+II}[□[Ax ∧ Bx]]]
- ∃x ∈ S[pex^{IE+II}[◇[Cx ∨ ICx]]]

pex triggers the homogeneity presupposition in the scope of the quantifier.
Presuppositions project universally from the scope of universal quantifiers
(@cite{chemla-2009a}, @cite{fox-2013}, @cite{mayr-sauerland-2015}).
Combined with the assertive content, (universal/existential) FC follows.
-/

/-- Universal FC: universally projected homogeneity + universal assertion
    entails universal FC. -/
theorem universal_fc {Student : Type*}
    (S : Student → Prop) (permC permIC : Student → Prop)
    (hassert : ∀ x, S x → (permC x ∨ permIC x))
    (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    (∀ x, S x → permC x) ∧ (∀ x, S x → permIC x) := by
  constructor
  · intro x hx
    rcases hassert x hx with hC | hIC
    · exact hC
    · exact (hhomog x hx).mpr hIC
  · intro x hx
    rcases hassert x hx with hC | hIC
    · exact (hhomog x hx).mp hC
    · exact hIC

/-- Universal negative FC: universally projected homogeneity + negated
    existential assertion entails universal negative FC. -/
theorem universal_negative_fc {Student : Type*}
    (S : Student → Prop) (reqA reqB : Student → Prop)
    (hassert : ¬∃ x, S x ∧ (reqA x ∧ reqB x))
    (hhomog : ∀ x, S x → (reqA x ↔ reqB x)) :
    (¬∃ x, S x ∧ reqA x) ∧ (¬∃ x, S x ∧ reqB x) := by
  constructor
  · intro ⟨x, hx, hA⟩
    exact hassert ⟨x, hx, hA, (hhomog x hx).mp hA⟩
  · intro ⟨x, hx, hB⟩
    exact hassert ⟨x, hx, (hhomog x hx).mpr hB, hB⟩

/-- Existential FC: universally projected homogeneity + existential assertion
    entails existential FC.

    ∃x ∈ S[pex^{IE+II}[◇[Cx ∨ ICx]]] yields:
    - presupposes: ∀x ∈ S(◇Cx ↔ ◇ICx)  (universal projection)
    - asserts: ∃x ∈ S(◇(Cx ∨ ICx))

    Together: ∃x ∈ S(◇Cx ∧ ◇ICx). -/
theorem existential_fc {Student : Type*}
    (S : Student → Prop) (permC permIC : Student → Prop)
    (hassert : ∃ x, S x ∧ (permC x ∨ permIC x))
    (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    ∃ x, S x ∧ permC x ∧ permIC x := by
  obtain ⟨x, hx, hDisj⟩ := hassert
  exact ⟨x, hx, by
    rcases hDisj with hC | hIC
    · exact ⟨hC, (hhomog x hx).mp hC⟩
    · exact ⟨(hhomog x hx).mpr hIC, hIC⟩⟩

/-- Universal FC via `PrProp.forallPr`: when each student's pex output
    holds (presupposition projected universally + assertion holds),
    universal FC follows.

    This connects the abstract entailment theorems above to the concrete
    `forallPr` combinator from `Core.Semantics.Presupposition`. -/
theorem forallPr_fc {Student W : Type*}
    (S : Student → Prop) (pexPerStudent : Student → PrProp W) (w : W)
    (projA projB : Student → Prop' W)
    (hFC : ∀ x, S x → (pexPerStudent x).holds w →
      projA x w ∧ projB x w)
    (hHolds : (PrProp.forallPr S pexPerStudent).holds w) :
    (∀ x, S x → projA x w) ∧ (∀ x, S x → projB x w) := by
  obtain ⟨hPresup, hAssert⟩ := hHolds
  constructor
  · intro x hx; exact (hFC x hx ⟨hPresup x hx, hAssert x hx⟩).1
  · intro x hx; exact (hFC x hx ⟨hPresup x hx, hAssert x hx⟩).2

/-- Existential FC via `PrProp.existsPrUniv`: with universal presupposition
    projection from an existential quantifier, we get existential FC.

    This connects the existential entailment theorem to the concrete
    `existsPrUniv` combinator from `Core.Semantics.Presupposition`. -/
theorem existsPrUniv_fc {Student W : Type*}
    (S : Student → Prop) (pexPerStudent : Student → PrProp W) (w : W)
    (projA projB : Student → Prop' W)
    (hFC : ∀ x, S x → (pexPerStudent x).holds w →
      projA x w ∧ projB x w)
    (hHolds : (PrProp.existsPrUniv S pexPerStudent).holds w) :
    ∃ x, S x ∧ projA x w ∧ projB x w := by
  obtain ⟨hPresup, ⟨x, hx, hAssert⟩⟩ := hHolds
  exact ⟨x, hx, hFC x hx ⟨hPresup x hx, hAssert⟩⟩

/-- Universal negative FC via `PrProp.negExistsPr`: with universal
    presupposition projection and negated existential assertion,
    universal negative FC follows.

    This connects `universal_negative_fc` to the concrete
    `negExistsPr` combinator from `Core.Semantics.Presupposition`,
    completing the set of quantifier bridges alongside
    `forallPr_fc` and `existsPrUniv_fc`.

    The shape differs from the positive bridges: `forallPr_fc` and
    `existsPrUniv_fc` use `hFC : holds → projA ∧ projB` (assertion
    decomposes to FC). Here, the assertion is *negated*, so we need:
    - `hAssertEq`: assertion ↔ reqA ∧ reqB (decomposition)
    - `hHomog`: presup → reqA ↔ reqB (homogeneity)
    These are exactly the inputs to `universal_negative_fc`. -/
theorem negExistsPr_negative_fc {Student W : Type*}
    (S : Student → Prop) (pexPerStudent : Student → PrProp W) (w : W)
    (reqA reqB : Student → Prop' W)
    (hAssertEq : ∀ x, S x → ((pexPerStudent x).assertion w ↔
      (reqA x w ∧ reqB x w)))
    (hHomog : ∀ x, S x → (pexPerStudent x).presup w →
      (reqA x w ↔ reqB x w))
    (hHolds : (PrProp.negExistsPr S pexPerStudent).holds w) :
    (¬∃ x, S x ∧ reqA x w) ∧ (¬∃ x, S x ∧ reqB x w) := by
  obtain ⟨hPresup, hNegAssert⟩ := hHolds
  exact universal_negative_fc S (fun x => reqA x w) (fun x => reqB x w)
    (fun ⟨x, hx, hAB⟩ => hNegAssert ⟨x, hx, (hAssertEq x hx).mpr hAB⟩)
    (fun x hx => hHomog x hx (hPresup x hx))

-- ============================================================================
-- §6b. FC Under Non-Monotonic Quantifiers (§5.2)
-- ============================================================================

/-!
## §5.2: Non-Monotonic Quantifiers

@cite{gotzner-romoli-santorio-2020} show that "exactly one"-sentences have
salient readings where one student has FC/double prohibition while all others
have the opposite. pex handles these straightforwardly via universal
homogeneity projection + the cardinality constraint.

### (76): "Exactly one student can take Logic or Calculus"

The LF: ∃!x ∈ S[pex^{IE+II}[◇[Lx ∨ Cx]]]

pex triggers homogeneity ◇Lx ↔ ◇Cx universally (for all students).
The assertive part says exactly one student satisfies ◇(Lx ∨ Cx).

Combined:
- The unique student has ◇(L ∨ C) ∧ (◇L ↔ ◇C) → ◇L ∧ ◇C (FC)
- All other students have ¬◇(L ∨ C) ∧ (◇L ↔ ◇C) → ¬◇L ∧ ¬◇C (double prohibition)

### (77): "Exactly one student can't take Logic or Calculus"

The LF: ∃!x ∈ S[¬ pex^{IE+II}[◇[Lx ∨ Cx]]]

Combined:
- The unique student has ¬◇(L ∨ C) ∧ (◇L ↔ ◇C) → ¬◇L ∧ ¬◇C (double prohibition)
- All other students have ◇(L ∨ C) ∧ (◇L ↔ ◇C) → ◇L ∧ ◇C (FC)
-/

/-- Non-monotonic FC (76a): universal homogeneity + "exactly one has ◇∨"
    entails that the unique student has FC and all others have double
    prohibition.

    @cite{gotzner-romoli-santorio-2020}, @cite{delpinal-bassi-sauerland-2024} §5.2 -/
theorem exactly_one_fc {Student : Type*}
    (S : Student → Prop) (permL permC : Student → Prop)
    (witness : Student) (hw : S witness)
    (hassert_pos : permL witness ∨ permC witness)
    (hassert_neg : ∀ x, S x → x ≠ witness → ¬(permL x ∨ permC x))
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    -- The witness has FC
    (permL witness ∧ permC witness) ∧
    -- All others have double prohibition
    (∀ x, S x → x ≠ witness → ¬permL x ∧ ¬permC x) := by
  constructor
  · rcases hassert_pos with hL | hC
    · exact ⟨hL, (hhomog witness hw).mp hL⟩
    · exact ⟨(hhomog witness hw).mpr hC, hC⟩
  · intro x hx hne
    have hNotDisj := hassert_neg x hx hne
    exact ⟨fun hL => hNotDisj (Or.inl hL), fun hC => hNotDisj (Or.inr hC)⟩

/-- Non-monotonic FC (77a): universal homogeneity + "exactly one lacks ◇∨"
    entails that the unique student has double prohibition and all others
    have FC.

    @cite{gotzner-romoli-santorio-2020}, @cite{delpinal-bassi-sauerland-2024} §5.2 -/
theorem exactly_one_double_prohibition {Student : Type*}
    (S : Student → Prop) (permL permC : Student → Prop)
    (witness : Student) (_hw : S witness)
    (hassert_neg : ¬(permL witness ∨ permC witness))
    (hassert_pos : ∀ x, S x → x ≠ witness → (permL x ∨ permC x))
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    -- The witness has double prohibition
    (¬permL witness ∧ ¬permC witness) ∧
    -- All others have FC
    (∀ x, S x → x ≠ witness → permL x ∧ permC x) := by
  constructor
  · exact ⟨fun hL => hassert_neg (Or.inl hL),
           fun hC => hassert_neg (Or.inr hC)⟩
  · intro x hx hne
    rcases hassert_pos x hx hne with hL | hC
    · exact ⟨hL, (hhomog x hx).mp hL⟩
    · exact ⟨(hhomog x hx).mpr hC, hC⟩

-- ============================================================================
-- §7. Why Flat exh Fails on Embedded Puzzles (§3.1, §4.1)
-- ============================================================================

/-!
## Why Flat exh Cannot Solve the Embedded FC Puzzles

The paper's central argument is that flat **exh** (including exh^{IE+II})
cannot solve the presupposed & filtering FC puzzles because its output
is fully assertive. Here we formalize the specific failure modes.

### Failure 1: exh under negative factives (§3.1)

With exh^{IE+II}, the output for ◇(L∨A) is flat:
  exh(◇(L∨A)) = ◇(L∨A) ∧ ◇L ∧ ◇A ∧ ¬◇(L∧A)

Under "S is unaware that exh(◇(L∨A))":
  - presupposes: ◇(L∨A) ∧ ◇L ∧ ◇A ∧ ¬◇(L∧A) (the flat conjunction)
  - asserts: ¬B_S(◇(L∨A) ∧ ◇L ∧ ◇A ∧ ¬◇(L∧A))

The problem: the assertion says S doesn't believe the *whole conjunction*.
This is too weak — S might fail to believe ¬◇(L∧A) while still believing
◇L ∧ ◇A. The target is that S doesn't believe Olivia can take *either*
class individually (a stronger claim about S's beliefs).

### Failure 2: exh in filtering disjunction (§4.1)

For "Either Maria can't study linguistics, or she can study syntax or
semantics": the FC content (◇syn ∧ ◇sem) is assertive in exh's output,
so it's trapped inside the second disjunct. In disjunction, only
*presuppositions* project/filter — assertions don't. So the FC inference
cannot reach the overall sentence meaning.

With pex, FC content is presuppositional, so it projects through
disjunction via Karttunen filtering.
-/

/-- **Flat exh output**: exh^{IE+II}(◇(p∨q)) is fully assertive —
    no presuppositional component. -/
def flatExhFC : Prop' FCWorld := exhIEII fcALT fcPrejacent

/-- Negative factive embedding of FLAT exh.
    "S is unaware that exh(◇(L∨A))":
    - presupposes: the flat conjunction holds
    - asserts: S doesn't believe the flat conjunction -/
def negFactiveOfFlatExh
    (believes : (FCWorld → Prop) → FCWorld → Prop) : PrProp FCWorld where
  presup := flatExhFC
  assertion := fun w => ¬(believes flatExhFC w)

/-- **Failure 1a**: Under flat exh, the factive asserts non-belief of the
    *entire* flat conjunction (FC + exclusivity). S might fail to believe the
    conjunction by not believing ¬◇(L∧A), while still believing ◇L ∧ ◇A. -/
theorem exh_factive_asserts_flat_conjunction
    (believes : (FCWorld → Prop) → FCWorld → Prop) :
    (negFactiveOfFlatExh believes).assertion =
      (fun w => ¬(believes flatExhFC w)) := rfl

/-- **Failure 1b**: In contrast, pex's factive asserts non-belief of just the
    prejacent — the correct content for S's doxastic state. -/
theorem pex_factive_asserts_prejacent
    (believes : (FCWorld → Prop) → FCWorld → Prop) :
    (PrProp.negFactive pexFC believes).assertion =
      (fun w => ¬(believes fcPrejacent w)) := rfl

/-- **Failure 2**: When flat exh is placed in a filtering disjunction,
    the FC content is assertive and thus trapped inside the disjunct.
    Only presuppositions can project/filter in disjunctions.

    For "A ∨ exh(◇(p∨q))": the presupposition is trivial (True). -/
theorem exh_filtering_no_presupposition (firstDisjunct : FCWorld → Prop) :
    (PrProp.disjFilterLeft firstDisjunct (PrProp.ofProp' flatExhFC)).presup =
      (fun _ => True) := by
  funext; simp [PrProp.disjFilterLeft, PrProp.ofProp']

/-- pex's filtering disjunction has a non-trivial presupposition (homogeneity
    conditioned on ¬firstDisjunct). -/
theorem pex_filtering_has_presupposition (firstDisjunct : FCWorld → Prop) :
    (PrProp.disjFilterLeft firstDisjunct pexFC).presup =
      (fun w => ¬firstDisjunct w → pexFC.presup w) := rfl

-- ============================================================================
-- §8. Empirical Predictions Summary
-- ============================================================================

/-!
## Empirical Predictions

| Puzzle | exh | pex | Status |
|--------|-----|-----|--------|
| Basic FC: ◇(p∨q) → ◇p∧◇q | ✓ | ✓ | `pex_fc` |
| Double prohibition: ¬◇(p∨q) → ¬◇p∧¬◇q | needs economy | ✓ | `pex_double_prohibition` |
| Negative FC: ¬□(p∧q) → ¬□p∧¬□q | needs economy | ✓ | `pex_negative_fc` |
| FC under neg. factive | ✗ | ✓ | `fc_presupposed_under_neg_factive` |
| Filtering FC | ✗ | ✓ | `filtering_fc` |
| Universal FC | ✓ (matrix exh) | ✓ | `universal_fc` |
| Existential FC | ✗ (matrix exh) | ✓ | `existential_fc` |
| Universal neg. FC | ✗ | ✓ | `universal_negative_fc` |
| Non-monotonic FC | problematic | ✓ | `exactly_one_fc` |
| Non-monotonic DP | problematic | ✓ | `exactly_one_double_prohibition` |

pex is the mirror image of "only" (@cite{horn-1969}): *only* presupposes its
prejacent and asserts the negation of alternatives; *pex* asserts its
prejacent and presupposes the alternative-derived content. Both split meaning
into assertive and presuppositional components; they swap which goes where.

The key advantage of pex is that embedded FC puzzles are solved by
**standard presupposition projection** — no new mechanisms needed.
-/

-- ============================================================================
-- §9. Grounding: pex Predictions ← Projection Theory
-- ============================================================================

/-!
## Grounding in Projection Theory

@cite{delpinal-bassi-sauerland-2024}'s central claim is that pex solves embedded
FC puzzles using *standard presupposition projection* — no new mechanisms. We
verify this by showing each embedding prediction is derived from independently
formalized projection infrastructure:

| Prediction | Infrastructure | Bridge |
|---|---|---|
| Filtering FC (§4) | `localCtxSecondDisjunct` | `local_context_matches_disjFilterLeft` |
| Presupposed FC (§3) | `transparentProjection` | `negFactive_entails_transparent` |
| Double prohibition (§2) | `negation_preserves_projection` | definitional (`PrProp.neg`) |
| Quantificational FC (§5.1) | `forallPr`/`existsPrUniv`/`negExistsPr` | universal projection |
| Non-monotonic FC (§5.2) | universal homogeneity + cardinality | `exactly_one_fc` |
| Accommodation (§4.4) | `heimSelect` | `accommodation_grounded_in_heim` |
-/

variable {Agent : Type*}

/-- Filtering FC is grounded in Schlenker's local context algorithm.

    `filtering_fc` uses `PrProp.disjFilterLeft` as a combinator.
    `local_context_matches_disjFilterLeft` proves this is equivalent to
    filtering at Schlenker's local context for the second disjunct:
    the presupposition ψ of the second disjunct is satisfied in
    the local context c ∧ ¬A iff ∀w∈c, ¬A(w) → ψ(w). -/
theorem filtering_grounded_in_schlenker (c : ContextSet FCWorld)
    (firstDisjunct : PrProp FCWorld) (w : FCWorld) (hc : c w)
    (hFirst : ¬firstDisjunct.assertion w)
    (hSchlenkerFiltered : presupFiltered
      (localCtxSecondDisjunct (initialLocalCtx c) firstDisjunct) pexFC)
    (hassert : pexFC.assertion w) :
    permA w ∧ permB w :=
  pex_fc w ⟨hSchlenkerFiltered w ⟨hc, hFirst⟩, hassert⟩

/-- Presupposed FC is grounded in transparent projection.

    `fc_presupposed_under_neg_factive` uses `PrProp.negFactive` as a
    combinator. Here we decompose this into two steps:
    1. `negFactive_entails_transparent`: negFactive's presupposition
       (complement holds) entails transparent projection of the presup.
    2. Transparent projection + assertion → FC.

    This shows that presupposed FC is an instance of Schlenker's
    transparent projection, not a stipulated combinator. -/
theorem presupposed_fc_grounded_in_transparent
    (globalCtx : ContextSet FCWorld)
    (believes : (FCWorld → Prop) → FCWorld → Prop) (w : FCWorld)
    (hGlobal : globalCtx w)
    (hNegFactive : ∀ v, globalCtx v →
      (PrProp.negFactive pexFC believes).presup v) :
    permA w ∧ permB w := by
  -- Step 1: negFactive → transparent projection (presup holds globally)
  have hTransparent : transparentProjection globalCtx pexFC :=
    negFactive_entails_transparent pexFC believes globalCtx hNegFactive
  -- Step 2: transparent projection provides the presup; negFactive provides the assertion
  exact pex_fc w ⟨hTransparent w hGlobal, (hNegFactive w hGlobal).2⟩

/-- Opaque FC under belief embedding: when pex's presupposition is attributed
    to the attitude holder (opaque projection), the agent *believes* FC.

    "Noah believes he may have tea or cake":
    - pex applies locally: assertion = ◇(t∨c), presup = ◇t ↔ ◇c
    - Opaque projection: Noah believes ◇t ↔ ◇c
    - Combined with Noah believes ◇(t∨c): Noah believes ◇t ∧ ◇c

    Both opaque and transparent projection yield FC — they differ in
    *whose* context the inference is anchored to. -/
theorem opaque_fc_under_belief
    (blc : BeliefLocalCtx FCWorld Agent) (w_star : FCWorld)
    (hw_star : blc.globalCtx w_star)
    (hOpaque : presupAttributedToHolder blc pexFC)
    (hassert : ∀ v, blc.atWorld w_star v → pexFC.assertion v) :
    ∀ v, blc.atWorld w_star v → permA v ∧ permB v := by
  intro v hv
  exact pex_fc v ⟨hOpaque w_star hw_star v hv, hassert v hv⟩

/-- Double prohibition is grounded in negation transparency.

    `PrProp.neg` preserves presuppositions by construction (assertion negated,
    presupposition unchanged). This matches `negation_preserves_projection`:
    Schlenker's local context under negation has the same world set as the
    parent context, so presuppositions project through negation unchanged. -/
theorem negation_grounding :
    pexFC.neg.presup = pexFC.presup := rfl

/-- Accommodation is grounded in Heim's global preference.

    @cite{delpinal-bassi-sauerland-2024} §4.4: in standard cases, pex's
    homogeneity presupposition is accommodated globally (added to the
    common ground). This follows from `heimSelect` choosing global
    accommodation whenever the result is consistent.

    The bridge: when global accommodation of pex's presupposition is
    consistent, Heim's strategy selects global accommodation, matching
    the paper's prediction that homogeneity projects to the top level.

    In "enemy territory" (§4.4), local ACC blocks global projection —
    this corresponds to the case where `heimSelect` falls back to local
    because global accommodation would be inconsistent. -/
theorem accommodation_grounded_in_heim {W : Type*}
    (c : ContextSet W) (pex_output : PrProp W)
    (h_consistent : ContextSet.nonEmpty
      (globalAccommodate c pex_output.presup)) :
    heimSelect c pex_output.presup = .global :=
  heim_projection_when_consistent c pex_output.presup h_consistent

/-- When global accommodation is inconsistent (enemy territory), Heim's
    strategy falls back to local accommodation — blocking projection.
    This models the ACC operator from §4.4 that prevents homogeneity
    from projecting in hostile environments. -/
theorem enemy_territory_blocks_projection {W : Type*}
    (c : ContextSet W) (pex_output : PrProp W)
    (h_inconsistent : ¬ContextSet.nonEmpty
      (globalAccommodate c pex_output.presup)) :
    heimSelect c pex_output.presup = .local :=
  heim_cancellation_equivalence c pex_output.presup h_inconsistent

end DelPinalBassiSauerland2024
