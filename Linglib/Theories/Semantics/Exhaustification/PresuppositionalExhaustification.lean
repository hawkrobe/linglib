import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Theories.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional Exhaustification (pex)
@cite{delpinal-bassi-sauerland-2024} @cite{bassi-delpinal-sauerland-2021}

Formalization of @cite{delpinal-bassi-sauerland-2024} "Free choice and
presuppositional exhaustification" Semantics & Pragmatics 17, Article 3: 1–52.

## Core idea

Standard exhaustification (**exh**) produces flat, fully assertive output:
it asserts the prejacent plus negated IE alternatives plus II alternatives.
**pex** splits this output into two dimensions:

- **asserts**: only the prejacent φ
- **presupposes**: (i) the negation of each IE alternative, and
  (ii) a *homogeneity presupposition* — that all II alternatives have the
  same truth value

This structuring is the mirror image of **only**: *only* presupposes its
prejacent and asserts the negation of alternatives.

## Why it matters

The assertive/presuppositional split lets pex derive:
1. Free choice for ◇∨ from local application
2. Double prohibition for ¬◇∨ from negation over pex's assertive component
3. Negative FC for ¬□∧ analogously
4. Correct predictions for embedded FC puzzles (under negative factives,
   in disjunctions, under quantifiers) via standard presupposition
   projection and filtering

Standard **exh** cannot solve these embedded puzzles because its output is
flat — negation, factives, and filtering operators cannot distinguish
assertive from presuppositional content.

## Architecture

`pexIEII` takes the same IE/II computation from `Operators.lean` and
produces a `PrProp World` — a Prop-based partial proposition with separate
assertive and presuppositional components. This directly integrates with
the presupposition projection infrastructure in `Core.Semantics.Presupposition`.

For embedding under factives and filtering connectives (§3–§5 of the paper),
see the study file `Phenomena/Modality/Studies/DelPinalBassiSauerland2024.lean`.
-/

namespace Exhaustification.Presuppositional

open Exhaustification
open Exhaustification.FreeChoice
open Core.Presupposition (PrProp)

variable {World : Type*}

-- ============================================================================
-- SECTION 2: Homogeneity
-- ============================================================================

/-!
## Homogeneity

A set of propositions is **homogeneous** at a world `w` when all members
agree on their truth value at `w`: either all true or all false.

This captures the presupposition triggered by pex for II alternatives.
For FC: the II alternatives are ◇p and ◇q, so homogeneity gives ◇p ↔ ◇q.
-/

/-- Homogeneity: all propositions in a set have the same truth value.
    For the empty set, homogeneity holds vacuously. -/
def homogeneous (S : Set (Prop' World)) (w : World) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, (α w ↔ β w)

/-- Homogeneity over a two-element set is biconditional. -/
theorem homogeneous_pair (p q : Prop' World) (w : World) :
    homogeneous {p, q} w ↔ (p w ↔ q w) := by
  constructor
  · intro h
    exact h p (Set.mem_insert _ _) q (Set.mem_insert_of_mem _ rfl)
  · intro hiff α hα β hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      first | exact Iff.rfl | exact hiff | exact hiff.symm

/-- Homogeneity + at-least-one-holds → all hold. -/
theorem homogeneous_and_exists_imp_all (S : Set (Prop' World)) (w : World)
    (hHomog : homogeneous S w) (α : Prop' World) (hα : α ∈ S) (ha : α w) :
    ∀ β ∈ S, β w :=
  fun β hβ => (hHomog α hα β hβ).mp ha

-- ============================================================================
-- SECTION 3: pex^{IE+II}
-- ============================================================================

/-!
## pex^{IE+II}: Presuppositional Exhaustification

Definition (9) from the paper. For a structure φ of propositional type
and a local context c:

⟦pex^{IE+II}(φ)⟧:
  a. **asserts**: ⟦φ⟧
  b. **presupposes**:
     (i) ⋀{¬⟦ψ⟧ : ψ ∈ IE(φ) ∧ ⟦ψ⟧ ∈ Rₓ}
     (ii) homogeneity over relevant II alternatives

We treat Rₓ (the relevance predicate) as a parameter; for basic cases
all alternatives are relevant.
-/

/-- **pex^{IE+II}**: Presuppositional exhaustification with IE and II.

    Unlike `exhIEII` which returns `Prop' World` (flat, fully assertive),
    `pexIEII` returns `PrProp World` (assertive + presuppositional).

    - **assertion** = φ (the prejacent)
    - **presupposition** = (negation of relevant IE alternatives) ∧
                           (homogeneity of relevant II alternatives) -/
def pexIEII (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World)) : PrProp World where
  assertion := φ
  presup := fun w =>
    -- (i) all relevant IE alternatives are false
    (∀ ψ, isInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w) ∧
    -- (ii) relevant II alternatives are homogeneous
    homogeneous {α ∈ II ALT φ | α ∈ Rc} w

/-- pex with all alternatives relevant (the default case). -/
def pexIEII_full (ALT : Set (Prop' World)) (φ : Prop' World) : PrProp World :=
  pexIEII ALT φ ALT

-- ============================================================================
-- SECTION 4: Basic Properties
-- ============================================================================

/-- pex asserts the prejacent. -/
theorem pex_assertion_eq (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World)) :
    (pexIEII ALT φ Rc).assertion = φ := rfl

/-- The overall meaning of pex (presupposition ∧ assertion) entails φ. -/
theorem pex_holds_entails_prejacent (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World)) (w : World)
    (h : (pexIEII ALT φ Rc).holds w) : φ w :=
  h.2

/-- Negation applies only to the assertive component; presupposition projects. -/
theorem pex_neg_assertion (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World)) :
    ((pexIEII ALT φ Rc).neg).assertion = fun w => ¬φ w := rfl

/-- Negation preserves the presupposition (projection from under negation). -/
theorem pex_neg_presup (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World)) :
    ((pexIEII ALT φ Rc).neg).presup = (pexIEII ALT φ Rc).presup := rfl

-- ============================================================================
-- SECTION 5: Free Choice Derivation (§2.2)
-- ============================================================================

/-!
## Free Choice via pex

For ◇∨-sentences:
- φ = ◇(p ∨ q) = `permAorB`
- ALT = {◇(p ∨ q), ◇p, ◇q, ◇(p ∧ q)} = `fcALT`
- IE = {◇(p ∧ q)}
- II = {◇p, ◇q}

**pex^{IE+II}[◇(p ∨ q)]**:
  asserts: ◇(p ∨ q)
  presupposes: ¬◇(p ∧ q) ∧ (◇p ↔ ◇q)

Since ◇(p ∨ q) ∧ (◇p ↔ ◇q) entails ◇p ∧ ◇q, pex derives FC.
-/

/-- The pex output for free choice: pex^{IE+II}[◇(p ∨ q)] -/
def pexFC : PrProp FCWorld := pexIEII_full fcALT fcPrejacent

/-- FC via pex: when presupposition and assertion hold, we get ◇p ∧ ◇q.

    This is the paper's (14)–(15):
    ⟦pex^{IE+II}[◇[p ∨ q]]⟧ = ◇(p ∨ q)_{◇p↔◇q} ⊨ ◇p ∧ ◇q -/
theorem pex_fc :
    ∀ w, pexFC.holds w → permA w ∧ permB w := by
  intro w ⟨hpresup, hassert⟩
  simp only [pexFC, pexIEII_full, pexIEII] at hpresup hassert
  obtain ⟨_, hHomog⟩ := hpresup
  -- hassert : fcPrejacent w, i.e., permAorB w
  -- hHomog : homogeneous {α ∈ II fcALT fcPrejacent | α ∈ fcALT} w
  -- We need: permA and permB are in II ∩ fcALT
  have hA_II : isInnocentlyIncludable fcALT fcPrejacent permA :=
    target_in_II permA (by simp [fcALT]) trivial
      (fun u h => by cases u <;> simp_all [permAandB, permA])
  have hB_II : isInnocentlyIncludable fcALT fcPrejacent permB :=
    target_in_II permB (by simp [fcALT]) trivial
      (fun u h => by cases u <;> simp_all [permAandB, permB])
  have hA_in : permA ∈ ({α | α ∈ II fcALT fcPrejacent ∧ α ∈ fcALT} : Set _) :=
    ⟨hA_II, by simp [fcALT]⟩
  have hB_in : permB ∈ ({α | α ∈ II fcALT fcPrejacent ∧ α ∈ fcALT} : Set _) :=
    ⟨hB_II, by simp [fcALT]⟩
  -- Homogeneity gives: permA w ↔ permB w
  have hiff : permA w ↔ permB w := hHomog permA hA_in permB hB_in
  -- From fcPrejacent w: at least one of permA, permB holds
  have hAtLeastOne : permA w ∨ permB w := by
    cases w <;> simp_all [fcPrejacent, permAorB, permA, permB]
  rcases hAtLeastOne with hA | hB
  · exact ⟨hA, hiff.mp hA⟩
  · exact ⟨hiff.mpr hB, hB⟩

-- ============================================================================
-- SECTION 6: Double Prohibition (§2.2)
-- ============================================================================

/-!
## Double Prohibition via pex

For ¬◇∨-sentences, pex is applied locally below negation:

  ⟦¬[pex^{IE+II}[◇(p ∨ q)]]⟧

Negation applies to the assertive component: ¬◇(p ∨ q).
The homogeneity presupposition projects: ◇p ↔ ◇q.

Together: ¬◇(p ∨ q) ∧ (◇p ↔ ◇q) ⊨ ¬◇p ∧ ¬◇q
  (since ¬◇(p ∨ q) → ¬◇p ∧ ¬◇q in standard modal logic)

This is double prohibition — crucially derived WITHOUT dropping pex
from under negation (unlike exh-based accounts that need economy).
-/

/-- Negation of pex FC: ¬pex^{IE+II}[◇(p ∨ q)] -/
def negPexFC : PrProp FCWorld := pexFC.neg

/-- Double prohibition: the negated pex output entails ¬◇p ∧ ¬◇q.

    This is the paper's (16):
    ⟦¬[pex^{IE+II}[◇[T ∨ B]]]⟧ = ¬◇(T ∨ B)_{◇T↔◇B} ⊨ ¬◇T ∧ ¬◇B -/
theorem pex_double_prohibition :
    ∀ w, negPexFC.holds w → ¬permA w ∧ ¬permB w := by
  intro w ⟨hpresup, hassert⟩
  simp only [negPexFC, PrProp.neg,
             pexFC, pexIEII_full, pexIEII] at hpresup hassert
  -- hassert : ¬fcPrejacent w, i.e., ¬permAorB w
  -- ¬permAorB w → ¬permA w ∧ ¬permB w
  constructor
  · intro hA; exact hassert (by cases w <;> simp_all [fcPrejacent, permAorB, permA])
  · intro hB; exact hassert (by cases w <;> simp_all [fcPrejacent, permAorB, permB])

-- ============================================================================
-- SECTION 7: Negative FC for ¬□∧ (§2.2)
-- ============================================================================

/-!
## Negative Free Choice

For ¬□(p ∧ q)-sentences:
- φ = ¬□(p ∧ q)
- The pex output presupposes ¬□p ↔ ¬□q

Combined with ¬□(p ∧ q), this entails ¬□p ∧ ¬□q.

This result is stated as a pure entailment theorem: the interaction
of the assertion ¬□(p ∧ q) and homogeneity ¬□p ↔ ¬□q suffices for
negative FC, regardless of how IE/II are computed.
-/

/-- Negative FC entailment: ¬□(p ∧ q) + homogeneity(¬□p, ¬□q) → ¬□p ∧ ¬□q.

    This is the paper's (19a):
    ⟦pex^{IE+II}[¬□[T ∧ B]]⟧ = (¬□T ∨ ¬□B)_{¬□T↔¬□B} ⊨ ¬□T ∧ ¬□B -/
theorem negative_fc_entailment {W : Type*}
    (boxP boxQ : Prop' W) (w : W)
    (hassert : ¬(boxP w ∧ boxQ w))
    (hhomog : (¬boxP w) ↔ (¬boxQ w)) :
    ¬boxP w ∧ ¬boxQ w := by
  -- hassert: ¬(□p ∧ □q), i.e., ¬□p ∨ ¬□q
  -- hhomog: ¬□p ↔ ¬□q
  -- From ¬(□p ∧ □q): at least one of ¬□p, ¬□q holds
  -- By homogeneity: both hold
  constructor
  · intro hP
    -- □p holds → ¬(¬□p) → ¬(¬□q) by homogeneity → □q → □p ∧ □q → contradiction
    exact hassert ⟨hP, by_contra fun hNQ => absurd (hhomog.mpr hNQ) (not_not.mpr hP)⟩
  · intro hQ
    exact hassert ⟨by_contra fun hNP => absurd (hhomog.mp hNP) (not_not.mpr hQ), hQ⟩

-- ============================================================================
-- SECTION 7b: Negative FC via pex Computation (§2.2)
-- ============================================================================

/-!
## Negative FC via pex: Full Computation

The entailment theorem above (`negative_fc_entailment`) shows that the
entailment pattern works. But the paper's derivation (18a–e) involves
actually computing IE and II for ¬□(p∧q). Here we show that this
computation reduces to the existing ◇∨ computation by duality.

The key observation: the alternative set for ¬□(p∧q) is
{¬□(p∧q), ¬□p, ¬□q, ¬□(p∨q)}, which is **isomorphic** to the ◇∨
alternative set {◇(a∨b), ◇a, ◇b, ◇(a∧b)} under the mapping:

| ¬□ world | ◇ world | Reinterpretation |
|----------|---------|------------------|
| ¬□(p∧q)  | ◇(a∨b)  | notReqAandB = fcPrejacent |
| ¬□p      | ◇b      | notReqA = permB |
| ¬□q      | ◇a      | notReqB = permA |
| ¬□(p∨q)  | ◇(a∧b)  | notReqAorB = permAandB |

This isomorphism holds because ¬□ propositions obey the same
entailment structure as ◇ propositions (by modal duality).
Consequently, `pexFC` simultaneously derives both positive FC
(◇a ∧ ◇b) and negative FC (¬□p ∧ ¬□q) under reinterpretation.
-/

/-- ¬□p: p is not required (= ◇¬p by duality). Under the isomorphism, this
    is `permB` on `FCWorld`. -/
abbrev notReqA : Prop' FCWorld := permB

/-- ¬□q: q is not required. Under the isomorphism, this is `permA`. -/
abbrev notReqB : Prop' FCWorld := permA

/-- ¬□(p∧q): not both required. Under the isomorphism, this is
    `permAorB` = `fcPrejacent`. -/
abbrev notReqAandB : Prop' FCWorld := permAorB

/-- ¬□(p∨q): neither required. Under the isomorphism, this is
    `permAandB`. -/
abbrev notReqAorB : Prop' FCWorld := permAandB

/-- The alternative set for ¬□(p∧q) is the same set as fcALT. -/
theorem negNecALT_eq_fcALT :
    ({notReqAandB, notReqA, notReqB, notReqAorB} : Set (Prop' FCWorld)) = fcALT := by
  simp only [notReqAandB, notReqA, notReqB, notReqAorB, fcALT]
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Negative FC via pex: pex^{IE+II}[¬□(p∧q)] ⊨ ¬□p ∧ ¬□q.

    The paper's (19a): since pexFC on the ¬□-reinterpreted `FCWorld`
    entails ◇b ∧ ◇a (= permB ∧ permA), and notReqA = permB,
    notReqB = permA, we get ¬□p ∧ ¬□q. -/
theorem pex_negative_fc :
    ∀ w, pexFC.holds w → notReqA w ∧ notReqB w := by
  intro w h
  have ⟨hA, hB⟩ := pex_fc w h
  exact ⟨hB, hA⟩

/-- Double requirement for necessity: ¬pex^{IE+II}[¬□(p∧q)] gives
    the negation of negative FC — i.e., both are required: □p ∧ □q.

    This is the paper's (20):
    ⟦¬ pex^{IE+II}[¬□[T ∧ B]]⟧ = ¬(¬□T ∨ ¬□B)_{¬□T↔¬□B} ⊨ □T ∧ □B -/
theorem pex_neg_necessity_double_req :
    ∀ w, negPexFC.holds w → ¬notReqA w ∧ ¬notReqB w := by
  intro w h
  have ⟨hA, hB⟩ := pex_double_prohibition w h
  exact ⟨hB, hA⟩

-- ============================================================================
-- SECTION 8: Equivalence with exhIEII for Basic Cases (§2.1)
-- ============================================================================

/-!
## Equivalence for Non-FC Cases

For basic (non-FC) scalar sentences, pex^{IE+II} and exh^{IE+II} predict
the same overall entailments. When II is empty (no innocent inclusion),
pex reduces to asserting φ and presupposing ¬IE — matching pex^{IE}.

This is the paper's (11a): ⟦pex^{IE+II}(∃)⟧ = ⟦pex^{IE}(∃)⟧ = ∃_{¬∀}
-/

/-- For basic scalar sentences (where II ∩ Rc is empty), pex's presupposition
    reduces to just the negated IE alternatives (homogeneity is vacuous). -/
theorem pex_basic_scalar (ALT : Set (Prop' World)) (φ : Prop' World)
    (Rc : Set (Prop' World))
    (hII_empty : ∀ α, α ∈ II ALT φ → α ∈ Rc → False) (w : World) :
    (pexIEII ALT φ Rc).presup w ↔
      (∀ ψ, isInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w) := by
  simp only [pexIEII]
  constructor
  · exact fun ⟨hIE, _⟩ => hIE
  · intro hIE
    exact ⟨hIE, fun α ⟨hα_II, hα_Rc⟩ => absurd hα_Rc (fun h => hII_empty α hα_II h)⟩

-- ============================================================================
-- SECTION 9: Comparison with exhIEII
-- ============================================================================

/-!
## Structural Difference: pex vs exh

The key structural difference:

  **exh^{IE+II}(φ)** = φ ∧ ¬IE ∧ II                (flat, fully assertive)
  **pex^{IE+II}(φ)** = φ_{¬IE ∧ homog(II)}          (structured)

For FC (φ = ◇(p∨q)):
  exh: ◇(p∨q) ∧ ◇p ∧ ◇q ∧ ¬◇(p∧q)
  pex: asserts ◇(p∨q), presupposes (◇p ↔ ◇q) ∧ ¬◇(p∧q)

The overall entailments are the same (both entail ◇p ∧ ◇q), but the
at-issue structure differs. This difference is what allows pex to solve
the embedded FC puzzles that exh cannot.
-/

/-- exhIEII entails FC (from InnocentInclusion.lean). -/
theorem exhIEII_fc : ∀ w, exhIEII fcALT fcPrejacent w → permA w ∧ permB w :=
  free_choice

/-- pexIEII entails FC (proven above). -/
theorem pexIEII_fc : ∀ w, pexFC.holds w → permA w ∧ permB w :=
  pex_fc

end Exhaustification.Presuppositional
