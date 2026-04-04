import Linglib.Core.Modality.ModalTypes
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Phenomena.Modality.ModalConcord.Data

/-!
# @cite{ciardelli-guerrini-2026} — Against Wide Scope Free Choice
@cite{ciardelli-guerrini-2026} @cite{zeijlstra-2007}

Semantics and Pragmatics 19(4). 2026.

## The Reductionist Thesis

The free-choice reading of sentences like "You may A or you may B" does
NOT arise from the wide-scope LF ◇A ∨ ◇B. It arises from the narrow-scope
LF ◇(A ∨ B). There is no separate problem of "wide-scope free choice."

The two LFs are **truth-conditionally equivalent** in standard modal logic
(`diamond_distributes_iff`). The difference is compositional: only ◇(A ∨ B)
feeds into pragmatic enrichment mechanisms (exhaustification, RSA, BSML)
that derive the conjunctive free-choice inference ◇A ∧ ◇B.

## Evidence (§2)

"MOD A COORD MOD B" sentences are systematically scope-ambiguous:

| Surface form            | Wide-scope LF    | Narrow-scope LF |
|------------------------|------------------|-----------------|
| may A or may B          | ◇A ∨ ◇B         | ◇(A ∨ B)       |
| must A or must B        | □A ∨ □B         | □(A ∨ B)       |
| may A and may B         | ◇A ∧ ◇B         | ◇(A ∧ B)       |

- **Must-or-must**: "You must write an essay or you must give a presentation"
  naturally receives the narrow-scope reading □(essay ∨ presentation) —
  a disjunctive obligation, not uncertainty between two obligations.

- **May-and-may**: "You may go to Bob's party and you may go to Charlie's
  party" naturally receives the narrow-scope reading ◇(Bob ∧ Charlie) —
  permission to attend BOTH, not two separate permissions.

## Compositional Mechanism (§3)

The narrow-scope LF arises via **modal concord** (@cite{zeijlstra-2007}).
Modal auxiliaries carry uninterpretable features [u∃/∀-MOD]. When two
auxiliaries with the same feature appear in a coordination, a single
silent operator [i∃/∀-MOD] c-commands the coordination and checks both
features. The silent operator is semantically interpreted; the auxiliaries
are vacuous. This yields Δ(A ∘ B), not ΔA ∘ ΔB.

## Key Predictions (§4)

1. **Auxiliary vs non-auxiliary**: Non-auxiliary modal constructions
   ("it's ok that", "be allowed to") carry interpretable features and
   cannot participate in concord → no FC reading in coordination.

2. **Either position**: Initial "either" does not block narrow-scope
   readings, contra @cite{meyer-sauerland-2017}, because the silent
   operator can check features from above "either."

3. **Negation flips force for concord**: derived from `ModalForce.dual`
   — ALLOW[i∃](¬NEED[u∀]) is well-formed because ¬∀ = ∃ = dual(∀).

-/

namespace Phenomena.Modality.Studies.CiardelliGuerrini2026

open Core.Modality
open Exhaustification.FreeChoice (diamond pdisj diamond_distributes_iff)
open Exhaustification (pand)
open Fragments.English.FunctionWords

-- ============================================================================
-- §1. Semantic Equivalence: ◇(A∨B) ↔ ◇A ∨ ◇B
-- ============================================================================

/-!
## The Two LFs are Truth-Conditionally Equivalent

In standard modal logic, ◇(A ∨ B) ↔ ◇A ∨ ◇B. The forward direction is
`diamond_distributes` (from `Exhaustification/FreeChoice.lean`). The
reverse is trivially provable. This equivalence is *the point* of C&G:
the scope distinction cannot be detected truth-conditionally — it
matters only for compositional derivation and pragmatic enrichment.
-/

/-- **The semantic equivalence**: ◇(A ∨ B) ↔ ◇A ∨ ◇B.

    Promoted to `Exhaustification.FreeChoice.diamond_distributes_iff`.
    The scope distinction is truth-conditionally vacuous — it matters
    only for pragmatic enrichment. This is the central observation of
    @cite{ciardelli-guerrini-2026}. -/
example {World : Type*} (p q : Prop' World) :
    diamond (pdisj p q) ↔ diamond p ∨ diamond q :=
  diamond_distributes_iff p q

-- ============================================================================
-- §2. Scope Ambiguity Data
-- ============================================================================

/-- Scope availability for "MOD A COORD MOD B" sentences. -/
inductive ModalCoordScope where
  | wideOnly    -- only ΔA ∘ ΔB
  | narrowOnly  -- only Δ(A ∘ B)
  | ambiguous   -- both readings available
  deriving DecidableEq, Repr, BEq

/-- A scope ambiguity datum for "MOD A COORD MOD B" sentences. -/
structure ScopeAmbiguityDatum where
  sentence : String
  coord : String           -- "or" / "and"
  modalForce : ModalForce
  /-- Which reading is dominant in context? -/
  dominantReading : String
  /-- Is the sentence scope-ambiguous? -/
  scopeAvailability : ModalCoordScope
  deriving Repr

/-- (2) "You may do A or you may do B" — FC reading from narrow-scope. -/
def mayOrMay : ScopeAmbiguityDatum :=
  { sentence := "You may do A or you may do B"
  , coord := "or", modalForce := .possibility
  , dominantReading := "narrow-scope (free choice)"
  , scopeAvailability := .ambiguous }

/-- (5) "You must write an essay or you must give a presentation." -/
def mustOrMust : ScopeAmbiguityDatum :=
  { sentence := "You must write an essay or you must give a presentation"
  , coord := "or", modalForce := .necessity
  , dominantReading := "narrow-scope (disjunctive obligation)"
  , scopeAvailability := .ambiguous }

/-- (7) "You may go to Bob's party and you may go to Charlie's party." -/
def mayAndMay : ScopeAmbiguityDatum :=
  { sentence := "You may go to Bob's party and you may go to Charlie's party"
  , coord := "and", modalForce := .possibility
  , dominantReading := "narrow-scope (conjunctive permission)"
  , scopeAvailability := .ambiguous }

def scopeData : List ScopeAmbiguityDatum := [mayOrMay, mustOrMust, mayAndMay]

/-- All MOD-COORD-MOD sentences are scope-ambiguous (central claim). -/
theorem all_ambiguous :
    scopeData.all (·.scopeAvailability == .ambiguous) = true := rfl

-- ============================================================================
-- §3. Modal Concord Derivation (connected to Fragment entries)
-- ============================================================================

/-!
## Deriving Narrow-Scope LF via Modal Concord

@cite{zeijlstra-2007}'s feature system explains how the narrow-scope LF
◇(A ∨ B) arises compositionally for "may A or may B":

1. Each "may" carries [u∃-MOD] (uninterpretable existential feature)
2. A silent ◇ operator [i∃-MOD] is projected above the coordination
3. The silent operator checks both [u∃-MOD] features in the conjuncts
4. Only the silent operator is semantically interpreted → ◇(A ∨ B)
-/

/-- The modal feature carried by English "may" — fully derived from the
    Fragment entry's force AND interpretability. -/
def mayFeature : ModalFeature := may.toModalFeature.get!

/-- The modal feature carried by English "must" — fully derived from Fragment. -/
def mustFeature : ModalFeature := must.toModalFeature.get!

/-- "May" carries [u∃-MOD]: possibility force, uninterpretable. -/
theorem may_feature_eq :
    may.toModalFeature = some ⟨.possibility, .uninterpretable⟩ := rfl

/-- "Must" carries [u∀-MOD]: necessity force, uninterpretable. -/
theorem must_feature_eq :
    must.toModalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The silent operator that checks a given u-feature: same force, but
    interpretable. This is the operator C&G posit above the coordination. -/
def silentChecker (f : ModalFeature) : ModalFeature := ⟨f.force, .interpretable⟩

/-- **Core derivation**: for any u-feature, the matching silent operator
    checks it. This is the general form of C&G's concord mechanism —
    not just "may" or "must", but ANY auxiliary carrying a u-feature. -/
theorem silent_checker_works (f : ModalFeature) (h : f.interp = .uninterpretable) :
    (silentChecker f).checks f = true := by
  simp only [silentChecker, ModalFeature.checks, h]
  cases f.force <;> decide

/-- A silent [i-MOD] with force f₁ checks any [u-MOD] with matching concord class. -/
private theorem silent_checks_matching (g₁ g₂ : ModalFeature)
    (hI : g₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce g₁.force = ConcordType.fromModalForce g₂.force) :
    (silentChecker g₁).checks g₂ = true := by
  unfold silentChecker ModalFeature.checks
  rw [hI, hF]
  simp
  exact ⟨rfl, rfl⟩

/-! ### ConcordDerivation: packaging the full derivation chain -/

/-- A concord derivation witnesses that two modal features can be checked
    by a single silent operator. This is the formal content of
    @cite{ciardelli-guerrini-2026}'s compositional mechanism.

    A `ConcordDerivation` exists iff:
    1. Both features are uninterpretable (u-MOD)
    2. They belong to the same concord class (both ∃-type or both ∀-type)

    The silent operator, checking proofs, and resulting narrow-scope
    interpretation are all derived automatically from these two conditions. -/
structure ConcordDerivation where
  /-- The feature of the first modal auxiliary -/
  f₁ : ModalFeature
  /-- The feature of the second modal auxiliary -/
  f₂ : ModalFeature
  /-- Both are uninterpretable -/
  uInterp₁ : f₁.interp = .uninterpretable
  uInterp₂ : f₂.interp = .uninterpretable
  /-- Same concord class -/
  sameClass : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force

namespace ConcordDerivation

/-- The silent interpretable operator — derived, not stipulated. -/
def checker (cd : ConcordDerivation) : ModalFeature :=
  silentChecker cd.f₁

/-- The checker is interpretable (semantically active). -/
theorem checker_interpretable (cd : ConcordDerivation) :
    cd.checker.interp = .interpretable := rfl

/-- The checker checks the first feature. -/
theorem checks_first (cd : ConcordDerivation) :
    cd.checker.checks cd.f₁ = true :=
  silent_checker_works cd.f₁ cd.uInterp₁

/-- The checker checks the second feature. -/
theorem checks_second (cd : ConcordDerivation) :
    cd.checker.checks cd.f₂ = true :=
  silent_checks_matching cd.f₁ cd.f₂ cd.uInterp₂ cd.sameClass

/-- Cross-force checking fails: a checker with different concord class
    cannot check a feature. -/
theorem cross_class_blocked (cd : ConcordDerivation)
    (g : ModalFeature) (hU : g.interp = .uninterpretable)
    (hDiff : ConcordType.fromModalForce cd.f₁.force ≠ ConcordType.fromModalForce g.force) :
    cd.checker.checks g = false := by
  unfold checker silentChecker ModalFeature.checks
  simp only [BEq.beq, Bool.and_eq_false_imp]
  intro _ _
  exact Bool.eq_false_iff.mpr (by intro h; exact hDiff (LawfulBEq.eq_of_beq h))

end ConcordDerivation

/-- Construct a `ConcordDerivation` from two `AuxEntry`s. The derivation
    is built entirely from Fragment data — no stipulation. -/
def ConcordDerivation.fromAux (a₁ a₂ : AuxEntry)
    {f₁ f₂ : ModalFeature}
    (_h₁ : a₁.toModalFeature = some f₁) (_h₂ : a₂.toModalFeature = some f₂)
    (hI₁ : f₁.interp = .uninterpretable) (hI₂ : f₂.interp = .uninterpretable)
    (hF : ConcordType.fromModalForce f₁.force = ConcordType.fromModalForce f₂.force) :
    ConcordDerivation :=
  ⟨f₁, f₂, hI₁, hI₂, hF⟩

/-! ### Universal modal properties -/

/-- The modal auxiliaries that participate in concord: all entries in the
    Fragment with uninterpretable features. -/
def modalAuxiliaries : List AuxEntry :=
  allAuxiliaries.filter (λ a => a.interpretability == some .uninterpretable)

/-- Exactly 13 English modal auxiliaries carry u-features. -/
theorem modal_aux_count : modalAuxiliaries.length = 13 := by native_decide

/-- Every modal auxiliary has a derivable modal feature. -/
theorem modal_aux_all_have_features :
    modalAuxiliaries.all (λ a => a.toModalFeature.isSome) = true := by native_decide

/-- Every modal auxiliary's feature is uninterpretable. -/
theorem modal_aux_all_uninterpretable :
    modalAuxiliaries.all (λ a =>
      match a.toModalFeature with
      | some f => f.interp == .uninterpretable
      | none => false) = true := by native_decide

/-- Non-modal auxiliaries have no modal feature — they cannot participate
    in concord at all. -/
theorem do_no_feature : do_.toModalFeature = none := rfl
theorem be_no_feature : am.toModalFeature = none := rfl
theorem have_no_feature : have_.toModalFeature = none := rfl

/-! ### Instantiations -/

/-- "May A or may B" concord derivation — fully derived from Fragment. -/
def mayMayConcord : ConcordDerivation :=
  .fromAux may may may_feature_eq may_feature_eq rfl rfl rfl

/-- "Must A or must B" concord derivation — fully derived from Fragment. -/
def mustMustConcord : ConcordDerivation :=
  .fromAux must must must_feature_eq must_feature_eq rfl rfl rfl

/-- Cross-force checking fails: silent □ cannot check "may"[u∃]. -/
theorem cross_force_blocked :
    (silentChecker mustFeature).checks mayFeature = false := by native_decide

-- ============================================================================
-- §3b. The FC Pipeline: Concord → Narrow Scope → Free Choice
-- ============================================================================

/-!
## The Full Pipeline: From Lexical Features to Free Choice

This is the deepest formalization of @cite{ciardelli-guerrini-2026}'s
reductionist thesis. The pipeline has three stages:

1. **Feature matching** → `ConcordDerivation` (§3 above)
2. **Narrow scope** → single modal operator over coordination
3. **Exhaustification** → free choice inference

The key insight: the narrow-scope / wide-scope distinction is
**truth-conditionally vacuous** (`scope_equivalence`) but **pragmatically
active** — exhaustification produces opposite results:

- Narrow scope: Exh²(◇(A∨B)) → ◇A ∧ ◇B  (free choice: both permitted)
- Wide scope: Exh(◇A ∨ ◇B) → ¬(◇A ∧ ◇B)  (exclusive: at most one)
-/

/-- The **free choice pipeline**: narrow-scope ◇(A∨B), when doubly
    exhaustified, yields free choice ◇A ∧ ◇B.

    This IS the reductionist thesis in action: FC arises from the
    narrow-scope LF (derived via concord) fed to the standard
    exhaustification mechanism. Uses `free_choice_forward` from
    `Exhaustification/FreeChoice.lean`. -/
theorem narrowScope_yields_fc {World : Type*} (A B : Prop' World)
    (hExh : (FCAltSet.mk A B).exh2) : diamond A ∧ diamond B :=
  free_choice_forward ⟨A, B⟩ hExh

/-- Wide-scope exhaustification: Exh(◇A ∨ ◇B) asserts the disjunction
    while negating the conjunction — yielding exclusive disjunction.

    This is the standard scalar implicature for disjunction: "A or B"
    implicates "not both." -/
def wideScopeExh {World : Type*} (A B : Prop' World) : Prop :=
  (diamond A ∨ diamond B) ∧ ¬(diamond A ∧ diamond B)

/-- Wide-scope exhaustification is **incompatible** with free choice.
    FC = ◇A ∧ ◇B, but wide-scope Exh asserts ¬(◇A ∧ ◇B). -/
theorem wideScope_blocks_fc {World : Type*} (A B : Prop' World)
    (h : wideScopeExh A B) : ¬(diamond A ∧ diamond B) :=
  h.2

/-- Truth-conditional equivalence: the scope distinction is semantically
    vacuous. ◇(A∨B) ↔ ◇A∨◇B in standard modal logic. -/
theorem scope_equivalence {World : Type*} (A B : Prop' World) :
    diamond (pdisj A B) ↔ diamond A ∨ diamond B :=
  diamond_distributes_iff A B

/-- **The Reductionist Thesis** (@cite{ciardelli-guerrini-2026}, formalized).

    Despite truth-conditional equivalence (`scope_equivalence`),
    the two LFs diverge under pragmatic enrichment:

    1. Narrow scope + Exh² → FC (both permitted)
    2. Wide scope + Exh → ¬FC (at most one)

    There is no separate problem of "wide-scope free choice" — the FC
    reading arises exclusively from the narrow-scope LF, which is
    derived via modal concord (`ConcordDerivation`). -/
theorem reductionist_thesis {World : Type*} (A B : Prop' World) :
    -- (1) Narrow scope + exhaustification → free choice
    ((FCAltSet.mk A B).exh2 → diamond A ∧ diamond B) ∧
    -- (2) Wide scope + exhaustification → NOT free choice
    (wideScopeExh A B → ¬(diamond A ∧ diamond B)) :=
  ⟨narrowScope_yields_fc A B, wideScope_blocks_fc A B⟩

-- ============================================================================
-- §4. Auxiliary vs Non-Auxiliary Prediction
-- ============================================================================

/-!
## Prediction: Non-Auxiliary Modals Block FC in Coordination

@cite{meyer-sauerland-2017} observed that (19a-b) lack FC readings:

  (19a) It's ok for John to sing or it's ok for John to dance.  (*FC)
  (19b) John is allowed to sing or he is allowed to dance.      (*FC)

@cite{ciardelli-guerrini-2026} explain this: "it's ok" and "be allowed"
carry **interpretable** features. They cannot participate in concord
with a higher silent operator, so no narrow-scope LF is available.

Modal auxiliaries ("may", "must", "can") carry **uninterpretable**
features and CAN participate in concord → FC available.

The auxiliary status of "may", "must", "can", "need" is derived from
`Fragments.English.FunctionWords` — they are all `.modal` entries.
-/

/-- Fragment-derived: all English modals used by C&G are modal auxiliaries
    with uninterpretable features. -/
theorem may_is_modal : may.auxType = .modal := rfl
theorem must_is_modal : must.auxType = .modal := rfl
theorem can_is_modal : can.auxType = .modal := rfl
theorem need_is_modal : need.auxType = .modal := rfl

/-- All C&G modals carry uninterpretable features in the Fragment. -/
theorem may_uninterpretable : may.interpretability = some .uninterpretable := rfl
theorem must_uninterpretable : must.interpretability = some .uninterpretable := rfl
theorem can_uninterpretable : can.interpretability = some .uninterpretable := rfl
theorem need_uninterpretable : need.interpretability = some .uninterpretable := rfl

/-- Non-auxiliary modal constructions — these have no Fragment entry
    because they are multi-word periphrastic constructions, not
    single-word auxiliaries in Zwicky & Pullum's sense. Their absence
    from the auxiliary lexicon IS the prediction: no `AuxEntry` →
    no uninterpretable feature → no concord → no narrow-scope LF. -/
structure NonAuxModalDatum where
  form : String
  fcInCoordination : Bool  -- can FC arise in "X A or X B"?
  deriving Repr

def nonAuxData : List NonAuxModalDatum :=
  [ ⟨"it's ok that", false⟩
  , ⟨"be allowed to", false⟩
  , ⟨"be required to", false⟩ ]

/-- No non-auxiliary modal construction permits FC in coordination. -/
theorem nonAux_no_fc : nonAuxData.all (·.fcInCoordination == false) = true := rfl

-- ============================================================================
-- §5. ATB Movement Counterexample
-- ============================================================================

/-!
## Against ATB Movement (§1, ex. 3)

@cite{simons-2005} proposed that the narrow-scope LF ◇(A ∨ B) arises
from across-the-board (ATB) movement of the modal at LF. C&G note there
is evidence AGAINST this: ATB movement is independently blocked for
nominal quantifiers:

  (3a) Everyone sang or everyone danced.
  (3b) Everyone sang or danced.

(3a) CANNOT be interpreted as (3b). If ATB movement of "everyone" were
possible at LF, (3a) should receive the (3b) reading — but it doesn't.
This undermines ATB as the mechanism for deriving narrow-scope modal LFs.

C&G's modal concord account avoids this problem: the narrow-scope LF is
derived via feature checking (specific to modals), not movement (which
would overgeneralize to quantifiers).
-/

/-- ATB counterexample data. -/
structure ATBCounterexample where
  surface : String
  atbReading : String
  atbReadingAvailable : Bool
  deriving Repr

/-- (3) "Everyone sang or everyone danced" ≠ "Everyone sang or danced." -/
def everyoneATB : ATBCounterexample :=
  { surface := "Everyone sang or everyone danced"
  , atbReading := "Everyone sang or danced"
  , atbReadingAvailable := false }

-- ============================================================================
-- §6. Negation Flips Force for Concord
-- ============================================================================

/-!
## Concord Across Negation (§4.2)

Modal concord across negation requires **opposite** forces. The checking
uses `ModalForce.dual` — negation over a modal operator yields its dual:

  (24) The countess allowed that I needn't do it again.
       ALLOW[i∃](¬NEED[u∀]) ✓  — dual(∀) = ∃, matches checker

  (26) *The countess firmly demanded that I needn't do it again.
       *DEMAND[i∀](¬NEED[u∀]) ✗  — dual(∀) = ∃ ≠ ∀

  (25) A restraining order demands that Roiland may not harass the plaintiff.
       DEMAND[i∀](¬MAY[u∃]) ✓  — dual(∃) = ∀, matches checker

  (27) *A special permit allows that Roiland may not recycle.
       *ALLOW[i∃](¬MAY[u∃]) ✗  — dual(∃) = ∀ ≠ ∃

The pattern: checking across negation succeeds iff the checker's force
equals the dual of the checked item's force. This follows from
`ModalFeature.checksAcrossNegation`, which uses `ModalForce.dual`.
-/

/-- (24) ALLOW[i∃] checks ¬NEED[u∀]: well-formed (dual(∀) = ∃). -/
theorem allow_neg_need_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = true := by native_decide

/-- (26) *DEMAND[i∀] checks ¬NEED[u∀]: ill-formed (dual(∀) = ∃ ≠ ∀). -/
theorem demand_neg_need_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.necessity, .uninterpretable⟩)
    = false := by native_decide

/-- (25) DEMAND[i∀] checks ¬MAY[u∃]: well-formed (dual(∃) = ∀). -/
theorem demand_neg_may_ok :
    (ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = true := by native_decide

/-- (27) *ALLOW[i∃] checks ¬MAY[u∃]: ill-formed (dual(∃) = ∀ ≠ ∃). -/
theorem allow_neg_may_bad :
    (ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      ⟨.possibility, .uninterpretable⟩)
    = false := by native_decide

/-- General pattern: cross-negation concord succeeds ↔ forces are duals.
    This is the content of the negation-concord generalization from
    @cite{grosz-2010} and @cite{anand-brasoveanu-2010}, formalized
    as a consequence of `checksAcrossNegation` using `ModalForce.dual`. -/
theorem negation_concord_pattern (checkerForce checkedForce : ModalForce)
    (hNec : checkerForce = .necessity ∨ checkerForce = .possibility)
    (hChk : checkedForce = .necessity ∨ checkedForce = .possibility) :
    ModalFeature.checksAcrossNegation
      ⟨checkerForce, .interpretable⟩
      ⟨checkedForce, .uninterpretable⟩ = true
    ↔ checkerForce = checkedForce.dual := by
  rcases hNec with rfl | rfl <;> rcases hChk with rfl | rfl <;> decide

-- ============================================================================
-- §7. "I need not cook and I need not clean" (§4.2, ex. 28-29)
-- ============================================================================

/-!
## Concord + Negation + Coordination (§4.2, ex. 28-29)

"I need not cook and I need not clean" can convey ◇(¬Cook ∧ ¬Clean) —
permission to do neither — but NOT □(¬Cook ∧ ¬Clean) — obligation to do
neither. This follows from the concord-across-negation generalization.

The "need" u-feature force comes from the Fragment: necessity.
-/

/-- "Need" carries [u∀-MOD] in the Fragment. -/
theorem need_feature_eq :
    need.toModalFeature = some ⟨.necessity, .uninterpretable⟩ := rfl

/-- The existential reading is available: ◇[i∃] checks ¬NEED[u∀]. -/
theorem need_not_existential_ok :
    ModalFeature.checksAcrossNegation
      ⟨.possibility, .interpretable⟩
      need.toModalFeature.get!
    = true := by native_decide

/-- The universal reading is blocked: □[i∀] cannot check ¬NEED[u∀]. -/
theorem need_not_universal_blocked :
    ModalFeature.checksAcrossNegation
      ⟨.necessity, .interpretable⟩
      need.toModalFeature.get!
    = false := by native_decide

-- ============================================================================
-- §8. Conjunctive Permission (may-and-may)
-- ============================================================================

/-!
## Conjunctive Permission (§2, ex. 7-8)

"You may go to Bob's party and you may go to Charlie's party" has a
reading where Alice is allowed to go to BOTH parties: ◇(Bob ∧ Charlie).

This is distinct from ◇Bob ∧ ◇Charlie. Unlike disjunction, ◇(A ∧ B)
is strictly STRONGER than ◇A ∧ ◇B — so the scope distinction has
truth-conditional consequences for conjunction.
-/

/-- For conjunction, narrow scope is strictly stronger than wide scope:
    ◇(A ∧ B) → ◇A ∧ ◇B but not conversely. -/
theorem conjunctive_narrow_stronger {World : Type*}
    (p q : Prop' World)
    (h : diamond (pand p q)) : diamond p ∧ diamond q := by
  obtain ⟨w, hp, hq⟩ := h
  exact ⟨⟨w, hp⟩, ⟨w, hq⟩⟩

-- ============================================================================
-- §9. Bridge to Rotter & Liu 2025 Modal Concord Data
-- ============================================================================

/-!
## Connection to Empirical Modal Concord (@cite{rotter-liu-2025})

@cite{rotter-liu-2025} study "must have to VP" stacking, where two necessity
modals yield a single-necessity reading (concord). This is the same phenomenon
C&G exploit: modal concord — one modal is semantically vacuous.

The `ModalFeature.checks` infrastructure from §3 models this directly: in
"must have to", one auxiliary carries [i∀-MOD] and the other [u∀-MOD].
The i-feature checks the u-feature, leaving only one semantic operator.

The empirical finding that "must have to" preserves single-necessity meaning
(`meaning_must_close_to_mustHaveTo`) is predicted by the concord mechanism.
-/

/-- "Must" and "have to" have the same modal feature (both [u∀-MOD]).
    Concord between them is predicted: same-force u-features. -/
theorem must_haveTo_same_feature :
    must.toModalFeature = haveTo.toModalFeature := rfl

/-- Feature checking between "must"[i∀] and "have to"[u∀] succeeds.
    In "must have to" stacking, one carries the i-feature (semantically
    active) and the other carries the u-feature (semantically vacuous).
    This models the @cite{rotter-liu-2025} finding: "must have to" yields
    single necessity, not double necessity. -/
theorem must_haveTo_concord :
    (ModalFeature.checks
      ⟨must.toModalFeature.get!.force, .interpretable⟩
      must.toModalFeature.get!)
    = true := by native_decide

/-- Cross-force concord fails: "must"[u∀] cannot be checked by a silent
    [i∃-MOD] operator. This predicts no concord between necessity and
    possibility modals. -/
theorem must_may_no_concord :
    (ModalFeature.checks
      ⟨may.toModalFeature.get!.force, .interpretable⟩
      must.toModalFeature.get!)
    = false := by native_decide

-- ============================================================================
-- §10. Scope Data Verification (derived from Fragment)
-- ============================================================================

/-!
## Verifying Scope Data Against Fragment Entries

The `modalForce` field in each `ScopeAmbiguityDatum` is independently
verifiable against the Fragment's modal meaning entries.
-/

/-- The force in mayOrMay matches the Fragment entry for "may". -/
theorem mayOrMay_force_verified :
    mayOrMay.modalForce = may.toModalFeature.get!.force := rfl

/-- The force in mustOrMust matches the Fragment entry for "must". -/
theorem mustOrMust_force_verified :
    mustOrMust.modalForce = must.toModalFeature.get!.force := rfl

/-- The force in mayAndMay matches the Fragment entry for "may". -/
theorem mayAndMay_force_verified :
    mayAndMay.modalForce = may.toModalFeature.get!.force := rfl

end Phenomena.Modality.Studies.CiardelliGuerrini2026
