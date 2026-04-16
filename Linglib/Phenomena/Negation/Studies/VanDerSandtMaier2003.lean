import Linglib.Theories.Semantics.Dynamic.DRT.Basic
import Linglib.Phenomena.Negation.Denial
import Linglib.Core.Semantics.ContentLayer

/-!
# Van der Sandt & Maier (2003) — Denials in Discourse
@cite{van-der-sandt-maier-2003}

Denials in Discourse. Michigan Linguistics and Philosophy Workshop, 2003.

Formalization of directed reverse anaphora (RA*) applied to the paper's
worked examples. Connects three linglib modules:

- `Core.Semantics.ContentLayer` — `Off` (which layers are offensive)
- `Theories.Semantics.Dynamic.DRT.Basic` — LDRT types and RA*
- `Phenomena.Negation.Denial` — empirical denial data

## Layer Naming Convention

The paper's layer labels map to `ContentLayer` constructors as follows:

| Paper | Code | Meaning |
|-------|------|---------|
| `pr` | `.presupposition` | Backgrounded precondition |
| `fr` (Frege) | `.atIssue` | Assertoric/at-issue content |
| `imp` | `.implicature` | Scalar implicature or connotation |

## Core Mechanism

Denial is a non-monotonic discourse operation that selectively retracts
content. The RA* algorithm (§4.3):
1. Identifies offensive layers via `Off` — those inconsistent with the
   correction
2. Moves conditions at offensive layers under negation
3. Preserves conditions at non-offensive layers

## Verified Examples

| Example | Denial type | Off | RA* result |
|---------|-------------|-----|------------|
| King of France (49) | Presuppositional | {pr, fr} | 1 cond: ¬[pr+fr] |
| Possible/necessary (68) | Implicature | {imp} | 3 conds: pr, fr + ¬[imp] |
| Lady/wife (69) | Connotation | {imp} | 4 conds: pr, fr, fr + ¬[imp] |
-/

set_option autoImplicit false

namespace VanDerSandtMaier2003

open Core.Semantics.ContentLayer
open Semantics.Dynamic.DRT
open Semantics.Dynamic.Core.DRSExpr (DRSExpr)
open Phenomena.Negation.Denial

-- ════════════════════════════════════════════════════
-- § 1. Presuppositional Denial — King of France (§3.5, ex. 49)
-- ════════════════════════════════════════════════════

/-! σ₁: "The King of France walks in the park."
    σ₂: "No, he doesn't,"
    σ₃: "France doesn't have a king."

The correction targets the existence presupposition of the definite.
Off = {pr, fr}: both layers conflict with "no king."

Note: the Denial.lean datum `kingBald_presuppositional` uses a different
sentence (ex. 30b: "The king of France is not bald") but the same denial
type — presuppositional. The bridge theorem below connects the Off
computation to that datum's target layer. -/

private inductive KFW | kingWalks | kingStands | noKing
  deriving DecidableEq, Repr

private def kfLayered : LayeredProp KFW :=
  { presupposition := fun | .kingWalks | .kingStands => true | .noKing => false
  , atIssue := fun | .kingWalks => true | _ => false }

private def kfWorlds : List KFW := [.kingWalks, .kingStands, .noKing]

/-- Off: "no king" conflicts with both pr (king exists) and fr (king walks). -/
theorem kf_off :
    offensiveLayers kfLayered (fun w => w == .noKing) kfWorlds
    = [.presupposition, .atIssue] := by native_decide

/-- LDRS for σ₁: "The King of France walks in the park."
    Rel 0 = KF (pr layer), Rel 1 = walkInPark (fr layer). -/
private def kfAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩ ] }

/-- After RA* with Off = {pr, fr}: no conditions survive (both are
offensive). All material moves under a single negation wrapper. -/
theorem kf_ra_length :
    (kfAssertion.directedRA [.presupposition, .atIssue]).conditions.length
    = 1 := by native_decide

/-- The sole surviving condition is at fr level (the negation wrapper
is assertoric content: "it is not the case that ..."). -/
theorem kf_ra_layers :
    (kfAssertion.directedRA [.presupposition, .atIssue]).conditions.map (·.layer)
    = [.atIssue] := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. Implicature Denial — Possible/Necessary (§4.4, ex. 68)
-- ════════════════════════════════════════════════════

/-! σ₁: "It is possible the Pope is right."
    σ₂: "No, it's not POssible,"
    σ₃: "it's NECessary that he's right."

The correction targets the scalar implicature ¬□p.
Off = {imp}: only the implicature conflicts with correction □p.
At-issue content ◇p survives (□p entails ◇p). -/

private inductive ModalW | possNotNec | nec
  deriving DecidableEq, Repr

private def modalLayered : LayeredProp ModalW :=
  { presupposition := fun _ => true
  , atIssue := fun _ => true
  , implicature := fun | .possNotNec => true | .nec => false }

private def modalWorlds : List ModalW := [.possNotNec, .nec]

/-- Off: correction "necessary" (□p) conflicts only with imp (¬□p). -/
theorem modal_off :
    offensiveLayers modalLayered (fun w => w == .nec) modalWorlds
    = [.implicature] := by native_decide

/-- LDRS for σ₁.
    Rel 0 = pope (pr), Rel 1 = ◇right (fr), Rel 2 = □right.
    The imp layer carries ¬□right. -/
private def modalAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.implicature, .neg (.atom 2 [0])⟩ ] }

/-- After RA* with Off = {imp}: pr and fr survive; imp moves under
negation. Result: 2 surviving + 1 negation wrapper = 3 conditions. -/
theorem modal_ra_length :
    (modalAssertion.directedRA [.implicature]).conditions.length = 3 := by
  native_decide

/-- Surviving layers: pr, fr at top level; negated imp tagged fr. -/
theorem modal_ra_layers :
    (modalAssertion.directedRA [.implicature]).conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue] := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Connotation Denial — Lady/Wife (§4.4, ex. 69)
-- ════════════════════════════════════════════════════

/-! σ₁: "Now, THAT's a nice lady."
    σ₂: "Yes, she is,"
    σ₃: "but she's not a LAdy,"
    σ₄: "she's my WIfe."

The correction targets the connotation of "a lady" (implicature:
the person is a stranger, not a close relative). The literal
predication (lady, nice) and presupposition (pointing) survive;
only the stranger implicature is retracted. Off = {imp}.

The paper's derivation has 4 utterances; σ₂ (affirmation "yes, she is")
is treated as monotonic merge and omitted here. The Off computation
depends only on σ₁ + σ₄.

Note: the Denial.lean datum `lady_wife` uses a related sentence
(ex. 13: "That wasn't a lady I kissed last night") but the same denial
type — implicature targeting the connotation of "lady." -/

private inductive LadyW | ladyStranger | ladyWife | notLadyWife
  deriving DecidableEq, Repr

private def ladyLayered : LayeredProp LadyW :=
  { presupposition := fun _ => true
  , atIssue := fun | .ladyStranger | .ladyWife => true | _ => false
  , implicature := fun | .ladyStranger => true | _ => false }

private def ladyWorlds : List LadyW := [.ladyStranger, .ladyWife, .notLadyWife]

/-- Off: correction "wife" conflicts only with imp (stranger).
    Crucially, lady (fr) is consistent with wife — Off does NOT
    retract the literal predication "lady." -/
theorem lady_off :
    offensiveLayers ladyLayered
      (fun w => w == .ladyWife || w == .notLadyWife) ladyWorlds
    = [.implicature] := by native_decide

/-- LDRS for σ₁.
    Rel 0 = pointed_at (pr), Rel 1 = lady (fr), Rel 2 = nice (fr),
    Rel 3 = stranger (imp). -/
private def ladyAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.atIssue, .atom 2 [0]⟩
                   , ⟨.implicature, .atom 3 [0]⟩ ] }

/-- After RA*: pr, fr (lady), fr (nice) survive. imp (stranger)
moves under negation. Result: 3 surviving + 1 negated = 4. -/
theorem lady_ra_length :
    (ladyAssertion.directedRA [.implicature]).conditions.length = 4 := by
  native_decide

/-- Surviving layers: pr, fr, fr at top level; negated imp as fr. -/
theorem lady_ra_layers :
    (ladyAssertion.directedRA [.implicature]).conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue, .atIssue] := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Discourse Pipeline: Assertion → Denial
-- ════════════════════════════════════════════════════

/-! Full pipeline for the modal example: assertion adds content
(monotonic merge), denial selectively retracts (non-monotonic RA*).

This demonstrates the paper's central architectural claim: assertion
and denial are dual discourse operations, one monotonic and one not. -/

private def modalBackground : LDRS :=
  { drefs := [0], conditions := [⟨.presupposition, .atom 0 [0]⟩] }

private def modalContent : LDRS :=
  { drefs := []
  , conditions := [ ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.implicature, .neg (.atom 2 [0])⟩ ] }

private def modalCorrection : LDRS :=
  { drefs := [], conditions := [⟨.atIssue, .atom 2 [0]⟩] }

/-- Step 1: Assertion is monotonic — merge adds conditions. -/
private def φ₁ : LDRS := modalBackground.merge modalContent

theorem assertion_grows :
    φ₁.conditions.length > modalBackground.conditions.length := by
  native_decide

/-- Step 2: Denial update — merge correction, then apply RA*. -/
private def φ₃ : LDRS := φ₁.denialUpdate modalCorrection [.implicature]

/-- Denial update: 4 conditions = 2 surviving (pr + ◇right) +
1 correction (□right) + 1 negated wrapper (¬[¬□right]). -/
theorem denial_result_length : φ₃.conditions.length = 4 := by
  native_decide

/-- All surviving content is at pr or fr level.
No imp content remains at the top level. -/
theorem denial_result_layers :
    φ₃.conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue, .atIssue] := by native_decide

/-- The imp layer has been fully retracted from the top level. -/
theorem implicature_retracted :
    (φ₃.conditions.map (·.layer)).count .implicature = 0 := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Off → DenialDatum Bridge
-- ════════════════════════════════════════════════════

/-! The Off computations from §§ 1–3 agree with the denial-type
classification in `Phenomena.Negation.Denial`. Each Off result
contains the target layer of the corresponding `DenialDatum`.

This is the end-to-end chain: a semantic computation over layered
propositions (Off) yields offensive layers that match the empirical
denial-type taxonomy. -/

/-- The Off result for the modal example includes the datum's target layer.
The semantic Off computation (checking proposition consistency) agrees
with the empirical classification (implicature denial). -/
theorem modal_off_agrees_with_datum :
    (offensiveLayers modalLayered (fun w => w == .nec) modalWorlds).contains
    possible_necessary.denialType.targetLayer = true := by native_decide

/-- The Off result for the KF example includes the datum's target layer. -/
theorem kf_off_agrees_with_datum :
    (offensiveLayers kfLayered (fun w => w == .noKing) kfWorlds).contains
    kingBald_presuppositional.denialType.targetLayer = true := by native_decide

/-- The Off result for the lady/wife example includes the datum's target layer. -/
theorem lady_off_agrees_with_datum :
    (offensiveLayers ladyLayered
      (fun w => w == .ladyWife || w == .notLadyWife) ladyWorlds).contains
    lady_wife.denialType.targetLayer = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Denial ≠ Negation (§2.1)
-- ════════════════════════════════════════════════════

/-! @cite{van-der-sandt-maier-2003} §2.1: denial and negation are
orthogonal concepts. Denial is a discourse operation (non-monotonic
correction); negation is a semantic operator (truth-functional
connective). A denial can use a positive sentence (ex. 6), and a
negative sentence can be a plain assertion, not a denial (ex. 2). -/

/-- Positive denial exists: the denial utterance IS the correction,
with no negation involved. Denial is a discourse function, not a
syntactic form. -/
theorem positive_denial_is_correction :
    maryHappy_positive.denial = maryHappy_positive.correction := rfl

/-- Positive denial is propositional — it targets fr (at-issue content),
just like negative propositional denials. The mechanism is the same
regardless of surface polarity. -/
theorem positive_denial_targets_fr :
    maryHappy_positive.denialType.targetLayer = .atIssue := rfl

/-- The same surface negation can correspond to different denial types,
disambiguated by the correction (§2.3: "still" denials, ex. 19–20). -/
theorem same_surface_different_types :
    still_propositional.denial = still_presuppositional.denial ∧
    still_propositional.denialType ≠ still_presuppositional.denialType :=
  ⟨rfl, by decide⟩

end VanDerSandtMaier2003
