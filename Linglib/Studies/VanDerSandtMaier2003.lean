import Linglib.Phenomena.Negation.Denial
import Linglib.Semantics.ContentLayer

/-!
# Van der Sandt & Maier (2003) — Denials in Discourse
@cite{van-der-sandt-maier-2003}

Denials in Discourse. Michigan Linguistics and Philosophy Workshop, 2003.

Formalization of directed reverse anaphora (RA*) applied to the paper's worked
examples, connecting:

- `Semantics.ContentLayer` — `offensiveLayers` (which layers are offensive)
- `Phenomena.Negation.Denial` — empirical denial data

## Layered DRT apparatus

The Layered-DRT machinery (`LCond`/`LDRS`/`directedRA`/`denialUpdate`) is
**single-paper substrate**, defined locally here. It is orthogonal to the
faithful model-theoretic DRS core (`Semantics/Dynamic/DRS/`): that core supplies
K&R's model theory and subordination, whereas LDRT's content-layer/RA* algebra
is a purely *syntactic* discourse-update operation (no model-theoretic
interpretation is exercised by this paper). Condition formulas (`LCond`) are
therefore opaque atoms — the paper's claims are about the layer bookkeeping, not
truth conditions.

## Layer naming convention

The paper's layer labels map to `ContentLayer` constructors as follows:

| Paper | Code | Meaning |
|-------|------|---------|
| `pr` | `.presupposition` | Backgrounded precondition |
| `fr` (Frege) | `.atIssue` | Assertoric/at-issue content |
| `imp` | `.implicature` | Scalar implicature or connotation |

## Core mechanism

Denial is a non-monotonic discourse operation that selectively retracts content.
The RA* algorithm: (1) identify offensive layers via `offensiveLayers` — those
inconsistent with the correction; (2) move conditions at offensive layers under
negation; (3) preserve conditions at non-offensive layers.

## Verified examples

| Example | Denial type | Off | RA* result |
|---------|-------------|-----|------------|
| King of France (49) | Presuppositional | {pr, fr} | 1 cond: ¬[pr+fr] |
| Possible/necessary (68) | Implicature | {imp} | 3 conds: pr, fr + ¬[imp] |
| Lady/wife (69) | Connotation | {imp} | 4 conds: pr, fr, fr + ¬[imp] |
-/

set_option autoImplicit false

namespace VanDerSandtMaier2003

open Semantics.ContentLayer
open Phenomena.Negation.Denial

/-! ### Layered DRT (LDRT) substrate

@cite{van-der-sandt-maier-2003} extend DRT with content layers: each condition
carries a label (`pr`, `fr`, `imp`) marking its discourse role. -/

/-- A condition formula. Opaque atoms (`Nat`-indexed predicate over `Nat`-indexed
referents) closed under negation and boxing; never interpreted semantically — the
paper reasons over the layer tags, not truth conditions. -/
inductive LCond
  | atom (pred : Nat) (args : List Nat)
  | neg (c : LCond)
  | box (drefs : List Nat) (conds : List LCond)

/-- A condition tagged with its content layer. -/
structure TaggedCondition where
  /-- The content layer this condition contributes to. -/
  layer : ContentLayer
  /-- The underlying condition formula. -/
  condition : LCond

/-- A Layered DRS: a DRS whose conditions carry content-layer tags. A standard
DRS is the special case where every condition is `atIssue`. -/
structure LDRS where
  /-- Universe: discourse referent indices. -/
  drefs : List Nat
  /-- Layered conditions. -/
  conditions : List TaggedCondition

/-- LDRS merge: combine two layered DRSs, preserving layer tags. -/
def LDRS.merge (k1 k2 : LDRS) : LDRS :=
  { drefs := k1.drefs ++ k2.drefs
  , conditions := k1.conditions ++ k2.conditions }

/-- The offensive conditions of an LDRS w.r.t. a correction: those whose layer is
in the offensive set. In denial, these are retracted. -/
def LDRS.offensiveConditions (k : LDRS) (offLayers : List ContentLayer) :
    List TaggedCondition :=
  k.conditions.filter (offLayers.contains ·.layer)

/-- The surviving conditions after denial: those NOT at offensive layers. -/
def LDRS.survivingConditions (k : LDRS) (offLayers : List ContentLayer) :
    List TaggedCondition :=
  k.conditions.filter (!offLayers.contains ·.layer)

/-! ### Assertion vs. denial: monotonicity

The paper's deepest architectural claim: assertion is monotonic (merge only adds
conditions), denial is non-monotonic (surviving conditions are a subset). Denial
is the only operation that removes information from the discourse context. -/

/-- Offensive + surviving = all conditions (partition). -/
theorem LDRS.offensive_surviving_partition (k : LDRS)
    (offLayers : List ContentLayer) :
    (k.offensiveConditions offLayers).length +
    (k.survivingConditions offLayers).length = k.conditions.length := by
  simp only [offensiveConditions, survivingConditions]
  induction k.conditions with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter]
    cases offLayers.contains hd.layer <;> simp_all <;> omega

/-- Assertion (merge) is monotonic: the result has at least as many conditions as
the original LDRS. -/
theorem merge_monotonic (k1 k2 : LDRS) :
    k1.conditions.length ≤ (k1.merge k2).conditions.length := by
  simp only [LDRS.merge, List.length_append]; omega

/-- Denial (surviving conditions) is non-monotonic: the result has at most as
many conditions as the original LDRS. -/
theorem denial_nonmonotonic (k : LDRS) (offLayers : List ContentLayer) :
    (k.survivingConditions offLayers).length ≤ k.conditions.length :=
  List.length_filter_le _ _

/-! ### Directed reverse anaphora (RA*)

@cite{van-der-sandt-maier-2003}: given the offensive layers (computed by
`offensiveLayers`), RA* partitions the conditions — surviving conditions remain in
the main DRS, offensive conditions are moved under a single negation. -/

/-- Directed reverse anaphora (RA*): move offensive-layer conditions under
negation, preserving non-offensive conditions. -/
def LDRS.directedRA (k : LDRS) (offLayers : List ContentLayer) : LDRS :=
  let surviving := k.survivingConditions offLayers
  let offensive := k.offensiveConditions offLayers
  { drefs := k.drefs
  , conditions :=
    surviving ++ match offensive with
    | [] => []
    | cs => [⟨.atIssue, .neg (.box [] (cs.map (·.condition)))⟩] }

/-- Denial pipeline: merge correction, then apply RA*. In an
assertion-denial-correction sequence, the correction is merged with the discourse
state, then RA* retracts the offensive layers. -/
def LDRS.denialUpdate (state correction : LDRS) (offLayers : List ContentLayer) :
    LDRS :=
  (state.merge correction).directedRA offLayers

/-- RA* preserves discourse referents — denial retracts conditions, not referent
introductions, so drefs introduced by σ₁ remain available for anaphora even after
denial ("A man jumped off the bridge. He didn't jump, he was pushed."). -/
theorem LDRS.directedRA_preserves_drefs (k : LDRS) (offLayers : List ContentLayer) :
    (k.directedRA offLayers).drefs = k.drefs := rfl

/-! ### §1. Presuppositional denial — King of France (§3.5, ex. 49)

σ₁: "The King of France walks in the park." σ₂: "No, he doesn't," σ₃: "France
doesn't have a king."

The correction targets the existence presupposition of the definite. Off = {pr,
fr}: both layers conflict with "no king".

The `Denial.lean` datum `kingBald_presuppositional` uses a different sentence (ex.
30b) but the same denial type — presuppositional; the bridge theorem below
connects the Off computation to that datum's target layer. -/

private inductive KFW | kingWalks | kingStands | noKing
  deriving DecidableEq, Repr

private def kfLayered : LayeredProp KFW :=
  { presupposition := fun | .kingWalks | .kingStands => true | .noKing => false
  , atIssue := fun | .kingWalks => true | _ => false }

private def kfWorlds : List KFW := [.kingWalks, .kingStands, .noKing]

/-- Off: "no king" conflicts with both pr (king exists) and fr (king walks). -/
theorem kf_off :
    offensiveLayers kfLayered (fun w => w == .noKing) kfWorlds
    = [.presupposition, .atIssue] := by decide

/-- LDRS for σ₁. Rel 0 = KF (pr layer), Rel 1 = walkInPark (fr layer). -/
private def kfAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩ ] }

/-- After RA* with Off = {pr, fr}: no conditions survive (both offensive); all
material moves under a single negation wrapper. -/
theorem kf_ra_length :
    (kfAssertion.directedRA [.presupposition, .atIssue]).conditions.length
    = 1 := by decide

/-- The sole surviving condition is at fr level (the negation wrapper is
assertoric: "it is not the case that ..."). -/
theorem kf_ra_layers :
    (kfAssertion.directedRA [.presupposition, .atIssue]).conditions.map (·.layer)
    = [.atIssue] := by decide

/-! ### §2. Implicature denial — Possible/Necessary (§4.4, ex. 68)

σ₁: "It is possible the Pope is right." σ₂: "No, it's not POssible," σ₃: "it's
NECessary that he's right."

The correction targets the scalar implicature ¬□p. Off = {imp}: only the
implicature conflicts with correction □p. At-issue content ◇p survives (□p
entails ◇p). -/

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
    = [.implicature] := by decide

/-- LDRS for σ₁. Rel 0 = pope (pr), Rel 1 = ◇right (fr), Rel 2 = □right; the imp
layer carries ¬□right. -/
private def modalAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.implicature, .neg (.atom 2 [0])⟩ ] }

/-- After RA* with Off = {imp}: pr and fr survive; imp moves under negation.
Result: 2 surviving + 1 negation wrapper = 3 conditions. -/
theorem modal_ra_length :
    (modalAssertion.directedRA [.implicature]).conditions.length = 3 := by decide

/-- Surviving layers: pr, fr at top level; negated imp tagged fr. -/
theorem modal_ra_layers :
    (modalAssertion.directedRA [.implicature]).conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue] := by decide

/-! ### §3. Connotation denial — Lady/Wife (§4.4, ex. 69)

σ₁: "Now, THAT's a nice lady." σ₂: "Yes, she is," σ₃: "but she's not a LAdy,"
σ₄: "she's my WIfe."

The correction targets the connotation of "a lady" (implicature: a stranger, not
a close relative). The literal predication (lady, nice) and presupposition
(pointing) survive; only the stranger implicature is retracted. Off = {imp}.

The paper's derivation has 4 utterances; σ₂ (affirmation) is monotonic merge and
omitted; Off depends only on σ₁ + σ₄. The `Denial.lean` datum `lady_wife` uses a
related sentence (ex. 13) but the same denial type. -/

private inductive LadyW | ladyStranger | ladyWife | notLadyWife
  deriving DecidableEq, Repr

private def ladyLayered : LayeredProp LadyW :=
  { presupposition := fun _ => true
  , atIssue := fun | .ladyStranger | .ladyWife => true | _ => false
  , implicature := fun | .ladyStranger => true | _ => false }

private def ladyWorlds : List LadyW := [.ladyStranger, .ladyWife, .notLadyWife]

/-- Off: correction "wife" conflicts only with imp (stranger). Crucially, lady
(fr) is consistent with wife — Off does NOT retract the literal predication. -/
theorem lady_off :
    offensiveLayers ladyLayered
      (fun w => w == .ladyWife || w == .notLadyWife) ladyWorlds
    = [.implicature] := by decide

/-- LDRS for σ₁. Rel 0 = pointed_at (pr), Rel 1 = lady (fr), Rel 2 = nice (fr),
Rel 3 = stranger (imp). -/
private def ladyAssertion : LDRS :=
  { drefs := [0]
  , conditions := [ ⟨.presupposition, .atom 0 [0]⟩
                   , ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.atIssue, .atom 2 [0]⟩
                   , ⟨.implicature, .atom 3 [0]⟩ ] }

/-- After RA*: pr, fr (lady), fr (nice) survive; imp (stranger) moves under
negation. Result: 3 surviving + 1 negated = 4. -/
theorem lady_ra_length :
    (ladyAssertion.directedRA [.implicature]).conditions.length = 4 := by decide

/-- Surviving layers: pr, fr, fr at top level; negated imp as fr. -/
theorem lady_ra_layers :
    (ladyAssertion.directedRA [.implicature]).conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue, .atIssue] := by decide

/-! ### §4. Discourse pipeline: assertion → denial

Full pipeline for the modal example: assertion adds content (monotonic merge),
denial selectively retracts (non-monotonic RA*) — the paper's central claim that
assertion and denial are dual discourse operations, one monotonic and one not. -/

private def modalBackground : LDRS :=
  { drefs := [0], conditions := [⟨.presupposition, .atom 0 [0]⟩] }

private def modalContent : LDRS :=
  { drefs := []
  , conditions := [ ⟨.atIssue, .atom 1 [0]⟩
                   , ⟨.implicature, .neg (.atom 2 [0])⟩ ] }

private def modalCorrection : LDRS :=
  { drefs := [], conditions := [⟨.atIssue, .atom 2 [0]⟩] }

/-- Step 1: assertion is monotonic — merge adds conditions. -/
private def φ₁ : LDRS := modalBackground.merge modalContent

theorem assertion_grows :
    φ₁.conditions.length > modalBackground.conditions.length := by decide

/-- Step 2: denial update — merge correction, then apply RA*. -/
private def φ₃ : LDRS := φ₁.denialUpdate modalCorrection [.implicature]

/-- Denial update: 4 conditions = 2 surviving (pr + ◇right) + 1 correction
(□right) + 1 negated wrapper (¬[¬□right]). -/
theorem denial_result_length : φ₃.conditions.length = 4 := by decide

/-- All surviving content is at pr or fr level; no imp content remains. -/
theorem denial_result_layers :
    φ₃.conditions.map (·.layer)
    = [.presupposition, .atIssue, .atIssue, .atIssue] := by decide

/-- The imp layer has been fully retracted from the top level. -/
theorem implicature_retracted :
    (φ₃.conditions.map (·.layer)).count .implicature = 0 := by decide

/-! ### §5. Off → DenialDatum bridge

The Off computations above agree with the denial-type classification in
`Phenomena.Negation.Denial`: each Off result contains the target layer of the
corresponding `DenialDatum` — a semantic computation over layered propositions
matching the empirical denial-type taxonomy. -/

/-- The Off result for the modal example includes the datum's target layer. -/
theorem modal_off_agrees_with_datum :
    (offensiveLayers modalLayered (fun w => w == .nec) modalWorlds).contains
    possible_necessary.denialType.targetLayer = true := by decide

/-- The Off result for the KF example includes the datum's target layer. -/
theorem kf_off_agrees_with_datum :
    (offensiveLayers kfLayered (fun w => w == .noKing) kfWorlds).contains
    kingBald_presuppositional.denialType.targetLayer = true := by decide

/-- The Off result for the lady/wife example includes the datum's target layer. -/
theorem lady_off_agrees_with_datum :
    (offensiveLayers ladyLayered
      (fun w => w == .ladyWife || w == .notLadyWife) ladyWorlds).contains
    lady_wife.denialType.targetLayer = true := by decide

/-! ### §6. Denial ≠ negation (§2.1)

@cite{van-der-sandt-maier-2003} §2.1: denial and negation are orthogonal. Denial
is a discourse operation (non-monotonic correction); negation is a semantic
operator. A denial can use a positive sentence, and a negative sentence can be a
plain assertion. -/

/-- Positive denial exists: the denial utterance IS the correction, with no
negation involved. Denial is a discourse function, not a syntactic form. -/
theorem positive_denial_is_correction :
    maryHappy_positive.denial = maryHappy_positive.correction := rfl

/-- Positive denial is propositional — it targets fr, like negative propositional
denials. The mechanism is the same regardless of surface polarity. -/
theorem positive_denial_targets_fr :
    maryHappy_positive.denialType.targetLayer = .atIssue := rfl

/-- The same surface negation can correspond to different denial types,
disambiguated by the correction (§2.3: "still" denials, ex. 19–20). -/
theorem same_surface_different_types :
    still_propositional.denial = still_presuppositional.denial ∧
    still_propositional.denialType ≠ still_presuppositional.denialType :=
  ⟨rfl, by decide⟩

end VanDerSandtMaier2003
