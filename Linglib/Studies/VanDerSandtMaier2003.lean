import Linglib.Semantics.Presupposition.ContentLayer
import Linglib.Data.Examples.VanDerSandtMaier2003

/-!
# Van der Sandt & Maier (2003) — Denials in Discourse
[van-der-sandt-maier-2003]

Denials in Discourse. Michigan Linguistics and Philosophy Workshop, 2003.

Formalization of directed reverse anaphora (RA*) applied to the paper's worked
examples, connecting:

- `Semantics.ContentLayer` — `offensiveLayers` (which layers are offensive)
- `Data/Examples/VanDerSandtMaier2003.json` — the paper's denial/correction
  discourse rows

## Denial ≠ negation

The paper's central architectural claim: denial and negation are orthogonal.
Negation is a semantic operator; denial is a discourse operation
(non-monotonic correction of contextual information). A denial can use a
positive sentence ("Mary IS happy" denying "Mary is unhappy", ex. 6), and a
negative sentence can be a plain assertion. The `DenialType` taxonomy below
classifies denials by the content layer the correction targets — one
mechanism, three targets.

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
open Data.Examples

/-! ### Denial taxonomy

[van-der-sandt-maier-2003]'s three denial types are not different operations
but one mechanism (non-monotonic discourse correction) targeting different
content layers. The fourth empirical category — register/connotation denials
like "not a LAdy — my WIfe" (69) — maps to the implicature layer alongside
scalar implicature. -/

/-- The type of a denial, determined by which content layer the correction
targets. -/
inductive DenialType where
  /-- Targets at-issue content; the presupposition survives.
      (5): "Mary is not happy." -/
  | propositional
  /-- Targets presupposed content; the assertion falls with it.
      (30b): "The king of France is NOT bald — France does not have a king." -/
  | presuppositional
  /-- Targets enrichment beyond truth conditions; literal meaning survives.
      (29b): "It's not POSSIBLE — it's NECESSARY." -/
  | implicature
  deriving DecidableEq, Repr

/-- Map a denial type to the content layer it targets. -/
def DenialType.targetLayer : DenialType → ContentLayer
  | .propositional => .atIssue
  | .presuppositional => .presupposition
  | .implicature => .implicature

/-- No two denial types target the same layer: the taxonomy is exactly the
layer structure. -/
theorem DenialType.targetLayer_injective :
    Function.Injective DenialType.targetLayer := by
  intro d₁ d₂ h
  cases d₁ <;> cases d₂ <;> simp_all [targetLayer]

/-! ### Layered DRT (LDRT) substrate

[van-der-sandt-maier-2003] extend DRT with content layers: each condition
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

[van-der-sandt-maier-2003]: given the offensive layers (computed by
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

The row `vdsm2003_ex30b_king` uses a different sentence (ex. 30b) but the same
scenario and denial type — presuppositional; the §5 transfer theorem connects
the Off computation to every row tagged with this scenario. -/

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
omitted; Off depends only on σ₁ + σ₄. The row `vdsm2003_ex13_lady` uses a
related sentence (ex. 13) but the same scenario and denial type. -/

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

/-! ### §5. Off → row transfer

The Off computations above agree with the paper's denial-type classification
of its rows (`Data/Examples/VanDerSandtMaier2003.json`): for every row whose
discourse scenario is formalized as a `LayeredProp` above, the computed
offensive layers include the layer targeted by the row's denial type. -/

/-- Denial-type adapter: the row's `denial_type` feature as a `DenialType`. -/
def denialTypeOf (row : LinguisticExample) : Option DenialType :=
  match row.feature? "denial_type" with
  | some "propositional" => some .propositional
  | some "presuppositional" => some .presuppositional
  | some "implicature" => some .implicature
  | _ => none

/-- The Off computation of the `LayeredProp` scenario named by the row's
`scenario` feature. -/
private def scenarioOff (row : LinguisticExample) : Option (List ContentLayer) :=
  match row.feature? "scenario" with
  | some "kingOfFrance" =>
      some (offensiveLayers kfLayered (fun w => w == .noKing) kfWorlds)
  | some "modal" =>
      some (offensiveLayers modalLayered (fun w => w == .nec) modalWorlds)
  | some "lady" =>
      some (offensiveLayers ladyLayered
        (fun w => w == .ladyWife || w == .notLadyWife) ladyWorlds)
  | _ => none

/-- **Transfer**: the Off computation of every formalized scenario contains
the target layer of each row classified under that scenario. -/
theorem off_contains_target_layer :
    ∀ row ∈ Examples.all, ∀ d ∈ denialTypeOf row, ∀ off ∈ scenarioOff row,
      off.contains d.targetLayer = true := by
  decide

/-! ### §6. Denial ≠ negation (§2.1)

[van-der-sandt-maier-2003] §2.1: denial and negation are orthogonal. Denial
is a discourse operation (non-monotonic correction); negation is a semantic
operator. A denial can use a positive sentence, and a negative sentence can be a
plain assertion. -/

/-- Positive denial is propositional: every row whose denial utterance is
syntactically positive (ex. 6, where the denial IS the correction) targets fr,
like negative propositional denials. The mechanism is the same regardless of
surface polarity. -/
theorem positive_denial_propositional :
    ∀ row ∈ Examples.all, row.feature? "surface_polarity" = some "positive" →
      denialTypeOf row = some .propositional := by
  decide

/-- The same surface negation can correspond to different denial types,
disambiguated by the correction (§2.3: "still" denials, ex. 19–20): two rows
share the denial utterance (second discourse segment) but target different
layers. -/
theorem same_surface_different_types :
    ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all,
      r₁.discourseSegments[1]? = r₂.discourseSegments[1]? ∧
      denialTypeOf r₁ = some .propositional ∧
      denialTypeOf r₂ = some .presuppositional := by
  decide

end VanDerSandtMaier2003
