import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Powerset
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Fragments.Mayan.Chuj.ModalIndefinites
import Linglib.Fragments.Spanish.ModalIndefinites
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.Romance.French.ModalIndefinites
import Linglib.Fragments.Italian.ModalIndefinites
import Linglib.Data.Examples.AlonsoOvalleRoyer2024

/-!
# Alonso-Ovalle & Royer (2024): modal indefinites and semantic variation in Chuj

Chuj *yalnhej* DPs are existential quantifiers with an at-issue modal component (59): some
member of the domain satisfies restrictor and scope, and every member does so in some world
projected from the DP's event anchor (`modalIndefiniteSat`, over the anchored Kratzer
background of `Semantics/Modality/EventRelativity`). Anchored to the VP event of a
volitional verb, the worlds are those fulfilling the agent's decision, and the component is
random choice: an indiscriminate decision, or a decision to take everything, satisfies it and
a decision for one particular item does not (`randomChoice`, Fig. 1, (32)–(33)). Anchored to
the assertion, the worlds are the speaker's doxastic alternatives and the component is
epistemic, compatible with total or partial ignorance and with knowing that the whole domain
qualifies, but not with knowing a proper part (`epistemic`, Figs. 2–3, (29)). A non-volitional
verb supplies no decision (`nonvolitional`, (34)), and external arguments sit too high to be
cobound with the VP event, so position and volitionality fix the available flavors
(`flavors`, §3.4). The existential component has no upper bound, unlike *algún* and *uno
cualquiera* (`upperBoundedSat`, `notUpperBounded`, (122)–(127)); under an imperative or an
attitude the anchor can be coindexed with the external modal's, the harmonic readings of
§4.3 (`harmonic`, (82)–(85)).

The rows record the paper's context-relative judgments: `position_rows` checks the
flavor pattern and the epistemic and decision scenarios against the models, and
`entry_rows` checks the cross-linguistic contrasts of §§5–6 (at-issue status under
embedding, flavor selectivity, unremarkable readings, upper bounds) against the
`ModalIndefiniteEntry` fragments.

## References

* [alonso-ovalle-royer-2024]
* [alonso-ovalle-royer-2022]
* [alonso-ovalle-royer-2021]
* [alonso-ovalle-menendez-benito-2018]
* [alonso-ovalle-menendez-benito-2010]
* [hacquard-2006]
* [kratzer-shimoyama-2002]
* [von-fintel-2000-whatever]
* [jayez-tovena-2006]
* [chierchia-2013]
-/

namespace AlonsoOvalleRoyer2024

open Modality Modality.Kratzer ModalLogic Features.ModalIndefinite Data.Examples Finset

/-! ### The denotation (59) -/

section Denotation

variable {Event W E : Type*} (f : AnchoringFn Event W) (e : Event) (D : Finset E)
  (P Q : E → W → Prop) (w : W)

/-- (59): some member of the domain satisfies restrictor and scope, and every restrictor
member satisfies the scope in some world projected from the anchor `e`. Events are
collapsed into worlds: `Q y w'` stands for the existence of an alternative event `e' ≈ e` in
`w'` with `y` as its argument. -/
def modalIndefiniteSat : Prop :=
  (∃ x ∈ D, P x w ∧ Q x w) ∧ ∀ y ∈ D, P y w → simplePossibility (f e) (Q y) w

/-- The upper-bounded variant of *algún* and *uno cualquiera* (§6.2): not every member of
the domain satisfies the scope. -/
def upperBoundedSat : Prop := modalIndefiniteSat f e D P Q w ∧ ¬ ∀ x ∈ D, P x w → Q x w

theorem upperBounded_entails (h : upperBoundedSat f e D P Q w) :
    modalIndefiniteSat f e D P Q w := h.1

end Denotation

/-! ### Anchors: decisions and belief states (§4) -/

/-- Two items; a world records which of them the agent took (bought, liked, grabbed). -/
abbrev Item := Fin 2

abbrev World := Finset Item

/-- The values of the DP's event variable: cobound with the VP event (62), free and
restricted to the assertion (71), or coindexed with an external modal's anchor (87). -/
inductive Anchor | vpEvent | assertion | external
  deriving DecidableEq

/-- The worlds a scenario projects from each anchor: the VP event the worlds fulfilling the
agent's decision (§4.1), the assertion the speaker's doxastic alternatives (§4.2), and an
external modal its own domain. -/
def accessible (decision dox ext : Finset World) : Anchor → Finset World
  | .vpEvent => decision
  | .assertion => dox
  | .external => ext

/-- The anchoring function of a scenario. -/
def anchor (decision dox ext : Finset World) : AnchoringFn Anchor World :=
  fun a _ => [(· ∈ accessible decision dox ext a)]

/-- Item `y` is among what was taken. -/
def taken (y : Item) (w : World) : Prop := y ∈ w

instance (y : Item) : DecidablePred (taken y) := fun w => inferInstanceAs (Decidable (y ∈ w))

/-- The claim of a *yalnhej* DP over the whole domain, with the scenario's anchors. -/
def claim (decision dox ext : Finset World) (a : Anchor) (w : World) : Prop :=
  modalIndefiniteSat (anchor decision dox ext) a univ (fun _ _ => True) taken w

/-- The upper-bounded claim of *algún* or *uno cualquiera*. -/
def claimUB (decision dox ext : Finset World) (a : Anchor) (w : World) : Prop :=
  upperBoundedSat (anchor decision dox ext) a univ (fun _ _ => True) taken w

theorem claim_iff (decision dox ext : Finset World) (a : Anchor) (w : World) :
    claim decision dox ext a w ↔
      (∃ x, x ∈ w) ∧ ∀ y, ∃ w' ∈ accessible decision dox ext a, y ∈ w' := by
  unfold claim modalIndefiniteSat simplePossibility anchor
  simp [diamond, kratzerR, taken]

theorem claimUB_iff (decision dox ext : Finset World) (a : Anchor) (w : World) :
    claimUB decision dox ext a w ↔ claim decision dox ext a w ∧ ¬ ∀ x, x ∈ w := by
  simp [claimUB, upperBoundedSat, claim, taken]

instance (decision dox ext : Finset World) (a : Anchor) (w : World) :
    Decidable (claim decision dox ext a w) :=
  decidable_of_iff _ (claim_iff decision dox ext a w).symm

/-- Worlds in which something was taken. -/
abbrev nonempty : Finset World := univ.filter Finset.Nonempty

/-- Fig. 1, (32)–(33): the indiscriminate decision *buy a book* and the decision *buy all
books* satisfy the modal component; the decision *buy b₁* does not. -/
theorem randomChoice :
    claim nonempty ∅ ∅ .vpEvent {0} ∧ claim {{0, 1}} ∅ ∅ .vpEvent {0, 1} ∧
      ¬ claim {{0}} ∅ ∅ .vpEvent {0} := by
  simp only [claim_iff]; decide

/-- Figs. 2–3, (29): the epistemic component holds under total or partial ignorance and when
the speaker knows the whole domain qualifies, but not when the speaker knows which proper
part does. -/
theorem epistemic :
    claim ∅ nonempty ∅ .assertion {0} ∧ claim ∅ {{0}, {0, 1}} ∅ .assertion {0} ∧
      claim ∅ {{0, 1}} ∅ .assertion {0, 1} ∧ ¬ claim ∅ {{0}} ∅ .assertion {0} := by
  simp only [claim_iff]; decide

/-- (34): a non-volitional VP event contains no decision, so nothing projects from it and
the random choice reading is unavailable whatever the world. -/
theorem nonvolitional (dox ext : Finset World) (w : World) : ¬ claim ∅ dox ext .vpEvent w := by
  simp [claim_iff, accessible]

/-- (122)–(127): where everyone danced, *yalnhej* is fine and the upper-bounded item is not. -/
theorem notUpperBounded :
    claim ∅ {{0, 1}} ∅ .assertion {0, 1} ∧ ¬ claimUB ∅ {{0, 1}} ∅ .assertion {0, 1} := by
  simp only [claimUB_iff, claim_iff]; decide

/-- (82)–(85): under the imperative, projection from the addressee's deliberate decision
fails while projection from the order — any card permitted — succeeds. -/
theorem harmonic :
    ¬ claim {{0}} ∅ {{0}, {1}} .vpEvent {0} ∧ claim {{0}} ∅ {{0}, {1}} .external {0} := by
  simp only [claim_iff]; decide

/-! ### Position and flavor (§3.4) -/

/-- The base position of the DP. -/
inductive Position | external | internal | adjunct
  deriving DecidableEq

/-- The anchors a position can take: an external argument sits above the VP event and
must leave its anchor free (fn. 17); internal arguments and adjuncts may be cobound with
it. -/
def anchors : Position → List Anchor
  | .external => [.assertion]
  | .internal | .adjunct => [.vpEvent, .assertion]

/-- The flavor an anchor projects: the assertion is epistemic; the VP event projects random
choice only when the verb is volitional, since only then it contains a decision. -/
def flavorOf (volitional : Bool) : Anchor → Option ModalFlavor
  | .assertion => some .epistemic
  | .vpEvent => if volitional then some .circumstantial else none
  | .external => none

/-- The flavors available in a position with a volitional or non-volitional verb. -/
def flavors (pos : Position) (volitional : Bool) : List ModalFlavor :=
  (anchors pos).filterMap (flavorOf volitional)

/-! ### The paper's judgments -/

/-- The reading a row names, as a flavor. -/
def readingFlavor : String → Option ModalFlavor
  | "epistemic" => some .epistemic
  | "random choice" => some .circumstantial
  | _ => none

/-- The doxastic alternatives a row's `epistemicState` names, with `{0}` the actual world. -/
def doxOf : String → Option (Finset World)
  | "ignorant" => some nonempty
  | "knows which, not all" => some {{0}}
  | "knows all" => some {{0, 1}}
  | _ => none

/-- The decision a row's `decision` feature names. -/
def decisionOf : String → Option (Finset World)
  | "indiscriminate" => some nonempty
  | "specific" => some {{0}}
  | "all" => some {{0, 1}}
  | _ => none

/-- A position row is predicted acceptable iff its reading's flavor is available there and,
when a scenario is given, the scenario satisfies the modal component. -/
def positionPredicted (row : LinguisticExample) : Option Bool := do
  let pos ← match row.feature? "position" with
    | some "external" => some Position.external
    | some "internal" => some .internal
    | some "adjunct" => some .adjunct
    | _ => none
  let fl ← row.feature? "reading" >>= readingFlavor
  let vol := row.feature? "volitional" == some "yes"
  let scenario : Bool := match fl, row.feature? "epistemicState", row.feature? "decision" with
    | .epistemic, some s, _ => (doxOf s).any fun dox =>
      decide (claim ∅ dox ∅ .assertion (if s = "knows all" then {0, 1} else {0}))
    | .circumstantial, _, some d => (decisionOf d).any fun dec =>
      decide (claim dec ∅ ∅ .vpEvent (if d = "all" then {0, 1} else {0}))
    | _, _, _ => true
  return (flavors pos vol).contains fl && scenario

/-- Every Chuj position row carries the predicted judgment. -/
theorem position_rows :
    ∀ row ∈ Examples.all, ∀ b, positionPredicted row = some b →
      (row.judgment == .acceptable) = b := by decide +kernel

/-- The fragment entry a row's `item` feature names. -/
def entryOf : String → Option ModalIndefiniteEntry
  | "yalnhej" => some Chuj.ModalIndefinites.yalnhejEntry
  | "komon" => some Chuj.ModalIndefinites.komonEntry
  | "algún" => some Spanish.ModalIndefinites.algúnEntry
  | "uno cualquiera" => some Spanish.ModalIndefinites.unoCualquieraEntry
  | "irgendein" => some German.ModalIndefinites.irgendeinEntry
  | "n'importe quel" => some French.ModalIndefinites.nimporteQuelEntry
  | "un qualsiasi" => some Italian.ModalIndefinites.unQualsiasiEntry
  | _ => none

/-- The judgment a reading carries in a row's `readings`, if listed. -/
def readingJudgment (row : LinguisticExample) (r : String) : Option Bool :=
  (row.readings.find? (·.1 == r)).map (·.2 == .acceptable)

/-- A cross-linguistic row's prediction from its fragment entry: a reading is available iff
the entry has its flavor (or an unremarkable reading), it survives embedding iff the entry's
modal component is at-issue, a universal scenario is tolerated iff the entry is not
upper-bounded, and a predicative position needs a predicative entry. -/
def entryPredicted (row : LinguisticExample) : Option Bool := do
  let e ← row.feature? "item" >>= entryOf
  if (row.feature? "position").any (· ∈ ["external", "internal", "adjunct"]) then none
  if row.feature? "scenario" == some "universal" then return !e.upperBounded
  if let some s := row.feature? "survives" then return (s == "yes") == (e.status == .atIssue)
  let predicative := row.feature? "position" == some "predicative"
  match row.feature? "reading" with
  | none => if predicative then return e.canBePredicate else none
  | some reading =>
    let hasReading := match reading with
      | "unremarkable" => e.hasUnremarkableReading
      | r => (readingFlavor r).any e.hasFlavor
    return (!predicative || e.canBePredicate) && hasReading

/-- Every cross-linguistic row carries the judgment its fragment entry predicts, and every
reading it lists is available iff the entry has the flavor. -/
theorem entry_rows :
    ∀ row ∈ Examples.all, ∀ e ∈ row.feature? "item" >>= entryOf,
      (∀ b ∈ entryPredicted row, (row.judgment == .acceptable) = b) ∧
        ((row.feature? "survives").isNone →
          ∀ r ∈ row.readings, ∀ fl ∈ readingFlavor r.1, (r.2 == .acceptable) = e.hasFlavor fl) := by
  decide +kernel

example : (∃ row ∈ Examples.all, (positionPredicted row).isSome) ∧
    ∃ row ∈ Examples.all, (entryPredicted row).isSome := by decide +kernel

end AlonsoOvalleRoyer2024
