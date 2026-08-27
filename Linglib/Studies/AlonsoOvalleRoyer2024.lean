import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Powerset
import Linglib.Semantics.Modality.IndefiniteDenotation
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
projected from the DP's event anchor (`Modality.modalIndefiniteSat`). The DP's event
variable is bound by the abstraction over the VP event (62), left free and read as the
assertion (69)/(71), or bound by an external modal's anchor (87)/(91); what the anchor
projects depends on the event (`Modality.ModalSource`): the decision that caused a
volitional event gives random choice — an indiscriminate decision, or one to take
everything, satisfies the component and a decision for one item does not (`randomChoice`,
Fig. 1, (32)–(33)) — and the assertion's content gives an epistemic component compatible
with any degree of ignorance and with knowing that the whole domain qualifies, but not with
knowing a proper part (`epistemic`, Figs. 2–3, (29)). A non-volitional verb's event has no
decision (`nonvolitional`, (34)), and an external argument merges above the VP abstraction,
so the flavors available at a site follow from the binders that reach it (`flavors`, §3.4,
fn. 17). *Yalnhej*'s claim has no upper bound where *algún*'s has (`notUpperBounded`,
(122)–(127)); *uno cualquiera* admits only decisions as anchors, so it has no epistemic
reading (`unoCualquiera_no_epistemic`, (67)–(68), (93)); under an imperative or an
attitude the anchor can be coindexed with the external modal's (`harmonic`, (82)–(85)).

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

open Modality Modality.Kratzer ModalLogic Mood Presupposition Data.Examples Finset

/-! ### Events and what they project -/

/-- Two items; a world records which of them the agent took (bought, liked, grabbed). -/
abbrev Item := Fin 2

abbrev World := Finset Item

/-- Item `y` is among what was taken. -/
def taken (y : Item) (w : World) : Prop := y ∈ w

instance (y : Item) : DecidablePred (taken y) := fun w => inferInstanceAs (Decidable (y ∈ w))

/-- The events of a scenario: the VP event, the assertion, an order, and a belief. -/
inductive Ev | vp | assertion | order | belief
  deriving DecidableEq

/-- A scenario: the worlds each event projects — the decision that caused the VP event, if
the verb is volitional; the speaker's doxastic alternatives; the addressee's to-do list; the
attitude holder's belief state. -/
structure Scenario where
  decision : Option (Finset World)
  dox : Finset World := ∅
  todo : Finset World := ∅
  belief : Finset World := ∅

/-- A scenario from the decision and the doxastic alternatives, with an optional order and
belief state. -/
def scenario (decision : Option (Finset World)) (dox : Finset World := ∅)
    (todo : Finset World := ∅) (belief : Finset World := ∅) : Scenario :=
  ⟨decision, dox, todo, belief⟩

/-- The worlds a scenario's event projects. -/
def Scenario.worlds (s : Scenario) : Ev → Option (Finset World)
  | .vp => s.decision
  | .assertion => some s.dox
  | .order => some s.todo
  | .belief => some s.belief

/-- The source of each event: a decision for the VP event, the declarative and imperative
speech acts, and the attitude. -/
def Scenario.source (s : Scenario) : Ev → Option (ModalSource World)
  | .vp => s.decision.map fun d => .decision fun _ => [(· ∈ d)]
  | .assertion => some (.speechAct (.declarative fun _ => [(· ∈ s.dox)]))
  | .order => some (.speechAct (.imperative fun _ => [(· ∈ s.todo)]))
  | .belief => some (.attitude fun _ => [(· ∈ s.belief)])

/-- The claim of a *yalnhej* DP over the whole domain, anchored to `e`. -/
def claim (s : Scenario) (e : Ev) (w : World) : Prop :=
  ∃ src ∈ s.source e, modalIndefiniteSat src univ (fun _ _ => True) taken w

theorem claim_iff (s : Scenario) (e : Ev) (w : World) :
    claim s e w ↔ ∃ d ∈ s.worlds e, (∃ x, x ∈ w) ∧ ∀ y, ∃ w' ∈ d, y ∈ w' := by
  cases e <;> cases s.decision <;>
    simp [claim, Scenario.source, Scenario.worlds, modalIndefiniteSat, simplePossibility,
      diamond, kratzerR, ModalSource.background, SpeechEvent.declarative, SpeechEvent.imperative,
      taken]

instance (s : Scenario) (e : Ev) (w : World) : Decidable (claim s e w) :=
  decidable_of_iff _ (claim_iff s e w).symm

/-- Worlds in which something was taken. -/
abbrev nonempty : Finset World := univ.filter Finset.Nonempty

/-- Fig. 1, (32)–(33): the indiscriminate decision *buy a book* and the decision *buy all
books* satisfy the modal component; the decision *buy b₁* does not. -/
theorem randomChoice :
    claim (scenario (some nonempty)) .vp {0} ∧ claim (scenario (some {{0, 1}})) .vp {0, 1} ∧
      ¬ claim (scenario (some {{0}})) .vp {0} := by
  simp only [claim_iff]; decide

/-- Figs. 2–3, (29): anchored to the assertion, the component holds under total or partial
ignorance and when the speaker knows the whole domain qualifies, but not when the speaker
knows which proper part does. -/
theorem epistemic :
    claim (scenario none nonempty) .assertion {0} ∧
      claim (scenario none {{0}, {0, 1}}) .assertion {0} ∧
      claim (scenario none {{0, 1}}) .assertion {0, 1} ∧
      ¬ claim (scenario none {{0}}) .assertion {0} := by
  simp only [claim_iff]; decide

/-- (34): a non-volitional VP event contains no decision, so nothing projects from it and
the random choice reading is unavailable whatever the world. -/
theorem nonvolitional (dox todo belief : Finset World) (w : World) :
    ¬ claim (scenario none dox todo belief) .vp w := by
  simp [claim_iff, Scenario.worlds, scenario]

/-- (82)–(85): under the imperative, projection from the addressee's deliberate decision
fails while projection from the order — any card permitted — succeeds. -/
theorem harmonic :
    ¬ claim (scenario (some {{0}}) ∅ {{0}, {1}}) .vp {0} ∧
      claim (scenario (some {{0}}) ∅ {{0}, {1}}) .order {0} := by
  simp only [claim_iff]; decide

/-! ### Items (§§4.2, 6.2) -/

/-- The denotation of a fragment entry in the scenario, anchored to `e`. -/
def denotes (mi : ModalIndefinite) (s : Scenario) (e : Ev) (w : World) : Prop :=
  ∃ src ∈ s.source e, (mi.denotation src univ (fun _ _ => True) taken).holds w

/-- (122)–(127): where everyone danced, *yalnhej* holds and the upper-bounded *algún* does
not. -/
theorem notUpperBounded :
    denotes Chuj.ModalIndefinites.yalnhej (scenario none {{0, 1}}) .assertion {0, 1} ∧
      ¬ denotes Spanish.ModalIndefinites.algún (scenario none {{0, 1}}) .assertion {0, 1} := by
  simp [denotes, Scenario.source, ModalIndefinite.denotation, PartialProp.holds,
    Chuj.ModalIndefinites.yalnhej, Spanish.ModalIndefinites.algún, upperBoundedSat,
    modalIndefiniteSat, simplePossibility, diamond, kratzerR, ModalSource.background,
    SpeechEvent.declarative, taken, AnchorConstraint.Admits]
  decide

/-- (67)–(68), (93): *uno cualquiera* admits only decisions as anchors, so anchored to the
assertion it is undefined — it has no epistemic reading. -/
theorem unoCualquiera_no_epistemic (s : Scenario) (w : World) :
    ¬ denotes Spanish.ModalIndefinites.unoCualquiera s .assertion w := by
  simp [denotes, Scenario.source, ModalIndefinite.denotation, PartialProp.holds,
    Spanish.ModalIndefinites.unoCualquiera, AnchorConstraint.Admits, ModalSource.IsDecision]

/-! ### Position and flavor (§3.4) -/

/-- The base position of the DP relative to the abstraction over the VP event: an external
argument merges above it (74), internal arguments and adjuncts below (62). -/
inductive Site | external | internal | adjunct
  deriving DecidableEq

def Site.belowVPAbstraction : Site → Bool
  | .external => false
  | .internal | .adjunct => true

/-- The events the DP's variable can be bound to at a site: the VP event where its
abstraction c-commands the DP, an external modal's anchor when embedded under one, and the
assertion when left free (fn. 17). -/
def binders (site : Site) (embedded : Option Ev) : List Ev :=
  (if site.belowVPAbstraction then [.vp] else []) ++ embedded.toList ++ [.assertion]

/-- The flavors a DP can express at a site in a scenario: those the sources of its
available binders project. -/
def flavors (s : Scenario) (site : Site) (embedded : Option Ev) : List ModalFlavor :=
  (binders site embedded).filterMap fun e => (s.source e).map ModalSource.flavor

/-- §3.4: an external argument is epistemic only; an internal argument or adjunct of a
volitional verb is random choice or epistemic, of a non-volitional verb epistemic only. -/
theorem flavors_pattern (d dox : Finset World) :
    flavors (scenario (some d) dox) .external none = [.epistemic] ∧
      flavors (scenario none dox) .external none = [.epistemic] ∧
      flavors (scenario (some d) dox) .internal none = [.circumstantial, .epistemic] ∧
      flavors (scenario none dox) .internal none = [.epistemic] ∧
      flavors (scenario (some d) dox) .adjunct none = [.circumstantial, .epistemic] ∧
      flavors (scenario none dox) .adjunct none = [.epistemic] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- A position row is predicted acceptable iff some binder available at its site projects
the reading's flavor and, when the row gives a scenario, the claim anchored there holds. -/
def positionPredicted (row : LinguisticExample) : Option Bool := do
  let site ← match row.feature? "position" with
    | some "external" => some Site.external
    | some "internal" => some .internal
    | some "adjunct" => some .adjunct
    | _ => none
  let fl ← row.feature? "reading" >>= readingFlavor
  let decision := if row.feature? "volitional" == some "yes" then
    some ((row.feature? "decision" >>= decisionOf).getD nonempty) else none
  let dox := (row.feature? "epistemicState" >>= doxOf).getD nonempty
  let s : Scenario := scenario decision dox
  let w : World := if row.feature? "epistemicState" == some "knows all" ||
    row.feature? "decision" == some "all" then {0, 1} else {0}
  return (binders site none).any fun e =>
    (s.source e).map ModalSource.flavor == some fl && decide (claim s e w)

/-- Every Chuj position row carries the predicted judgment. -/
theorem position_rows :
    ∀ row ∈ Examples.all, ∀ b ∈ positionPredicted row,
      (row.judgment == .acceptable) = b := by decide +kernel

/-- The fragment entry a row's `item` feature names. -/
def entryOf : String → Option ModalIndefinite
  | "yalnhej" => some Chuj.ModalIndefinites.yalnhej
  | "komon" => some Chuj.ModalIndefinites.komon
  | "algún" => some Spanish.ModalIndefinites.algún
  | "uno cualquiera" => some Spanish.ModalIndefinites.unoCualquiera
  | "irgendein" => some German.ModalIndefinites.irgendein
  | "n'importe quel" => some French.ModalIndefinites.nimporteQuel
  | "un qualsiasi" => some Italian.ModalIndefinites.unQualsiasi
  | _ => none

/-- A cross-linguistic row's prediction from its fragment entry: a reading is available iff
the entry has its flavor (or an unremarkable reading), it survives embedding iff the entry's
component is at-issue, a universal scenario is tolerated iff the entry is not upper-bounded,
and a predicative position needs a predicative entry. -/
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
      | r => (readingFlavor r).any (· ∈ e.flavors)
    return (!predicative || e.canBePredicate) && hasReading

/-- Every cross-linguistic row carries the judgment its fragment entry predicts, and every
reading it lists is available iff the entry has the flavor. -/
theorem entry_rows :
    ∀ row ∈ Examples.all, ∀ e ∈ row.feature? "item" >>= entryOf,
      (∀ b ∈ entryPredicted row, (row.judgment == .acceptable) = b) ∧
        ((row.feature? "survives").isNone →
          ∀ r ∈ row.readings, ∀ fl ∈ readingFlavor r.1,
            (r.2 == .acceptable) = decide (fl ∈ e.flavors)) := by
  decide +kernel

example : (∃ row ∈ Examples.all, (positionPredicted row).isSome) ∧
    ∃ row ∈ Examples.all, (entryPredicted row).isSome := by decide +kernel

end AlonsoOvalleRoyer2024
