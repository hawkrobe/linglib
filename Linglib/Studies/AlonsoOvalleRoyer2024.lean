import Linglib.Features.ModalIndefinite
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Studies.Coon2019
import Linglib.Fragments.Mayan.Chuj.ModalIndefinites
import Linglib.Fragments.Spanish.ModalIndefinites
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.Romance.French.ModalIndefinites
import Linglib.Fragments.Italian.ModalIndefinites

/-!
# Modal indefinites and semantic variation: lessons from Chuj

[alonso-ovalle-royer-2024]'s account of Chuj *yalnhej*: the modal
component is at-issue, event-relative
(`Semantics/Modality/EventRelativity`, after [hacquard-2006]), and its
flavor is derived from structural position and predicate volitionality
rather than stipulated lexically. The lexical entries live in the
`ModalIndefinites` fragments (Chuj, Spanish, German, French, Italian);
this file holds the paper's denotation, the cross-linguistic typology
over the pooled entries, the position × volitionality derivation, and
finite-model witnesses for non-maximality, upper-boundedness, and
harmonic anchoring.

One departure from [hacquard-2006] (§4.1, fn. 17): *yalnhej*'s anchor
can be left free — bound by the speech-act event rather than the
closest event binder — which is how external arguments above AspP still
access the speech event.

## Main declarations

* `modalIndefiniteSat`, `upperBoundedSat` — the paper's denotation (59).
* `allEntries` — the pooled fragment paradigms.
* `predictedMIFlavors`, `flavor_pattern_derived` — the position ×
  volitionality pattern, derived from `accessibleBinders` and
  `rcAvailable`.
-/

namespace AlonsoOvalleRoyer2024

open Semantics.Modality (ModalFlavor)
open Features.ModalIndefinite
open Semantics.Modality.EventRelativity
open Chuj.ModalIndefinites
open Spanish.ModalIndefinites
open German.ModalIndefinites
open French.ModalIndefinites
open Italian.ModalIndefinites

/-! ### The modal indefinite denotation ((59)) -/

section Denotation

variable {Event W Entity : Type*} (f : AnchoringFn Event W) (e : Event) (allW : List W)
  (domain : List Entity) (P Q : Entity → W → Prop) (w : W)

/-- The modal indefinite denotation (59):

    `⟦MI⟧^{f,e₁} = λP.λQ.λw. ∃x[P(x)(w) ∧ Q(x)(w)] ∧ ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]`

Some domain member satisfies restrictor and scope, and every restrictor
member is a possible scope-satisfier — the modal-variation effect. -/
def modalIndefiniteSat : Prop :=
  (∃ x ∈ domain, P x w ∧ Q x w) ∧
    ∀ y ∈ domain, P y w → possibility f e allW (λ w' => Q y w') w

instance [∀ y, DecidablePred (P y)] [∀ y, DecidablePred (Q y)] :
    Decidable (modalIndefiniteSat f e allW domain P Q w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The upper-bounded denotation: additionally, not every P is Q in the
actual world — *algún*'s witness upper bound (§4.2; distinct from the
anti-singleton *domain* constraint of
[alonso-ovalle-menendez-benito-2010]). -/
def upperBoundedSat : Prop :=
  modalIndefiniteSat f e allW domain P Q w ∧ ¬ ∀ x ∈ domain, P x w → Q x w

instance [∀ y, DecidablePred (P y)] [∀ y, DecidablePred (Q y)] :
    Decidable (upperBoundedSat f e allW domain P Q w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Upper-boundedness strengthens the plain denotation. -/
theorem upperBounded_entails_plain (h : upperBoundedSat f e allW domain P Q w) :
    modalIndefiniteSat f e allW domain P Q w := h.1

end Denotation

/-! ### The pooled sample -/

/-- The pooled cross-linguistic sample: the five fragment paradigms. -/
def allEntries : List ModalIndefiniteEntry :=
  Chuj.ModalIndefinites.paradigm ++ Spanish.ModalIndefinites.paradigm ++
  German.ModalIndefinites.paradigm ++ French.ModalIndefinites.paradigm ++
  Italian.ModalIndefinites.paradigm

/-! ### Typological Generalizations (§6) -/

/-- Status and content are independent: *yalnhej* and *irgendein* share
the same flavor inventory but differ in status (§6.1). -/
theorem yalnhej_irgendein_minimal_pair :
    yalnhejEntry.flavors = irgendeinEntry.flavors ∧
    yalnhejEntry.status ≠ irgendeinEntry.status := ⟨rfl, by decide⟩

/-- *Yalnhej* is the sample's only at-issue item with both epistemic
and random-choice flavors. -/
theorem yalnhej_unique_profile :
    (allEntries.filter (λ e =>
      e.status == .atIssue && e.hasFlavor .epistemic &&
      e.hasFlavor .circumstantial)).length = 1 := rfl

/-! ### Independence of Dimensions -/

/-- Status and upper-boundedness are independent: all four cells of the
    2×2 matrix are attested (*uno cualquiera*, *yalnhej*, *algún*,
    *irgendein*). -/
theorem status_ub_independent :
    (allEntries.any (λ e => e.status == .atIssue && e.upperBounded) &&
     allEntries.any (λ e => e.status == .atIssue && !e.upperBounded) &&
     allEntries.any (λ e => e.status == .notAtIssue && e.upperBounded) &&
     allEntries.any (λ e => e.status == .notAtIssue && !e.upperBounded)) = true := rfl

/-! ### AnchorConstraint Bridge -/

/-- Anchored entries are at-issue: event-relative anchoring is the
paper's mechanism for at-issue modal components. The converse fails —
*komon* is at-issue yet fits neither anchor constructor (§6.2). True
by construction of the entries. -/
theorem anchored_entries_at_issue :
    allEntries.all (λ e =>
      !e.anchorConstraint.isSome || e.status == .atIssue) = true := rfl

/-- The anchor constraint underdetermines flavor (§6.2): *uno
cualquiera*'s volitional-only f blocks epistemic readings, while the
unrestricted constraint admits both an epistemic item (*yalnhej*) and
a random-choice-only one (*n'importe quel*). -/
theorem anchor_constraint_underdetermines_flavor :
    unoCualquieraEntry.anchorConstraint = some .volitionalOnly ∧
    unoCualquieraEntry.hasFlavor .epistemic = false ∧
    yalnhejEntry.anchorConstraint = some .unrestricted ∧
    yalnhejEntry.hasFlavor .epistemic = true ∧
    nimporteQuelEntry.anchorConstraint = some .unrestricted ∧
    nimporteQuelEntry.hasFlavor .epistemic = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Position and accessible binders -/

/-- Structural position of a DP in the Chuj clause.
    Factored from verb volitionality (an orthogonal property of the
    predicate, not of the structural position). -/
inductive ChujArgPosition where
  /-- External argument (above vP): subject of transitive -/
  | external
  /-- Internal argument (within vP): object, complement -/
  | internal
  /-- Adjunct (adjoined to vP): locative, manner, etc. -/
  | adjunct
  deriving DecidableEq, Repr

/-- The event binders accessible from a position: external arguments
sit above the aspectual projection that binds the VP event, so only
the speech-act event is accessible; internal arguments and adjuncts
access both. -/
def accessibleBinders : ChujArgPosition → List EventBinder
  | .external => [.speechAct]
  | .internal => [.speechAct, .vpEvent]
  | .adjunct  => [.speechAct, .vpEvent]

/-! ### MI Flavor Derivation via EventBinder -/

/-- The MI flavor projected by an event binder: speech-act events
project epistemic, VP events circumstantial (via
`EventBinder.toAnchorType` and `AnchorType.toFlavor`). -/
def miAnchorFlavor (b : EventBinder) : ModalFlavor :=
  b.toAnchorType.toFlavor

/-- One flavor per accessible binder. -/
def baseMIFlavors (pos : ChujArgPosition) : List ModalFlavor :=
  (accessibleBinders pos).map miAnchorFlavor

/-- Random choice requires VP-event access (internal or adjunct
position) and a volitional predicate, whose decision subevent anchors
the reading. -/
def rcAvailable (pos : ChujArgPosition) (volitional : Bool) : Bool :=
  (accessibleBinders pos).any (· == .vpEvent) && volitional

/-- Predicted MI flavors: where random choice is unavailable, the
circumstantial flavor is filtered out. -/
def predictedMIFlavors (pos : ChujArgPosition) (volitional : Bool) : List ModalFlavor :=
  if rcAvailable pos volitional then
    baseMIFlavors pos
  else
    (baseMIFlavors pos).filter (· != .circumstantial)

/-! ### Flavor Pattern Verification -/

/-- The position × volitionality flavor pattern of §3.4, derived from
accessible binders, flavor projection, and the volitionality
constraint. -/
theorem flavor_pattern_derived :
    -- External arg: epistemic only (no VP event access → no RC)
    predictedMIFlavors .external true = [.epistemic] ∧
    predictedMIFlavors .external false = [.epistemic] ∧
    -- Internal arg, volitional: epistemic + RC
    predictedMIFlavors .internal true = [.epistemic, .circumstantial] ∧
    -- Internal arg, non-volitional: epistemic only
    predictedMIFlavors .internal false = [.epistemic] ∧
    -- Adjunct, volitional: epistemic + RC
    predictedMIFlavors .adjunct true = [.epistemic, .circumstantial] ∧
    -- Adjunct, non-volitional: epistemic only
    predictedMIFlavors .adjunct false = [.epistemic] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Voice heads to flavors

Voice heads with [D] introduce a specifier above AspP, whose event
variable is bound by the speech-act event; without [D] the highest DP
is the internal argument, accessible to both binders. -/

open Minimalist.Voice (Head) in

/-- Argument position from the Voice head: [+D] heads project an
external argument above AspP. -/
def argPositionOf (vh : Head) : ChujArgPosition :=
  if vh.hasD then .external else .internal

open Minimalist.Voice (Head) in

/-- Flavor predictions for a Voice head and predicate volitionality. -/
def predictedMIFlavorsOf (vh : Head) (volitional : Bool) : List ModalFlavor :=
  predictedMIFlavors (argPositionOf vh) volitional

open Coon2019 in

/-- Flavor predictions per voice head: the external-argument heads (Ø,
-w) admit epistemic only; the internal-argument heads (-ch, -j) admit
both with a volitional predicate and epistemic only without (§3.4). -/
theorem voice_flavor_predictions :
    predictedMIFlavorsOf vØ true = [.epistemic] ∧
    predictedMIFlavorsOf v_w true = [.epistemic] ∧
    predictedMIFlavorsOf v_ch true = [.epistemic, .circumstantial] ∧
    predictedMIFlavorsOf v_j true = [.epistemic, .circumstantial] ∧
    predictedMIFlavorsOf v_ch false = [.epistemic] ∧
    predictedMIFlavorsOf v_j false = [.epistemic] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Flavor selectivity (§6.2) -/

/-- *Komon* can never express speaker ignorance
    ([alonso-ovalle-royer-2021]); *yalnhej* can. -/
theorem komon_never_epistemic :
    komonEntry.hasFlavor .epistemic = false ∧
    yalnhejEntry.hasFlavor .epistemic = true := ⟨rfl, rfl⟩

/-! ### Unremarkable Readings and Predicativity (§5) -/

/-- Predicativity and unremarkable readings coincide across all seven
entries (§5). True by construction of the entries — the two fields were
filled from the same diagnostics — so this records the encoding, not an
independent prediction. -/
theorem predicativity_correlates_unremarkable :
    allEntries.all (λ e =>
      e.canBePredicate == e.hasUnremarkableReading) = true := rfl

/-- Number-neutral items lack upper-boundedness. (Footnote 18 of
[alonso-ovalle-royer-2024], p. 32, crediting Louise McNally (p.c.):
the lack of an upper bound for *yalnhej* DPs may be tied to their
being semantically number neutral.) -/
theorem numberNeutral_implies_not_ub :
    (allEntries.filter (·.numberNeutral)).all (!·.upperBounded) = true := rfl

/-! ### Worked examples

Finite-model witnesses instantiating the denotations above:
non-maximality and the upper-bound contrast (book scenario, §3.2.4)
and the harmonic vs non-harmonic anchoring distinction (card scenario,
§4.3). -/

/-! ### Book scenario -/

/-- Three books for testing the modal indefinite semantics. -/
inductive Book where | a | b | c
  deriving DecidableEq, Repr, Inhabited

/-- Three possible worlds varying in which books are available. -/
inductive BookWorld where
  | abc   -- all three available
  | ab    -- only a, b available
  | ac    -- only a, c available
  deriving DecidableEq, Repr, Inhabited

instance : Fintype BookWorld where
  elems := {.abc, .ab, .ac}
  complete := λ w => by cases w <;> decide

private def allBooks : List Book := [.a, .b, .c]
private def allBW : List BookWorld := [.abc, .ab, .ac]

/-- "is a book": always true for our domain. -/
private def isBook : Book → BookWorld → Prop := λ _ _ => True

instance (book : Book) : DecidablePred (isBook book) := fun _ => instDecidableTrue

/-- "is available": varies by world. -/
private def isAvailable : Book → BookWorld → Prop
  | .a, _ => True            -- book a always available
  | .b, .abc => True
  | .b, .ab => True
  | .b, .ac => False
  | .c, .abc => True
  | .c, .ab => False
  | .c, .ac => True

instance : ∀ (book : Book), DecidablePred (isAvailable book)
  | .a, _ => instDecidableTrue
  | .b, .abc => instDecidableTrue
  | .b, .ab => instDecidableTrue
  | .b, .ac => instDecidableFalse
  | .c, .abc => instDecidableTrue
  | .c, .ab => instDecidableFalse
  | .c, .ac => instDecidableTrue

/-- A speech event and a described event. -/
inductive SpeechOrDescribed where | speech | described
  deriving DecidableEq, Repr

/-- Epistemic anchoring: the speaker considers all three worlds possible. -/
private def fEPI : AnchoringFn SpeechOrDescribed BookWorld :=
  λ _ _ => []  -- empty background → all worlds accessible

/-- *Yalnhej* on the book model: it holds both when every book is
    available (abc) and when not all are (ab) — non-maximal and not
    upper-bounded — while the upper-bounded denotation fails in abc.
    A maximal item would fail in ab; an upper-bounded item (*algún*)
    fails in abc. -/
theorem yalnhej_three_way_contrast :
    -- yalnhej OK in abc (all available)
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .abc ∧
    -- yalnhej OK in ab (not all available) — non-maximal
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .ab ∧
    -- UB fails in abc (all satisfy scope → anti-singleton violated)
    ¬ upperBoundedSat fEPI .speech allBW allBooks isBook isAvailable .abc := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Card scenario

Under an external modal the MI's anchor can be co-indexed with the
modal's event ("any X is fine" — harmonic) or bound to the described
event ("a random X" — non-harmonic). Three cards, worlds varying in
which cards are grabbable, and two anchoring events. -/

/-- Three cards for testing harmonic readings. -/
inductive Card where | c1 | c2 | c3
  deriving DecidableEq, Repr, Inhabited

/-- Three worlds varying in which cards are grabbable. -/
inductive CardWorld where
  | all    -- all three grabbable
  | only1  -- only c1 grabbable
  | only2  -- only c2 grabbable
  deriving DecidableEq, Repr, Inhabited

private def allCards : List Card := [.c1, .c2, .c3]
private def allCW : List CardWorld := [.all, .only1, .only2]

/-- "is a card": always true in our domain. -/
private def isCard : Card → CardWorld → Prop := λ _ _ => True

instance (c : Card) : DecidablePred (isCard c) := fun _ => instDecidableTrue

/-- "can grab": which cards are grabbable in which worlds. -/
private def canGrab : Card → CardWorld → Prop
  | .c1, .all   => True
  | .c1, .only1 => True
  | .c1, .only2 => False
  | .c2, .all   => True
  | .c2, .only1 => False
  | .c2, .only2 => True
  | .c3, .all   => True
  | .c3, .only1 => False
  | .c3, .only2 => False

instance : ∀ (c : Card), DecidablePred (canGrab c)
  | .c1, .all   => instDecidableTrue
  | .c1, .only1 => instDecidableTrue
  | .c1, .only2 => instDecidableFalse
  | .c2, .all   => instDecidableTrue
  | .c2, .only1 => instDecidableFalse
  | .c2, .only2 => instDecidableTrue
  | .c3, .all   => instDecidableTrue
  | .c3, .only1 => instDecidableFalse
  | .c3, .only2 => instDecidableFalse

/-- Three event types: speech, local (described), imperative. -/
inductive GrabEvent where | speech | local | imperative
  deriving DecidableEq, Repr

/-- Anchoring function for the card scenario.
    - Speech event: empty background (all worlds accessible).
    - Local event: restricts to worlds where local circumstances hold
      (only world `only1` — current situation has only c1 available).
    - Imperative event: all worlds accessible (any card COULD be
      grabbed if permitted). -/
private def fGrab : AnchoringFn GrabEvent CardWorld
  | .speech, _ => []  -- all worlds accessible
  | .local, _ => [λ w => w == .only1]  -- only `only1` accessible
  | .imperative, _ => []  -- all worlds accessible (permission domain)

/-- The two readings are formally distinct on the card model: anchored
    to the local event, only c1 is grabbable and the modal component
    fails; co-indexed with the imperative event, every card is
    grabbable in some accessible world — "any card is fine". Same
    world, domain, and predicates; only the anchoring event differs. -/
theorem harmonic_nonharmonic_contrast :
    ¬ modalIndefiniteSat fGrab .local allCW allCards isCard canGrab .only1 ∧
    modalIndefiniteSat fGrab .imperative allCW allCards isCard canGrab .only1 := by
  exact ⟨by decide, by decide⟩

end AlonsoOvalleRoyer2024
