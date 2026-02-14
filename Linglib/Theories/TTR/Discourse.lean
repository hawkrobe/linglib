import Linglib.Theories.TTR.Core
import Linglib.Theories.DynamicSemantics.Core.Basic

/-!
# Type Theory with Records — Discourse State & Pragmatics

Discourse-level infrastructure for TTR (Cooper 2023, Chapters 2, 4, 5):

**Signs & Illocutionary Force**: TTRSign, IllocForce, ForcedSign (§2.5–2.6).

**Information States**: InfoState (gameboard), agenda operations,
  bridge to Core.CommonGround (§2.6).

**Parametric Content**: Parametric bg/fg, PPpty, PQuant, PQuantDet, PRel2 (§4.2–4.3).
  Bridge to Core.Presupposition.PrProp.

**Reference & Mental States**: HasNamed, NameContext, semPropNameP,
  TotalInfoState, AccommodationKind, Paderewski puzzle,
  Assgnmnt/Cntxt, semPron, parametric verb semantics,
  Parametric.combine (§4.3–4.7).

**Frames & Descriptions**: AmbTempFrame, Scale, RiseEvent,
  IndPpty/FramePpty, Bot, unique, semDefArt, semUniversal,
  FixedPtType, FrameType, restrictPpty, TravelFrame/PassengerFrame,
  semBeID, semBeScalar (§5.2–5.8).

## References

- Cooper (2023). From Perception to Communication. OUP. Ch 2, 4, 5.
- Ginzburg (2012). The Interactive Stance.
- Kripke (1979). A Puzzle about Belief.
- Löbner (1979, 1981, 2015). Functional concepts.
- Partee (1973). Some structural analogies between tenses and pronouns.
-/

namespace DynamicSemantics.TTR

-- ============================================================================
-- Signs & Illocutionary Force (§2.5–2.6)
-- ============================================================================

/-! ## § 2.6 Illocutionary force (Cooper ex 91)

Signs may carry illocutionary force: assertion, query, command,
or acknowledgement. -/

/-- Illocutionary force in TTR. Cooper (2023) §2.6, ex (91). -/
inductive IllocForce where
  | assertion
  | query
  | command
  | acknowledgement
  deriving Repr, DecidableEq

/-- A sign with illocutionary force. Cooper (2023) ex (91). -/
structure ForcedSign (Phon Cont : Type) extends TTRSign Phon Cont where
  illoc : IllocForce

/-- ForcedSign ⊑ TTRSign (adding illoc = more fields = subtype). -/
instance (Phon Cont : Type) : SubtypeOf (ForcedSign Phon Cont) (TTRSign Phon Cont) where
  up := ForcedSign.toTTRSign

/-- Bridge: TTR IllocForce → linglib ClauseType. -/
def IllocForce.toClauseType? : IllocForce → Option ClauseType
  | .assertion => some .declarative
  | .query => some .matrixQuestion
  | .command => none
  | .acknowledgement => none

/-- Bridge: linglib ClauseType → TTR IllocForce. -/
def IllocForce.fromClauseType : ClauseType → IllocForce
  | .declarative => .assertion
  | .matrixQuestion => .query
  | .embeddedQuestion => .query
  | .echo => .assertion

/-- Round-trip: fromClauseType preserves the declarative↔assertion mapping. -/
theorem illoc_declarative_roundtrip :
    IllocForce.toClauseType? (IllocForce.fromClauseType .declarative) =
    some .declarative := rfl

/-- Round-trip: fromClauseType preserves the question↔query mapping. -/
theorem illoc_question_roundtrip :
    IllocForce.toClauseType? (IllocForce.fromClauseType .matrixQuestion) =
    some .matrixQuestion := rfl

-- ============================================================================
-- Information States (§2.6)
-- ============================================================================

/-! ## § 2.6 Information states and gameboards (Cooper ex 88–90)

An information state (gameboard) has two parts:
- **Private**: the agent's agenda (plan of upcoming type acts)
- **Shared**: latest utterance + shared commitments -/

/-- An agent's information state (gameboard).
Cooper (2023) §2.6, ex (88). -/
structure InfoState (SignT CommT : Type) where
  /-- The agent's agenda: sign types planned for realization -/
  agenda : List SignT
  /-- The most recent utterance sign -/
  latestUtterance : Option SignT
  /-- Shared commitments (accumulated accepted content) -/
  commitments : CommT

/-- Initial information state: empty agenda, no utterance, base commitments. -/
def InfoState.initial {SignT CommT : Type} (baseComm : CommT) :
    InfoState SignT CommT where
  agenda := []
  latestUtterance := none
  commitments := baseComm

/-- Pop the top agenda item (ExecTopAgenda).
Cooper (2023) §2.6, ex (120). -/
def InfoState.execTopAgenda {SignT CommT : Type}
    (s : InfoState SignT CommT) : Option (SignT × InfoState SignT CommT) :=
  match s.agenda with
  | [] => none
  | top :: rest => some (top, { s with agenda := rest })

/-- Remove top agenda item after observation (DownDateAgenda). -/
def InfoState.downDateAgenda {SignT CommT : Type}
    (s : InfoState SignT CommT) : InfoState SignT CommT :=
  { s with agenda := s.agenda.drop 1 }

/-- Record a new utterance and update commitments. -/
def InfoState.integrate {SignT CommT : Type}
    (s : InfoState SignT CommT) (utt : SignT) (newComm : CommT) :
    InfoState SignT CommT where
  agenda := s.agenda
  latestUtterance := some utt
  commitments := newComm

/-- Push a new sign type onto the front of the agenda (PlanAckAss). -/
def InfoState.pushAgenda {SignT CommT : Type}
    (s : InfoState SignT CommT) (signType : SignT) :
    InfoState SignT CommT :=
  { s with agenda := signType :: s.agenda }

/-! ## Bridge to Core.CommonGround -/

/-- Bridge: a BProp-based information state's commitments form a CG. -/
def InfoState.toCG {W SignT : Type}
    (s : InfoState SignT (List (Core.Proposition.BProp W))) :
    Core.CommonGround.CG W where
  propositions := s.commitments

/-- Bridge theorem: initial state maps to empty common ground. -/
theorem infoState_initial_eq_empty_cg (W SignT : Type) :
    (InfoState.initial (SignT := SignT)
      ([] : List (Core.Proposition.BProp W))).toCG =
    Core.CommonGround.CG.empty := rfl

/-- Bridge: integrating a commitment = adding to common ground. -/
theorem integrate_comm_eq_cg_add {W SignT : Type}
    (s : InfoState SignT (List (Core.Proposition.BProp W)))
    (utt : SignT) (p : Core.Proposition.BProp W) :
    (s.integrate utt (p :: s.commitments)).toCG = s.toCG.add p := rfl

/-! ## Bridge to DynamicSemantics.Core.InfoState -/

/-- TTR's InfoState tracks discourse state via agenda/commitments.
DynamicSemantics.Core.InfoState tracks possibilities (world + assignment).
Bridge: a TTR InfoState with BProp commitments induces a Core InfoState
by filtering possibilities that satisfy all commitments. -/
def InfoState.toCoreInfoState {W E SignT : Type}
    (s : InfoState SignT (List (Core.Proposition.BProp W))) :
    Set (_root_.DynamicSemantics.Core.Possibility W E) :=
  { p | s.commitments.Forall (· p.world) }

-- ============================================================================
-- Information State Phenomena
-- ============================================================================

section InfoStatePhenomena

/-- String type example: a fetch game decomposes into sub-events. -/
inductive FetchEvent where
  | pickUp | throw | runAfter | pickUpReturn | return_
  deriving Repr, DecidableEq

def fetchGame : StringType FetchEvent where
  events := [.pickUp, .throw, .runAfter, .pickUpReturn, .return_]
  ne := by simp

def fetchThrow : StringType FetchEvent :=
  StringType.singleton .throw

def fetchRunAfter : StringType FetchEvent :=
  StringType.singleton .runAfter

example : (fetchThrow ⌢ fetchRunAfter).events = [.throw, .runAfter] := rfl

/-- The three type acts map to the three basic speech act types. -/
theorem typeAct_covers_illoc :
    ∀ ta : TypeAct, ∃ i : IllocForce,
      (ta = .judge ∧ i = .assertion) ∨
      (ta = .query ∧ i = .query) ∨
      (ta = .create ∧ i = .command) := by
  intro ta; cases ta
  · exact ⟨.assertion, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨.query, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨.command, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

example (T₁ T₂ : Type) (a : T₁) (b : T₂) : MeetType T₁ T₂ := (a, b)

/-- ExecTopAgenda returns None on empty agenda. -/
theorem exec_empty_agenda {SignT CommT : Type} (c : CommT) :
    (InfoState.initial c : InfoState SignT CommT).execTopAgenda = none := rfl

/-- PushAgenda then ExecTopAgenda recovers the pushed item. -/
theorem push_then_exec {SignT CommT : Type}
    (s : InfoState SignT CommT) (item : SignT) :
    (s.pushAgenda item).execTopAgenda = some (item, s) := by
  simp only [InfoState.pushAgenda, InfoState.execTopAgenda]

end InfoStatePhenomena

-- ============================================================================
-- Parametric Content (§4.2–4.3)
-- ============================================================================

/-! ## § 4.2–4.3 Parametric content

Cooper (2023) §4.3 introduces *parametric content*: semantic content that
depends on a context (a presupposition). A parametric content has:
- `bg` (background): a context type — the presupposition
- `fg` (foreground): a function from satisfying contexts to content -/

/-- Parametric content: a background type (presupposition) paired with
a foreground function from satisfying contexts to content.
Cooper (2023) §4.3, (14). -/
structure Parametric (Content : Type*) where
  /-- Background type — what the context must provide (presupposition) -/
  Bg : Type*
  /-- Foreground — content given a context satisfying the background -/
  fg : Bg → Content

/-- Parametric property: context-dependent property. -/
abbrev PPpty (E : Type) := Parametric (Ppty E)

/-- Parametric quantifier: context-dependent quantifier. -/
abbrev PQuant (E : Type) := Parametric (Quant E)

/-- Parametric quantifier determiner: context-dependent Det meaning. -/
abbrev PQuantDet (E : Type) := Parametric (Ppty E → Quant E)

/-- Parametric binary relation: context-dependent transitive verb meaning. -/
abbrev PRel2 (E : Type) := Parametric (Quant E → Ppty E)

/-- A trivial parametric content: no presupposition (bg = Unit). -/
def Parametric.trivial {Content : Type*} (c : Content) : Parametric Content :=
  ⟨Unit, λ _ => c⟩

/-- A trivial parametric content yields the same value for any context. -/
theorem Parametric.trivial_fg {Content : Type*} (c : Content) (u : Unit) :
    (Parametric.trivial c).fg u = c := rfl

/-! ## Bridge: Parametric ↔ PrProp (presupposition/assertion) -/

/-- Convert a Parametric (BProp W) to a PrProp. -/
def Parametric.toPrProp {W : Type*} (p : Parametric (Core.Proposition.BProp W))
    (presupTest : W → Bool) (bgWitness : (w : W) → presupTest w = true → p.Bg) :
    Core.Presupposition.PrProp W where
  presup := presupTest
  assertion := λ w =>
    if h : presupTest w = true then p.fg (bgWitness w h) w else false

/-- Convert a PrProp back to a Parametric. -/
def _root_.Core.Presupposition.PrProp.toParametric {W : Type*}
    (p : Core.Presupposition.PrProp W) :
    Parametric (Core.Proposition.BProp W) where
  Bg := { w : W // p.presup w = true }
  fg := λ _ => p.assertion

/-- Parametric ↔ PrProp roundtrip: the assertion component survives
when the presupposition holds. -/
theorem toParametric_toPrProp_assertion {W : Type*} (p : Core.Presupposition.PrProp W) (w : W)
    (hp : p.presup w = true) :
    (p.toParametric.toPrProp p.presup
      (λ w h => ⟨w, h⟩)).assertion w = p.assertion w := by
  simp only [Parametric.toPrProp, Core.Presupposition.PrProp.toParametric, dif_pos hp]

/-- When a Parametric has a Bool-valued background, it directly maps to PrProp. -/
def Parametric.toPrPropSimple {W : Type*}
    (presup : W → Bool) (assertion : (w : W) → presup w = true → Bool) :
    Core.Presupposition.PrProp W where
  presup := presup
  assertion := λ w => if h : presup w = true then assertion w h else false

-- ============================================================================
-- Reference & Mental States (§4.3–4.7)
-- ============================================================================

/-! ## § 4.3 Named predicate and parametric proper names -/

/-- The `named` predicate: `Named a n` means individual `a` bears name `n`. -/
class HasNamed (E : Type) where
  named : E → String → Prop

/-- Context for a proper name: an individual bearing the right name. -/
structure NameContext (E : Type) [HasNamed E] (name : String) where
  individual : E
  isNamed : HasNamed.named individual name

/-- Parametric proper name content (revised from Ch3). -/
def semPropNameP {E : Type} [HasNamed E] (name : String) : PQuant E :=
  ⟨NameContext E name, λ ctx => semPropName ctx.individual⟩

/-- Bridge: parametric proper name reduces to Ch3 `semPropName`
when the context is resolved to a specific individual. -/
theorem semPropNameP_resolved {E : Type} [HasNamed E] (name : String)
    (ctx : NameContext E name) :
    (semPropNameP name).fg ctx = semPropName ctx.individual := rfl

/-! ## § 4.4 Total information state and accommodation -/

/-- A total information state: long-term memory + dialogue gameboard. -/
structure TotalInfoState (Memory Board : Type) where
  /-- Long-term memory: persistent knowledge about individuals -/
  ltm : Memory
  /-- Dialogue gameboard: dependent on ltm for anchoring -/
  gb : Board

/-- The three accommodation strategies for presupposition resolution.
Cooper (2023) §4.4, (74). -/
inductive AccommodationKind where
  | gameboard
  | longTermMemory
  | noMatch
  deriving Repr, DecidableEq

/-- Accommodation preference: gameboard > long-term memory > no match. -/
def AccommodationKind.preference : AccommodationKind → Nat
  | .gameboard => 0
  | .longTermMemory => 1
  | .noMatch => 2

theorem gameboard_preferred_over_ltm :
    AccommodationKind.gameboard.preference < AccommodationKind.longTermMemory.preference := by
  decide

theorem ltm_preferred_over_noMatch :
    AccommodationKind.longTermMemory.preference < AccommodationKind.noMatch.preference := by
  decide

/-! ## § 4.5 Paderewski puzzle (Kripke 1979) -/

section Paderewski

variable {E : Type}

/-- Two-concept state: an agent has two memory entries for "Paderewski". -/
structure TwoConcept (E : Type) (pianist statesman : E → Prop) where
  asMusician : E
  asPolitician : E
  isPianist : pianist asMusician
  isStatesman : statesman asPolitician

/-- One-concept state: after learning the identity. -/
structure OneConcept (E : Type) (pianist statesman : E → Prop) where
  person : E
  isPianist : pianist person
  isStatesman : statesman person

/-- Merging two concepts when they turn out to be the same individual. -/
def TwoConcept.merge {pianist statesman : E → Prop}
    (tc : TwoConcept E pianist statesman)
    (identity : tc.asMusician = tc.asPolitician) :
    OneConcept E pianist statesman where
  person := tc.asMusician
  isPianist := tc.isPianist
  isStatesman := identity ▸ tc.isStatesman

theorem merge_person_eq {pianist statesman : E → Prop}
    (tc : TwoConcept E pianist statesman)
    (h : tc.asMusician = tc.asPolitician) :
    (tc.merge h).person = tc.asMusician := rfl

theorem merge_preserves_both {pianist statesman : E → Prop}
    (tc : TwoConcept E pianist statesman)
    (h : tc.asMusician = tc.asPolitician) :
    pianist (tc.merge h).person ∧ statesman (tc.merge h).person := by
  simp only [TwoConcept.merge]
  exact ⟨tc.isPianist, h ▸ tc.isStatesman⟩

/-- Bridge to Core.Intension: the Paderewski puzzle is an instance
of non-rigid identity. -/
theorem paderewski_nonrigid_identity
    (musician_concept politician_concept : Fin 2 → E)
    (w : Fin 2)
    (_hAgree : musician_concept w = politician_concept w)
    (hDisagree : ∃ w', musician_concept w' ≠ politician_concept w') :
    ¬ Core.Intension.CoExtensional musician_concept politician_concept := by
  intro hCoExt
  obtain ⟨w', hw'⟩ := hDisagree
  exact hw' (hCoExt w')

end Paderewski

/-! ## § 4.6 Unbound pronouns -/

/-- Variable assignment: maps natural-number indices to individuals. -/
def Assgnmnt (E : Type) := Nat → Option E

/-- An assignment with at least n bindings (all indices < n defined). -/
def Assgnmnt.hasBindings {E : Type} (g : Assgnmnt E) (n : Nat) : Prop :=
  ∀ i, i < n → (g i).isSome = true

/-- Empty assignment: no bindings. -/
def Assgnmnt.empty {E : Type} : Assgnmnt E := λ _ => none

/-- Update assignment at index i. -/
def Assgnmnt.update {E : Type} (g : Assgnmnt E) (i : Nat) (val : E) : Assgnmnt E :=
  λ j => if j = i then some val else g j

/-- Merge two assignments (left-biased). -/
def Assgnmnt.merge {E : Type} (g₁ g₂ : Assgnmnt E) : Assgnmnt E :=
  λ i => (g₁ i).orElse (λ _ => g₂ i)

/-- Updating then looking up the same index returns the value. -/
theorem Assgnmnt.update_same {E : Type} (g : Assgnmnt E) (i : Nat) (val : E) :
    (g.update i val) i = some val := by
  simp [Assgnmnt.update]

/-- Updating then looking up a different index returns the original. -/
theorem Assgnmnt.update_other {E : Type} (g : Assgnmnt E) (i j : Nat) (val : E)
    (h : j ≠ i) : (g.update i val) j = g j := by
  simp [Assgnmnt.update, h]

/-- Empty assignment has no bindings at any index. -/
theorem Assgnmnt.empty_none {E : Type} (i : Nat) :
    (Assgnmnt.empty : Assgnmnt E) i = none := rfl

/-- Merge with empty on the left returns the right assignment. -/
theorem Assgnmnt.merge_empty_left {E : Type} (g : Assgnmnt E) :
    Assgnmnt.merge Assgnmnt.empty g = g := by
  funext i; simp [Assgnmnt.merge, Assgnmnt.empty, Option.orElse]

/-- Propositional context. -/
abbrev PropCntxt := Type

/-- Full context: assignment + propositional context. -/
structure Cntxt (E : Type) (C : Type) where
  assignment : Assgnmnt E
  propCtx : C

/-- Pronoun semantics as a parametric quantifier. -/
def semPron {E : Type} : PQuant E :=
  ⟨E, λ a => semPropName a⟩

/-- Bridge: pronoun semantics reduces to semPropName when resolved. -/
theorem semPron_resolved {E : Type} (a : E) :
    (semPron (E := E)).fg a = semPropName a := rfl

/-! ### Parametric verb semantics -/

/-- Parametric intransitive verb content. -/
def semIntransVerbP {E : Type} (Bg : Type) (p : E → Type) : PPpty E :=
  ⟨Bg, λ _ => semCommonNoun p⟩

/-- Parametric transitive verb content. -/
def semTransVerbP {E : Type} (Bg : Type) (p : E → E → Type) :
    Parametric (Quant E → Ppty E) :=
  ⟨Bg, λ _ Q x => Q (λ y => p x y)⟩

/-- Bridge: transitive verb with trivial context reduces to Montague pattern. -/
theorem semTransVerbP_trivial {E : Type} (p : E → E → Type)
    (u : Unit) (Q : Quant E) (x : E) :
    (semTransVerbP Unit p).fg u Q x = Q (λ y => p x y) := rfl

/-! ### S-combinator for parametric content (α@β) -/

/-- Combine two parametric contents via function application. -/
def Parametric.combine {A B : Type*}
    (f : Parametric (A → B)) (x : Parametric A) : Parametric B :=
  ⟨f.Bg × x.Bg, λ ⟨bf, bx⟩ => f.fg bf (x.fg bx)⟩

/-- Combining trivial parametric contents is trivial. -/
theorem Parametric.combine_trivial {A B : Type*} (f : A → B) (a : A) :
    (Parametric.trivial f).combine (Parametric.trivial a) =
    ⟨Unit × Unit, λ ⟨_, _⟩ => f a⟩ := rfl

-- ============================================================================
-- Reference Phenomena
-- ============================================================================

section ReferencePhenomena

/-- Extended individuals for Ch4. -/
inductive Ind4 where
  | dudamel | beethoven | uchida | sam
  deriving Repr, DecidableEq

inductive Conductor4 : Ind4 → Type where
  | mk : Conductor4 .dudamel
inductive Composer4 : Ind4 → Type where
  | mk : Composer4 .beethoven
inductive Pianist4 : Ind4 → Type where
  | mk : Pianist4 .uchida
inductive Leaves4 : Ind4 → Type where
  | mk : Leaves4 .sam

instance : HasNamed Ind4 where
  named a n := match a, n with
    | .dudamel, "Dudamel" => True
    | .beethoven, "Beethoven" => True
    | .uchida, "Uchida" => True
    | .sam, "Sam" => True
    | _, _ => False

def samContext : NameContext Ind4 "Sam" :=
  ⟨.sam, trivial⟩

def samPQuant : PQuant Ind4 := semPropNameP "Sam"

theorem sam_resolves :
    samPQuant.fg samContext = semPropName .sam := rfl

def leavePPpty : PPpty Ind4 := semIntransVerbP Unit Leaves4

def samLeaves : Parametric Type :=
  samPQuant.combine leavePPpty

theorem samLeaves_resolved :
    samLeaves.fg ⟨samContext, ()⟩ = Leaves4 .sam := rfl

def samLeavesTrue : samLeaves.fg ⟨samContext, ()⟩ := Leaves4.mk

/-! ### Paderewski puzzle in the fragment -/

inductive PadInd where
  | paderewski
  deriving Repr, DecidableEq

inductive IsPianist : PadInd → Prop where
  | mk : IsPianist .paderewski

inductive IsStatesman : PadInd → Prop where
  | mk : IsStatesman .paderewski

def peterTwoConcept : TwoConcept PadInd IsPianist IsStatesman :=
  ⟨.paderewski, .paderewski, .mk, .mk⟩

def peterOneConcept : OneConcept PadInd IsPianist IsStatesman :=
  peterTwoConcept.merge rfl

theorem paderewski_both :
    IsPianist peterOneConcept.person ∧ IsStatesman peterOneConcept.person :=
  ⟨peterOneConcept.isPianist, peterOneConcept.isStatesman⟩

/-! ### Pronoun resolution -/

def samAssignment : Assgnmnt Ind4 := λ i =>
  match i with | 0 => some .sam | _ => none

theorem pronoun_resolves_to_sam :
    (semPron (E := Ind4)).fg .sam = semPropName .sam := rfl

end ReferencePhenomena

-- ============================================================================
-- Frames & Descriptions (§5.2–5.8)
-- ============================================================================

/-! ## §5.2–5.3 Common nouns, individual concepts, and the Partee puzzle -/

section FramesAndDescriptions

/-! ## §5.4 Frames as records -/

/-- Ambient temperature frame.
Cooper (2023) §5.4, (14). -/
structure AmbTempFrame (Loc : Type) (temp : Loc → Nat → Prop) where
  x : Nat
  loc : Loc
  constraint : temp loc x

/-- A scale maps frames to natural numbers. -/
abbrev Scale (Frame : Type) := Frame → Nat

/-- The canonical temperature scale. -/
def ζ_temp {Loc : Type} {temp : Loc → Nat → Prop} :
    Scale (AmbTempFrame Loc temp) :=
  λ r => r.x

/-! ### Rise events -/

/-- A rise event for a given frame type and scale. -/
structure RiseEvent (Frame : Type) (scale : Scale Frame) where
  before : Frame
  after : Frame
  rises : scale before < scale after

abbrev TempRiseEvent {Loc : Type} {temp : Loc → Nat → Prop} :=
  RiseEvent (AmbTempFrame Loc temp) ζ_temp

/-! ## §5.5 Individual-level vs frame-level properties -/

/-- Individual-level property. -/
abbrev IndPpty (E : Type) := Ppty E

/-- Frame-level property. -/
abbrev FramePpty (Frame : Type) := Frame → Type

/-- The bottom type: no witnesses. -/
abbrev Bot := Empty

/-- Applying a frame-level property to a non-frame yields ⊥. -/
def framePptyOnInd {E Frame : Type} (_p : FramePpty Frame) (_x : E) : Type := Bot

/-- Partee puzzle resolution: "ninety is rising" is type-inappropriate. -/
theorem partee_blocked {Loc : Type} {temp : Loc → Nat → Prop}
    (n : Nat) (rising : FramePpty (AmbTempFrame Loc temp)) :
    framePptyOnInd rising n = Bot := rfl

/-! ## §5.6 Definite descriptions as dynamic generalized quantifiers -/

/-- Uniqueness predicate: exactly one witness of type P. -/
def unique {E : Type} (P : Ppty E) : Prop :=
  ∃ x : E, Nonempty (P x) ∧ ∀ y : E, Nonempty (P y) → y = x

/-- Universal quantifier as a type. -/
def semUniversal {E : Type} (restr scope : Ppty E) : Type :=
  (x : E) → restr x → scope x

/-- The definite article as a type. -/
def semDefArt {E : Type} (restr scope : Ppty E) : Type :=
  propT (unique restr) × semUniversal restr scope

/-- The definite article entails the universal. -/
def defArt_entails_universal {E : Type} (P Q : Ppty E)
    (h : semDefArt P Q) : semUniversal P Q :=
  h.2

/-- Uniqueness and universality together give the definite article. -/
def unique_and_universal_gives_defArt {E : Type} (P Q : Ppty E)
    (hu : unique P) (hf : semUniversal P Q) : semDefArt P Q :=
  ⟨⟨hu⟩, hf⟩

/-! ## §5.6 Fixed-point types (ℱ) -/

/-- Fixed-point type of an individual-level property. -/
def FixedPtType {E : Type} (P : Ppty E) : Type := (x : E) × P x

theorem fixedPtType_sigma {E : Type} (P : Ppty E) :
    FixedPtType P = ((x : E) × P x) := rfl

/-! ## §5.7 Individual vs frame level nouns -/

/-- FrameType maps a predicate to its fixed-point type. -/
def FrameType {E : Type} (p : Ppty E) : Type := FixedPtType p

/-- A frame-level version of an individual-level predicate. -/
def pFrame {E : Type} (p : Ppty E) : FramePpty (FrameType p) :=
  λ frame => p frame.1

theorem pFrame_reduces {E : Type} (p : Ppty E) (x : E) (e : p x) :
    pFrame p ⟨x, e⟩ = p x := rfl

def frameType_subtype {E : Type} (p : Ppty E) (r : FrameType p) :
    p r.1 := r.2

def frame_implies_fixedPt {E : Type} (p : Ppty E) (r : FrameType p)
    (_e : pFrame p r) : p r.1 := r.2

/-! ### RestrictCommonNoun -/

/-- Restrict a property to a subtype. -/
def restrictPpty {E : Type} (P : Ppty E) (T : Ppty E) : Ppty E :=
  λ x => P x × T x

def restrictPpty_strengthens {E : Type} (P T : Ppty E) (x : E)
    (h : restrictPpty P T x) : P x := h.1

/-! ## §5.8 Passengers and ships -/

/-- A travel frame. -/
structure TravelFrame (Loc : Type) where
  source : Loc
  goal : Loc
  deriving DecidableEq

/-- A passenger frame. -/
structure PassengerFrame (E Loc : Type) (passenger : E → Prop)
    (take_journey : E → TravelFrame Loc → Prop) where
  x : E
  isPassenger : passenger x
  journey : TravelFrame Loc
  takesJourney : take_journey x journey

/-- IntransVerbIndToFrame. -/
def intransVerbFrame {E Frame : Type} (getInd : Frame → E) (p : E → Type) :
    FramePpty Frame :=
  λ frame => p (getInd frame)

/-! ### Plural predicates -/

/-- A plural (distributive) predicate. -/
def pluralPred {E : Type} (p : E → Type) (A : E → Prop) : Type :=
  ∀ a : E, A a → p a

def pluralPred_entails_each {E : Type} (p : E → Type) (A : E → Prop)
    (h : pluralPred p A) (a : E) (ha : A a) : p a := h a ha

/-! ### Proper parts of records (mereology) -/

/-- A projection from record type R₂ to R₁ witnesses that R₁ is
a "part" of R₂. -/
structure IsProperPart (R₁ R₂ : Type) where
  project : R₂ → R₁
  notIso : ¬ Function.Bijective project

def passengerToInd {E Loc : Type} {passenger : E → Prop}
    {take_journey : E → TravelFrame Loc → Prop} :
    PassengerFrame E Loc passenger take_journey → E :=
  λ pf => pf.x

/-- Two different passenger frames can project to the same individual. -/
theorem same_person_different_journeys
    {E Loc : Type} {passenger : E → Prop}
    {take_journey : E → TravelFrame Loc → Prop}
    (pf₁ pf₂ : PassengerFrame E Loc passenger take_journey)
    (_hx : pf₁.x = pf₂.x) (hj : pf₁.journey ≠ pf₂.journey) :
    pf₁ ≠ pf₂ :=
  λ heq => hj (congrArg PassengerFrame.journey heq)

end FramesAndDescriptions

/-! ### Copula variants -/

/-- SemBe_ID: identity for individuals. -/
def semBeID {E : Type} (x y : E) : Type := propT (x = y)

/-- SemBe_scalar: scalar identity via a scale function. -/
def semBeScalar {Frame : Type} (scale : Scale Frame) (frame : Frame) (n : Nat) : Type :=
  propT (scale frame = n)

-- ============================================================================
-- Frame Phenomena
-- ============================================================================

section FramePhenomena

inductive TempLoc where
  | chicago | stLouis
  deriving Repr, DecidableEq

def tempAt : TempLoc → Nat → Prop :=
  λ _loc _x => True

abbrev ConcreteTempFrame := AmbTempFrame TempLoc tempAt

def chicago90 : ConcreteTempFrame :=
  ⟨90, .chicago, trivial⟩

def chicago95 : ConcreteTempFrame :=
  ⟨95, .chicago, trivial⟩

def tempRising : RiseEvent ConcreteTempFrame ζ_temp :=
  ⟨chicago90, chicago95, by native_decide⟩

theorem temp_is_ninety : ζ_temp chicago90 = 90 := rfl

theorem ninety_not_a_frame :
    framePptyOnInd (λ _ : ConcreteTempFrame => PUnit) (90 : Nat) = Bot := rfl

/-! ### "The dog is Fido" vs "The temperature is ninety" -/

inductive Dog5 : Ind4 → Type where
  | fido : Dog5 .sam

def dogIsFido : semBeID Ind4.sam Ind4.sam := ⟨rfl⟩

def tempIsNinety : semBeScalar ζ_temp chicago90 90 := ⟨rfl⟩

/-! ### Definite article phenomena -/

theorem dogUnique : unique Dog5 :=
  ⟨.sam, ⟨Dog5.fido⟩, λ y hy => hy.elim (by intro h; cases h; rfl)⟩

def theDogLeft : semDefArt Dog5 Leaves4 :=
  ⟨⟨dogUnique⟩, λ x h => by cases h; exact Leaves4.mk⟩

/-! ### Fixed-point type phenomena -/

def fidoDogFrame : FixedPtType Dog5 := ⟨.sam, Dog5.fido⟩

def fixedPt_witness_satisfies : Dog5 fidoDogFrame.1 := fidoDogFrame.2

/-! ### Passenger individuation -/

def isPassenger5 : Ind4 → Prop := λ _ => True
def takesJourney5 : Ind4 → TravelFrame TempLoc → Prop := λ _ _ => True

def journey1 : TravelFrame TempLoc := ⟨.chicago, .stLouis⟩
def journey2 : TravelFrame TempLoc := ⟨.stLouis, .chicago⟩

def samPassenger1 : PassengerFrame Ind4 TempLoc isPassenger5 takesJourney5 :=
  ⟨.sam, trivial, journey1, trivial⟩

def samPassenger2 : PassengerFrame Ind4 TempLoc isPassenger5 takesJourney5 :=
  ⟨.sam, trivial, journey2, trivial⟩

theorem passenger_individuation :
    samPassenger1.x = samPassenger2.x ∧ samPassenger1 ≠ samPassenger2 :=
  ⟨rfl, λ h => absurd (congrArg PassengerFrame.journey h) (by decide)⟩

end FramePhenomena

end DynamicSemantics.TTR
