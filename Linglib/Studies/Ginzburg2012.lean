import Linglib.Discourse.Gameboard.Basic
import Linglib.Data.Examples.Ginzburg2012

/-!
# Ginzburg (2012): The Interactive Stance

[ginzburg-2012] gives each conversational participant their own *dialogue
gameboard* — turn holder and addressee, the commonly accepted FACTS, the
MOVES made, the questions under discussion (QUD) and, once metacommunication
is added, the ungrounded utterances PENDING — and analyses conversation as the
application of *conversational rules*, partial maps from gameboards meeting a
precondition type to gameboards of an effects type. This file states the book's
rule inventory (Appendix B) over the substrate `DGB`, checks its worked traces,
and proves the two structural claims it draws from them: participants who
process the same utterances need not end up with the same gameboard (the
Turn-Taking Puzzle), and self-repair is other-initiated clarification with the
turn held.

## Main definitions

* `Content`, `Clarifiable` — what the content types supply: `p?`, aboutness and
  influence (q-specificity), resolution (`⊨`), and the questions clarification
  accommodates, `λx.Mean(A, u, x)` and `λx.v(u ↦ x)`.
* `Rule`, `Rule.apply` — the named rules of Chs. 4, 6 and 8 as partial maps on
  `Board`; `run` composes a trace; `Coherent`, `Reachable`.
* `Fulfilled`, `GenreRelevant`, `IsInitiating` — the outcome of a gameboard
  relative to a genre and activity relevance (§4.6).
* `NSUClass`, `CRForm` — the non-sentential-utterance (Tables 7.3–7.4) and
  clarification-request (§6.2) taxonomies.

## Main statements

* `askQud_nonResolveCond`, `factUpdate_nonResolveCond`, `factUpdate_polar` —
  the Question Introduction Appropriateness Condition (`non-resolve-cond`) is
  kept by QUD-incrementation of an unresolved question and restored by FACTS
  update, which in particular removes `p?`.
* `Ex66.trace`, `Ex66.trace68`, `Ex79.trace` — the Ch. 4 traces (66), (68) and
  (79) reach the tabulated gameboards.
* `George.dgb_A`, `George.dgb_B`, `George.differ` — after "Is George here? /
  Is WHO here?" the two gameboards are those of Ch. 6 (91), and differ in QUD
  and PENDING.
* `parameterIdentification_eq_repair_swapTurn` — Parameter Identification and
  Backwards-looking appropriateness repair accommodate the same question and
  differ only in the turn (§8.2).

## Errata

Trace (66) labels the QUD update after B's question "Assert
QUD-incrementation"; it is Ask QUD-incrementation. Trace (68) ends with
`QUD := ⟨q0⟩` although no `q0` occurs; Fact update/QUD-downdate leaves QUD
empty. Table 7.4 heads the Answers block with 413 while its cells sum to 403
(the total 1283 of Table 7.3 needs 403).
-/

namespace Discourse.Gameboard.DGB

variable {P Fact Q : Type*} {Cont : Type}

/-- Turn change: the addressee takes the turn ([ginzburg-2012] Appendix B). -/
def swapTurn (d : DGB P Fact Q Cont) : DGB P Fact Q Cont :=
  { d with spkr := d.addr, addr := d.spkr }

/-- The question of MaxQUD. -/
def maxQud (d : DGB P Fact Q Cont) : Option Q := d.qud.head?.map (·.q)

/-- The content of the latest move. -/
def latestContent (d : DGB P Fact Q Cont) : Option Cont := d.latestMove.map (·.cont)

@[simp] theorem swapTurn_pushQud (d : DGB P Fact Q Cont) (q : Q) :
    d.swapTurn.pushQud q = (d.pushQud q).swapTurn := rfl

@[simp] theorem swapTurn_recordMove (d : DGB P Fact Q Cont) (m : LocProp Cont) :
    d.swapTurn.recordMove m = (d.recordMove m).swapTurn := rfl

@[simp] theorem latestMove_recordMove (d : DGB P Fact Q Cont) (m : LocProp Cont) :
    (d.recordMove m).latestMove = some m := by
  simp [latestMove, recordMove]

end Discourse.Gameboard.DGB

deriving instance DecidableEq for Discourse.Gameboard.DGB

namespace Ginzburg2012

open Discourse.Gameboard Question

/-- What a gameboard's content types supply: the polar question `p?`, the
aboutness and influence relations of q-specificity, and resolution (`⊨`), with
`p` resolving `p?`. -/
class Content (Fact Q : Type) extends DecidableSupport Fact Q where
  polar : Fact → Q
  About : Fact → Q → Prop
  Influences : Q → Q → Prop
  decAbout : DecidableRel About
  decInfluences : DecidableRel Influences
  supports_polar (p : Fact) : supports p (polar p)

attribute [reducible, instance] Content.decAbout Content.decInfluences

/-- The questions clarification accommodates: `λx.Mean(A, u, x)`, what `A`
meant by the sub-utterance `u` (Parameter Identification), and `λx.v(u ↦ x)`,
the content `v` with `u`'s contextual parameter abstracted (Parameter
Focussing). -/
class Clarifiable (P Fact Q : Type) where
  mean : P → SubUtterance → Q
  focus : IllocMove Fact Q → SubUtterance → Q

/-- A gameboard whose utterances, in MOVES and PENDING, carry illocutionary
content. -/
abbrev Board (P Fact Q : Type) := DGB P Fact Q (IllocMove Fact Q)

/-- An utterance record. -/
abbrev Utt (Fact Q : Type) := LocProp (IllocMove Fact Q)

/-- The two participants of a duologue. -/
inductive Agent
  | A
  | B
  deriving DecidableEq, Repr

section Rules

variable {P Fact Q : Type} [DecidableEq Fact] [DecidableEq Q] [Content Fact Q]

/-- The utterance of a bare move, when only its content matters (Ch. 4). -/
def ofMove (m : IllocMove Fact Q) : Utt Fact Q := { phon := "", cat := "", cont := m }

/-- The question a move contributes to QUD: `q` for `Ask(q)`, `p?` for `Assert(p)`. -/
def qudContrib : IllocMove Fact Q → Option Q
  | .ask q => some q
  | .assert p => some (Content.polar p)
  | _ => none

/-- `r` is specific to `q`: About `q` for an assertion, Influencing `q` for a
question. -/
def QSpecific : IllocMove Fact Q → Q → Prop
  | .assert p, q => Content.About p q
  | .ask q', q => Content.Influences (Fact := Fact) q' q
  | _, _ => False

instance (m : IllocMove Fact Q) (q : Q) : Decidable (QSpecific m q) := by
  unfold QSpecific; split <;> infer_instance

/-- `w` contextually extends `u`: the same utterance with some of its contextual
parameters witnessed. -/
def ContextuallyExtends (w u : Utt Fact Q) : Prop :=
  w.phon = u.phon ∧ w.cat = u.cat ∧ w.cont = u.cont ∧ w.constits = u.constits ∧
    ∀ c ∈ w.cparams, c ∈ u.cparams

instance (w u : Utt Fact Q) : Decidable (ContextuallyExtends w u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Who speaks next: the turn is kept (No-Turn-Change) or changes; a rule whose
turn is underspecified takes either. -/
inductive Turn
  | keep
  | change

/-- Effect the turn on a gameboard. -/
def Turn.act : Turn → Board P Fact Q → Board P Fact Q
  | .keep, d => d
  | .change, d => d.swapTurn

/-- The conversational rules of [ginzburg-2012] (Appendix B), with the utterance,
question or turn a nondeterministic rule chooses made an argument. Ch. 4:
greeting and counter-greeting, Free Speech, QSPEC, Ask and Assert
QUD-incrementation, Assertion checking, Accept and Confirm, Fact update/QUD-
downdate, QCoord. Ch. 6: Pending Update, Contextual Instantiation,
pendification of a move-update rule (the move originates in PENDING), the
two CCURs — Parameter Identification and Parameter Focussing, each merged with
Utterance Interpolation — and CR Accommodation. §8.2: Backwards-looking
appropriateness repair. -/
inductive Rule (P Fact Q : Type)
  | greeting
  | counterGreeting
  | freeSpeech (u : Utt Fact Q) (t : Turn)
  | qspec (u : Utt Fact Q) (t : Turn)
  | askQud
  | assertQud
  | check (u : Utt Fact Q) (t : Turn)
  | accept (u : Utt Fact Q)
  | confirm (u : Utt Fact Q)
  | factUpdate
  | qcoord (u : Utt Fact Q)
  | pendingUpdate (u : Utt Fact Q) (spkr addr : P)
  | contextualInstantiation (w : Utt Fact Q)
  | pendified (r : Rule P Fact Q)
  | parameterIdentification (u : SubUtterance) (cr : Utt Fact Q)
  | parameterFocussing (u : SubUtterance) (cr : Utt Fact Q)
  | crAccommodation (u : SubUtterance)
  | repair (u : SubUtterance) (cr : Utt Fact Q)

variable [Clarifiable P Fact Q]

/-- A rule as a partial map: `none` when the gameboard fails its preconditions.
Accept, Confirm and the CCURs change the turn; Free Speech, QSPEC and
checking leave it underspecified; the rest keep it. Contextual Instantiation
is applied by an agent who believes the witnessed record `w` is the one the
speaker intended; CR Accommodation integrates the other party's clarification
request, so the clarified speaker is the current addressee. -/
def Rule.apply : Rule P Fact Q → Board P Fact Q → Option (Board P Fact Q)
  | .greeting, d => match d.moves, d.qud with
    | [], [] => some (d.recordMove (ofMove IllocMove.greet))
    | _, _ => none
  | .counterGreeting, d => match d.latestContent with
    | some .greet => some (d.swapTurn.recordMove (ofMove IllocMove.counterGreet))
    | _ => none
  | .freeSpeech u t, d => match d.qud with
    | [] => some ((t.act d).recordMove u)
    | _ => none
  | .qspec u t, d => match d.qud with
    | i :: _ => if QSpecific u.cont i.q then some ((t.act d).recordMove u) else none
    | [] => none
  | .askQud, d => match d.latestContent with
    | some (.ask q) => some (d.pushQud q)
    | _ => none
  | .assertQud, d => match d.latestContent with
    | some (.assert p) => some (d.pushQud (Content.polar p))
    | _ => none
  | .check u t, d => match d.latestContent, u.cont with
    | some (.assert p), .check p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some ((t.act d).recordMove u) else none
    | _, _ => none
  | .accept u, d => match d.latestContent, u.cont with
    | some (.assert p), .accept p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some (d.swapTurn.recordMove u) else none
    | _, _ => none
  | .confirm u, d => match d.latestContent, u.cont with
    | some (.check p), .confirm p' =>
      if p = p' ∧ d.maxQud = some (Content.polar p) then some (d.swapTurn.recordMove u) else none
    | _, _ => none
  | .factUpdate, d => match d.latestContent with
    | some (.accept p) | some (.confirm p) =>
      if d.maxQud = some (Content.polar p) then some (d.addFact p).downdateQud else none
    | _ => none
  | .qcoord u, d => match d.latestContent, u.cont, d.qud with
    | some (.ask q), .ask q₁, i :: rest =>
      if i.q = q ∧ ¬ Content.Influences (Fact := Fact) q₁ q then
        some { d.recordMove u with qud := i :: .fromQuestion q₁ :: rest } else none
    | _, _, _ => none
  | .pendingUpdate u s a, d => some { d.pushPending u with spkr := some s, addr := some a }
  | .contextualInstantiation w, d => match d.pending with
    | u :: rest => if ContextuallyExtends w u then some { d with pending := w :: rest } else none
    | [] => none
  | .pendified r, d => match d.pending with
    | u :: rest =>
      if u.cparams = [] then (r.apply { d with pending := rest }).filter (·.latestMove = some u)
      else none
    | [] => none
  | .parameterIdentification u cr, d => match d.pending, d.spkr with
    | v :: _, some a =>
      if u ∈ v.constits ∧ qudContrib cr.cont = some (Clarifiable.mean (Fact := Fact) a u) then
        some ((d.swapTurn.pushQud (Clarifiable.mean (Fact := Fact) a u)).recordMove cr) else none
    | _, _ => none
  | .parameterFocussing u cr, d => match d.pending with
    | v :: _ =>
      if u ∈ v.constits ∧ qudContrib cr.cont = some (Clarifiable.focus (P := P) v.cont u) then
        some ((d.swapTurn.pushQud (Clarifiable.focus (P := P) v.cont u)).recordMove cr)
      else none
    | [] => none
  | .crAccommodation u, d => match d.pending, d.latestMove, d.addr with
    | v :: rest, some v₀, some a =>
      if u ∈ v₀.constits ∧ (qudContrib v.cont = some (Clarifiable.mean (Fact := Fact) a u) ∨
          qudContrib v.cont = some (Clarifiable.focus (P := P) v₀.cont u)) then
        match qudContrib v.cont with
        | some q => some { (d.pushQud q).recordMove v with pending := rest }
        | none => none
      else none
    | _, _, _ => none
  | .repair u cr, d => match d.pending, d.spkr with
    | v :: _, some a =>
      if u ∈ v.constits ∧ qudContrib cr.cont = some (Clarifiable.mean (Fact := Fact) a u) then
        some ((d.pushQud (Clarifiable.mean (Fact := Fact) a u)).recordMove cr) else none
    | _, _ => none

/-- Apply a trace of rules in sequence (the composition of conversational rules). -/
def run (trace : List (Rule P Fact Q)) (d : Board P Fact Q) : Option (Board P Fact Q) :=
  trace.foldlM (λ d r => r.apply d) d

/-- An utterance is coherent relative to a gameboard when some rule makes it the
latest move (Ch. 4 M-Coherence; Appendix B Utterance Coherence). -/
def Coherent (d : Board P Fact Q) (u : Utt Fact Q) : Prop :=
  ∃ r : Rule P Fact Q, ∃ d', r.apply d = some d' ∧ d'.latestMove = some u

/-- `d'` is a possible development of `d`. -/
def Reachable (d d' : Board P Fact Q) : Prop := ∃ trace, run trace d = some d'

/-! ### QUD well-formedness

The Question Introduction Appropriateness Condition — a question enters QUD
only if no established fact resolves it — is built into the gameboard type as
`non-resolve-cond` (`DGB.nonResolveCond`). -/

/-- Ask QUD-incrementation keeps `non-resolve-cond` when no fact resolves the
question asked. -/
theorem askQud_nonResolveCond {d d' : Board P Fact Q} {q : Q} (hd : d.nonResolveCond)
    (hm : d.latestContent = some (.ask q)) (hq : ∀ f ∈ d.facts, ¬ f ⊨ q)
    (h : Rule.askQud.apply d = some d') : d'.nonResolveCond := by
  simp only [Rule.apply, hm, Option.some.injEq] at h
  subst h
  exact List.forall_mem_cons.2 ⟨λ ⟨f, hf, hfq⟩ => hq f hf hfq, hd⟩

/-- Fact update/QUD-downdate restores `non-resolve-cond`. -/
theorem factUpdate_nonResolveCond {d d' : Board P Fact Q}
    (h : Rule.factUpdate.apply d = some d') : d'.nonResolveCond := by
  unfold Rule.apply at h
  split at h <;> simp only [Option.ite_none_right_eq_some, reduceCtorEq] at h <;>
    exact Option.some.inj h.2 ▸ downdateQud_restores_nonResolveCond _

/-- Accepting `p` downdates `p?`. -/
theorem factUpdate_polar {d d' : Board P Fact Q} {p : Fact}
    (hm : d.latestContent = some (.accept p))
    (h : Rule.factUpdate.apply d = some d') : ∀ i ∈ d'.qud, i.q ≠ Content.polar p := by
  have := factUpdate_nonResolveCond h
  intro i hi hq
  refine this i hi ⟨p, ?_, hq ▸ Content.supports_polar p⟩
  simp only [Rule.apply, hm, Option.ite_none_right_eq_some] at h
  exact Option.some.inj h.2 ▸ List.mem_cons_self

/-! ### Conversational genres (§4.6)

A genre is the type of a participant's information state at the end of a
conversation of that kind (ex. 88 pp. 104–105); the `qnud` field lists the
issues such a conversation raises and resolves. A gameboard fulfils the
outcome `outcome(dgb, G)` (ex. 89 p. 105) when its QUD is empty and FACTS
resolve every anticipated issue, and a move is relevant to a genre when some
continuation after it fulfils the outcome (ex. 90 p. 105). Initiating Move
(ex. 94 p. 108) is Free Speech restricted to moves the speaker takes to be
relevant to the genre in the private part of their information state
(`TIS.priv.genre`, ex. 93 p. 107). -/

/-- The outcome of `d` relative to `G` is fulfilled. -/
def Fulfilled (G : GenreType Fact Q) (d : Board P Fact Q) : Prop :=
  d.qud = [] ∧ ∀ q ∈ G.qnud, ∃ f ∈ d.facts, f ⊨ q

instance (G : GenreType Fact Q) (d : Board P Fact Q) : Decidable (Fulfilled G d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `u` is relevant to `G` in `d`: some development of `d` extended by `u`
fulfils the outcome. -/
def GenreRelevant (G : GenreType Fact Q) (d : Board P Fact Q) (u : Utt Fact Q) : Prop :=
  ∃ d', Reachable (d.recordMove u) d' ∧ Fulfilled G d'

/-- Initiating Move: with QUD empty, a move relevant to the assumed genre. -/
def IsInitiating (G : GenreType Fact Q) (d : Board P Fact Q) (u : Utt Fact Q) : Prop :=
  d.qud = [] ∧ GenreRelevant G d u

/-- Every initiating move is coherent by Free Speech. -/
theorem coherent_of_isInitiating {G : GenreType Fact Q} {d : Board P Fact Q} {u : Utt Fact Q}
    (h : IsInitiating G d u) : Coherent d u :=
  ⟨.freeSpeech u .keep, d.recordMove u, by simp [Rule.apply, h.1, Turn.act], by simp⟩

/-! ### Self- and other-correction (§8.2)

Backwards-looking appropriateness repair (ex. 31 p. 287) is Parameter
Identification (ex. 70 p. 192) without the turn change: the speaker of a
pending utterance accommodates the issue of what they meant by one of its
constituents and continues co-propositionally with it. -/

/-- Parameter Identification is repair followed by a turn change. -/
theorem parameterIdentification_eq_repair_swapTurn (u : SubUtterance) (cr : Utt Fact Q)
    (d : Board P Fact Q) :
    (Rule.parameterIdentification u cr).apply d =
      ((Rule.repair u cr).apply d).map DGB.swapTurn := by
  unfold Rule.apply
  split <;> simp

/-! ### Worked traces (Ch. 4)

The book abbreviates contents as `qᵢ` and `pᵢ` and tabulates each trace as
the sequence of rules applied with the gameboard they produce. The schematic
content types below fix exactly the relations each trace's side conditions
require. -/

/-- The initial gameboard: `A` addressing `B`, with no moves. -/
def initial (facts : List Fact := []) : Board Agent Fact Q :=
  { spkr := some .A, addr := some .B, facts := facts }

/-- The columns of a trace table: FACTS, QUD and the contents of MOVES. -/
def table (d : Board Agent Fact Q) : List Fact × List Q × List (IllocMove Fact Q) :=
  (d.facts, d.qud.map (·.q), d.moves.map (·.cont))

end Rules

/-! Trace (66) p. 95 of dialogue (65): `q₀` who to invite, `q₁` who will agree to
come (influencing `q₀`), `p₁` an answer resolving `q₁`, `p₂` About `q₀`; and
trace (68) p. 95 of dialogue (67): A asserts `p₁`, checks it, B confirms. -/
namespace Ex66

inductive Fact
  | p₁
  | p₂
  deriving DecidableEq, Repr

inductive Q
  | q₀
  | q₁
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  supports f q := q = .polar f ∨ f = .p₁ ∧ q = .q₁
  decSupports _ _ := inferInstanceAs (Decidable (_ ∨ _))
  polar := .polar
  About f q := f = .p₁ ∧ q = .q₁ ∨ f = .p₂ ∧ q = .q₀
  Influences q q' := q = .q₁ ∧ q' = .q₀
  decAbout _ _ := inferInstanceAs (Decidable (_ ∨ _))
  decInfluences _ _ := inferInstanceAs (Decidable (_ ∧ _))
  supports_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .q₀
  focus _ _ := .q₀

/-- A asks `q₀`; B asks `q₁`; A asserts `p₁`; B accepts; B asserts `p₂`; A accepts. -/
def trace66 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.ask .q₀)) .keep, .askQud,
   .qspec (ofMove (.ask .q₁)) .change, .askQud,
   .qspec (ofMove (.assert .p₁)) .change, .assertQud,
   .accept (ofMove (.accept .p₁)), .factUpdate,
   .qspec (ofMove (.assert .p₂)) .keep, .assertQud,
   .accept (ofMove (.accept .p₂)), .factUpdate]

/-- After (65): FACTS `{p₁, p₂}`, QUD `⟨q₀⟩`, the six moves recorded. -/
theorem trace : (run trace66 initial).map table =
    some ([.p₂, .p₁], [.q₀],
      [.ask .q₀, .ask .q₁, .assert .p₁, .accept .p₁, .assert .p₂, .accept .p₂]) := by decide

/-- A asserts `p₁`, checks it, B confirms. -/
def trace68 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.assert .p₁)) .keep, .assertQud,
   .check (ofMove (.check .p₁)) .keep, .confirm (ofMove (.confirm .p₁)), .factUpdate]

/-- After (67): FACTS `{p₁}` and QUD empty. -/
theorem trace68_table : (run trace68 initial).map table =
    some ([.p₁], [], [.assert .p₁, .check .p₁, .confirm .p₁]) := by decide

end Ex66

/-! Trace (79) p. 99 of dialogue (78): `q₀` whom Max invites, `q₁` when the
guests arrive, not influencing `q₀`; `p₀` resolves `q₀`, `p₁` is About `q₁`. -/
namespace Ex79

inductive Fact
  | p₀
  | p₁
  deriving DecidableEq, Repr

inductive Q
  | q₀
  | q₁
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  supports f q := q = .polar f ∨ f = .p₀ ∧ q = .q₀
  decSupports _ _ := inferInstanceAs (Decidable (_ ∨ _))
  polar := .polar
  About f q := f = .p₀ ∧ q = .q₀ ∨ f = .p₁ ∧ q = .q₁
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable (_ ∨ _))
  decInfluences _ _ := inferInstanceAs (Decidable False)
  supports_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .q₀
  focus _ _ := .q₀

/-- A asks `q₀` then `q₁` (QCoord); B answers `q₀`; A accepts; B answers `q₁`. -/
def trace79 : List (Rule Agent Fact Q) :=
  [.freeSpeech (ofMove (.ask .q₀)) .keep, .askQud, .qcoord (ofMove (.ask .q₁)),
   .qspec (ofMove (.assert .p₀)) .change, .assertQud,
   .accept (ofMove (.accept .p₀)), .factUpdate,
   .qspec (ofMove (.assert .p₁)) .change, .assertQud]

/-- After (78): FACTS `{p₀}`, QUD `⟨p₁?, q₁⟩`. -/
theorem trace : (run trace79 initial).map table =
    some ([.p₀], [.polar .p₁, .q₁],
      [.ask .q₀, .ask .q₁, .assert .p₀, .accept .p₀, .assert .p₁]) := by decide

end Ex79

/-! ### Activity relevance: dialogue (95) p. 108

B takes the genre to be CasualChat (ex. 88a), whose anticipated issues are
how A is and how B is. "I'm off" is About the latter and, once accepted,
resolves it; that A is present already resolves the former. -/

namespace Ex95

inductive Fact
  | here
  | off
  deriving DecidableEq, Repr

inductive Q
  | howA
  | howB
  | polar (p : Fact)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  supports f q := q = .polar f ∨ f = .here ∧ q = .howA ∨ f = .off ∧ q = .howB
  decSupports _ _ := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
  polar := .polar
  About f q := f = .off ∧ q = .howB
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable (_ ∧ _))
  decInfluences _ _ := inferInstanceAs (Decidable False)
  supports_polar _ := Or.inl rfl

instance : Clarifiable Agent Fact Q where
  mean _ _ := .howA
  focus _ _ := .howA

/-- CasualChat: the issues `λP.P(A)`, `λP.P(B)` are to be discussed. -/
def casualChat : GenreType Fact Q := { name := "CasualChat", qnud := [.howA, .howB] }

/-- After A's greeting, "I'm off" is an initiating move relative to CasualChat:
B's assertion, accepted by A, resolves how B is. -/
theorem initiating_off :
    IsInitiating casualChat ((initial [.here]).recordMove (ofMove IllocMove.greet))
      (ofMove (.assert .off)) :=
  ⟨rfl, _, ⟨[.assertQud, .accept (ofMove (.accept .off)), .factUpdate], rfl⟩, by decide⟩

end Ex95

/-! ### Grounding and clarification: dialogue (90) of Ch. 6, p. 201

A asks whether George is here. A, omniscient about her own utterance,
instantiates its contextual parameter and integrates it; B cannot, and
initiates clarification by Parameter Focussing with "Is WHO here?". After that
utterance the two gameboards are those of Ch. 6 (91) p. 202: A has `p?` under
discussion and B's clarification request pending; B has the question who A is
asking about under discussion and A's utterance pending. -/

namespace George

inductive Fact
  | georgeHere
  deriving DecidableEq, Repr

/-- `p?`; `λx.Ask(A, B, ?In(l, x))`, the focussed question; and `λx.Mean(A, u, x)`. -/
inductive Q
  | polar (p : Fact)
  | whoAsked
  | meant (u : SubUtterance)
  deriving DecidableEq, Repr

instance : Content Fact Q where
  supports f q := q = .polar f
  decSupports _ _ := inferInstanceAs (Decidable (_ = _))
  polar := .polar
  About _ _ := False
  Influences _ _ := False
  decAbout _ _ := inferInstanceAs (Decidable False)
  decInfluences _ _ := inferInstanceAs (Decidable False)
  supports_polar _ := rfl

instance : Clarifiable Agent Fact Q where
  mean _ u := .meant u
  focus _ _ := .whoAsked

/-- The sub-utterance "George". -/
def george : SubUtterance := { phon := "George", cat := "NP", cont := "g" }

/-- A's utterance, with the referent of "George" a contextual parameter. -/
def u₀ : Utt Fact Q :=
  { phon := "Is George here?", cat := "S", cont := .ask (.polar .georgeHere),
    cparams := [{ index := "g", restriction := "Named(George, g)" }], constits := [george] }

/-- A's utterance with its parameter witnessed. -/
def w₀ : Utt Fact Q := { u₀ with cparams := [] }

/-- B's clarification request. -/
def u₁ : Utt Fact Q := { phon := "Is WHO here?", cat := "S", cont := .ask .whoAsked }

/-- A: utter `u₀`, instantiate it, integrate it by Free Speech, hear `u₁`. -/
def traceA : List (Rule Agent Fact Q) :=
  [.pendingUpdate u₀ .A .B, .contextualInstantiation w₀,
   .pendified (.freeSpeech w₀ .keep), .askQud, .pendingUpdate u₁ .B .A]

/-- B: hear `u₀`, clarify by Parameter Focussing with `u₁`. -/
def traceB : List (Rule Agent Fact Q) :=
  [.pendingUpdate u₀ .A .B, .parameterFocussing george u₁]

/-- (91b): A's gameboard. -/
theorem dgb_A : run traceA initial = some
    { spkr := some .B, addr := some .A, pending := [u₁],
      qud := [.fromQuestion (.polar .georgeHere)], moves := [w₀] } := by decide

/-- (91c): B's gameboard. -/
theorem dgb_B : run traceB initial = some
    { spkr := some .B, addr := some .A, pending := [u₀],
      qud := [.fromQuestion .whoAsked], moves := [u₁] } := by decide

/-- The two participants have processed the same utterances and disagree on
QUD and on PENDING. -/
theorem differ : ∀ dA ∈ run traceA initial, ∀ dB ∈ run traceB initial,
    dA.qud ≠ dB.qud ∧ dA.pending ≠ dB.pending := by
  simp only [dgb_A, dgb_B, Option.mem_def, Option.some.injEq]
  rintro _ rfl _ rfl
  decide

/-- A integrates B's request by CR Accommodation: the focussed question becomes
MaxQUD and the request is no longer pending. -/
theorem accommodate :
    (run (traceA ++ [.crAccommodation george]) initial).map
        (λ d => (d.qud.map (·.q), d.pending)) =
      some ([.whoAsked, .polar .georgeHere], []) := by decide

end George

/-! ### Taxonomies

The clarification-request forms of the BNC study reported in §6.2.1 (Table
6.1 p. 153), and the non-sentential-utterance classes of Table 7.3 p. 221 with
their functional grouping in Table 7.4 p. 222, Sluice split into its reprise
and direct uses. Readings of clarification requests are `RFReading`. -/

/-- The eight clarification-request forms (§6.2.1). -/
inductive CRForm
  /-- "Eh? / What? / Pardon?" -/
  | wot
  /-- A context-independent request, "What did you say?" -/
  | explicit
  /-- Verbatim repetition of the troubled utterance -/
  | literalReprise
  /-- Repetition with a constituent replaced by a wh-phrase -/
  | whSubstitutedReprise
  /-- A bare wh-phrase -/
  | repriseSluice
  /-- A bare phrase -/
  | repriseFragment
  /-- The sentence with the targeted constituent omitted -/
  | gap
  /-- A guess completing an unfinished sentence -/
  | filler
  deriving DecidableEq, Repr

/-- The functional grouping of Table 7.4. -/
inductive NSUFunction
  | positiveFeedback
  | answer
  | metacommunicativeQuery
  | extensionMove
  deriving DecidableEq, Repr

/-- The NSU classes of Table 7.3, with Sluice split as in Table 7.4. -/
inductive NSUClass
  /-- "mmh" -/
  | plainAcknowledgement
  /-- "Bo, hmm." -/
  | repeatedAcknowledgement
  /-- "Bo?" -/
  | clarificationEllipsis
  /-- "Okay?" -/
  | checkQuestion
  /-- "Who?" reprising the antecedent -/
  | repriseSluice
  /-- completing "Did Bo …" with "leave?" -/
  | filler
  /-- "Bo" -/
  | shortAnswer
  /-- "Yes" -/
  | affirmativeAnswer
  /-- "No" -/
  | rejection
  /-- "Bo, yes." -/
  | repeatedAffirmativeAnswer
  /-- "No, Max." -/
  | helpfulRejection
  /-- "Maybe" -/
  | propositionalModifier
  /-- "Great!" -/
  | factiveModifier
  /-- "Yesterday" -/
  | bareModifierPhrase
  /-- "Who?" requesting new information -/
  | directSluice
  /-- "And Max." -/
  | conjunctionFragment
  deriving DecidableEq, Repr

/-- The function of each class (Table 7.4). -/
def NSUClass.function : NSUClass → NSUFunction
  | .plainAcknowledgement | .repeatedAcknowledgement => .positiveFeedback
  | .clarificationEllipsis | .checkQuestion | .repriseSluice | .filler => .metacommunicativeQuery
  | .shortAnswer | .affirmativeAnswer | .rejection | .repeatedAffirmativeAnswer
  | .helpfulRejection | .propositionalModifier => .answer
  | .factiveModifier | .bareModifierPhrase | .directSluice | .conjunctionFragment => .extensionMove

end Ginzburg2012
