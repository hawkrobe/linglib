module

public import Linglib.Semantics.Events.PreExistence
public import Linglib.Semantics.Attitudes.Anchor
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Quantified
public import Linglib.Semantics.Events.Basic
public import Linglib.Data.Examples.Bondarenko2020

/-!
# Bondarenko (2020): factivity from pre-existence

This file formalizes [bondarenko-2020]'s account of the factivity alternation of Barguzin Buryat
*hanaxa*, 'think' with a finite CP (1) and 'remember' with a nominalized clause (2). The
nominalized clause presupposes that the event it describes started before the thinking: a
*began* continuation must place the event's start before the matrix time (4), a future child or
a fictional cat cannot be the object (5), (6), and the inference survives questions and negation
(14), (15). The alternation is not an ambiguity of the verb. A CP modifies the thinking event,
whose content its complementizer fixes (25), and adds no presupposition, so the report imposes
nothing on the actual world (`reportThat_presup`). A nominalized clause
saturates the internal argument that the head θTh introduces, and θTh presupposes that this
argument started before the matrix time (`thetaTh`, (55)). Closed by a strong Kleene existential
(58) ([fox-2013]), the report presupposes exactly that (`presup_closure_thetaTh`, (59)), and in
the past tense that such an event preceded some past thinking time ((62):
`exists_preExists_of_report_presup`). Pre-existence entails that the event exists in the world
of evaluation, which is the factive inference (`exists_of_report_presup`). A nominalized CP is a
predicate of contentful individuals (64), so its pre-existence presupposition concerns a claim
with the content, not an event of it (65), (66).

## Implementation notes

* Pre-existence is `Event.PreExists` of `Semantics/Events/PreExistence.lean`, shared with
  [williams-2025]. Time spans are a function `τ` into `NonemptyInterval`, the run time of an
  event or the life span of an entity, and the paper's `LB(τ(x)) < t` is `(τ x).fst < t.fst`.
* Truth values are trivalent, as in the paper: a sentence is a `PartialProp`, defined when it is
  true or false. The existential closure (58) and the past tense (60) are both the strong Kleene
  existential `PartialProp.existsPartialStrong`, the tense over the past times `t' < t`
  (`t'.precedes t`) within the contextual interval `g(1)` (`t' ≤ g₁`).
* The simplification from (57) and (58) to (59) assumes a nonempty domain of events, as the
  paper's fn. 36 says, and (62) follows from (61) only for a nonempty contextual past: over an
  empty one the falsity condition of (61) holds vacuously and the sentence is defined whatever
  the complement. Both are hypotheses here.
* The verb and the Voice head are one predicate of events `P` at a world and time, so the
  external argument joins θTh's assertion and leaves its presupposition, as in (57). This is the
  weak Kleene conjunction `PartialProp.and` with a presuppositionless conjunct, not the strong
  Kleene one the paper adopts elsewhere; the two differ only when the subject is the experiencer
  of no event. θTh's `about` is a function from contentful events to their topics, as in (46).
* A report with both a nominalized clause and a CP (21) is θTh with a `P` that includes the CP's
  content condition, and has the nominalized clause's presupposition.
* Not formalized: the *tuxai* 'about' phrases (7), (48), which carry no presupposition and get
  no formula in the paper; the allosemy of θTh (49); and the plan readings of the future
  participle -xA (70)–(73), which the paper leaves open.

## References

* [bondarenko-2020]
* [fox-2013]
* [kleene-1952]
* [williams-2025]
-/

@[expose] public section

namespace Bondarenko2020

open Presupposition PartialProp Event

variable {W T X E I : Type*} [LinearOrder T]

/-! ### θTh and its presupposition, (55), (56) -/

/-- θTh (55), (56) with *hanaxa*, at the matrix time `t`: the event `e` is a `P`-event about an
individual of `Q` that started before `t`, presupposing that `Q` describes such an individual. -/
def thetaTh (τ : X → NonemptyInterval T) (about : E → X) (P : W → NonemptyInterval T → E → Prop)
    (Q : W → NonemptyInterval T → X → Prop) (t : NonemptyInterval T) (e : E) : PartialProp W where
  presup w := PreExists τ (Q w t) t.fst
  assertion w := ∃ x, Q w t x ∧ (τ x).fst < t.fst ∧ P w t e ∧ about e = x

/-- The past tense (60) over the existentially closed (58) θTh-report (57), within the
contextual interval `g₁`: (61). -/
def report (τ : X → NonemptyInterval T) (about : E → X) (P : W → NonemptyInterval T → E → Prop)
    (Q : W → NonemptyInterval T → X → Prop) (g₁ t : NonemptyInterval T) : PartialProp W :=
  existsPartialStrong (fun t' ↦ t'.precedes t ∧ t' ≤ g₁) fun t' ↦
    existsPartialStrong (fun _ ↦ True) (thetaTh τ about P Q t')

/-- The past tense (28) over a report with a CP (27): a thinking event whose content the
complementizer (25) fixes as `p`, (29). -/
def reportThat [Anchor E I] (P : W → NonemptyInterval T → E → Prop) (p : I → Prop)
    (g₁ t : NonemptyInterval T) : PartialProp W :=
  existsPartialStrong (fun t' ↦ t'.precedes t ∧ t' ≤ g₁) fun t' ↦
    ofProp fun w ↦ ∃ e, P w t' e ∧ Anchor.comp p e

variable {τ : X → NonemptyInterval T} {about : E → X} {P : W → NonemptyInterval T → E → Prop}
  {Q : W → NonemptyInterval T → X → Prop} {g₁ t : NonemptyInterval T} {w : W}

/-- (55), (56): θTh's assertion repeats its presupposition, so θTh is true exactly when its
assertion holds. -/
theorem thetaTh_holds_iff {e : E} :
    (thetaTh τ about P Q t e).holds w ↔ (thetaTh τ about P Q t e).assertion w :=
  ⟨And.right, fun h ↦ ⟨let ⟨x, hx, hlt, _⟩ := h; ⟨x, hx, hlt⟩, h⟩⟩

/-! ### A CP adds no presupposition, §3.1 -/

/-- §3.1.2: a report with a CP is defined at every world, so it presupposes nothing about the
actual world. -/
theorem reportThat_presup [Anchor E I] (p : I → Prop) : (reportThat P p g₁ t).presup w :=
  existsPartialStrong_presup_of_forall fun _ _ ↦ trivial

/-! ### A nominalized clause presupposes pre-existence, §3.2.3 -/

/-- (59): the existentially closed θTh-report presupposes pre-existence. -/
theorem presup_closure_thetaTh [Nonempty E] :
    (existsPartialStrong (fun _ ↦ True) (thetaTh τ about P Q t)).presup w ↔
      PreExists τ (Q w t) t.fst :=
  existsPartialStrong_presup_iff (π := fun w ↦ PreExists τ (Q w t) t.fst)
    ⟨Classical.arbitrary E, trivial⟩ fun _ _ ↦ rfl

/-- (62): over a nonempty contextual past, the report presupposes that the complement describes
something that started before a past thinking time. -/
theorem exists_preExists_of_report_presup [Nonempty E] (hpast : ∃ t', t'.precedes t ∧ t' ≤ g₁)
    (h : (report τ about P Q g₁ t).presup w) :
    ∃ t', t'.precedes t ∧ t' ≤ g₁ ∧ PreExists τ (Q w t') t'.fst := by
  obtain ⟨t', ⟨hprec, hle⟩, hp⟩ := exists_presup_of_existsPartialStrong hpast h
  exact ⟨t', hprec, hle, presup_closure_thetaTh.1 hp⟩

/-- Over an empty contextual past the report is defined whatever the complement describes, so
(62) needs the past to be nonempty. -/
theorem report_presup_of_not_exists (hpast : ¬ ∃ t', t'.precedes t ∧ t' ≤ g₁) :
    (report τ about P Q g₁ t).presup w :=
  existsPartialStrong_presup_of_not_exists hpast

/-- (2b), (3): the factive inference. The report presupposes that the complement describes
something in the world of evaluation. -/
theorem exists_of_report_presup [Nonempty E] (hpast : ∃ t', t'.precedes t ∧ t' ≤ g₁)
    (h : (report τ about P Q g₁ t).presup w) : ∃ t' x, t'.precedes t ∧ Q w t' x :=
  let ⟨t', hprec, _, hpre⟩ := exists_preExists_of_report_presup hpast h
  let ⟨x, hx⟩ := hpre.exists
  ⟨t', x, hprec, hx⟩

/-- (15): negation keeps the presupposition. -/
theorem neg_report_presup :
    (neg (report τ about P Q g₁ t)).presup = (report τ about P Q g₁ t).presup :=
  rfl

/-- (64), (65): with a nominalized CP, a predicate of contentful individuals, the presupposition
is that an individual with the content started before the matrix time; it does not depend on
the world of evaluation, so it cannot require the content to be true there. -/
theorem presup_closure_thetaTh_comp [Nonempty E] [Anchor X I] (p : I → Prop) :
    (existsPartialStrong (fun _ ↦ True)
        (thetaTh τ about P (fun _ _ ↦ Anchor.comp p) t)).presup w ↔
      PreExists τ (Anchor.comp p) t.fst :=
  presup_closure_thetaTh

/-- (1b): a report with a CP can be true while its content is false. One thinking event, at
the past time `1` and with the content that the world is `true`, makes the report true at the
world `false`. -/
example :
    letI : Anchor Unit (Bool × NonemptyInterval ℤ) := ⟨fun _ i ↦ i.1 = true⟩
    (reportThat (I := Bool × NonemptyInterval ℤ) (fun (_ : Bool) _ (_ : Unit) ↦ True)
      (fun i ↦ i.1 = true) (.pure 1) (.pure 2)).holds false := by
  refine existsPartialStrong_holds_iff.2 ⟨.pure 1, ⟨by decide, le_rfl⟩, trivial, (), trivial, rfl⟩

/-! ### The judgments

Days are integers, Monday `1`, Tuesday `2`, Wednesday `3` (fn. 3), and the thinking is on
Tuesday. -/

/-- (4b): a breaking begun on Monday is one Sajana can remember on Tuesday. -/
example : PreExists Event.τ (· = ⟨.pure 1, .action⟩) (2 : ℤ) := by
  simp

/-- (4c): one begun on Wednesday is not. -/
example : ¬ PreExists Event.τ (· = ⟨.pure 3, .action⟩) (2 : ℤ) := by
  simp

/-- (5), (8): a child conceived before the time talked about, here `0`, can be remembered, and
neither it nor Badma need have stopped existing; a child not yet conceived cannot. -/
example : PreExists (fun (x : NonemptyInterval ℤ) ↦ x) (· = ⟨(-1, 10), by decide⟩) 0 ∧
    ¬ PreExists (fun (x : NonemptyInterval ℤ) ↦ x) (· = ⟨(2, 10), by decide⟩) 0 := by
  simp

end Bondarenko2020
