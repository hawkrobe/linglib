module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Studies.White2014
public import Linglib.Data.Examples.Williams2025

/-!
# Williams (2025): the presuppositions of *forget*

This file formalizes [williams-2025]'s account of when the complement of *forget* carries a
covert modal. *forget* is factive whatever its complement ([kiparsky-kiparsky-1970]), and with a
plain infinitive the presupposed proposition is modal: *John forgot to stop by the flower shop*
presupposes that John was supposed to stop by it (5a). [white-2014] puts the modal in every
nonfinite complement. Williams shows that a PRO-ing gerund (7)–(10) and a Spanish perfect
infinitive (13)–(14), both nonfinite, presuppose the event and not an obligation, so the modal
heads plain infinitives only (SMINC, (15)); in Table 1 Italian and German modalize the plain
infinitive and not the perfect infinitive, and Hungarian modalizes the plain infinitive. The
modal is a last resort for the pre-existence presupposition of [bondarenko-2020], that the
embedded event started before the forgetting (28b), which the continuations of (18)–(21) test.

A complement describes events at a reference time (30). The plain infinitive is an AspP whose
perfective locates the event within the reference time (`aspP`, (30c)), and the gerund's past
tense (30a) and the perfect (30b) both move the reference time back (`anterior`). At the
forgetting, pre-existence follows from an anterior complement as soon as the complement holds
((32), (34): `preEx_anterior_aspP_iff`) and contradicts a plain infinitive ((36):
`not_preEx_aspP`), so the plain infinitive needs the modal (`needsMod_aspP`) and the anterior
complements do not (`not_needsMod_anterior_aspP`). Under the plan modal (37) the presupposition
is that the plan holds and began before the forgetting ((39): `preEx_mod_iff`). Since
pre-existence entails the complement at the forgetting (`PreEx.closure`), the presupposition is
modal exactly when the modal heads the complement. White's Modalized Complement Analysis
modalizes the gerund and infinitive frames alike, while the infinitive frame hosts both a
complement that needs the modal and one that does not (`mca_overgenerates`). The judgments are
`Williams2025.Examples`.

## Implementation notes

* The paper's complements are [champollion-2015] continuations, from a predicate of events to a
  proposition at a time (28). Each one the paper builds closes a predicate of events against the
  continuation, and the only continuations applied are the trivial one of [krifka-1989]'s closure
  (27) and equality with the embedded event in (28b), so a complement here is the predicate of
  events itself (`Complement`), and closure binds its event (`Complement.closure`).
* mathlib orders intervals by inclusion: the paper's `τ(e) ⊆ t` is `e.τ ≤ t`, its `t' < t` in
  (30a) and (30b) is `t'.precedes t`, the `t ≤ t'` of (37) is `t.isBefore t'`, and `LB` is
  `.fst`.
* (28b) as printed binds the complement's time existentially, and so bound it cannot tell the
  plain infinitive from the anterior complements (`exists_anterior_iff`). The derivations (32),
  (34) and (36) evaluate the complement at the attitude holder's subjective now, which `PreEx`
  takes to be the run time of the forgetting.
* (30a) and (30b) are printed as one formula, so (32) and (34) are one theorem. The paper
  implements the perfect after [kratzer-1998], and (30b) prints it as strict precedence, not the
  `ViewpointType.perfect` relation, whose intervals may touch.
* (40)(i) and (40)(ii) are assumptions about the plan state, not consequences of (37), and the
  proper inclusion of the subjective now in the plan's run time in (40)(ii) does not by itself
  start the plan earlier; the prose does ("the runtime of Mod begins before this"). The plan
  state's starting earlier is a hypothesis of `not_needsMod_mod`. A state with no plan worlds
  satisfies (37) vacuously.
* Plain infinitives are simultaneous with the matrix reference time ([wurmbrand-2014]), which
  places AspP at the subjective now in (36).
* The assertion of (28a), that the attitude holder does not believe the complement, plays no
  part in the argument and is not formalized; neither is the necessity and sufficiency
  presupposition (5b), which the paper leaves to future work, nor the implicative entailment of
  *forgot to* ([karttunen-1971]), which it sets aside (fn. 1).
* The English fragment has an implicative *forget* taking an infinitive and a factive one taking
  a finite clause, `English.Verbs.forget` and `English.Verbs.forget_rog`; Williams' uniformity
  hypothesis takes them to be one verb.

## References

* [williams-2025]
* [white-2014]
* [kiparsky-kiparsky-1970]
* [bondarenko-2020]
* [champollion-2015]
* [krifka-1989]
* [kratzer-1998]
* [wurmbrand-2014]
* [karttunen-1971]
-/

@[expose] public section

namespace Williams2025

variable {W T : Type*} [LinearOrder T]

/-! ### Complements -/

/-- A complement: the events it describes at a reference time in a world. -/
abbrev Complement (W T : Type*) [LinearOrder T] := W → NonemptyInterval T → Event T → Prop

/-- The closure (27) of a complement, binding its event. -/
def Complement.closure (C : Complement W T) : Aspect.IntervalPred W T :=
  fun w t ↦ ∃ e, C w t e

/-- AspP (30c), the plain infinitive: perfective aspect locates the event within the reference
time. -/
def aspP (P : W → Event T → Prop) : Complement W T :=
  fun w t e ↦ e.τ ≤ t ∧ P w e

/-- Closing AspP gives the perfective. -/
theorem closure_aspP (P : W → Event T → Prop) : (aspP P).closure = Aspect.PRFV P := rfl

/-- The past tense of the gerund (30a) and the perfect (30b): the complement holds at a
reference time preceding `t`. -/
def anterior (C : Complement W T) : Complement W T :=
  fun w t e ↦ ∃ t', t'.precedes t ∧ C w t' e

/-- The plan modal (37): the plan state `s` is the complement's event, and in every world of its
plan the complement holds at a time from `t` on. -/
def mod (plan : Event T → NonemptyInterval T → W → Set W) (C : Complement W T) :
    Complement W T :=
  fun w t s ↦ ∀ w' ∈ plan s t w, ∃ t', t.isBefore t' ∧ C.closure w' t'

/-! ### Pre-existence -/

/-- Pre-existence (28b) at the forgetting `e`: the complement describes an event at the
subjective now, the run time of `e`, that starts before `e` does. -/
def PreEx (C : Complement W T) (e : Event T) (w : W) : Prop :=
  ∃ e'', C w e.τ e'' ∧ e''.τ.fst < e.τ.fst

/-- A complement needs the modal when it contradicts pre-existence at every forgetting, so that
without the modal the sentence is a presupposition failure (§5). -/
def NeedsMod (C : Complement W T) : Prop :=
  ∀ e w, ¬ PreEx C e w

variable {P : W → Event T → Prop} {C : Complement W T}
  {plan : Event T → NonemptyInterval T → W → Set W} {w : W} {t : NonemptyInterval T} {e : Event T}

/-- Factivity from pre-existence: the complement holds at the forgetting. -/
theorem PreEx.closure (h : PreEx C e w) : C.closure w e.τ :=
  let ⟨e'', hC, _⟩ := h
  ⟨e'', hC⟩

/-- (28b) as printed, `∃ e'' t, C w t e'' ∧ e''.τ.fst < e.τ.fst`, binds the complement's time,
and an existentially bound time absorbs the anterior shift. -/
theorem exists_anterior_iff [NoMaxOrder T] {p : Event T → Prop} :
    (∃ e t, anterior C w t e ∧ p e) ↔ ∃ e t, C w t e ∧ p e := by
  refine ⟨fun ⟨e, _, ⟨t', _, hC⟩, hp⟩ ↦ ⟨e, t', hC, hp⟩, fun ⟨e, t, hC, hp⟩ ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_gt t.snd
  exact ⟨e, .pure b, ⟨t, hb, hC⟩, hp⟩

/-! ### The complements under pre-existence, §6 -/

/-- (32)(iii), (34)(iii): under the anterior shift the embedded event precedes the reference
time. -/
theorem precedes_of_anterior_aspP (h : anterior (aspP P) w t e) : e.τ.precedes t :=
  let ⟨_, ht, hle, _⟩ := h
  hle.2.trans_lt ht

/-- (32), (34): for the gerund and the perfect infinitive, pre-existence is the complement's
holding at the forgetting. -/
theorem preEx_anterior_aspP_iff :
    PreEx (anterior (aspP P)) e w ↔ (anterior (aspP P)).closure w e.τ :=
  ⟨PreEx.closure, fun ⟨e'', h⟩ ↦
    ⟨e'', h, e''.τ.fst_le_snd.trans_lt (precedes_of_anterior_aspP h)⟩⟩

/-- (36): a plain infinitive contradicts pre-existence. -/
theorem not_preEx_aspP : ¬ PreEx (aspP P) e w :=
  fun ⟨_, ⟨hle, _⟩, hlt⟩ ↦ hlt.not_ge hle.1

/-- (39): under the modal, the presupposition is that the plan holds and began before the
forgetting. -/
theorem preEx_mod_iff : PreEx (mod plan C) e w ↔ ∃ s, mod plan C w e.τ s ∧ s.τ.fst < e.τ.fst :=
  Iff.rfl

/-! ### The modal as a last resort, (15) -/

/-- (15a): a plain infinitive needs the modal. -/
theorem needsMod_aspP (P : W → Event T → Prop) : NeedsMod (aspP P) :=
  fun _ _ ↦ not_preEx_aspP

/-- (15b): the gerund and the perfect infinitive do not, once the predicate has an event. -/
theorem not_needsMod_anterior_aspP [NoMaxOrder T] (h : P w e) :
    ¬ NeedsMod (anterior (aspP P)) := by
  obtain ⟨b, hb⟩ := exists_gt e.τ.snd
  exact fun hn ↦ hn ⟨.pure b, .action⟩ w ⟨e, ⟨e.τ, hb, le_rfl, h⟩, e.τ.fst_le_snd.trans_lt hb⟩

/-- (40): the modal meets pre-existence, given a plan holding at the subjective now that began
before it. -/
theorem not_needsMod_mod {s : Event T} (hs : mod plan C w t s) (hlt : s.τ.fst < t.fst) :
    ¬ NeedsMod (mod plan C) :=
  fun hn ↦ hn ⟨t, .action⟩ w ⟨s, hs, hlt⟩

/-! ### Against the Modalized Complement Analysis, §3.1 -/

/-- [white-2014] modalizes the gerund and the infinitive frames alike, but the infinitive frame
hosts the plain infinitive, which needs the modal, and the perfect infinitive, which like the
gerund does not: whether the modal heads a complement is not a matter of its frame. -/
theorem mca_overgenerates [NoMaxOrder T] (h : P w e) :
    White2014.Modalized .gerund ∧ White2014.Modalized .infinitival ∧
      NeedsMod (aspP P) ∧ ¬ NeedsMod (anterior (aspP P)) :=
  ⟨by decide, by decide, needsMod_aspP P, not_needsMod_anterior_aspP h⟩

/-! ### The *began* tests, (19) and (21)

Days are integers, Monday `1`, Tuesday `2`, Wednesday `3`, and Mary forgets on Tuesday. -/

/-- (19a): a call begun on Monday is one Mary can have forgotten calling back. -/
example : PreEx (anterior (aspP fun (_ : Unit) e ↦ e = ⟨.pure 1, .action⟩))
    ⟨.pure 2, .action⟩ () :=
  preEx_anterior_aspP_iff.2 ⟨_, .pure 1, by decide, le_rfl, rfl⟩

/-- (19b): a call begun on Wednesday is not. -/
example : ¬ PreEx (anterior (aspP fun (_ : Unit) e ↦ e = ⟨.pure 3, .action⟩))
    ⟨.pure 2, .action⟩ () := by
  rintro ⟨_, ⟨_, -, -, rfl⟩, h⟩
  exact absurd h (by decide)

/-- (21a): Mary forgot to call back her twin, as told on Monday; in the plan world `true` she
calls on Wednesday. -/
example : PreEx (mod (fun _ _ _ ↦ {true})
      (aspP fun w e ↦ w = true ∧ e = ⟨.pure 3, .action⟩)) ⟨.pure 2, .action⟩ false :=
  ⟨⟨.pure 1, .state⟩, fun _ hw ↦ ⟨.pure 3, by decide, _, le_rfl, hw, rfl⟩, by decide⟩

end Williams2025
