import Linglib.Data.Examples.CoppockWechsler2018
import Linglib.Discourse.Commitment.Table
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Reference.Kaplan
import Linglib.Studies.Pearson2015

/-!
# Coppock & Wechsler (2018): The Proper Treatment of Egophoricity in Kathmandu Newari

This file formalizes [coppock-wechsler-2018]'s Egophoric Logic. Kathmandu Newari verbs carry no
person marking; the egophoric (conjunct) form appears in first-person statements, second-person
polar questions and de se speech reports, and the plain form elsewhere. Extensions are relative
to a context, a world and an agent, the perspectival center, so a sentence has a centered
intension, a partial proposition over centered worlds. The first-person pronoun and the
epistemic authority are indexicals, read off the context; the egophor SELF is the center, a
parameter of content. The egophoric suffix is a partial identity on predicates that presupposes
its subject to be SELF, following [wechsler-2018]'s proposal that conjunct marking expresses
self-ascription in the sense of [lewis-1979-attitudes].

Speech acts update the Table of [farkas-bruce-2010]. The common ground is uncentered: an
assertion projects the intension of its clause uncentered by the authority of the context, and a
polar question those of its two answers. The authority is the speaker of a declarative, the
addressee of a question and the source of a reportative evidential. A projected set must be
viable, which here is the Table not being in crisis, and an egophoric clause whose subject is
not the authority uncenters to the empty proposition. The interrogative flip and the loss of
egophoric marking under evidentials follow. Embedding verbs have the centered Hintikka semantics
of [pearson-2015], so an egophoric report has the holder identify the subject as herself, which
fails in the scenario of the unrecognized photograph, and under double embedding the subject is
the closest reported speaker.

The paper sets its account against the authority-indexical one of [bickel-nichols-2007] and of
[mccready-2007] for Japanese *zibun*, on which the suffix presupposes its subject to be the
authority. The two agree on every root clause, but the indexical account needs a context shift
in reports, a monster, and then predicts coreference where Newari requires self-reference.

## Main definitions

* `Context`: a Kaplanian context with an epistemic authority.
* `ego`, `plain`, `egoAuth`: the centered intensions of an egophoric clause, a plain clause, and
  an egophoric clause on the authority-indexical account.
* `uncenter`: the ordinary intension of a centered proposition at an agent.
* `assert`, `ask`: assertion and polar question as moves on the Table.
* `Says`, `report`: the centered Hintikka semantics of a verb of saying.

## Main statements

* `inCrisis_assert_ego`, `inCrisis_ask_ego`: an egophoric clause whose subject is not the
  authority leaves no viable projected set, asserted or asked.
* `ask_ego_of_eq`: with the authority as subject, the egophoric question is the default polar
  question on the uncentered prejacent.
* `says_ego_iff`: an egophoric report is identification of the subject as oneself together with
  self-ascription of the property.
* `eq_of_says_report_ego`: under double embedding the subject is the closest reported speaker.
* `uncenter_egoAuth`, `lampshade`: the authority-indexical account agrees on root clauses and
  diverges on the unrecognized photograph.
* `ego_acceptable_iff`: each egophoric example of the paper is acceptable exactly when its
  subject is the authority.

## Implementation notes

The Table records the public side of the paper's discourse model, whose common ground and
projected set are uncentered; the centered intension the authority commits to is the argument
of `assert`, `ask` and `Says`. Expressions of Egophoric Logic are given by their extensions
rather than as syntax, and time is ignored as in the paper.

## TODO

The paper stars the second-person polar question with the plain form. The viability constraint
derives where egophoric marking is excluded, not where it is obligatory, so that judgment is not
derived here.

## References

* [coppock-wechsler-2018]
* [wechsler-2018]
* [farkas-bruce-2010]
* [pearson-2015]
* [lewis-1979-attitudes]
* [bickel-nichols-2007]
* [mccready-2007]
-/

namespace CoppockWechsler2018

open Presupposition Commitment Question Filter
open Pearson2015 (Centered sayDeSe)

variable {W E P T : Type*}

/-! ### Egophoric Logic -/

/-- A context of utterance with an epistemic authority, the participant whose commitment to the
at-issue content the speech act projects. -/
structure Context (W E P T : Type*) extends Reference.Context W E P T where
  /-- The epistemic authority of the context. -/
  authority : E

/-- In a declarative context the authority is the speaker. -/
def Context.IsDeclarative (c : Context W E P T) : Prop := c.authority = c.agent

/-- In an interrogative context the authority is the addressee. -/
def Context.IsInterrogative (c : Context W E P T) : Prop := c.authority = c.addressee

/-- An individual term, given by its extension at a context and a perspectival center. -/
abbrev Term (W E P T : Type*) := Context W E P T → E → E

/-- The first-person indexical, the speaker of the context. -/
def I : Term W E P T := fun c _ ↦ c.agent

/-- The second-person indexical, the addressee of the context. -/
def you : Term W E P T := fun c _ ↦ c.addressee

/-- The authority indexical. -/
def auth : Term W E P T := fun c _ ↦ c.authority

/-- The egophor, the perspectival center. -/
def self : Term W E P T := fun _ a ↦ a

/-- A name or a free pronoun, rigid across contexts and centers. -/
def name (x : E) : Term W E P T := fun _ _ ↦ x

/-- A centered proposition with a presupposition, which is true, false or undefined at a world
and a center. -/
abbrev CenteredProp (W E : Type*) := PartialProp (Centered W E)

variable (V : E → W → Prop) (t : Term W E P T) (c : Context W E P T)

/-- The centered intension of a clause with the egophoric suffix, which asserts that the subject
has the property and presupposes that the subject is the center. -/
def ego : CenteredProp W E where
  presup p := t c p.2 = p.2
  assertion p := V (t c p.2) p.1

/-- The centered intension of a clause with the plain verb form. -/
def plain : CenteredProp W E := .ofProp fun p ↦ V (t c p.2) p.1

/-- The centered intension of an egophoric clause on the authority-indexical account, which
presupposes that the subject is the authority of the context. -/
def egoAuth : CenteredProp W E where
  presup p := t c p.2 = c.authority
  assertion p := V (t c p.2) p.1

/-- The ordinary intension of a centered proposition at the agent `x` is the set of worlds where
it is defined and true with `x` at the center. -/
def uncenter (φ : CenteredProp W E) (x : E) : Set W := {w | φ.holds (w, x)}

variable {V t c} {x : E}

theorem uncenter_ego_of_eq (h : t c x = x) : uncenter (ego V t c) x = {w | V x w} := by
  ext w; simp [uncenter, ego, PartialProp.holds, h]

theorem uncenter_ego_of_ne (h : t c x ≠ x) : uncenter (ego V t c) x = ∅ := by
  ext w; simp [uncenter, ego, PartialProp.holds, h]

theorem uncenter_neg_ego_of_eq (h : t c x = x) :
    uncenter (ego V t c).neg x = {w | V x w}ᶜ := by
  ext w; simp [uncenter, ego, PartialProp.neg, PartialProp.holds, h]

theorem uncenter_neg_ego_of_ne (h : t c x ≠ x) : uncenter (ego V t c).neg x = ∅ := by
  ext w; simp [uncenter, ego, PartialProp.neg, PartialProp.holds, h]

/-- The authority-indexical account and the egophoric account give a root clause the same
authority-uncentered intension. -/
theorem uncenter_egoAuth :
    uncenter (egoAuth V t c) c.authority = uncenter (ego V t c) c.authority := rfl

/-! ### Assertions and questions -/

/-- Asserting `φ` in `c` commits the authority and proposes the authority-uncentered intension
for the common ground. -/
def assert (K : Table E W) (c : Context W E P T) (φ : CenteredProp W E) : Table E W :=
  K.assert c.authority (uncenter φ c.authority)

/-- Asking whether `φ` in `c` raises the two answers, each with the presuppositions of `φ`,
uncentered by the authority. -/
def ask (K : Table E W) (c : Context W E P T) (φ : CenteredProp W E) : Table E W :=
  K.push (ofSet (uncenter φ c.authority) ⊔ ofSet (uncenter φ.neg c.authority))

variable {K : Table E W}

/-- An issue whose only answer is the empty proposition leaves no viable projected set. -/
theorem inCrisis_push_ofSet_empty : (K.push (ofSet (∅ : Set W))).InCrisis := by
  refine (Table.inCrisis_iff _).2 fun f hf ↦ ?_
  obtain ⟨⟨g, -, q, hq, rfl⟩, hne⟩ := hf
  rw [alt_ofSet, Set.mem_singleton_iff] at hq
  simp [hq] at hne

/-- An egophoric assertion whose subject is not the authority is not viable. -/
theorem inCrisis_assert_ego (h : t c c.authority ≠ c.authority) :
    (assert K c (ego V t c)).InCrisis := by
  rw [assert, uncenter_ego_of_ne h]
  exact inCrisis_push_ofSet_empty (K := K.commit c.authority ∅)

/-- An egophoric question whose subject is not the authority is not viable. -/
theorem inCrisis_ask_ego (h : t c c.authority ≠ c.authority) :
    (ask K c (ego V t c)).InCrisis := by
  rw [ask, uncenter_ego_of_ne h, uncenter_neg_ego_of_ne h, sup_idem]
  exact inCrisis_push_ofSet_empty

/-- With the authority as subject, an egophoric assertion is the default assertion of the
property of the authority. -/
theorem assert_ego_of_eq (h : t c c.authority = c.authority) :
    assert K c (ego V t c) = K.assert c.authority {w | V c.authority w} := by
  rw [assert, uncenter_ego_of_eq h]

/-- With the authority as subject, an egophoric question is the default polar question on the
property of the authority. -/
theorem ask_ego_of_eq (h : t c c.authority = c.authority) :
    ask K c (ego V t c) = K.polarQuestion {w | V c.authority w} := by
  rw [ask, uncenter_ego_of_eq h, uncenter_neg_ego_of_eq h]; rfl

/-- An egophoric assertion with the authority as subject is viable from a stable Table whose
common ground is consistent with the authority having the property. -/
theorem not_inCrisis_assert_ego (h : t c c.authority = c.authority) (hK : K.IsStable)
    (hV : K.commonGround ⊓ 𝓟 {w | V c.authority w} ≠ ⊥) :
    ¬ (assert K c (ego V t c)).InCrisis := by
  rw [assert_ego_of_eq h, Table.inCrisis_iff, Table.projectedSet_assert,
    Table.projectedSet_of_isStable hK, Table.project_singleton_ofSet hV]
  exact fun hf ↦ hV (hf _ rfl)

/-- An egophoric question with the authority as subject is viable from a stable Table whose
common ground leaves open whether the authority has the property. -/
theorem not_inCrisis_ask_ego (h : t c c.authority = c.authority) (hK : K.IsStable)
    (hV : K.commonGround ⊓ 𝓟 {w | V c.authority w} ≠ ⊥)
    (hV' : K.commonGround ⊓ 𝓟 {w | V c.authority w}ᶜ ≠ ⊥) :
    ¬ (ask K c (ego V t c)).InCrisis := by
  rw [ask_ego_of_eq h, Table.inCrisis_iff, Table.projectedSet_polarQuestion,
    Table.projectedSet_of_isStable hK, Table.project_singleton_polar hV hV']
  exact fun hf ↦ hV (hf _ (Set.mem_insert _ _))

/-! ### The egophoric paradigm -/

/-- A second-person egophoric statement is not viable. -/
theorem inCrisis_assert_ego_you (hne : c.agent ≠ c.addressee) (hc : c.IsDeclarative) :
    (assert K c (ego V you c)).InCrisis :=
  inCrisis_assert_ego (t := you) fun h ↦ hne (h.trans hc).symm

/-- A first-person egophoric question is not viable. -/
theorem inCrisis_ask_ego_I (hne : c.agent ≠ c.addressee) (hc : c.IsInterrogative) :
    (ask K c (ego V I c)).InCrisis :=
  inCrisis_ask_ego (t := I) fun h ↦ hne (h.trans hc)

/-- Under a reportative evidential whose source is not the speaker, a first-person egophoric
statement is not viable. -/
theorem inCrisis_assert_ego_I_of_source (hs : c.agent ≠ c.authority) :
    (assert K c (ego V I c)).InCrisis :=
  inCrisis_assert_ego (t := I) hs

/-- The subject of a viable egophoric assertion is the authority, which is the speaker of a
plain declarative and the source under a reportative evidential. -/
theorem eq_authority_of_not_inCrisis_assert (h : ¬ (assert K c (ego V t c)).InCrisis) :
    t c c.authority = c.authority :=
  of_not_not fun hne ↦ h (inCrisis_assert_ego hne)

/-- The subject of a viable egophoric question is the authority, the addressee. -/
theorem eq_authority_of_not_inCrisis_ask (h : ¬ (ask K c (ego V t c)).InCrisis) :
    t c c.authority = c.authority :=
  of_not_not fun hne ↦ h (inCrisis_ask_ego hne)

/-! ### The Newari paradigm -/

section Rows

open Data.Examples

/-- The subject term of an example, from the person of its pronoun. -/
def subject? (r : LinguisticExample) : Option (Term W E P T) :=
  match r.feature? "subject" with
  | some "1" => some I
  | some "2" => some you
  | _ => none

/-- The context of an example over a Kaplanian context, with the speaker as the authority of a
declarative and the addressee as the authority of an interrogative. -/
def context? (r : LinguisticExample) (c₀ : Reference.Context W E P T) :
    Option (Context W E P T) :=
  match r.feature? "clause" with
  | some "declarative" => some ⟨c₀, c₀.agent⟩
  | some "interrogative" => some ⟨c₀, c₀.addressee⟩
  | _ => none

/-- An egophoric example of the paper is acceptable exactly when its subject is the authority
of its context, the condition under which its speech act can be viable. -/
theorem ego_acceptable_iff (c₀ : Reference.Context W E P T) (hne : c₀.agent ≠ c₀.addressee) :
    ∀ r ∈ Examples.all, r.feature? "marking" = some "ego" →
      ∃ t ∈ subject? r, ∃ c ∈ context? r c₀,
        (r.judgment = .acceptable ↔ t c c.authority = c.authority) := by
  intro r hr hm
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨I, rfl, _, rfl, by simp [I, Examples.ex_27]⟩
  · exact ⟨you, rfl, _, rfl, by simp [you, Examples.ex_28, hne.symm]⟩
  · exact ⟨I, rfl, _, rfl, by simp [I, Examples.ex_34a, hne]⟩
  · exact absurd hm (by decide)
  · exact ⟨you, rfl, _, rfl, by simp [you, Examples.ex_35a]⟩
  · exact absurd hm (by decide)

end Rows

/-! ### Speech reports -/

/-- `x` says `φ` in `w` when `φ` is defined and true at every centered world compatible with
what `x` says in `w`. -/
def Says (R : Centered W E → Centered W E → Prop) (x : E) (φ : CenteredProp W E) (w : W) :
    Prop :=
  ∀ p, R (w, x) p → φ.holds p

/-- The centered intension of a speech report, which does not depend on its own center. -/
def report (R : Centered W E → Centered W E → Prop) (x : E) (φ : CenteredProp W E) :
    CenteredProp W E :=
  .ofProp fun p ↦ Says R x φ p.1

variable {R : Centered W E → Centered W E → Prop} {φ : CenteredProp W E} {w : W} {y z : E}

/-- Saying is the de se *say* of [pearson-2015] over the alternatives of the say relation. -/
theorem says_iff_sayDeSe {alts : List (Centered W E)} (h : ∀ p, R (w, x) p ↔ p ∈ alts) :
    Says R x φ w ↔ sayDeSe alts fun a w' ↦ φ.holds (w', a) := by
  simp [Says, sayDeSe, h]

/-- In an egophoric report the holder identifies the subject as herself and self-ascribes the
property. -/
theorem says_ego_iff :
    Says R x (ego V t c) w ↔
      (∀ p, R (w, x) p → t c p.2 = p.2) ∧ Says R x (ego V self c) w := by
  simp only [Says, ego, self, PartialProp.holds, true_and]
  exact ⟨fun h ↦ ⟨fun p hp ↦ (h p hp).1, fun p hp ↦ (h p hp).1 ▸ (h p hp).2⟩,
    fun h p hp ↦ ⟨h.1 p hp, (h.1 p hp).symm ▸ h.2 p hp⟩⟩

/-- An egophoric report entails the plain report. -/
theorem says_plain_of_says_ego (h : Says R x (ego V t c) w) : Says R x (plain V t c) w :=
  fun p hp ↦ ⟨trivial, (h p hp).2⟩

/-- A holder who says something, and who takes herself to be who she is. -/
structure SelfAware (R : Centered W E → Centered W E → Prop) (x : E) : Prop where
  serial : ∀ w, ∃ p, R (w, x) p
  center : ∀ w p, R (w, x) p → p.2 = x

/-- Under double embedding the egophoric subject is the closest reported speaker, whoever the
outer speaker is. -/
theorem eq_of_says_report_ego (hy : ∀ w, ∃ p, R (w, y) p) (hx : SelfAware R x)
    (h : Says R y (report R x (ego V (name z) c)) w) : z = x := by
  obtain ⟨p, hp⟩ := hy w
  obtain ⟨q, hq⟩ := hx.serial p.1
  exact ((h p hp).2 q hq).1.trans (hx.center _ _ hq)

/-! ### The authority-indexical account -/

/-- The context shift a report needs on the authority-indexical account: the reported speaker
becomes the authority. -/
def authorityShift (x : E) : Function.End (Context W E P T) := fun c ↦ { c with authority := x }

/-- The shift is a monster. -/
theorem isMonster_authorityShift (h : c.authority ≠ x) :
    Reference.IsMonster (authorityShift (W := W) (P := P) (T := T) x) :=
  (Reference.isMonster_iff _).2 ⟨c, fun e ↦ h (congrArg Context.authority e).symm⟩

/-- On the authority-indexical account a shifted report of a rigid subject is the plain report
together with coreference of the subject and the reported speaker. -/
theorem says_egoAuth_name_iff (hR : ∃ p, R (w, x) p) :
    Says R x (egoAuth V (name z) (authorityShift x c)) w ↔
      z = x ∧ Says R x (plain V (name z) c) w := by
  obtain ⟨p₀, hp₀⟩ := hR
  simp only [Says, egoAuth, plain, name, authorityShift, PartialProp.holds,
    PartialProp.ofProp, true_and]
  exact ⟨fun h ↦ ⟨(h p₀ hp₀).1, fun p hp ↦ (h p hp).2⟩, fun h p hp ↦ ⟨h.1, h.2 p hp⟩⟩

/-! ### The unrecognized photograph

Syam points at a photograph of a man with a lampshade on his head and says *that guy drank too
much*, not realizing that the man is himself. -/

section Lampshade

/-- Syam, and the man Syam takes himself to be. -/
inductive Person | syam | other
  deriving DecidableEq

/-- The world of the report and the world as Syam describes it. -/
inductive World | actual | said
  deriving DecidableEq

/-- What Syam says is compatible with his being someone other than the man in the photograph. -/
def sayAlt : Centered World Person → Centered World Person → Prop :=
  fun p q ↦ p = (.actual, .syam) ∧ q = (.said, .other)

/-- The man in the photograph drank too much. -/
def drank : Person → World → Prop := fun x w ↦ x = .syam ∧ w = .said

variable (c : Context World Person Unit Unit)

/-- The plain report is true and the egophoric report false, while the authority-indexical
account, which sees only coreference, makes the egophoric report true. -/
theorem lampshade :
    Says sayAlt .syam (plain drank (name .syam) c) .actual ∧
    ¬ Says sayAlt .syam (ego drank (name .syam) c) .actual ∧
    Says sayAlt .syam (egoAuth drank (name .syam) (authorityShift .syam c)) .actual := by
  refine ⟨?_, fun h ↦ ?_, ?_⟩
  · rintro p ⟨-, rfl⟩; exact ⟨trivial, rfl, rfl⟩
  · exact absurd (h (.said, .other) ⟨rfl, rfl⟩).1 (by simp [ego, name])
  · rintro p ⟨-, rfl⟩; exact ⟨rfl, rfl, rfl⟩

end Lampshade

end CoppockWechsler2018
