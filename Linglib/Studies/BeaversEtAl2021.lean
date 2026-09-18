import Linglib.Studies.BeaversKoontzGarboden2020
import Linglib.Data.Examples.BeaversEtAl2021
import Mathlib.Data.Fintype.Basic

/-!
# Beavers et al. (2021): States and Changes of State

This file formalizes the argument of Beavers and colleagues that some roots entail change. A
property-concept root, such as that of *bright*, describes a state that need not have come
about. A result root, such as that of *shatter*, describes a state that always arises from a
change (`Verb.Model.EntailsChange`). This contradicts the Bifurcation Thesis, on which change
is introduced by the verbal template and never by a root.

A root entails change exactly when its stative cannot be conjoined with a denial of change
(`entailsChange_iff_forall_not_deniesChange`), and with such a root restitutive *again*
presupposes an earlier change (`change_of_againRestitutive_presup`). The morphology follows
from a default realization rule: a verb is unmarked iff its root entails change, and a stative
is unmarked iff its complement does not. A language that spells out the unmarked form only when
it spells out the marked one belongs to one of the three attested types
(`Exponence.trichotomy`).

## Implementation notes

* The semantics is stated on `Verb.Model`, the change-of-state model of Beavers and
  Koontz-Garboden's book, and *again* is `Presupposition.again`.
* The realization rule reads whether a root entails change off its kind signature.
* The tables of the typological survey are not represented. Its coding of markedness is
  (`Code.IsMarked`).

## References

* [beavers-etal-2021]
* [beavers-koontz-garboden-2020]
* [embick-2009]
* [arad-2005]
* [haspelmath-1993]
-/

namespace BeaversEtAl2021

open Semantics Presupposition

/-! ### Roots that entail change -/

section Model

variable {Entity State Event : Type*} (M : Verb.Model Entity State Event)
  {ltS : State → State → Prop} {ltE : Event → Event → Prop} {v : Verb} {x : Entity}
  {s : State}

/-- The deverbal stative holds of the states of the root's property that a change gave rise
to. -/
def resultStative (v : Verb) (x : Entity) (s : State) : Prop :=
  M.rootState v x s ∧ ∃ e, M.become s e

/-- The stative description `P` holds of `x` in the state `s`, and no change gave rise to `s`. -/
def DeniesChange (P : Entity → State → Prop) (x : Entity) (s : State) : Prop :=
  P x s ∧ ¬ ∃ e, M.become s e

/-- A deverbal stative never survives the denial of change, whatever its root. -/
theorem not_deniesChange_resultStative : ¬ DeniesChange M (resultStative M v) x s :=
  fun h ↦ h.2 h.1.2

/-- A root entails change iff its basic stative never survives the denial of change. -/
theorem entailsChange_iff_forall_not_deniesChange :
    M.EntailsChange v ↔ ∀ x s, ¬ DeniesChange M (M.rootState v) x s :=
  forall₂_congr fun _ _ ↦ by simp [DeniesChange]

/-- With a root that entails change the basic and the deverbal stative coincide. -/
theorem resultStative_iff_rootState (h : M.EntailsChange v) :
    resultStative M v x s ↔ M.rootState v x s :=
  and_iff_left_of_imp (h x s)

/-- With a root that entails change, *again* attached to the root presupposes an earlier
change, so the restitutive reading is lost. -/
theorem change_of_againRestitutive_presup (h : M.EntailsChange v)
    (hp : (M.againRestitutive ltS v x).presup s) : ∃ s', ltS s' s ∧ ∃ e, M.become s' e :=
  M.againRestitutive_presup_entails_change (h x) hp

/-- *Again* attached to `vbecome` presupposes an earlier change with every root. -/
theorem change_of_againRepetitiveBecome_presup {e : Event}
    (hp : (M.againRepetitiveBecome ltE v x).presup e) :
    ∃ e', ltE e' e ∧ ∃ s, M.become s e' :=
  let ⟨e', hlt, s, hb, _⟩ := hp; ⟨e', hlt, s, hb⟩

end Model

/-! ### A knife forged sharp -/

/-- A knife forged sharp is sharp in its first state `false`, and in its later state `true`,
which a sharpening gave rise to. -/
def forged : Verb.Model Unit Bool Unit where
  rootState _ _ _ := True
  become s _ := s = true
  cause _ _ := False
  effector _ _ := False
  manner _ _ := False

variable {v : Verb}

/-- The forged state of the knife survives the denial of change. -/
theorem forged_deniesChange : DeniesChange forged (forged.rootState v) () false :=
  ⟨trivial, fun ⟨_, h⟩ ↦ Bool.false_ne_true h⟩

/-- The root of the knife's property does not entail change. -/
theorem not_entailsChange_forged : ¬ forged.EntailsChange v :=
  fun h ↦ (entailsChange_iff_forall_not_deniesChange forged).1 h () false forged_deniesChange

/-- The restitutive presupposition holds at the later state of the knife although no change gave
rise to an earlier one. -/
theorem forged_restitutive :
    (forged.againRestitutive (· < ·) v ()).presup true ∧
      ¬ ∃ s', s' < true ∧ ∃ e, forged.become s' e :=
  ⟨⟨false, Bool.false_lt_true, trivial⟩, fun ⟨_, hlt, _, h⟩ ↦ absurd (h ▸ hlt) (lt_irrefl _)⟩

/-! ### Default realization -/

/-- The realization of a head in a category is the form for the unmarked semantic association
or the form for the marked one. -/
inductive Markedness
  | unmarked
  | marked
  deriving DecidableEq, Repr

/-- The two structures of a stative. -/
inductive AdjectivalStructure
  /-- The stative head over the bare root. -/
  | basic
  /-- The stative head over a `vbecome` phrase. -/
  | result
  deriving DecidableEq, Repr

/-- The default realization of `vbecome` over a root is unmarked iff the root entails change. -/
def verbRealization (r : Root) : Markedness :=
  if Root.Kind.result ∈ r.closedKinds then .unmarked else .marked

/-- The default realization of the stative head is marked iff its complement entails change, as
a `vbecome` phrase always does. -/
def stativeRealization (r : Root) : AdjectivalStructure → Markedness
  | .basic => if Root.Kind.result ∈ r.closedKinds then .marked else .unmarked
  | .result => .marked

variable {r p : Root}

/-- The verb and the simple stative of a root are realized as mirror images. -/
theorem verbRealization_ne_stativeRealization_basic :
    verbRealization r ≠ stativeRealization r .basic := by
  unfold verbRealization stativeRealization; split_ifs <;> decide

/-- An unmarked stative is the simple stative of a root that does not entail change, so result
roots lack one. -/
theorem stativeRealization_eq_unmarked_iff {a : AdjectivalStructure} :
    stativeRealization r a = .unmarked ↔ a = .basic ∧ Root.Kind.result ∉ r.closedKinds := by
  cases a <;> simp [stativeRealization]

/-- A language's spell-out of the two realizations, in which the unmarked one is overt only if
the marked one is. -/
structure Exponence where
  /-- The realization is spelled out overtly. -/
  Overt : Markedness → Prop
  /-- The unmarked realization is overt only if the marked one is. -/
  overt_marked : Overt .unmarked → Overt .marked

/-- A language is asymmetric, with only the marked realization overt, equipollent, with both
overt, or labile, with neither. -/
theorem Exponence.trichotomy (L : Exponence) :
    (¬ L.Overt .unmarked ∧ L.Overt .marked) ∨ (L.Overt .unmarked ∧ L.Overt .marked) ∨
      (¬ L.Overt .unmarked ∧ ¬ L.Overt .marked) := by
  have := L.overt_marked; tauto

/-- No language is the reverse of English, with overt verbs for the roots that entail change and
bare verbs for those that do not. -/
theorem Exponence.not_reverse_asymmetric (L : Exponence)
    (hr : Root.Kind.result ∈ r.closedKinds) (hp : Root.Kind.result ∉ p.closedKinds) :
    ¬ (L.Overt (verbRealization r) ∧ ¬ L.Overt (verbRealization p)) := by
  simp only [verbRealization, hr, hp, ite_true, ite_false]
  exact fun ⟨h, hn⟩ ↦ hn (L.overt_marked h)

/-! ### The coding of the survey -/

/-- The five positions of a root's paradigm. -/
inductive ParadigmPosition
  | underlyingRoot
  | simpleStative
  | inchoative
  | causative
  | resultStative
  deriving DecidableEq, Fintype, Repr

/-- The relation of a form `X` to a member `Y` of its paradigm. -/
inductive MorphRelation
  /-- The code `i` says that `X` is the input to a rule forming `Y`. -/
  | input
  /-- The code `d` says that `X` is the output of a rule on `Y`. -/
  | derived
  /-- The code `t` says that `X` is related to `Y` through a series of input and output pairs. -/
  | transitive
  /-- The code `l` says that `X` and `Y` are labile. -/
  | labile
  /-- The code `e` says that `X` and `Y` are equipollent. -/
  | equipollent
  /-- The code `u` says that no other relation applies. -/
  | unrelated
  /-- The code `n` says that `Y` is unattested. -/
  | unattested
  /-- The code `s` says that `X` is `Y`. -/
  | same
  deriving DecidableEq, Repr

/-- The code of a form gives its relation to each position of its paradigm. -/
abbrev Code := ParadigmPosition → MorphRelation

/-- The code with the given relations to the five positions, in their order. -/
def Code.of (a b c d e : MorphRelation) : Code
  | .underlyingRoot => a
  | .simpleStative => b
  | .inchoative => c
  | .causative => d
  | .resultStative => e

/-- A form is marked when it is derived from or equipollent to another member of its paradigm;
a form with only the other relations is unmarked. -/
def Code.IsMarked (c : Code) : Prop := ∃ k, c k = .derived ∨ c k = .equipollent

instance : DecidablePred Code.IsMarked := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

/-- A root's verbal paradigm is marked when its inchoative and its causative both are. -/
def VerbalParadigmMarked (inchoative causative : Code) : Prop :=
  inchoative.IsMarked ∧ causative.IsMarked

instance (i c : Code) : Decidable (VerbalParadigmMarked i c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- In the Tzeltal paradigm of 'small' the simple stative *tut* is unmarked, and the verbs
*tut-ub* and *tut-ub-tes* and the deverbal stative *tut-ub-en* are marked. -/
theorem tzeltal_small :
    ¬ (Code.of .unattested .same .input .transitive .transitive).IsMarked ∧
      VerbalParadigmMarked (.of .unattested .derived .same .input .input)
        (.of .unattested .transitive .derived .same .equipollent) ∧
      (Code.of .unattested .transitive .derived .equipollent .same).IsMarked := by
  decide

/-- In the Oromo paradigm of 'long' every form is built on the underlying root *dheer-*, so the
simple stative *dheer-aa* is marked along with the verbs. -/
theorem oromo_long :
    (Code.of .derived .same .equipollent .equipollent .unattested).IsMarked ∧
      VerbalParadigmMarked (.of .derived .equipollent .same .equipollent .unattested)
        (.of .derived .equipollent .equipollent .same .unattested) := by
  decide

/-! ### The judgments -/

open Data.Examples in
/-- A stative survives the denial of change in the examples exactly when its root is a
property-concept root. -/
theorem changeDenial_acceptable_iff :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "change denial" →
      (e.judgment = .acceptable ↔ e.feature? "root class" = some "property concept") := by
  decide

open Data.Examples in
/-- Outside Kakataibo no result root is accepted with restitutive *again*. -/
theorem restitutive_unacceptable_of_result :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "restitutive again" →
      e.language ≠ "cash1251" → e.feature? "root class" = some "result" →
      e.judgment = .unacceptable := by
  decide

end BeaversEtAl2021
