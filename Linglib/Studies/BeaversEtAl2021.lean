import Linglib.Studies.BeaversKoontzGarboden2020
import Linglib.Data.Examples.BeaversEtAl2021
import Mathlib.Data.Fintype.Basic

/-!
# Beavers et al. (2021): States and Changes of State

This file formalizes the argument of Beavers and colleagues that some roots entail change. The
roots of deadjectival change-of-state verbs, the property-concept roots (*bright*, *red*,
*flat*), describe states that need not have come about. The roots of the other change-of-state
verbs, the result roots (*shatter*, *cook*, *thaw*), describe states that are never found
without a change having produced them. The Bifurcation Thesis of Embick and of Arad says that a
meaning introduced by a templatic head, such as the change that `vbecome` introduces, is never
part of a root, so it cannot draw this distinction in the roots.

The analysis is that of Beavers and Koontz-Garboden's book, on the change-of-state model
`Verb.CosModel`. A root denotes a state predicate, (20a), and a result root is one whose state
always arises from a change, (21) (`EntailsChange`). Two diagnostics follow. A stative
description survives the denial of change, as in *the bright photo has never brightened*,
unless the root entails change, as in *#the shattered vase has never shattered*, (10)–(11), and
a deverbal stative never survives it whatever the root
(`entailsChange_iff_forall_not_deniesChange`, `not_deniesChange_resultStative`). *Again*
attached to the root gives a restitutive reading that needs no earlier change, as when a knife
forged sharp is sharpened again, (15), and with a result root its presupposition brings an
earlier change with it, so that *thaw again* requires two thawings, (16)
(`change_of_againRestitutive_presup`). The model `forged` is a knife that was forged sharp,
and witnesses both property-concept patterns. The analysis that keeps bifurcation, section 3.5,
must stipulate that *again* attaches no lower than `vbecome` with result roots, where the same
entailment holds of every root (`change_of_againRepetitiveBecome_presup`).

The morphology follows by the default realization rule (44). `vbecome` is realized by the
unmarked form when its root entails change and by the marked one otherwise, and the stative
head the other way around, so the verbs and the simple statives of a root are mirror images
(`verbRealization_ne_stativeRealization_basic`) and only a root that does not entail change has
an unmarked stative (`stativeRealization_eq_unmarked_iff`). A language spells the two
realizations out, the unmarked one overtly only if the marked one is overt too, which leaves the
three attested types: the asymmetric one of English and Greek, the equipollent one of Hebrew and
the labile one of Kakataibo and Kinyarwanda (`Exponence.trichotomy`). The fourth type, with overt
result-root verbs beside bare property-concept verbs, is excluded
(`Exponence.not_reverse_asymmetric`).

In the typological survey of 88 languages and 72 root meanings a form is marked when its code
records that it is derived from or equipollent to another member of its paradigm, (40)–(41)
(`Code.IsMarked`), which is checked on the two coded paradigms of (42). Property-concept roots
have simple statives in a median 95.67% of languages against 1.59% for result roots, and marked
verbal paradigms in a median 56.01% against 15.20%, both differences significant on a
Mann-Whitney test; the survey tables are not represented.

## Main definitions

* `EntailsChange`: every state of the root's property arises from a change, (21).
* `resultStative`, `DeniesChange`: the deverbal stative (8b) and the denial of change, (10).
* `Markedness`, `verbRealization`, `stativeRealization`: the default realizations of (44).
* `Exponence`: a language's spell-out of the two realizations.
* `MorphRelation`, `Code`, `Code.IsMarked`: the relation codes of (41) and the markedness of a
  coded form.

## Main results

* `entailsChange_iff_forall_not_deniesChange`: a root entails change iff its basic stative never
  survives the denial of change.
* `change_of_againRestitutive_presup`: with a result root restitutive *again* presupposes an
  earlier change.
* `forged_deniesChange`, `forged_restitutive`: a property-concept root passes both diagnostics.
* `Exponence.trichotomy`, `Exponence.not_reverse_asymmetric`: the three language types and the
  excluded fourth.

## Implementation notes

The stative head is the identity on a root, (20b). The paper gives no denotation for it over a
`vbecome` phrase; `resultStative` takes the state that the change gives rise to. Whether a root
entails change is read for (44) off its kind signature, `Root.Kind.result ∈ r.closedKinds`.

## References

* [beavers-etal-2021]
* [beavers-koontz-garboden-2020]
* [embick-2004]
* [embick-2009]
* [arad-2005]
* [haspelmath-1993]
-/

namespace BeaversEtAl2021

open Semantics Presupposition

/-! ### Roots that entail change, (20)–(21) -/

section Model

variable {Entity State T : Type*} [LinearOrder T] (M : Verb.CosModel Entity State T)
  {ltS : State → State → Prop} {ltE : Event T → Event T → Prop} {v : Verb} {x : Entity}
  {s : State}

/-- The root of `v` entails change when every state of its property arises from a change, the
meaning postulate of (21). -/
def EntailsChange (v : Verb) : Prop := ∀ x s, M.rootState v x s → ∃ e, M.become s e

/-- The deverbal stative of (8b) holds of the states of the root's property that a change gave
rise to. -/
def resultStative (v : Verb) (x : Entity) (s : State) : Prop :=
  M.rootState v x s ∧ ∃ e, M.become s e

/-- The stative description `P` of `x` in the state `s` is conjoined with the denial that `s`
arose from a change, as in (10)–(11). -/
def DeniesChange (P : Entity → State → Prop) (x : Entity) (s : State) : Prop :=
  P x s ∧ ¬ ∃ e, M.become s e

/-- A deverbal stative never survives the denial of change, whatever its root, as in *#the
brightened photo has never brightened*, (10a). -/
theorem not_deniesChange_resultStative : ¬ DeniesChange M (resultStative M v) x s :=
  fun h ↦ h.2 h.1.2

/-- A root entails change iff its basic stative never survives the denial of change, (11). -/
theorem entailsChange_iff_forall_not_deniesChange :
    EntailsChange M v ↔ ∀ x s, ¬ DeniesChange M (M.rootState v) x s :=
  forall₂_congr fun _ _ ↦ by simp [DeniesChange]

/-- With a root that entails change the two statives coincide, so the stative of a result root
entails change in either structure of (8). -/
theorem resultStative_iff_rootState (h : EntailsChange M v) :
    resultStative M v x s ↔ M.rootState v x s :=
  and_iff_left_of_imp (h x s)

/-- With a root that entails change, *again* attached to the root presupposes an earlier change,
so the restitutive reading is not found, (16). -/
theorem change_of_againRestitutive_presup (h : EntailsChange M v)
    (hp : (M.againRestitutive ltS v x).presup s) : ∃ s', ltS s' s ∧ ∃ e, M.become s' e :=
  M.againRestitutive_presup_entails_change (h x) hp

/-- *Again* attached to `vbecome` presupposes an earlier change with every root. The analysis of
section 3.5 that keeps bifurcation makes this the lowest attachment for result roots, (19b). -/
theorem change_of_againRepetitiveBecome_presup {e : Event T}
    (hp : (M.againRepetitiveBecome ltE v x).presup e) :
    ∃ e', ltE e' e ∧ ∃ s, M.become s e' :=
  let ⟨e', hlt, s, hb, _⟩ := hp; ⟨e', hlt, s, hb⟩

end Model

/-! ### A knife forged sharp, (15a) -/

/-- The knife of (15a) is sharp in its first state `false`, as forged, and in its later state
`true`, which a sharpening gave rise to. -/
def forged : Verb.CosModel Unit Bool ℕ where
  rootState _ _ _ := True
  become s _ := s = true
  cause _ _ := False
  effector _ _ := False
  manner _ _ := False

variable {v : Verb}

/-- The forged state of the knife survives the denial of change, as *the bright photo has never
brightened* does, (10a). -/
theorem forged_deniesChange : DeniesChange forged (forged.rootState v) () false :=
  ⟨trivial, fun ⟨_, h⟩ ↦ Bool.false_ne_true h⟩

/-- The root of the knife's property does not entail change. -/
theorem not_entailsChange_forged : ¬ EntailsChange forged v :=
  fun h ↦ (entailsChange_iff_forall_not_deniesChange forged).1 h () false forged_deniesChange

/-- *John sharpened the knife again* is true on one sharpening, (15a), since the restitutive
presupposition holds at the later state and no change gave rise to an earlier one. -/
theorem forged_restitutive :
    (forged.againRestitutive (· < ·) v ()).presup true ∧
      ¬ ∃ s', s' < true ∧ ∃ e, forged.become s' e :=
  ⟨⟨false, Bool.false_lt_true, trivial⟩, fun ⟨_, hlt, _, h⟩ ↦ absurd (h ▸ hlt) (lt_irrefl _)⟩

/-! ### Default realization, (44) -/

/-- The realization of a head in a category is the form for the unmarked semantic association
or the form for the marked one. -/
inductive Markedness
  | unmarked
  | marked
  deriving DecidableEq, Repr

/-- The adjectival structures of (8), after Embick. -/
inductive AdjectivalStructure
  /-- The stative head over the bare root, (8a). -/
  | basic
  /-- The stative head over a `vbecome` phrase, (8b). -/
  | result
  deriving DecidableEq, Repr

/-- The default realization of `vbecome` over a root, (44a), is unmarked iff the root entails
change. -/
def verbRealization (r : Root) : Markedness :=
  if Root.Kind.result ∈ r.closedKinds then .unmarked else .marked

/-- The default realization of the stative head, (44b), is marked iff its complement entails
change, as a `vbecome` phrase always does. -/
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

/-- A language's spell-out of the two realizations. When the two differ it is the marked one
that is overt. -/
structure Exponence where
  /-- The realization is spelled out overtly. -/
  Overt : Markedness → Prop
  /-- The unmarked realization is overt only if the marked one is. -/
  overt_marked : Overt .unmarked → Overt .marked

/-- A language is of the asymmetric type, as English and Greek are, of the equipollent type,
with both realizations overt as in Hebrew, or of the labile type, with neither overt as in
Kakataibo and Kinyarwanda. -/
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

/-! ### The coding of the survey, (40)–(42) -/

/-- The five positions of a root's paradigm, (40). -/
inductive ParadigmPosition
  | underlyingRoot
  | simpleStative
  | inchoative
  | causative
  | resultStative
  deriving DecidableEq, Fintype, Repr

/-- The relation of a form `X` to a member `Y` of its paradigm, (41), generalizing the
classification of Haspelmath. -/
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

/-- The code with the given relations to the five positions, in the order of (40). -/
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

/-- In the Tzeltal paradigm of 'small', (42a), the simple stative *tut* is unmarked, the verbs
*tut-ub* and *tut-ub-tes* are marked, and so is the deverbal stative *tut-ub-en*, as (44)
leads one to expect of a property-concept root. -/
theorem tzeltal_small :
    ¬ (Code.of .unattested .same .input .transitive .transitive).IsMarked ∧
      VerbalParadigmMarked (.of .unattested .derived .same .input .input)
        (.of .unattested .transitive .derived .same .equipollent) ∧
      (Code.of .unattested .transitive .derived .equipollent .same).IsMarked := by
  decide

/-- In the Oromo paradigm of 'long', (42b), every form is built on the underlying root *dheer-*,
so the simple stative *dheer-aa* is marked along with the verbs, the equipollent pattern that
neutralizes the contrast. -/
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
/-- Outside Kakataibo no result root is accepted with restitutive *again*. The paper attributes
the Kakataibo token *rëtë* 'kill' to its lexicalizing 'not alive', a state without change. -/
theorem restitutive_unacceptable_of_result :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "restitutive again" →
      e.language ≠ "cash1251" → e.feature? "root class" = some "result" →
      e.judgment = .unacceptable := by
  decide

end BeaversEtAl2021
