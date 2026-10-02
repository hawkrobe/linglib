module

public import Linglib.Semantics.Causation.VerbClass
public import Linglib.Semantics.Presupposition.Implicative
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Verbs.Copular

/-!
# Karttunen (1971)

Karttunen identifies the implicative verbs, *manage*, *remember*, *bother*, *dare*, *happen* and
the others listed in (2), whose assertion commits the speaker to the complement and whose
negation commits the speaker to its negation. He analyzes such a sentence as a
presupposition–proposition pair: the proposition `v(S)` is what is asserted, negated or
questioned, and the presupposition says what condition `v(S)` is for the complement. Schema (37)
makes `v(S)` necessary and sufficient for `S` (*manage*), (41) necessary and sufficient for `¬S`
(*fail*, *forget*), (54) necessary only (*be able*, *be possible*), and (59) sufficient only
(*force*, *cause*); the non-implicatives *hope*, *want* and *try* carry no such presupposition.

The schemas are `Implicative.Schema` under the material reading of the conditions
(`Implicative.Reading.material`), which gives the paper's entailment facts: double negation
cancels as in (13) (`manage_neg_neg_holds_imp`), and the one-way cells and the non-implicatives
leave the other direction open (`force_neg_not_entails`, `beAble_not_entails`,
`ofProp_not_entails`). The English fragment's entries for the verbs of (2), (38) and (44) carry
their schemas (`implicative_eq`) and so are presupposition triggers
(`isTrigger_of_mem_english`), while its entries for the non-implicatives of (2) carry none
(`implicative_eq_none`).

## References

* [karttunen-1971]
-/

@[expose] public section

namespace Karttunen1971a

open Presupposition Implicative

/-- Double negation cancels, (13): *John didn't remember not to lock his door* commits the
speaker to *John locked his door*. -/
theorem manage_neg_neg_holds_imp {W : Type*} {v S : W → Prop} {w : W}
    (hs : (PartialProp.neg (Schema.manage.sentence (Reading.material W) v fun w ↦ ¬ S w)).holds w) :
    S w :=
  not_not.mp (Schema.neg_holds_imp (k := .manage) trivial hs)

/-- (58) *John didn't force Mary to stay home* leaves open whether she stayed. -/
theorem force_neg_not_entails : ∃ (v S : Unit → Prop),
    (PartialProp.neg (Schema.force.sentence (Reading.material Unit) v S)).holds () ∧ S () :=
  ⟨fun _ ↦ False, fun _ ↦ True, ⟨⟨fun _ _ ↦ trivial, fun h ↦ False.elim h⟩, id⟩, trivial⟩

/-- (55) *John was able to come* leaves open whether he came. -/
theorem beAble_not_entails : ∃ (v S : Unit → Prop),
    (Schema.beAble.sentence (Reading.material Unit) v S).holds () ∧ ¬ S () :=
  ⟨fun _ ↦ True, fun _ ↦ False, ⟨⟨fun h ↦ False.elim h, fun _ _ ↦ trivial⟩, trivial⟩, id⟩

/-- A non-implicative, which has no presupposition, commits the speaker to nothing about its
complement in either polarity (5). -/
theorem ofProp_not_entails :
    (∃ (v S : Unit → Prop), (PartialProp.ofProp v).holds () ∧ ¬ S ()) ∧
      ∃ (v S : Unit → Prop), (PartialProp.neg (PartialProp.ofProp v)).holds () ∧ S () :=
  ⟨⟨fun _ ↦ True, fun _ ↦ False, ⟨trivial, trivial⟩, id⟩,
   ⟨fun _ ↦ False, fun _ ↦ True, ⟨trivial, id⟩, trivial⟩⟩

/-! ### The English lexicon -/

section Lexicon

open English.Verbs hiding Verb

/-- The English fragment's entries for the implicatives of (2), with schema (37), for the
negative implicatives of (38), with (41), and for *be able* of (44), with (54), as far as the
fragment covers the lists: its *get* is the causative sense and its *avoid* takes a noun phrase.
The verbs of (56), *force* and *prevent*, are causatives in the fragment and carry no implicative
polarity. -/
def english : List (Verb × Schema) :=
  [(manage.toVerb, .manage), (remember.toVerb, .manage), (bother.toVerb, .manage),
    (dare.toVerb, .manage), (venture.toVerb, .manage), (condescend.toVerb, .manage),
    (happen.toVerb, .manage), (fail.toVerb, .fail), (forget.toVerb, .fail),
    (neglect.toVerb, .fail), (Copular.beAble, .beAble)]

/-- Each entry carries its schema. -/
theorem implicative_eq : ∀ p ∈ english, p.1.implicative = some p.2 := by
  decide

/-- Every entry is a presupposition trigger, as (37), (41) and (54) each pair the proposition
with a presupposition. -/
theorem isTrigger_of_mem_english {p : Verb × Schema} (hp : p ∈ english) : p.1.IsTrigger :=
  Verb.isTrigger_iff.2 (.inr (.inl (by simp [implicative_eq p hp])))

/-- The fragment's entries for the non-implicatives of (2). -/
def nonImplicative : List Verb :=
  [try_.toVerb, promise.toVerb, want.toVerb, intend.toVerb, decide_.toVerb, hope.toVerb]

/-- The non-implicatives of (2) carry no schema. -/
theorem implicative_eq_none : ∀ v ∈ nonImplicative, v.implicative = none := by
  decide

end Lexicon

end Karttunen1971a
