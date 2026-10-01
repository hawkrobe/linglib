module

public import Linglib.Studies.ChatzikyriakidisLuo2017
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Data.Setoid.Basic

/-!
# Chatzikyriakidis & Luo (2020): Formal semantics in modern type theories

In the formal semantics of modern type theories, common nouns are interpreted as types rather than
predicates, and subtyping is coercive: one noun is a subtype of another when a unique coercion
between them may be inserted wherever an object of the second is expected. A noun modified by a
predicate is the Σ-type of its objects satisfying the predicate, a subtype of the noun through
the first projection. This file formalizes the book's classification of adjectival modification,
its operator NOT for the propositional forms of judgements, and its identity criteria for counting.

The book's Theorem 7.1 states that the laws (A1)–(A5) of NOT are provable once NOT is defined from
the heterogeneous equality JMeq. We show that with Lean's heterogeneous equality, which validates
the rules of JMeq, (A1) and (A2) hold but (A3), (A4) and (A5) fail at every proper finite Σ-subtype,
such as the men among the humans. With heterogeneous equality read as equality in a common
carrier, all five laws hold.

## Main definitions

* `sigma A P`: the Σ-type of the objects of `A` satisfying `P`, a subtype of `A` by `sigmaFst A P`.
* `DoesNot A P B b`: the operator NOT, from which `Is` and `Does` define IS and DO.
* `TypeDisjoint A B`: no inhabited noun is a subtype of both `A` and `B`.
* `SubSetoid A B sA sB`: `A` is a subtype of `B` whose identity criterion `sA` is inherited
  from `sB`.

## Main statements

* `range_sigma_comp`: intersective modification meets the noun's extension with the adjective's.
* `not_forall_nonempty_sub_sigma`: subsective modification need not respect subtyping.
* `forall_does_iff_injective`: law (A1) holds on a noun exactly when its embedding is injective.
* `not_doesNot_comp_heq`, `not_forall_doesNot_of_sub_heq`, `not_exists_doesNot_of_sub_heq`: laws
  (A3), (A4) and (A5) fail for `HEq`.
* `three₀_iff_two_lt_card`: three objects distinct under an identity criterion satisfy a predicate
  exactly when more than two of its identity classes do.

## Implementation notes

* Nouns are types embedded in a carrier of objects, as in [chatzikyriakidis-luo-2017]. The book's
  universe has no such carrier; here it supplies the heterogeneous equality, under which two
  objects are equal when their images are. This equality identifies an object with its image under
  a coercion, the axiom that [xue-luo-chatzikyriakidis-2018] add to prove (A3)–(A5).
* Coercions are explicit maps commuting with the embeddings rather than `Coe` instances, so that
  statements quantify over nouns.
* By propositional extensionality every modal collection `Prop → Prop` respects logical
  equivalence, the property for which the book rejects the belief contexts of [ranta-1994].

## TODO

* Gradable, multidimensional and adverbial modification.
* Dot-types for copredication, and counting under copredication.
* Negative occurrences (Definition 7.2) and dependent event types.
* A universe without a carrier, with coercions along a directed order.

## References

* [S. Chatzikyriakidis and Z. Luo, *Formal Semantics in Modern Type Theories*
  (2020)][chatzikyriakidis-luo-2020]
* [S. Chatzikyriakidis and Z. Luo, *On the Interpretation of Common Nouns: Types Versus
  Predicates* (2017)][chatzikyriakidis-luo-2017]
* [T. Xue, Z. Luo and S. Chatzikyriakidis, *Propositional Forms of Judgemental Interpretations*
  (2018)][xue-luo-chatzikyriakidis-2018]
* [H. Kamp, *Two theories about adjectives* (1975)][kamp-1975]
* [B. H. Partee, *Privative adjectives: Subsective plus coercion* (2010)][partee-2010]
* [A. Ranta, *Type-Theoretical Grammar* (1994)][ranta-1994]
-/

@[expose] public section

namespace ChatzikyriakidisLuo2020

open ChatzikyriakidisLuo2017

universe u

variable {Obj : Type u}

/-! ### Σ-types and coercive subtyping -/

/-- The Σ-type of the objects of `A` satisfying `P`, located through `A` ((2.41), (3.21)). -/
def sigma (A : CN Obj) (P : A.carrier → Prop) : CN Obj where
  carrier := {x // P x}
  embed x := A.embed x

/-- The first projection, which makes a modified noun a subtype of the noun ((2.42), (3.33)). -/
def sigmaFst (A : CN Obj) (P : A.carrier → Prop) : Sub (sigma A P) A :=
  ⟨Subtype.val, fun _ ↦ rfl⟩

/-- A Σ-type embeds injectively when its noun does, since by proof irrelevance two of its objects
are equal when their first projections are (p. 69). -/
theorem sigma_embed_injective {A : CN Obj} (hA : Function.Injective A.embed)
    (P : A.carrier → Prop) : Function.Injective (sigma A P).embed :=
  hA.comp Subtype.val_injective

/-- `A ≤ B` iff there is a coercion from `A` to `B`. -/
scoped instance : Preorder (CN Obj) where
  le A B := Nonempty (Sub A B)
  le_refl _ := ⟨⟨id, fun _ ↦ rfl⟩⟩
  le_trans _ _ _ := fun ⟨s⟩ ⟨t⟩ ↦ ⟨⟨t.ι ∘ s.ι, fun a ↦ (t.comm _).trans (s.comm a)⟩⟩

variable {A B C : CN Obj}

/-- Coercions into an injectively embedded noun are unique, as coherence requires (p. 40). -/
theorem subsingleton_sub (hB : Function.Injective B.embed) : Subsingleton (Sub A B) :=
  ⟨fun ⟨ι, hι⟩ ⟨κ, hκ⟩ ↦ by
    obtain rfl : ι = κ := funext fun a ↦ hB ((hι a).trans (hκ a).symm)
    rfl⟩

/-- A coercion out of an injectively embedded noun is injective. -/
theorem sub_injective (hA : Function.Injective A.embed) (s : Sub A B) :
    Function.Injective s.ι :=
  fun x y h ↦ hA ((s.comm x).symm.trans ((congrArg B.embed h).trans (s.comm y)))

/-! ### Adjectival modification -/

/-- Modification by a Π-polymorphic adjective is subsective in the subtyping order ((3.94),
(3.105)). -/
theorem isSubsective_sigma (adj : (A : CN Obj) → A.carrier → Prop) :
    Modifier.isSubsective fun A ↦ sigma A (adj A) :=
  fun A ↦ ⟨sigmaFst A (adj A)⟩

/-- Intersective modification respects subtyping, so a black cat is a black object (3.91). -/
def sigmaMap (s : Sub A B) (adj : Obj → Prop) :
    Sub (sigma A (adj ∘ A.embed)) (sigma B (adj ∘ B.embed)) where
  ι x := ⟨s.ι x.1, by simpa only [Function.comp_apply, s.comm] using x.2⟩
  comm x := s.comm x.1

/-- The extension of an intersectively modified noun is the meet of the noun's extension with the
adjective's, the intersective class of [kamp-1975] ((3.92)–(3.97)). -/
theorem range_sigma_comp (A : CN Obj) (adj : Obj → Prop) :
    Set.range (sigma A (adj ∘ A.embed)).embed =
      Modifier.intersective {o | adj o} (Set.range A.embed) := by
  ext o
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨ha, a, rfl⟩
  · rintro ⟨ho, a, rfl⟩
    exact ⟨⟨a, ho⟩, rfl⟩

/-- Since the instances of a Π-polymorphic adjective at two nouns are unrelated, a subtyping
need not lift to the modified nouns (3.101). -/
theorem not_forall_nonempty_sub_sigma :
    ¬ ∀ (A B : CN Bool) (_ : Sub A B) (adj : (C : CN Bool) → C.carrier → Prop),
      Nonempty (Sub (sigma A (adj A)) (sigma B (adj B))) := fun h ↦ by
  obtain ⟨s⟩ := h ⟨PUnit, fun _ ↦ true⟩ ⟨Bool, id⟩ ⟨fun _ ↦ true, fun _ ↦ rfl⟩
    (fun C _ ↦ Subsingleton C.carrier)
  exact Bool.noConfusion ((s.ι ⟨PUnit.unit, inferInstance⟩).2.elim true false)

section Privative

/-! Privative adjectives are subsective over the disjoint union of real and fake guns, as
[partee-2010] proposes. -/

/-- The disjoint union of two nouns, as in the type of guns `G = G_R + G_F` (3.110). -/
def sum (A B : CN Obj) : CN Obj := ⟨A.carrier ⊕ B.carrier, Sum.elim A.embed B.embed⟩

variable {GR GF : CN Obj}

/-- A gun is real when it comes from the real guns (3.111). -/
def IsReal : (sum GR GF).carrier → Prop := Sum.elim (fun _ ↦ True) (fun _ ↦ False)

/-- A gun is fake when it comes from the fake guns (3.112). -/
def IsFake : (sum GR GF).carrier → Prop := Sum.elim (fun _ ↦ False) (fun _ ↦ True)

/-- Every gun is real or fake (3.120). -/
theorem isReal_or_isFake (g : (sum GR GF).carrier) : IsReal g ∨ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

/-- A gun is real exactly when it is not fake (p. 71). -/
theorem isReal_iff_not_isFake (g : (sum GR GF).carrier) : IsReal g ↔ ¬ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

/-- A fake gun is not a real gun (3.121). -/
theorem not_isReal_sigmaFst (f : (sigma (sum GR GF) IsFake).carrier) :
    ¬ IsReal ((sigmaFst (sum GR GF) IsFake).ι f) :=
  (isReal_iff_not_isFake f.1).1.mt (not_not_intro f.2)

/-- When no object is both a real and a fake gun, fake guns and real guns have disjoint
extensions, so *fake* is privative relative to *real gun* (p. 72). -/
theorem disjoint_range_isFake (h : Function.Injective (sum GR GF).embed) :
    Disjoint (Set.range (sigma (sum GR GF) IsFake).embed)
      (Set.range (sigma (sum GR GF) IsReal).embed) := by
  rw [Set.disjoint_left]
  rintro _ ⟨f, rfl⟩ ⟨r, hr⟩
  exact (isReal_iff_not_isFake f.1).1 (h hr ▸ r.2) f.2

end Privative

/-! ### Propositional forms of judgements -/

/-- The operator NOT, read "`b` does not `P`", defined from heterogeneous equality as equality of
images in the carrier ((7.5), (7.11)). -/
def DoesNot (A : CN Obj) (P : A.carrier → Prop) (B : CN Obj) (b : B.carrier) : Prop :=
  ∀ x, A.embed x = B.embed b → ¬ P x

/-- The operator IS, the propositional form of the judgement that `y` is an `X` (7.7). -/
def Is (X : CN Obj) (y : B.carrier) : Prop := ¬ DoesNot X (p X) B y

/-- The operator DO, the propositional form of applying `P` to `y` (7.9). -/
def Does (P : A.carrier → Prop) (y : B.carrier) : Prop := ¬ DoesNot A P B y

theorem does_iff {P : A.carrier → Prop} {y : B.carrier} :
    Does P y ↔ ∃ x, A.embed x = B.embed y ∧ P x := by
  simp [Does, DoesNot]

theorem is_iff {y : B.carrier} : Is A y ↔ ∃ x, A.embed x = B.embed y := by
  simp [Is, DoesNot, p]

/-- IS holds of every object of its own noun (p. 64). -/
theorem is_self (a : A.carrier) : Is A a := is_iff.2 ⟨a, rfl⟩

/-- Law (A1) holds on a noun exactly when its embedding is injective (p. 153). -/
theorem forall_does_iff_injective :
    (∀ (P : A.carrier → Prop) x, Does P x ↔ P x) ↔ Function.Injective A.embed := by
  refine ⟨fun h x y hxy ↦ (h (· = y) x).1 (does_iff.2 ⟨y, hxy.symm, rfl⟩), fun hA P x ↦ ?_⟩
  rw [does_iff]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ hA hy ▸ hP, fun hP ↦ ⟨x, rfl, hP⟩⟩

/-- If `P` implies `Q`, not doing `Q` implies not doing `P`, which is law (A2). -/
theorem doesNot_mono {P Q : A.carrier → Prop} (h : ∀ x, P x → Q x) (y : B.carrier)
    (hQ : DoesNot A Q B y) : DoesNot A P B y :=
  fun x hx hP ↦ hQ x hx (h x hP)

/-- Along a coercion, not doing `P` as a `B` implies not doing it as an `A`, which is law (A3). -/
theorem doesNot_comp (s : Sub A B) (P : B.carrier → Prop) (z : C.carrier)
    (h : DoesNot B P C z) : DoesNot A (P ∘ s.ι) C z :=
  fun x hx ↦ h (s.ι x) ((s.comm x).trans hx)

/-- What no `B` does, no `A` does, which is law (A4). -/
theorem forall_doesNot_of_sub (s : Sub A B) (P : C.carrier → Prop)
    (h : ∀ y, DoesNot C P B y) (x : A.carrier) : DoesNot C P A x :=
  fun w hw ↦ h (s.ι x) w (hw.trans (s.comm x).symm)

/-- What some `A` does not do, some `B` does not do, which is law (A5). -/
theorem exists_doesNot_of_sub (s : Sub A B) (P : C.carrier → Prop)
    (h : ∃ x, DoesNot C P A x) : ∃ y, DoesNot C P B y :=
  let ⟨x, hx⟩ := h
  ⟨s.ι x, fun w hw ↦ hx w (hw.trans (s.comm x))⟩

/-- IS respects subtyping, as in the inference from "Teddy is a man" to "Teddy is a human"
(p. 154). -/
theorem is_of_sub (s : Sub A B) {z : C.carrier} (h : Is A z) : Is B z :=
  fun hB ↦ h (doesNot_comp s (p B) z hB)

/-- The negation operator of [chatzikyriakidis-luo-2017] is NOT with its object read in the
carrier. -/
theorem standardNeg_not_iff (P : A.carrier → Prop) (b : B.carrier) :
    (standardNeg Obj).not A P (B.embed b) ↔ DoesNot A P B b :=
  Iff.rfl

/-- Two nouns are disjoint when no inhabited noun is a subtype of both (Definition 7.1). -/
def TypeDisjoint (A B : CN Obj) : Prop :=
  ∀ C : CN Obj, Sub C A → Sub C B → IsEmpty C.carrier

/-- Two nouns are disjoint exactly when no object of the second is an object of the first, so that
"John is not a table" holds of every man ((3.66), (3.71)). -/
theorem typeDisjoint_iff : TypeDisjoint A B ↔ ∀ b : B.carrier, ¬ Is A b := by
  refine ⟨fun h b hb ↦ ?_, fun h C s t ↦ ⟨fun c ↦ h (t.ι c) (is_iff.2 ⟨s.ι c, ?_⟩)⟩⟩
  · obtain ⟨a, ha⟩ := is_iff.1 hb
    exact (h ⟨PUnit, fun _ ↦ B.embed b⟩ ⟨fun _ ↦ a, fun _ ↦ ha⟩ ⟨fun _ ↦ b, fun _ ↦ rfl⟩).false
      PUnit.unit
  · exact (s.comm c).trans (t.comm c).symm

/-- No coercion leads from an inhabited noun to a disjoint one, so `talk(t)` is ill-typed for a
table `t` ((3.5)–(3.7)). -/
theorem isEmpty_sub_of_typeDisjoint (h : TypeDisjoint A B) [Nonempty A.carrier] :
    IsEmpty (Sub A B) :=
  ⟨fun s ↦ (h A ⟨id, fun _ ↦ rfl⟩ s).false (Classical.arbitrary _)⟩

/-- An object is an alleged `M` when someone's collection of allegations contains that it is an
`M` (3.125). -/
def Alleged {Hum : CN Obj} (H : Hum.carrier → Prop → Prop) (M : CN Obj) (x : Hum.carrier) :
    Prop :=
  ∃ h, H h (Is M x)

/-- An alleged `M` need not be an `M`, and an `M` may be alleged (3.122). -/
theorem alleged_noncommittal {Hum M : CN Obj} {x y : Hum.carrier} (hx : ¬ Is M x) (hy : Is M y) :
    (∃ H, Alleged H M x ∧ ¬ Is M x) ∧ ∃ H, Alleged H M y ∧ Is M y :=
  ⟨⟨fun _ _ ↦ True, ⟨x, trivial⟩, hx⟩, ⟨fun _ q ↦ q, ⟨y, hy⟩, hy⟩⟩

/-! ### NOT with Lean's heterogeneous equality -/

section HEq

/-- The operator NOT defined as in (7.11), with `HEq` for JMeq. -/
def HDoesNot {A B : Type} (P : A → Prop) (b : B) : Prop := ∀ x : A, HEq x b → ¬ P x

/-- Law (A1) holds for `HDoesNot`. -/
theorem not_hDoesNot_self_iff {A : Type} {P : A → Prop} {x : A} : ¬ HDoesNot P x ↔ P x := by
  simp only [HDoesNot, not_forall, not_not, exists_prop]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ eq_of_heq hy ▸ hP, fun hP ↦ ⟨x, HEq.rfl, hP⟩⟩

/-- Law (A2) holds for `HDoesNot`. -/
theorem hDoesNot_mono {A B : Type} {P Q : A → Prop} (h : ∀ x, P x → Q x) {y : B}
    (hQ : HDoesNot Q y) : HDoesNot P y :=
  fun x hx hP ↦ hQ x hx (h x hP)

/-- NOT holds vacuously between distinct types, since `HEq` entails type equality. -/
theorem hDoesNot_of_ne {A B : Type} (h : A ≠ B) (P : A → Prop) (b : B) : HDoesNot P b :=
  fun _ hx ↦ (h (type_eq_of_heq hx)).elim

variable {α : Type} [Fintype α] {M : α → Prop} [DecidablePred M]

/-- A proper Σ-subtype of a finite type is a different type. -/
theorem subtype_ne (h : ∃ a, ¬ M a) : {a // M a} ≠ α := fun e ↦ by
  obtain ⟨a, ha⟩ := h
  exact (Fintype.card_subtype_lt ha).ne (Fintype.card_congr (Equiv.cast e))

/-- Law (A3) fails for `HDoesNot` at a proper finite Σ-subtype, such as the men among the humans. -/
theorem not_doesNot_comp_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (P : α → Prop) (C : Type) (z : C),
      HDoesNot P z → HDoesNot (P ∘ Subtype.val : {a // M a} → Prop) z :=
  fun h3 ↦ not_hDoesNot_self_iff.2 trivial
    (h3 (fun _ ↦ True) _ m (hDoesNot_of_ne (subtype_ne h).symm _ m))

/-- Law (A4) fails for `HDoesNot` at a proper finite Σ-subtype. -/
theorem not_forall_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∀ y : α, HDoesNot P y) → ∀ x : {a // M a}, HDoesNot P x :=
  fun h4 ↦ not_hDoesNot_self_iff.2 trivial
    (h4 _ (fun _ ↦ True) (hDoesNot_of_ne (subtype_ne h) _) m)

/-- Law (A5) fails for `HDoesNot` at a proper finite Σ-subtype. -/
theorem not_exists_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∃ x : {a // M a}, HDoesNot P x) → ∃ y : α, HDoesNot P y :=
  fun h5 ↦
    let ⟨_, hy⟩ := h5 α (fun _ ↦ True) ⟨m, hDoesNot_of_ne (subtype_ne h).symm _ m⟩
    not_hDoesNot_self_iff.2 trivial hy

/-- The axiom of [xue-luo-chatzikyriakidis-2018] identifying an object with its image under a
coercion fails for `HEq` at a proper finite Σ-subtype. -/
theorem not_heq_val (h : ∃ a, ¬ M a) (x : {a // M a}) : ¬ HEq x x.1 :=
  fun hx ↦ subtype_ne h (type_eq_of_heq hx)

end HEq

/-! ### Identity criteria and counting -/

section Setoid

/-- A sub-setoid is a subtype whose identity criterion is the restriction of the supertype's
(Definition 5.2). -/
structure SubSetoid (A B : CN Obj) (sA : Setoid A.carrier) (sB : Setoid B.carrier) where
  /-- The coercion from `A` to `B`. -/
  sub : Sub A B
  /-- The identity criterion of `A` is that of `B` restricted along the coercion. -/
  comap_eq : sA = Setoid.comap sub.ι sB

/-- `Three₀ B sB P` holds when three objects of `B`, pairwise distinct under `sB`, satisfy `P`
(Definition 5.3). -/
def Three₀ (B : CN Obj) (sB : Setoid B.carrier) (P : B.carrier → Prop) : Prop :=
  ∃ x y z, ¬ sB x y ∧ ¬ sB y z ∧ ¬ sB x z ∧ P x ∧ P y ∧ P z

/-- If men inherit the identity criterion of humans, three men who talk are three humans who talk
(5.26). -/
theorem three₀_of_subSetoid {sA : Setoid A.carrier} {sB : Setoid B.carrier}
    (h : SubSetoid A B sA sB) (P : B.carrier → Prop) (hA : Three₀ A sA (P ∘ h.sub.ι)) :
    Three₀ B sB P := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩ := hA
  exact ⟨_, _, _, hxy, hyz, hxz, hx, hy, hz⟩

/-- For a predicate respecting the identity criterion, `Three₀` holds exactly when more than two
identity classes satisfy it (p. 110). -/
theorem three₀_iff_two_lt_card (sB : Setoid B.carrier) [Fintype B.carrier] [DecidableRel sB]
    (P : B.carrier → Prop) [DecidablePred P] (hP : ∀ x y, sB x y → (P x ↔ P y)) :
    Three₀ B sB P ↔
      2 < Fintype.card {q : Quotient sB // Quotient.lift P (fun x y h ↦ propext (hP x y h)) q} := by
  rw [Fintype.two_lt_card_iff]
  constructor
  · rintro ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩
    exact ⟨⟨⟦x⟧, hx⟩, ⟨⟦y⟧, hy⟩, ⟨⟦z⟧, hz⟩, fun e ↦ hxy (Quotient.exact (Subtype.mk.inj e)),
      fun e ↦ hxz (Quotient.exact (Subtype.mk.inj e)),
      fun e ↦ hyz (Quotient.exact (Subtype.mk.inj e))⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    induction c using Quotient.inductionOn with | h z => ?_
    exact ⟨x, y, z, fun e ↦ hab (by simp [Quotient.sound e]),
      fun e ↦ hbc (by simp [Quotient.sound e]), fun e ↦ hac (by simp [Quotient.sound e]),
      ha, hb, hc⟩

end Setoid

end ChatzikyriakidisLuo2020
