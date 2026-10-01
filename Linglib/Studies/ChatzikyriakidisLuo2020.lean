module

public import Linglib.Studies.ChatzikyriakidisLuo2017
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Data.Setoid.Basic

/-!
# Chatzikyriakidis & Luo 2020: formal semantics in modern type theories

[chatzikyriakidis-luo-2020] develop MTT-semantics. Common nouns are interpreted as types in a
universe `CN`, adjectives and verbs as predicates over them, and subtyping is coercive: `A ≤c B`
when an implicit coercion `c : A → B` may be inserted wherever a `B` is expected (§2.4). A CN
modified by a predicate is the Σ-type of the objects satisfying it, a subtype of the CN through
the first projection (projective subtyping, (2.41)–(2.42), (3.33)).

This file formalizes four parts of the book over the CN universe of
[chatzikyriakidis-luo-2017], whose CNs are types embedded in a carrier `Obj`:

* **Coercive subtyping** (§2.4, §3.2.2): Σ-modification with its projection coercion, the
  coherence requirement (p. 40 fn 18), and proof irrelevance for Σ-types (p. 69).
* **Adjectival modification** (§3.3, Table 3.2). Intersective adjectives are Σ-types over one
  predicate; they propagate along subtyping ((3.91)) and land in [kamp-1975]'s intersective
  class. Subsective adjectives are Π-polymorphic predicates, Kamp-subsective in the subtyping
  order, which need not propagate ((3.101)). Privatives live over a disjoint union of real and
  fake guns ((3.110)–(3.121)), subsective in the type of all guns, following [partee-2010].
  Non-committal adjectives work through a modal collection ((3.125)–(3.127)).
* **Propositional forms of judgements** (§3.2.3, §7.1): the operator NOT, its derived operators
  IS and DO, the laws (A1)–(A5), and type disjointness (Definition 7.1).
* **Identity criteria** (§5.3.1–5.3.2): CNs as setoids, sub-setoids (Definition 5.2), and
  counting under an identity criterion (Definition 5.3, (5.26)).

## Main definitions

* `sigma`, `sigmaFst` — the Σ-type `Σx:A. P(x)` and its first projection as a coercion
* `DoesNot`, `Is`, `Does` — NOT (7.5), IS (7.7) and DO (7.9)
* `TypeDisjoint` — Definition 7.1
* `Alleged` — non-committal modification through a modal collection (3.125)
* `SubSetoid`, `Three₀` — Definitions 5.2 and 5.3

## Main results

* `subsingleton_sub`, `sigma_embed_injective` — coherence and proof irrelevance
* `sigmaMap`, `range_sigma_comp` — intersective modification propagates along subtyping and is
  Kamp-intersective; `isSubsective_sigma`, `not_forall_nonempty_sub_sigma` — subsective
  modification is Kamp-subsective and need not propagate
* `forall_does_iff_injective`, `doesNot_mono`, `doesNot_comp`, `forall_doesNot_of_sub`,
  `exists_doesNot_of_sub` — laws (A1)–(A5) for NOT
* `not_doesNot_comp_heq`, `not_forall_doesNot_of_sub_heq`, `not_exists_doesNot_of_sub_heq`,
  `not_heq_val` — Theorem 7.1 fails for a heterogeneous equality that entails type equality
* `typeDisjoint_iff`, `isEmpty_sub_of_typeDisjoint` — disjointness makes IS false across a pair
  of CNs and rules out coercions between them
* `three₀_of_subSetoid`, `three₀_iff_two_lt_card` — (5.26), and counting on the quotient

## Implementation notes

The book's CN universe has no top type. The carrier `Obj` of [chatzikyriakidis-luo-2017] serves
here only to realize the heterogeneous equality JMeq that the book uses to justify NOT (7.11):
two objects of different CNs are equal when their images in `Obj` are. This equality is
reflexive. It satisfies JMeq's homogeneous elimination on a CN exactly when the CN's embedding is
injective, and it identifies `x` with `c x` along every coercion, which is the extra axiom that
[xue-luo-chatzikyriakidis-2018] (§4.2) add to prove (A3)–(A5). Coercions are explicit `Sub`
values rather than Lean `Coe` instances, so that theorems quantify over the CN universe. The
coercive application and definition rules (CA)/(CD) (p. 40) are then function application.

Intersective adjectives take their argument in `Obj`; the book types *black* over a CN `Object`
with `Cat ≤ Object` ((3.88)–(3.90)). Proof irrelevance, which the book must enforce for Σ-types to
count correctly (p. 69), is definitional for Lean's `Prop`. Lean's propositional extensionality
makes every modal collection `Prop → Prop` respect logical equivalence, the property for which
the book rejects [ranta-1994]'s belief contexts (p. 73 fn 23); the encoding of (3.127) inherits
it. A setoid CN is a `CN` with a `Setoid` on its carrier.

## Finding: Theorem 7.1 as stated

Theorem 7.1 (p. 156) claims that, with NOT defined from JMeq as in (7.11), (A1)–(A5) "are all
provable in the type theory extended by JMeq". Lean's `HEq` validates JMeq's reflexivity and
homogeneous elimination (`HEq.rfl`, `eq_of_heq`), and (A1) and (A2) hold for it. But `HEq`
entails type equality, so NOT across two distinct types holds vacuously. As a result (A3), (A4)
and (A5) all fail at every proper finite Σ-subtype, such as the book's `Man ≤π₁ Human` once some
human is not male. The proof the book cites, [xue-luo-chatzikyriakidis-2018] §4.2 and its Coq
appendix, adds the axiom `∀ x : A, JMeq(A, x, B, c(x))` for injective coercions `c`. That axiom
fails at the same subtypes for any heterogeneous equality entailing type equality (`not_heq_val`;
Coq's inductive `JMeq`, which that appendix imports, is one). The appendix states the axiom over
abstract `Variables A B`, where `A = B` cannot be refuted. With JMeq read as equality in a common
carrier, all five laws hold, (A1) exactly on injectively embedded CNs.

## TODO

* Chapter 4: gradable adjectives and nouns (the latter as in
  `ChatzikyriakidisLuo2017.Idiot`), multidimensional adjectives, adverbial modification.
* §5.2, §5.3.3: dot-types for copredication, and counting under copredication (Definition 5.4
  and its third case, Definitions 5.5–5.6).
* §7.1 Definition 7.2 (negative occurrences) needs a deep embedding of formulae; §7.2 dependent
  event types; §3.2.2 homonymy and parameterized coercions ((3.34)–(3.53)).
* A top-free universe: a directed preorder of CNs with injective coercions, with JMeq read as
  equality at a common upper bound.

## References

* [chatzikyriakidis-luo-2020]
* [chatzikyriakidis-luo-2017]
* [xue-luo-chatzikyriakidis-2018]
* [kamp-1975]
* [partee-2010]
* [ranta-1994]
-/

@[expose] public section

namespace ChatzikyriakidisLuo2020

open ChatzikyriakidisLuo2017

universe u

variable {Obj : Type u}

/-! ### Σ-types and coercive subtyping (§2.4, §3.2.2) -/

/-- The Σ-type `Σx:A. P(x)` as a common noun ((2.41), (3.21)): the objects of `A` satisfying
`P`, located in `Obj` through `A`. -/
def sigma (A : CN Obj) (P : A.carrier → Prop) : CN Obj where
  carrier := {x // P x}
  embed x := A.embed x

/-- Projective subtyping `Σx:A. P(x) ≤π₁ A` ((2.42), (3.33)): every modified CN is a subtype of
the CN it modifies. -/
def sigmaFst (A : CN Obj) (P : A.carrier → Prop) : Sub (sigma A P) A :=
  ⟨Subtype.val, fun _ ↦ rfl⟩

/-- Proof irrelevance (p. 69): two objects of `Σx:A. P(x)` are equal when their first
projections are, so two black cats are the same just if they are the same cats. -/
theorem sigma_embed_injective {A : CN Obj} (hA : Function.Injective A.embed)
    (P : A.carrier → Prop) : Function.Injective (sigma A P).embed :=
  hA.comp Subtype.val_injective

/-- Subtyping between CNs: `A ≤ B` when a coercion from `A` to `B` exists. -/
scoped instance : Preorder (CN Obj) where
  le A B := Nonempty (Sub A B)
  le_refl _ := ⟨⟨id, fun _ ↦ rfl⟩⟩
  le_trans _ _ _ := fun ⟨s⟩ ⟨t⟩ ↦ ⟨⟨t.ι ∘ s.ι, fun a ↦ (t.comm _).trans (s.comm a)⟩⟩

variable {A B C : CN Obj}

/-- Coherence (p. 40 fn 18): between CNs embedded injectively there is at most one coercion. -/
theorem subsingleton_sub (hB : Function.Injective B.embed) : Subsingleton (Sub A B) :=
  ⟨fun ⟨ι, hι⟩ ⟨κ, hκ⟩ ↦ by
    obtain rfl : ι = κ := funext fun a ↦ hB ((hι a).trans (hκ a).symm)
    rfl⟩

/-- A coercion out of an injectively embedded CN is injective, so the condition `A ≼ B` that
(A3)–(A5) impose (p. 153) holds of every coercion of the model. -/
theorem sub_injective (hA : Function.Injective A.embed) (s : Sub A B) :
    Function.Injective s.ι :=
  fun x y h ↦ hA ((s.comm x).symm.trans ((congrArg B.embed h).trans (s.comm y)))

/-! ### Adjectival modification (§3.3, Table 3.2) -/

/-- `Adj[N] ⇒ N` ((3.94), (3.105)): Σ-modification by any CN-polymorphic adjective is
[kamp-1975]-subsective in the subtyping order. -/
theorem isSubsective_sigma (adj : (A : CN Obj) → A.carrier → Prop) :
    Modifier.isSubsective fun A ↦ sigma A (adj A) :=
  fun A ↦ ⟨sigmaFst A (adj A)⟩

/-- Intersective modification propagates along subtyping (3.91): if `A ≤ B` then
`Σx:A. adj(x) ≤ Σx:B. adj(x)`, so a black cat is a black object. -/
def sigmaMap (s : Sub A B) (adj : Obj → Prop) :
    Sub (sigma A (adj ∘ A.embed)) (sigma B (adj ∘ B.embed)) where
  ι x := ⟨s.ι x.1, by simpa only [Function.comp_apply, s.comm] using x.2⟩
  comm x := s.comm x.1

/-- The objects of `Σx:A. adj(x)` are those of `A` satisfying `adj`. Intersective modification is
[kamp-1975]'s intersective class at the extensions, giving both inferences of `Adj[N] ⇒ N & Adj`
((3.92)–(3.97)). -/
theorem range_sigma_comp (A : CN Obj) (adj : Obj → Prop) :
    Set.range (sigma A (adj ∘ A.embed)).embed =
      Modifier.intersective {o | adj o} (Set.range A.embed) := by
  ext o
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨ha, a, rfl⟩
  · rintro ⟨ho, a, rfl⟩
    exact ⟨⟨a, ho⟩, rfl⟩

/-- Subsective adjectives are Π-polymorphic over `CN` (3.102), so `small(Elephant)` and
`small(Animal)` are unrelated predicates and `Elephant ≤ Animal` does not yield
`small elephant ≤ small animal` (3.101). -/
theorem not_forall_nonempty_sub_sigma :
    ¬ ∀ (A B : CN Bool) (_ : Sub A B) (adj : (C : CN Bool) → C.carrier → Prop),
      Nonempty (Sub (sigma A (adj A)) (sigma B (adj B))) := fun h ↦ by
  obtain ⟨s⟩ := h ⟨PUnit, fun _ ↦ true⟩ ⟨Bool, id⟩ ⟨fun _ ↦ true, fun _ ↦ rfl⟩
    (fun C _ ↦ Subsingleton C.carrier)
  exact Bool.noConfusion ((s.ι ⟨PUnit.unit, inferInstance⟩).2.elim true false)

section Privative

/-- The disjoint union `A + B` of two CNs; the type of guns is `G = G_R + G_F` (3.110). -/
def sum (A B : CN Obj) : CN Obj := ⟨A.carrier ⊕ B.carrier, Sum.elim A.embed B.embed⟩

variable {GR GF : CN Obj}

/-- `real_g` (3.111): true of the real guns. -/
def IsReal : (sum GR GF).carrier → Prop := Sum.elim (fun _ ↦ True) (fun _ ↦ False)

/-- `fake_g` (3.112): true of the fake guns. -/
def IsFake : (sum GR GF).carrier → Prop := Sum.elim (fun _ ↦ False) (fun _ ↦ True)

/-- (3.120): every gun is real or fake. -/
theorem isReal_or_isFake (g : (sum GR GF).carrier) : IsReal g ∨ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

/-- A gun is real just if it is not fake (p. 71). -/
theorem isReal_iff_not_isFake (g : (sum GR GF).carrier) : IsReal g ↔ ¬ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

/-- (3.121): a fake gun, coerced to a gun by the first projection, is not real. -/
theorem not_isReal_sigmaFst (f : (sigma (sum GR GF) IsFake).carrier) :
    ¬ IsReal ((sigmaFst (sum GR GF) IsFake).ι f) :=
  (isReal_iff_not_isFake f.1).1.mt (not_not_intro f.2)

/-- Fake guns and real guns have disjoint extensions, so *fake* is privative relative to *real
gun*, while both are guns by `sigmaFst`: privatives "are in fact subsective" (p. 72). This holds
provided no object is both a real and a fake gun. -/
theorem disjoint_range_isFake (h : Function.Injective (sum GR GF).embed) :
    Disjoint (Set.range (sigma (sum GR GF) IsFake).embed)
      (Set.range (sigma (sum GR GF) IsReal).embed) := by
  rw [Set.disjoint_left]
  rintro _ ⟨f, rfl⟩ ⟨r, hr⟩
  exact (isReal_iff_not_isFake f.1).1 (h hr ▸ r.2) f.2

end Privative

/-! ### Propositional forms of judgements (§3.2.3, §7.1) -/

/-- `NOT(A, P, B, b)`, "`b` does not `P`" (7.5), defined from heterogeneous equality as in
(7.11), with two objects equal when their images in `Obj` are. -/
def DoesNot (A : CN Obj) (P : A.carrier → Prop) (B : CN Obj) (b : B.carrier) : Prop :=
  ∀ x, A.embed x = B.embed b → ¬ P x

/-- `IS_B(X, y)` (7.7): `y` is an `X`, the propositional form of the judgement `y : X`. -/
def Is (X : CN Obj) (y : B.carrier) : Prop := ¬ DoesNot X (p X) B y

/-- `DO_{A,B}(P, y)` (7.9): `y` does `P`, the propositional form of the application `P(y)`. -/
def Does (P : A.carrier → Prop) (y : B.carrier) : Prop := ¬ DoesNot A P B y

theorem does_iff {P : A.carrier → Prop} {y : B.carrier} :
    Does P y ↔ ∃ x, A.embed x = B.embed y ∧ P x := by
  simp [Does, DoesNot]

theorem is_iff {y : B.carrier} : Is A y ↔ ∃ x, A.embed x = B.embed y := by
  simp [Is, DoesNot, p]

/-- `IS(A, a)` holds for every `a : A`; it is equivalent to `p_A(a)` when `a : A` is derivable
(p. 64). -/
theorem is_self (a : A.carrier) : Is A a := is_iff.2 ⟨a, rfl⟩

/-- **(A1)** in the form (Ad1), `DO_{A,A}(P, x) ⇔ P(x)` (p. 154), holds on `A` exactly when `A`
embeds injectively. -/
theorem forall_does_iff_injective :
    (∀ (P : A.carrier → Prop) x, Does P x ↔ P x) ↔ Function.Injective A.embed := by
  refine ⟨fun h x y hxy ↦ (h (· = y) x).1 (does_iff.2 ⟨y, hxy.symm, rfl⟩), fun hA P x ↦ ?_⟩
  rw [does_iff]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ hA hy ▸ hP, fun hP ↦ ⟨x, rfl, hP⟩⟩

/-- **(A2)**: if `P` implies `Q`, then not doing `Q` implies not doing `P`. -/
theorem doesNot_mono {P Q : A.carrier → Prop} (h : ∀ x, P x → Q x) (y : B.carrier)
    (hQ : DoesNot A Q B y) : DoesNot A P B y :=
  fun x hx hP ↦ hQ x hx (h x hP)

/-- **(A3)**: along a coercion `A ≤ B`, not doing `P` as a `B` implies not doing it as an `A`. -/
theorem doesNot_comp (s : Sub A B) (P : B.carrier → Prop) (z : C.carrier)
    (h : DoesNot B P C z) : DoesNot A (P ∘ s.ι) C z :=
  fun x hx ↦ h (s.ι x) ((s.comm x).trans hx)

/-- **(A4)**: what no `B` does, no `A` does. -/
theorem forall_doesNot_of_sub (s : Sub A B) (P : C.carrier → Prop)
    (h : ∀ y, DoesNot C P B y) (x : A.carrier) : DoesNot C P A x :=
  fun w hw ↦ h (s.ι x) w (hw.trans (s.comm x).symm)

/-- **(A5)**: what some `A` does not do, some `B` does not do. -/
theorem exists_doesNot_of_sub (s : Sub A B) (P : C.carrier → Prop)
    (h : ∃ x, DoesNot C P A x) : ∃ y, DoesNot C P B y :=
  let ⟨x, hx⟩ := h
  ⟨s.ι x, fun w hw ↦ hx w (hw.trans (s.comm x))⟩

/-- Example (3) of §7.1 (p. 154): if Teddy is a man, Teddy is a human, for `Man ≤ Human` and
Teddy a toy. -/
theorem is_of_sub (s : Sub A B) {z : C.carrier} (h : Is A z) : Is B z :=
  fun hB ↦ h (doesNot_comp s (p B) z hB)

/-- [chatzikyriakidis-luo-2017]'s `NOT(A, P, o)` is `NOT(A, P, Obj, o)`: that chapter's witness
`standardNeg` is this model with the object read off at its image in `Obj`. -/
theorem standardNeg_not_iff (P : A.carrier → Prop) (b : B.carrier) :
    (standardNeg Obj).not A P (B.embed b) ↔ DoesNot A P B b :=
  Iff.rfl

/-- Type disjointness (Definition 7.1, p. 156): no non-empty CN is a subtype of both. -/
def TypeDisjoint (A B : CN Obj) : Prop :=
  ∀ C : CN Obj, Sub C A → Sub C B → IsEmpty C.carrier

/-- `A` and `B` are disjoint exactly when no `B` is an `A`, the condition under which "John is
not a table" ((3.66), (3.71)) is true of every man. -/
theorem typeDisjoint_iff : TypeDisjoint A B ↔ ∀ b : B.carrier, ¬ Is A b := by
  refine ⟨fun h b hb ↦ ?_, fun h C s t ↦ ⟨fun c ↦ h (t.ι c) (is_iff.2 ⟨s.ι c, ?_⟩)⟩⟩
  · obtain ⟨a, ha⟩ := is_iff.1 hb
    exact (h ⟨PUnit, fun _ ↦ B.embed b⟩ ⟨fun _ ↦ a, fun _ ↦ ha⟩ ⟨fun _ ↦ b, fun _ ↦ rfl⟩).false
      PUnit.unit
  · exact (s.comm c).trans (t.comm c).symm

/-- Selectional restriction by typing ((3.5)–(3.7)): no coercion leads from an inhabited CN to
one disjoint from it, so `talk(t)` with `talk : Human → Prop` and `t : Table` is ill-typed. -/
theorem isEmpty_sub_of_typeDisjoint (h : TypeDisjoint A B) [Nonempty A.carrier] :
    IsEmpty (Sub A B) :=
  ⟨fun s ↦ (h A ⟨id, fun _ ↦ rfl⟩ s).false (Classical.arbitrary _)⟩

/-- Non-committal modification ((3.125)–(3.127)): `x` is an alleged `M` when some human `h` has
`IS(M, x)` in their modal collection `H h` of allegations. -/
def Alleged {Hum : CN Obj} (H : Hum.carrier → Prop → Prop) (M : CN Obj) (x : Hum.carrier) :
    Prop :=
  ∃ h, H h (Is M x)

/-- (3.122): an alleged `M` may not be an `M`, and an `M` may be alleged; the modal collection
licenses neither inference. -/
theorem alleged_noncommittal {Hum M : CN Obj} {x y : Hum.carrier} (hx : ¬ Is M x) (hy : Is M y) :
    (∃ H, Alleged H M x ∧ ¬ Is M x) ∧ ∃ H, Alleged H M y ∧ Is M y :=
  ⟨⟨fun _ _ ↦ True, ⟨x, trivial⟩, hx⟩, ⟨fun _ q ↦ q, ⟨y, hy⟩, hy⟩⟩

/-! ### Theorem 7.1 with Lean's heterogeneous equality -/

section HEq

/-- (7.11) with Lean's `HEq` as JMeq. -/
def HDoesNot {A B : Type} (P : A → Prop) (b : B) : Prop := ∀ x : A, HEq x b → ¬ P x

/-- (A1) holds for `HDoesNot`. -/
theorem not_hDoesNot_self_iff {A : Type} {P : A → Prop} {x : A} : ¬ HDoesNot P x ↔ P x := by
  simp only [HDoesNot, not_forall, not_not, exists_prop]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ eq_of_heq hy ▸ hP, fun hP ↦ ⟨x, HEq.rfl, hP⟩⟩

/-- (A2) holds for `HDoesNot`. -/
theorem hDoesNot_mono {A B : Type} {P Q : A → Prop} (h : ∀ x, P x → Q x) {y : B}
    (hQ : HDoesNot Q y) : HDoesNot P y :=
  fun x hx hP ↦ hQ x hx (h x hP)

/-- `HEq` entails type equality, so NOT across two distinct types holds vacuously. -/
theorem hDoesNot_of_ne {A B : Type} (h : A ≠ B) (P : A → Prop) (b : B) : HDoesNot P b :=
  fun _ hx ↦ (h (type_eq_of_heq hx)).elim

variable {α : Type} [Fintype α] {M : α → Prop} [DecidablePred M]

/-- A proper Σ-subtype of a finite type, such as `Man = Σx:Human. male(x)` when some human is
not male, is a different type. -/
theorem subtype_ne (h : ∃ a, ¬ M a) : {a // M a} ≠ α := fun e ↦ by
  obtain ⟨a, ha⟩ := h
  exact (Fintype.card_subtype_lt ha).ne (Fintype.card_congr (Equiv.cast e))

/-- (A3) fails for `HDoesNot` at `Σx:α. M(x) ≤π₁ α`: no human is `HEq` to a man, so a man does
not do `True` as a human, yet he does as a man. -/
theorem not_doesNot_comp_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (P : α → Prop) (C : Type) (z : C),
      HDoesNot P z → HDoesNot (P ∘ Subtype.val : {a // M a} → Prop) z :=
  fun h3 ↦ not_hDoesNot_self_iff.2 trivial
    (h3 (fun _ ↦ True) _ m (hDoesNot_of_ne (subtype_ne h).symm _ m))

/-- (A4) fails for `HDoesNot` at `Σx:α. M(x) ≤π₁ α`. -/
theorem not_forall_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∀ y : α, HDoesNot P y) → ∀ x : {a // M a}, HDoesNot P x :=
  fun h4 ↦ not_hDoesNot_self_iff.2 trivial
    (h4 _ (fun _ ↦ True) (hDoesNot_of_ne (subtype_ne h) _) m)

/-- (A5) fails for `HDoesNot` at `Σx:α. M(x) ≤π₁ α`. -/
theorem not_exists_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∃ x : {a // M a}, HDoesNot P x) → ∃ y : α, HDoesNot P y :=
  fun h5 ↦
    let ⟨_, hy⟩ := h5 α (fun _ ↦ True) ⟨m, hDoesNot_of_ne (subtype_ne h).symm _ m⟩
    not_hDoesNot_self_iff.2 trivial hy

/-- [xue-luo-chatzikyriakidis-2018]'s axiom `∀ x : A, JMeq(A, x, B, c(x))` fails for `HEq` at
`Σx:α. M(x) ≤π₁ α`. -/
theorem not_heq_val (h : ∃ a, ¬ M a) (x : {a // M a}) : ¬ HEq x x.1 :=
  fun hx ↦ subtype_ne h (type_eq_of_heq hx)

end HEq

/-! ### Identity criteria and counting (§5.3.1–5.3.2) -/

section Setoid

/-- A sub-setoid `(A, =_A) ⊑ (B, =_B)` (Definition 5.2, p. 111): `A ≤ B`, and the identity
criterion of `A` is that of `B` restricted to `A` ((5.25)). -/
structure SubSetoid (A B : CN Obj) (sA : Setoid A.carrier) (sB : Setoid B.carrier) where
  /-- The coercion `A ≤ B` -/
  sub : Sub A B
  /-- `(=_A) = (=_B)|_A` -/
  comap_eq : sA = Setoid.comap sub.ι sB

/-- `Three₀(B, P)` (Definition 5.3, (5.27)): three objects of `B`, pairwise distinct under its
identity criterion, satisfy `P`. -/
def Three₀ (B : CN Obj) (sB : Setoid B.carrier) (P : B.carrier → Prop) : Prop :=
  ∃ x y z, ¬ sB x y ∧ ¬ sB y z ∧ ¬ sB x z ∧ P x ∧ P y ∧ P z

/-- (5.26): "three men talk" entails "three humans talk" when men inherit the identity criterion
of humans. -/
theorem three₀_of_subSetoid {sA : Setoid A.carrier} {sB : Setoid B.carrier}
    (h : SubSetoid A B sA sB) (P : B.carrier → Prop) (hA : Three₀ A sA (P ∘ h.sub.ι)) :
    Three₀ B sB P := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩ := hA
  exact ⟨_, _, _, hxy, hyz, hxz, hx, hy, hz⟩

/-- Counting under an identity criterion is counting on the quotient: `Three₀(B, P)` holds
exactly when more than two identity classes satisfy an identity-respecting `P` (p. 110 fn 7). -/
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
