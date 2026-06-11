import Mathlib.Logic.Basic
import Mathlib.Order.Basic

/-!
# Chatzikyriakidis & Luo 2017: common nouns as types versus predicates

[chatzikyriakidis-luo-2017] contrast the Montagovian CNs-as-predicates
interpretation ([montague-1973]) with the MTT-semantics CNs-as-types
interpretation ([ranta-1994]), argue that only the latter is compatible with
the subtyping needed for copredication ((5), after [asher-2011]: "John picked
up and mastered three books in the library"), and propose *predicational
forms* of judgemental interpretations: a trivial predicate `p_A` for the
judgement `a : A` (their Definition 1), a negation operator `NOT` with logical
laws (L1)/(L2) for negated sentences like "John is not a man", and `P_A`
(Definition 2) for hypothetical judgements in conditionals. Their §4 checks
the account in Coq; this file replays those experiments in Lean against the
same law set, and adds a concrete witness for the laws (the chapter
axiomatizes `NOT` via Coq `Parameter`/`Variable`s without exhibiting a model).

Their §5 handles gradable nouns with indexed types: `Idiot` is the Σ-type
`Σ i : Idiocy. Human(i) × (i > STND)` (their (62)), and *small idiot* is
deviant because *small* demands a degree below the standard that *idiot*
demands exceeding — formalized here from mathlib's order classes (the
chapter's grade axioms are `LinearOrder` plus `DenselyOrdered`).

## Main declarations

- `CN`, `Sub`: common nouns as types embedded in a top type `Obj`, with
  coercive subtyping
- `p`, `NegOperator`, `NegOperator.bigP`: Definitions 1–2 and the `NOT`
  operator bundled with laws (L1)/(L2)
- `standardNeg`: a witness model for the law set
- `man_and_not_man` … `not_human_not_man`: the chapter's §4 Coq examples
- `no_aspect_map`, `copredication`: the §2.2 copredication argument
- `Idiot`, `small_idiot_contradictory`: the §5 gradable-noun treatment
-/

namespace ChatzikyriakidisLuo2017

universe u

/-- A common noun interpreted as a type ([chatzikyriakidis-luo-2017] §2.2,
"CNs as Types"): a carrier together with its embedding into the top type
`Obj` of the universe `CN`. -/
structure CN (Obj : Type u) where
  /-- The type interpreting the CN -/
  carrier : Type u
  /-- The coercion into the top type `Obj` -/
  embed : carrier → Obj

variable {Obj : Type u}

/-- Coercive subtyping `A ≤ B` between CNs: a coercion commuting with the
embeddings into `Obj` (the chapter's `Man < Human < Animal < Object` chain,
declared as Coq `Coercion` axioms in their Appendix B). -/
structure Sub (A B : CN Obj) where
  /-- The coercion -/
  ι : A.carrier → B.carrier
  /-- The coercion commutes with the embeddings into `Obj` -/
  comm : ∀ a, B.embed (ι a) = A.embed a

/-- **Definition 1** (predicate `p_A`): the predicational form of the
non-hypothetical judgement `a : A` — `p_A(x) = true` for every `x : A`
(Coq: `Definition pr := fun (A : CN) (a : A) => True`). -/
def p (A : CN Obj) : A.carrier → Prop := λ _ => True

/-- The chapter's negation operator `NOT : ΠA : CN. (A → Prop) → (Obj → Prop)`
bundled with its logical laws, stated for the predicational forms `p_A` as in
the chapter:

- **(L1)** for any `A : CN` and `a : A`, `NOT(p_A, ā) ⟺ ¬ p_A(a)`;
- **(L2)** if `A ≤ B` then `NOT(p_B, c) ⟹ NOT(p_A, c)` for any `c`.

The chapter introduces `NOT` axiomatically (Coq `Parameter` plus per-type
`Variable` instances of the laws, Appendix B); bundling laws into a structure
plays the same role here. -/
structure NegOperator (Obj : Type u) where
  /-- The negation operator -/
  not : (A : CN Obj) → (A.carrier → Prop) → Obj → Prop
  /-- Law (L1) -/
  l1 : ∀ (A : CN Obj) (a : A.carrier), not A (p A) (A.embed a) ↔ ¬ p A a
  /-- Law (L2) -/
  l2 : ∀ {A B : CN Obj}, Sub A B → ∀ c : Obj, not B (p B) c → not A (p A) c

/-- **Definition 2** (predicate `P_A`): the predicational form of a
hypothetical judgement — `P_A(x) = ¬ NOT(p_A, x̄)`, used to interpret
conditionals like "If John is a student, he is happy" as
`P_Student(j) ⟹ happy(j)` (their (22)). -/
def NegOperator.bigP (N : NegOperator Obj) (A : CN Obj) (o : Obj) : Prop :=
  ¬ N.not A (p A) o

/-- A concrete witness for the law set (ours — the chapter never exhibits a
model): `NOT(A, P, o)` holds when no `A`-element located at `o` satisfies
`P`. Shows (L1)/(L2) are jointly satisfiable. -/
def standardNeg (Obj : Type u) : NegOperator Obj where
  not A P o := ∀ a, A.embed a = o → ¬ P a
  l1 _ a := iff_of_false (λ h => h a rfl trivial) (λ h => h trivial)
  l2 s _ hB a ha _ := hB (s.ι a) ((s.comm a).trans ha) trivial

/-! ### The §4 Coq experiments, replayed

Each theorem is one of the chapter's worked Coq examples, proved from the
bundled laws exactly as the chapter proves it from its `Variable`s. -/

section Examples
variable (N : NegOperator Obj) (Man Human Linguist Logician Table : CN Obj)

/-- **Example 1** ((25)–(27)): "John is a man and John is not a man" is
contradictory, by (L1). -/
theorem man_and_not_man (j : Man.carrier) :
    ¬ (p Man j ∧ N.not Man (p Man) (Man.embed j)) :=
  λ ⟨_, hn⟩ => (N.l1 Man j).mp hn trivial

/-- **Example 4** ((34)–(36)): "It is not the case that John is not a man",
for John a man. The chapter's Coq proof assumes a classical-negation axiom;
(L1) already yields it constructively. -/
theorem not_not_man (j : Man.carrier) :
    ¬ N.not Man (p Man) (Man.embed j) :=
  λ h => (N.l1 Man j).mp h trivial

/-- **Example 3** ((31)–(33), theorem `TABLE`): "Tables do not talk" entails
"Red tables do not talk". A red table is the Σ-type
`{rt :> Table; _ : Red rt}` with the first projection as coercion; the
entailment is pure coercion transport, no `NOT`-laws needed (matching the
chapter's `unfold`/`intros`/`apply` proof). `talk` lives on `Human`, as in
their Appendix B. -/
theorem tables_dont_talk_red (Red : Obj → Prop) (talk : Human.carrier → Prop)
    (h : ∀ x : Table.carrier, N.not Human talk (Table.embed x)) :
    ∀ y : {x : Table.carrier // Red (Table.embed x)},
      N.not Human talk (Table.embed y.1) :=
  λ y => h y.1

/-- **Example 8** ((47)–(49), theorem `NOTLL`): "It is not the case that
every linguist is a logician" entails "some linguist is not a logician"
(classical, as in the chapter). -/
theorem notll
    (h : ¬ ∀ l : Linguist.carrier, N.bigP Logician (Linguist.embed l)) :
    ∃ l : Linguist.carrier, N.not Logician (p Logician) (Linguist.embed l) := by
  obtain ⟨l, hl⟩ := not_forall.mp h
  exact ⟨l, not_not.mp hl⟩

/-- **Example 9** ((50)–(52), theorem `NOTHL`): "not every linguist is a
logician" entails "not every human is a logician", via `Linguist ≤ Human`. -/
theorem nothl (s : Sub Linguist Human)
    (h : ¬ ∀ l : Linguist.carrier, N.bigP Logician (Linguist.embed l)) :
    ¬ ∀ x : Human.carrier, N.bigP Logician (Human.embed x) :=
  λ hall => h (λ l => s.comm l ▸ hall (s.ι l))

/-- **Example 10** ((53)–(55), theorem `NOTHUMANMAN`): "If John is not a
human, then John is not a man" — law (L2) at `Man ≤ Human`. -/
theorem not_human_not_man (s : Sub Man Human) (c : Obj)
    (h : N.not Human (p Human) c) : N.not Man (p Man) c :=
  N.l2 s c h

/-- Appendix A's warm-up (theorem `EX`): "John walks" entails "some man
walks", with the chapter's quantifier `some A P := ∃ x : A, P x`. -/
theorem some_man_walks (s : Sub Man Human) (walk : Human.carrier → Prop)
    (j : Man.carrier) (h : walk (s.ι j)) :
    ∃ x : Man.carrier, walk (s.ι x) :=
  ⟨j, h⟩

end Examples

/-! ### §2.2: copredication needs CNs-as-types

The chapter's argument that CNs-as-predicates is incompatible with the
subtyping required for copredication: interpreting `heavy` at
`(Phy → t) → (Phy → t)` and `book` as a predicate over the dot type
`Phy • Info` would require `Phy ≤ Phy • Info` by contravariance — "in the
wrong direction (just the other way around!)". With CNs as types the problem
disappears: `Book ≤ Phy • Info` and both conjuncts of (5) type-check via the
projections. -/

section Copredication
variable {Phy Info Book : Type*}

/-- No map `Phy → Phy × Info` exists in general — "intuitively, not every
physical object has an informational aspect" (§2.2). This is the
contravariance direction the predicates approach would need. -/
theorem no_aspect_map (hp : Nonempty Phy) (hi : IsEmpty Info) :
    IsEmpty (Phy → Phy × Info) :=
  ⟨λ f => hp.elim (λ x => hi.false (f x).2)⟩

/-- Copredication ((5): "picked up and mastered three books") with CNs as
types: `Book ≤ Phy • Info` gives both aspect coercions, so
`pick up : Phy → Prop` and `master : Info → Prop` both apply to a book and
the coordination is typable —
`pick up, master : Book → Prop` by composition (§2.2's displayed subtyping
chains). -/
def copredication (toPhy : Book → Phy) (toInfo : Book → Info)
    (pickUp : Phy → Prop) (master : Info → Prop) (b : Book) : Prop :=
  pickUp (toPhy b) ∧ master (toInfo b)

end Copredication

/-! ### §5: gradable nouns via indexed types

CNs may be families indexed by grades (their (58): `Human : Height → CN`).
The chapter's grade axioms — reflexivity, anti-symmetry, transitivity,
totality, density — are mathlib's `LinearOrder` plus `DenselyOrdered`. -/

section Grades
variable {Idiocy : Type*} [LinearOrder Idiocy]

/-- **(62)**: `Idiot = Σ i : Idiocy. Human(i) × (i > STND)` — a triple of an
idiocy degree, a human indexed at that degree, and a proof the degree exceeds
the idiocy standard. Nouns like *idiot* "involve a degree parameter" yet "are
however not predicates but rather Σ types" — the chapter's explanation of why
adnominal degree modification differs from adjectival gradability. -/
structure Idiot (Human : Idiocy → Type*) (STND : Idiocy) where
  /-- The idiocy degree -/
  degree : Idiocy
  /-- The human indexed at that degree -/
  human : Human degree
  /-- The degree exceeds the idiocy standard -/
  above : STND < degree

/-- *Small idiot* is contradictory: *idiot* requires a degree above the
standard, *small* one below it — "one would end up with contradictory
statements like `i > STND_id ∧ i < STND_id`" (the chapter's
Constantinescu-style account of the deviance, against Morzycki's bigness
generalization). -/
theorem small_idiot_contradictory (STND : Idiocy) :
    ¬ ∃ i : Idiocy, STND < i ∧ i < STND :=
  λ ⟨_, h1, h2⟩ => lt_asymm h1 h2

end Grades

end ChatzikyriakidisLuo2017
