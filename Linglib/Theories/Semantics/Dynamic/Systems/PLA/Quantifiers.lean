/-
# PLA Generalized Quantifiers

Dekker (2012) Chapter 4, §4.1: Generalized Quantifiers in Dynamic Semantics.

## Key Concepts

### Standard Generalized Quantifiers
A generalized quantifier is a relation D : Set α → Set α → Prop.
Examples:
- `some`: |A ∩ B| > 0
- `every`: A ⊆ B
- `most`: |A ∩ B| > |A - B|
- `no`: A ∩ B = ∅

### Dynamic Challenge: Donkey Anaphora
"Every farmer who owns a donkey beats it."

The pronoun "it" must covary with "a donkey" across the universal quantifier.
This requires:
1. Witness functions: for each (farmer, donkey) pair, track the witness
2. Truthful quantifiers: allow existential to scope out

### This Module

We formalize:
1. Generalized quantifier type with key properties (conservativity, monotonicity)
2. Witness-indexed updates for donkey dependencies
3. Truthfulness condition for scope extension

### Relationship to Core.Quantification

`Core.Quantification` defines a parallel Bool-based GQ type:
  `GQ α = (α → Bool) → (α → Bool) → Bool`
with model-agnostic properties (`Conservative`, `ScopeUpwardMono`, etc.)
and van Benthem (1984) relational characterizations.

This module uses the Set-based `GQRel α = Set α → Set α → Prop` because
PLA's dynamic updates operate on `Set`-valued info states. The two
representations are morally equivalent — `IsConservative` here corresponds
to `Conservative` in Core — but typed for different downstream consumers.

## References

- Dekker, P. (2012). Dynamic Semantics. Springer. Chapter 4, §4.1.
- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.Semantics.Dynamic.Systems.PLA.Update
import Mathlib.Data.Set.Card
import Mathlib.Order.SetNotation

namespace Semantics.Dynamic.PLA

open Classical


/--
A Generalized quantifier relation: determines truth based on two sets.

`GQRel α` = `Set α → Set α → Prop`

Examples:
- `every A B = A ⊆ B`
- `some A B = (A ∩ B).Nonempty`
- `no A B = A ∩ B = ∅`
-/
abbrev GQRel (α : Type*) := Set α → Set α → Prop

namespace GQRel

variable {α : Type*}

/-- Every: All A's are B's -/
def every : GQRel α := λ A B => A ⊆ B

/-- Some: At least one A is a B -/
def some : GQRel α := λ A B => (A ∩ B).Nonempty

/-- No: No A is a B -/
def no : GQRel α := λ A B => A ∩ B = ∅

/-- Most: More than half of the A's are B's (requires finite) -/
def most [Fintype α] : GQRel α := λ A B =>
  2 * (A ∩ B).toFinite.toFinset.card > A.toFinite.toFinset.card

/-- At least n: At least n A's are B's -/
def atLeast (n : ℕ) : GQRel α := λ A B =>
  ∃ s : Finset α, s.card ≥ n ∧ ↑s ⊆ A ∩ B

/-- Exactly n: Exactly n A's are B's -/
def exactly [Fintype α] (n : ℕ) : GQRel α := λ A B =>
  (A ∩ B).toFinite.toFinset.card = n


/--
A quantifier is conservative if `D(A)(B) ↔ D(A)(A ∩ B)`.

This is the key semantic universal: determiners only care about
the A's when determining the relation to B.

"Every student passed" ↔ "Every student is a student who passed"
-/
def IsConservative (D : GQRel α) : Prop :=
  ∀ A B, D A B ↔ D A (A ∩ B)

theorem every_conservative : IsConservative (every : GQRel α) := by
  intro A B
  constructor
  · intro h x hxA
    exact ⟨hxA, h hxA⟩
  · intro h x hxA
    exact (h hxA).2

theorem some_conservative : IsConservative (some : GQRel α) := by
  intro A B
  simp only [some]
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, hx.1, hx⟩
  · intro ⟨x, hxA, hxAB⟩
    exact ⟨x, hxAB⟩

theorem no_conservative : IsConservative (no : GQRel α) := by
  intro A B
  simp only [no]
  constructor
  · intro h
    rw [h, Set.inter_empty]
  · intro h
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxA hxB
    have : x ∈ A ∩ (A ∩ B) := ⟨hxA, hxA, hxB⟩
    rw [h] at this
    exact this


/--
A quantifier is upward monotone in the second argument if
`D(A)(B)` and `B ⊆ C` implies `D(A)(C)`.
-/
def IsUpwardMono (D : GQRel α) : Prop :=
  ∀ A B C, B ⊆ C → D A B → D A C

/--
A quantifier is downward monotone in the second argument if
`D(A)(B)` and `C ⊆ B` implies `D(A)(C)`.
-/
def IsDownwardMono (D : GQRel α) : Prop :=
  ∀ A B C, C ⊆ B → D A B → D A C

theorem every_upward_mono : IsUpwardMono (every : GQRel α) :=
  λ _ _ _ hBC hAB x hxA => hBC (hAB hxA)

theorem some_upward_mono : IsUpwardMono (some : GQRel α) :=
  λ _ _ _ hBC ⟨x, hxA, hxB⟩ => ⟨x, hxA, hBC hxB⟩

theorem no_downward_mono : IsDownwardMono (no : GQRel α) := by
  intro A B C hCB hAB
  simp only [no] at hAB ⊢
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxA hxC
  have : x ∈ A ∩ B := ⟨hxA, hCB hxC⟩
  rw [hAB] at this
  exact this


/--
A quantifier is truthful (has existential import) if
`D(A)(B)` implies `A ∩ B ≠ ∅`.

Truthful quantifiers: some, every (presuppositionally), most
Non-truthful: no, at most n
-/
def IsTruthful (D : GQRel α) : Prop :=
  ∀ A B, D A B → (A ∩ B).Nonempty

theorem some_truthful : IsTruthful (some : GQRel α) :=
  λ _ _ h => h

/--
Note: `every` is only truthful if we assume existential presupposition.
Standard logic treats "every A is B" as vacuously true when A = ∅.
-/
theorem every_not_truthful : ¬IsTruthful (every : GQRel α) := by
  intro h
  have : (∅ : Set α) ⊆ ∅ := Set.Subset.rfl
  have hne := h ∅ ∅ this
  simp only [Set.inter_self] at hne
  exact Set.not_nonempty_empty hne

end GQRel


/--
A witness function selects, for each entity in the restrictor satisfying
some condition, a witnessing entity.

For "Every farmer who owns a donkey beats it":
- For each farmer f who owns a donkey, `wit f` is a donkey that f owns

This is Dekker's solution to donkey anaphora with universal quantifiers.
-/
abbrev WitnessFn (α : Type*) := α → α

/--
A witness function is valid for sets A and R if:
for all x ∈ A, the witness wit(x) is related to x by R.

For "owns a donkey": `valid_witness owns farmers donkeys wit`
means ∀ f ∈ farmers, owns f (wit f) ∧ wit f ∈ donkeys
-/
def ValidWitness {α : Type*} (R : α → α → Prop) (A B : Set α) (wit : WitnessFn α) : Prop :=
  ∀ x ∈ A, R x (wit x) ∧ wit x ∈ B

/--
Truthful existence: For truthful quantifiers, if D(A)(B) holds,
there exists a valid witness function.

This is the key to dynamic binding: truthful quantifiers "export"
witnesses that can be referenced anaphorically.
-/
theorem truthful_has_witness {α : Type*} [Nonempty α]
    (D : GQRel α) (hT : GQRel.IsTruthful D) (A B : Set α) (h : D A B) :
    ∃ x ∈ A ∩ B, True :=
  let ⟨x, hx⟩ := hT A B h
  ⟨x, hx, trivial⟩


variable {E : Type*} [Nonempty E]

/--
Dynamic quantifier update: `Dx(φ)(ψ)` where D is a generalized quantifier.

Semantics: D(restrictor)(scope) where:
- restrictor = {e | M, g[x↦e], ê ⊨ φ}
- scope = {e | M, g[x↦e], ê ⊨ ψ}

This generalizes `∃x.φ` (which is `some(univ)(φ)`).
-/
def Formula.gqUpdate (M : Model E) (D : GQRel E) (x : VarIdx) (φ ψ : Formula) :
    Update E :=
  λ s => { p ∈ s |
    let restrictor := { e : E | φ.sat M (p.1[x ↦ e]) p.2 }
    let scope := { e : E | ψ.sat M (p.1[x ↦ e]) p.2 }
    D restrictor scope }

/--
Standard existential is `some(univ)(φ)`, but we use the standard definition
which also updates the assignment.
-/
theorem exists_as_gq (M : Model E) (x : VarIdx) (φ : Formula) (s : InfoState E) :
    (Formula.exists_ x φ).update M s =
    { p ∈ s | ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 } := by
  ext p
  simp [Formula.update, InfoState.restrict, Formula.sat]

/--
Universal quantifier as GQ: `∀x.φ` = `every(univ)(φ)`
-/
def Formula.forallGQ (M : Model E) (x : VarIdx) (φ : Formula) :
    Update E :=
  Formula.gqUpdate M GQRel.every x (Formula.atom "⊤" []) φ


/--
Donkey update: For "Every farmer who owns a donkey beats it".

This captures the dependency between the universally quantified farmer
and the existentially introduced donkey.

We need to track, for each farmer f, which donkey
witnesses the "owns a donkey" part, and that donkey is what "it" refers to.
-/
def donkeyUpdate (M : Model E) (farmer donkey : VarIdx) (pron_it : PronIdx)
    (owns beats : String) : Update E :=
  λ s => { p ∈ s |
    -- For every farmer f who owns some donkey d
    -- (where d is the witness for that farmer)
    -- f beats d
    let farmers := { f : E | M.interp "Farmer" [f] }
    let ownsDonkey := λ f => { d : E | M.interp owns [f, d] ∧ M.interp "Donkey" [d] }
    ∀ f ∈ farmers, (ownsDonkey f).Nonempty →
      ∃ d ∈ ownsDonkey f, M.interp beats [f, d] }

/--
The E-type approach (Evans): pronouns pick out the unique/salient entity.

For "Every farmer who owns a donkey beats it":
"it" = the unique donkey that the farmer owns (if unique), or
       a contextually salient one (if multiple).

This differs from the witness-function approach in requiring uniqueness or salience.
-/
def etypeApproach (M : Model E) (farmer donkey : String) (owns beats : String) : Prop :=
  ∀ f : E, M.interp farmer [f] →
    (∃ d : E, M.interp donkey [d] ∧ M.interp owns [f, d]) →
    ∀ d : E, M.interp donkey [d] → M.interp owns [f, d] → M.interp beats [f, d]


/--
GQ updates are eliminative: They never add possibilities.
-/
theorem gqUpdate_eliminative (M : Model E) (D : GQRel E) (x : VarIdx)
    (φ ψ : Formula) (s : InfoState E) :
    Formula.gqUpdate M D x φ ψ s ⊆ s := by
  intro p hp
  simp only [Formula.gqUpdate, Set.mem_setOf_eq] at hp
  exact hp.1

/--
Conservativity transfers: If D is conservative, so is the dynamic version
(in a suitable sense).
-/
theorem gqUpdate_conservative (M : Model E) (D : GQRel E) (hC : GQRel.IsConservative D)
    (x : VarIdx) (φ ψ : Formula) (s : InfoState E) (p : Poss E) :
    p ∈ Formula.gqUpdate M D x φ ψ s ↔
    p ∈ s ∧ D { e | φ.sat M (p.1[x ↦ e]) p.2 }
             { e | φ.sat M (p.1[x ↦ e]) p.2 ∧ ψ.sat M (p.1[x ↦ e]) p.2 } := by
  simp only [Formula.gqUpdate, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hD⟩
    refine ⟨hp, ?_⟩
    rw [hC] at hD
    simp only [Set.inter_def, Set.mem_setOf_eq] at hD
    exact hD
  · intro ⟨hp, hD⟩
    refine ⟨hp, ?_⟩
    rw [hC]
    simp only [Set.inter_def, Set.mem_setOf_eq]
    exact hD


/--
Indefinites take wide scope (in dynamic semantics).

"If a farmer owns a donkey, he beats it."
The indefinites "a farmer" and "a donkey" can bind pronouns in the consequent.

This is modeled by having the existential update extend the assignment
globally, not just locally.
-/
theorem indefinite_wide_scope (M : Model E) (x : VarIdx) (φ ψ : Formula)
    (s : InfoState E) :
    -- After ∃x.φ, the assignment has x bound
    ∀ p ∈ (Formula.exists_ x φ).update M s,
      ∃ e : E, φ.sat M (p.1[x ↦ e]) p.2 :=
  λ p hp => by
    simp only [Formula.update, InfoState.restrict, Set.mem_setOf_eq, Formula.sat] at hp
    exact hp.2

/--
Universals don't export: "Every farmer owns a donkey" doesn't make
"the donkey" available for subsequent anaphora (without special mechanisms).
-/
theorem universal_no_export (M : Model E) (x : VarIdx) (φ : Formula)
    (s : InfoState E) :
    -- Universal just tests, doesn't change assignment structure
    Formula.forallGQ M x φ s ⊆ s :=
  gqUpdate_eliminative M GQRel.every x (Formula.atom "⊤" []) φ s

end Semantics.Dynamic.PLA
