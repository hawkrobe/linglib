module

public import Linglib.Semantics.Quantification.Exceptive
public import Linglib.Data.Examples.VonFintel1993
public import Mathlib.Tactic.FinCases

/-!
# von Fintel (1993): Exceptive Constructions

This file formalizes [von-fintel-1993]'s compositional semantics of the English *but*-phrase and
of the free exceptive *except for*. Domain subtraction alone, *students but John* as the students
minus John (11), neither explains why *but* occurs only with the universal determiners *every*
and *no* (10) nor blocks the inference from *every student but John* to *every student but John
and Jill* that the left downward monotonicity of the universal determiners licenses (14).
Adding restrictiveness, that the quantification fails without the subtraction (17), excludes the
left-upward-monotone determiners but not *most*, and still licenses the inference. The
*but*-phrase names the set of exceptions, the least set whose subtraction makes the
quantification true (20), `Exceptive.ExcLeast`, in three equivalent formulations (21). With
*every* the exception set is the restrictor minus the scope and with *no* their intersection
(23), so *every student but John* says that John is the only student who did not attend; the
exception set is unique, which blocks the inference (24) and the conjunction of two
*but*-phrases (28); and the co-occurrence restriction is a grammaticization of the fact that the
universal determiners alone guarantee a least exception set for every restrictor and scope
(`GuaranteesException`), whereas *some* never has one and *most* has none in the five-student
situation (25), though it has one in a two-student limiting case. Free exceptives carry
subtraction with restrictiveness only (38), `Exceptive.ExcRestrictive`, which is why they occur
with *most* (34c), and with a universal determiner the *but* reading is their pragmatic
strengthening to the exception set that contains only exceptions.

## Implementation notes

The exception set, the restrictor and the scope are predicates on the domain, sets in the
paper, and the least set is `IsLeast` in the pointwise order on predicates, so uniqueness and
the intersection formulation are the mathlib lemmas on least elements. The equivalence of the
second formulation of the uniqueness condition with the first holds for an exception set within
the restrictor, which the paper takes for granted. The syntax of §1.8 and §2.4, the two
curryings of the *but*-phrase and the Cooper variable free exceptives bind, and the rhetorical
questions of §1.7 are not formalized.

## References

* [von-fintel-1993]
* [keenan-stavi-1986]
* [hoeksema-1987]
-/

@[expose] public section

namespace VonFintel1993

open Quantifier Quantifier.GQ Quantifier.NP Quantifier.Exceptive

variable {α : Type*} {Q : GQ α} {A C B : α → Prop}

/-! ### The uniqueness condition (§1.5) -/

/-- The second formulation of (21): the subsets of the restrictor that verify the quantification
are disjoint from the exception set. It is equivalent to the first for an exception set within
the restrictor. -/
theorem excLeast_iff_forall_disjoint (hCA : C ≤ A) :
    ExcLeast Q A C B ↔
      Q (λ x => A x ∧ ¬ C x) B ∧ ∀ D, D ≤ A → Q D B → ∀ x, C x → ¬ D x := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, λ D hDA hD x hx hDx => ?_⟩
    have e : (λ x => A x ∧ ¬ (A x ∧ ¬ D x)) = D := funext λ x => propext
      ⟨λ h => by_contra λ hD => h.2 ⟨h.1, hD⟩, λ hD => ⟨hDA x hD, λ h => h.2 hD⟩⟩
    exact (h2 (show Q (λ x => A x ∧ ¬ (A x ∧ ¬ D x)) B by rw [e]; exact hD) x hx).2 hDx
  · rintro ⟨h1, h2⟩
    exact ⟨h1, λ S hS x hx => by_contra λ hSx =>
      h2 (λ x => A x ∧ ¬ S x) (λ _ h => h.1) hS x hx ⟨hCA x hx, hSx⟩⟩

/-- (23) for *every*: the exception set is the restrictor minus the scope. -/
theorem excLeast_every_iff : ExcLeast every_sem A C B ↔ ∀ x, C x ↔ A x ∧ ¬ B x := by
  constructor
  · rintro ⟨h1, h2⟩ x
    have hS : every_sem (λ x => A x ∧ ¬ (A x ∧ ¬ B x)) B :=
      λ _ ha => by_contra λ hB => ha.2 ⟨ha.1, hB⟩
    exact ⟨λ hx => h2 hS x hx, λ hx => by_contra λ hC => hx.2 (h1 x ⟨hx.1, hC⟩)⟩
  · intro hC
    refine ⟨λ x hx => by_contra λ hB => hx.2 ((hC x).2 ⟨hx.1, hB⟩), λ S hS x hx => ?_⟩
    exact by_contra λ hSx => ((hC x).1 hx).2 (hS x ⟨((hC x).1 hx).1, hSx⟩)

/-- (23) for *no*: the exception set is the intersection of restrictor and scope. -/
theorem excLeast_no_iff : ExcLeast no_sem A C B ↔ ∀ x, C x ↔ A x ∧ B x := by
  constructor
  · rintro ⟨h1, h2⟩ x
    have hS : no_sem (λ x => A x ∧ ¬ (A x ∧ B x)) B := λ _ ha hB => ha.2 ⟨ha.1, hB⟩
    exact ⟨λ hx => h2 hS x hx, λ hx => by_contra λ hC => h1 x ⟨hx.1, hC⟩ hx.2⟩
  · intro hC
    refine ⟨λ x hx hB => hx.2 ((hC x).2 ⟨hx.1, hB⟩), λ S hS x hx => ?_⟩
    exact by_contra λ hSx => hS x ⟨((hC x).1 hx).1, hSx⟩ ((hC x).1 hx).2

/-- (9): *every student but John attended* says that John is the only student who did not
attend. -/
theorem excLeast_every_singleton (j : α) :
    ExcLeast every_sem A (· = j) B ↔ ∀ x, x = j ↔ A x ∧ ¬ B x :=
  excLeast_every_iff

/-! ### Consequences of uniqueness (§1.5, §1.7) -/

/-- The inference from a *but*-phrase to one with a larger exception set (24) is blocked. -/
theorem not_excLeast_of_lt (h : ExcLeast Q A C B) {C' : α → Prop} (hlt : C < C') :
    ¬ ExcLeast Q A C' B :=
  λ h' => hlt.ne (h.unique h')

/-- Two *but*-phrases on one quantifier (28) name the same exception. -/
theorem eq_of_excLeast_singleton {j m : α} (hj : ExcLeast Q A (· = j) B)
    (hm : ExcLeast Q A (· = m) B) : j = m :=
  cast (congrFun (hj.unique hm) j) rfl

/-! ### The co-occurrence restrictions (§1.6) -/

/-- A determiner guarantees an exception set when every restrictor and scope have a least
exception. -/
def GuaranteesException (Q : GQ α) : Prop := ∀ A B : α → Prop, ∃ C, ExcLeast Q A C B

theorem guaranteesException_every : GuaranteesException (every_sem : GQ α) :=
  λ A B => ⟨λ x => A x ∧ ¬ B x, excLeast_every_iff.2 λ _ => Iff.rfl⟩

theorem guaranteesException_no : GuaranteesException (no_sem : GQ α) :=
  λ A B => ⟨λ x => A x ∧ B x, excLeast_no_iff.2 λ _ => Iff.rfl⟩

/-- *Some* guarantees no exception: when nothing in the restrictor is in the scope, no
subtraction helps. -/
theorem not_guaranteesException_some : ¬ GuaranteesException (some_sem : GQ α) := by
  rintro h
  obtain ⟨_, ⟨_, _, hx⟩, -⟩ := h (λ _ => True) (λ _ => False)
  exact hx

/-- The five students of (25): Tom, John and Harry did not attend, Bill and Mary did. -/
abbrev attended : Fin 5 → Prop := (3 ≤ ·)

/-- (25): *most students attended* is false, and no set of students is the least whose exclusion
makes it true, since excluding any two of the three nonattenders does. -/
theorem not_excLeast_most (C : Fin 5 → Prop) : ¬ ExcLeast most_sem (λ _ => True) C attended := by
  rintro ⟨h1, h2⟩
  have hTJ : most_sem (λ x : Fin 5 => True ∧ ¬ (x = 0 ∨ x = 1)) attended :=
    (mostOn_univ _ _).1 (by decide)
  have hTH : most_sem (λ x : Fin 5 => True ∧ ¬ (x = 0 ∨ x = 2)) attended :=
    (mostOn_univ _ _).1 (by decide)
  have hJH : most_sem (λ x : Fin 5 => True ∧ ¬ (x = 1 ∨ x = 2)) attended :=
    (mostOn_univ _ _).1 (by decide)
  have hC : ∀ x, ¬ C x := λ x hx => by
    have := h2 hTJ x hx
    have := h2 hTH x hx
    have := h2 hJH x hx
    omega
  have e : (λ x : Fin 5 => True ∧ ¬ C x) = λ _ => True :=
    funext λ x => propext ⟨λ _ => trivial, λ _ => ⟨trivial, hC x⟩⟩
  have h1' : most_sem (λ x : Fin 5 => True ∧ ¬ C x) attended := h1
  rw [e] at h1'
  exact absurd ((mostOn_univ _ _).2 h1') (by decide)

theorem not_guaranteesException_most : ¬ GuaranteesException (most_sem : GQ (Fin 5)) :=
  λ h => let ⟨C, hC⟩ := h (λ _ => True) attended; not_excLeast_most C hC

/-- The limiting case: with two students, John and Harry, of whom only Harry attended, *most*
has the unique exception John. -/
theorem exists_excLeast_most_two :
    ∃ C, ExcLeast most_sem (λ _ : Fin 2 => True) C (· = 1) := by
  refine ⟨(· = 0), (mostOn_univ _ _).1 (by decide), λ S hS x hx => ?_⟩
  subst hx
  have hS' : most_sem (λ x : Fin 2 => True ∧ ¬ S x) (· = 1) := hS
  by_contra h0
  by_cases h1 : S 1
  · have e : (λ x : Fin 2 => True ∧ ¬ S x) = (· = 0) :=
      funext λ x => propext (by fin_cases x <;> simp [h0, h1])
    rw [e] at hS'
    exact absurd ((mostOn_univ _ _).2 hS') (by decide)
  · have e : (λ x : Fin 2 => True ∧ ¬ S x) = λ _ => True :=
      funext λ x => propext (by fin_cases x <;> simp [h0, h1])
    rw [e] at hS'
    exact absurd ((mostOn_univ _ _).2 hS') (by decide)

/-! ### Free exceptives (§2) -/

/-- (34c): the free exceptive occurs with *most*; in situation (25) *except for Tom and John,
most students attended* holds, where no *but*-phrase does. -/
theorem excRestrictive_most :
    ExcRestrictive most_sem (λ _ : Fin 5 => True) (λ x => x = 0 ∨ x = 1) attended :=
  ⟨(mostOn_univ _ _).1 (by decide), λ h => absurd ((mostOn_univ _ _).2 h) (by decide)⟩

/-- With a universal determiner the *but* reading is the pragmatic strengthening of the free
exceptive to an exception set that contains only exceptions (§2.3). -/
theorem excLeast_every_of_excRestrictive (h : ExcRestrictive every_sem A C B)
    (hmin : ∀ x, C x → A x ∧ ¬ B x) : ExcLeast every_sem A C B :=
  excLeast_every_iff.2 λ x => ⟨hmin x, λ hx => by_contra λ hC => hx.2 (h.1 x ⟨hx.1, hC⟩)⟩

end VonFintel1993
