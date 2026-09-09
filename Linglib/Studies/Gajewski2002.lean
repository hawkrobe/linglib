import Linglib.Semantics.Quantification.Exceptive
import Linglib.Studies.BarwiseCooper1981
import Linglib.Data.Examples.Gajewski2002
import Mathlib.Data.Fin.VecNotation

/-!
# Gajewski (2002): On Analyticity in Natural Language

This file formalizes [gajewski-2002]'s principle that a sentence is ungrammatical if its
logical form contains an L-analytic constituent, one that is true, or false, in virtue of its
logical structure alone. Logical structure has two ingredients. The logical items are the
denotations invariant under permutations of the domain, the criterion of [van-benthem-1989]:
the determiners *every*, *some* and *no*, the truth-functional connectives, and expletive
*there*, which denotes the whole domain. The logical skeleton of a sentence replaces each maximal
constituent without logical items by a distinct variable of its type, and the sentence is
L-analytic when the skeleton receives one truth value under every assignment
(`Skeleton.IsLAnalytic`). The principle puts two analyses on firmer ground. [barwise-cooper-1981]
explained the definiteness restriction on *there*-sentences of [milsark-1977] by the tautology a
strong determiner produces there: the skeleton of *there is every new student* is an
L-tautology because every set is a subset of the domain (`thereSkeleton_isLTautology`), while
with *some* the skeleton is false under the empty assignment and true otherwise.
[von-fintel-1993] explained the restriction of *but*-exceptives to universal determiners by the
contradiction his least-exception semantics produces under a left-upward-monotone determiner,
which admits no nonempty least exception (`ExcLeast.not_of_restrictorUpwardMono`): the skeleton
with *some* is an L-contradiction (`exceptiveSkeleton_isLContradiction`), and the skeletons with
*every* and *no* are contingent. Both analyses had appealed to trivial truth conditions, which
*war is war* shows cannot be the explanation, and L-analyticity is narrower than triviality:
*every woman is a woman* and *John is smoking and John is not smoking* receive skeletons with
distinct variables for their repeated material, which are contingent, so the garden-variety
tautologies and contradictions come out grammatical. The paper's sentences are the rows, and the
principle predicts each (`rows_predicted`).

## Implementation notes

* A skeleton is a family of typed slots with the denotation it receives under an assignment;
  the paper's variables of type ⟨e,t⟩ are slots valued in `α → Prop` and its propositional
  variables slots valued in `Prop`. Davidson's formulation, that the truth value survives every
  rewriting of the non-logical parts, is `Skeleton.isLAnalytic_iff`.
* The exceptive skeleton carries the nonemptiness of the exception set that the paper's footnote
  adds to von Fintel's schema.
* The rows are evaluated over a two-element domain; the general theorems take any domain with
  the one point their witnesses need.
* The examples are `Data.Examples.Gajewski2002`.

## References

* [gajewski-2002]
* [barwise-cooper-1981]
* [von-fintel-1993]
* [milsark-1977]
* [van-benthem-1989]
-/

namespace Gajewski2002

open Quantification Quantification.Exceptive Data.Examples

/-- A logical skeleton (24): typed slots, one per maximal constituent without logical items, and
the denotation the skeleton receives under an assignment (27). -/
structure Skeleton (ι : Type*) (D : ι → Type*) where
  interpret : ((i : ι) → D i) → Prop

namespace Skeleton

variable {ι : Type*} {D : ι → Type*} (S : Skeleton ι D)

/-- The skeleton receives 1 under every assignment. -/
def IsLTautology : Prop := ∀ g, S.interpret g

/-- The skeleton receives 0 under every assignment. -/
def IsLContradiction : Prop := ∀ g, ¬ S.interpret g

/-- L-analytic (28): the same truth value under every assignment. -/
def IsLAnalytic : Prop := S.IsLTautology ∨ S.IsLContradiction

/-- Davidson's formulation: the truth value survives every significant rewriting of the
non-logical parts. -/
theorem isLAnalytic_iff [Nonempty ((i : ι) → D i)] :
    S.IsLAnalytic ↔ ∀ g g', S.interpret g ↔ S.interpret g' := by
  refine ⟨λ h g g' => ?_, λ h => ?_⟩
  · rcases h with h | h
    · exact iff_of_true (h g) (h g')
    · exact iff_of_false (h g) (h g')
  · obtain ⟨g₀⟩ := ‹Nonempty ((i : ι) → D i)›
    by_cases hg : S.interpret g₀
    · exact Or.inl λ g => (h g g₀).2 hg
    · exact Or.inr λ g hg' => hg ((h g g₀).1 hg')

end Skeleton

variable {α : Type*}

/-! ### The definiteness restriction (§3.3.1) -/

/-- The skeleton (25) of a *there*-sentence: the determiner applied to a property variable and to
*there*, which denotes the domain (23c). -/
def thereSkeleton (Q : GQ α) : Skeleton Unit (λ _ => α → Prop) :=
  ⟨λ g => Q (g ()) (λ _ => True)⟩

/-- (30): with a conservative positive strong determiner the *there*-skeleton is an
L-tautology, [barwise-cooper-1981]'s consequence that the domain belongs to every strong
quantifier. -/
theorem thereSkeleton_isLTautology {Q : GQ α} (hc : Conservative Q) (hs : PositiveStrong Q) :
    (thereSkeleton Q).IsLTautology :=
  λ g => BarwiseCooper1981.there_of_positiveStrong hc hs (g ())

/-- (25): with *some* the skeleton is false under the empty assignment and true under the total
one. -/
theorem thereSkeleton_some_not_isLAnalytic (a : α) :
    ¬ (thereSkeleton (some_sem : GQ α)).IsLAnalytic := by
  rintro (h | h)
  · obtain ⟨_, hx, -⟩ := h (λ _ _ => False)
    exact hx
  · exact h (λ _ _ => True) ⟨a, trivial, trivial⟩

/-! ### But-exceptives (§3.3.2) -/

/-- The skeleton (32)–(33) of *D n₁ but n₂ n₃*: von Fintel's least-exception schema (31), with
the exception set nonempty as the paper's footnote requires. -/
def exceptiveSkeleton (Q : GQ α) : Skeleton (Fin 3) (λ _ => α → Prop) :=
  ⟨λ g => (∃ x, g 1 x) ∧ ExcLeast Q (g 0) (g 1) (g 2)⟩

/-- (33): with a left-upward-monotone determiner the exceptive skeleton is an L-contradiction. -/
theorem exceptiveSkeleton_isLContradiction {Q : GQ α} (h : RestrictorUpwardMono Q) :
    (exceptiveSkeleton Q).IsLContradiction :=
  λ _ ⟨⟨x, hx⟩, he⟩ => he.not_of_restrictorUpwardMono h x hx

/-- No exceptive skeleton is an L-tautology: an empty exception set falsifies it. -/
theorem exceptiveSkeleton_not_isLTautology (Q : GQ α) :
    ¬ (exceptiveSkeleton Q).IsLTautology :=
  λ h => (h ![λ _ => True, λ _ => False, λ _ => True]).1.elim λ _ hx => hx

/-- (32): with *every* the exceptive skeleton is true when the exception is the one individual
outside the scope. -/
theorem exceptiveSkeleton_every_not_isLContradiction (a : α) :
    ¬ (exceptiveSkeleton (every_sem : GQ α)).IsLContradiction := λ h =>
  h ![λ _ => True, (· = a), (· ≠ a)]
    ⟨⟨a, rfl⟩, λ _ hx => hx.2, λ _ hS x hx => by_contra λ hs => hS x ⟨trivial, hs⟩ hx⟩

/-- With *no* the exceptive skeleton is true when the exception is the one individual inside the
scope. -/
theorem exceptiveSkeleton_no_not_isLContradiction (a : α) :
    ¬ (exceptiveSkeleton (no_sem : GQ α)).IsLContradiction := λ h =>
  h ![λ _ => True, (· = a), (· = a)]
    ⟨⟨a, rfl⟩, λ _ hx hxa => hx.2 hxa, λ _ hS x hx => by_contra λ hs => hS x ⟨trivial, hs⟩ hx⟩

/-! ### Garden-variety tautologies and contradictions (§3.3.3) -/

/-- The skeleton (35) of *every woman is a woman*, with distinct variables for the two
occurrences. -/
def everyIsSkeleton : Skeleton (Fin 2) (λ _ => α → Prop) := ⟨λ g => every_sem (g 0) (g 1)⟩

theorem everyIsSkeleton_not_isLAnalytic (a : α) : ¬ (everyIsSkeleton (α := α)).IsLAnalytic := by
  rintro (h | h)
  · exact h ![λ _ => True, λ _ => False] a trivial
  · exact h ![λ _ => True, λ _ => True] λ _ _ => trivial

/-- The skeleton (36) of *John is smoking and John is not smoking*, with two propositional
variables. -/
def andNotSkeleton : Skeleton (Fin 2) (λ _ => Prop) := ⟨λ g => g 0 ∧ ¬ g 1⟩

theorem andNotSkeleton_not_isLAnalytic : ¬ andNotSkeleton.IsLAnalytic := by
  rintro (h | h)
  · exact (h ![True, True]).2 trivial
  · exact h ![True, False] ⟨trivial, id⟩

/-! ### The paper's sentences -/

/-- The logical determiners of the paper's sentences. -/
inductive Determiner
  | every
  | some
  | no
  deriving DecidableEq, Repr

/-- The denotation of a determiner over a domain. -/
def Determiner.denote : Determiner → GQ α
  | .every => every_sem
  | .some => some_sem
  | .no => no_sem

/-- The constructions of the paper's sentences, with their determiner where one matters. -/
inductive Construction
  | there (d : Determiner)
  | exceptive (d : Determiner)
  | everyIs
  | andNot
  deriving DecidableEq, Repr

/-- A sentence of the paper: its construction and whether it is grammatical. -/
structure Row where
  construction : Construction
  grammatical : Bool
  deriving DecidableEq

/-- Whether the sentence's skeleton over a two-element domain is L-analytic. -/
def Row.LAnalytic (r : Row) : Prop :=
  match r.construction with
  | .there d => (thereSkeleton (d.denote : GQ Bool)).IsLAnalytic
  | .exceptive d => (exceptiveSkeleton (d.denote : GQ Bool)).IsLAnalytic
  | .everyIs => (everyIsSkeleton (α := Bool)).IsLAnalytic
  | .andNot => andNotSkeleton.IsLAnalytic

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let g ← ex.parse? "grammatical" [("yes", true), ("no", false)]
  let d := ex.parse? "determiner" [("every", Determiner.every), ("some", .some), ("no", .no)]
  let c ← match ex.feature? "construction", d with
    | some "there", some d => some (Construction.there d)
    | some "exceptive", some d => some (.exceptive d)
    | some "everyIs", _ => some .everyIs
    | some "andNot", _ => some .andNot
    | _, _ => none
  pure ⟨c, g⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

private theorem rows_eq : rows =
    [⟨.there .every, false⟩, ⟨.there .every, false⟩, ⟨.there .some, true⟩, ⟨.there .some, true⟩,
     ⟨.exceptive .every, true⟩, ⟨.exceptive .no, true⟩, ⟨.exceptive .some, false⟩,
     ⟨.everyIs, true⟩, ⟨.andNot, true⟩] := by
  decide

/-- Principle (29): the paper's sentences are grammatical exactly when their skeletons are not
L-analytic. -/
theorem rows_predicted : ∀ r ∈ rows, (r.grammatical = true ↔ ¬ r.LAnalytic) := by
  have hevery : (thereSkeleton (every_sem : GQ Bool)).IsLAnalytic :=
    Or.inl (thereSkeleton_isLTautology every_conservative every_positive_strong)
  have hsome : (exceptiveSkeleton (some_sem : GQ Bool)).IsLAnalytic :=
    Or.inr (exceptiveSkeleton_isLContradiction some_restrictor_up)
  rw [rows_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact iff_of_false Bool.false_ne_true (not_not.2 hevery)
  · exact iff_of_false Bool.false_ne_true (not_not.2 hevery)
  · exact iff_of_true rfl (thereSkeleton_some_not_isLAnalytic true)
  · exact iff_of_true rfl (thereSkeleton_some_not_isLAnalytic true)
  · exact iff_of_true rfl λ h => h.elim (exceptiveSkeleton_not_isLTautology _)
      (exceptiveSkeleton_every_not_isLContradiction true)
  · exact iff_of_true rfl λ h => h.elim (exceptiveSkeleton_not_isLTautology _)
      (exceptiveSkeleton_no_not_isLContradiction true)
  · exact iff_of_false Bool.false_ne_true (not_not.2 hsome)
  · exact iff_of_true rfl (everyIsSkeleton_not_isLAnalytic true)
  · exact iff_of_true rfl andNotSkeleton_not_isLAnalytic

end Gajewski2002
