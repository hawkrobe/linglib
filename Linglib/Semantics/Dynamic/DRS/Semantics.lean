import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.ModelTheory.Semantics

/-!
# Model-theoretic semantics of DRSs
[kamp-reyle-1993]

DRS truth via *verifying embeddings* into a mathlib `FirstOrder.Language.Structure`
— Kamp & Reyle's Def. 1.4.4 in the *total-assignment* rendering. An
embedding is an assignment `v : V → M` of discourse referents to the model
domain; the discourse referents introduced by a sub-DRS are existentially
(re)assigned when that sub-DRS is entered, which is what
`(∀ x ∉ K.referents, v' x = v x)` expresses (`v'` extends `v` on `K`'s universe).

**Deviation** ([muskens-1996], fn. 4): K&R's embeddings are *partial* functions
that sub-DRSs strictly *extend*, so a re-declared referent keeps its value; here
embeddings are total and a re-declared referent is freely reassigned. The two
agree on DRSs that declare each referent once — the construction algorithm never
re-declares — but diverge on re-declaration: `[ | [x | man x] ⇒ [x | mortal x]]`
says "every man is mortal" for K&R, "if there is a man there is a mortal" here.

## Main declarations

* `DRS.Realize` / `Condition.Realize` — the verifying-embedding relation
  (Def. 1.4.4), reusing mathlib's `Structure.RelMap` for atomic conditions.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

mutual
/-- `v` *verifies* `K` ([kamp-reyle-1993], Def. 1.4.4): every condition of `K`
holds under the assignment `v`. -/
def DRS.Realize (v : V → M) : DRS L V → Prop
  | .mk _ conds => Condition.RealizeAll v conds
/-- `v` verifies a condition — Def. 1.4.4(ii) for the atomic and `¬` clauses;
the `⇒`/`∨` clauses are K&R's Chapter 2 conditional and disjunction semantics.
A sub-DRS `K` is entered by existentially (re)assigning the referents of its
universe (`v'` agrees with `v` off `K.referents`). For `imp`, the consequent
witness `v''` extends the *antecedent* assignment `v'` (not the host `v`):
antecedent referents are visible in the consequent — the `⇒` accessibility
asymmetry. -/
def Condition.Realize (v : V → M) : Condition L V → Prop
  | .rel R args => Structure.RelMap R (fun i => v (args i))
  | .eq a b => v a = v b
  | .neg K => ¬ ∃ v' : V → M, (∀ x, x ∉ K.referents → v' x = v x) ∧ DRS.Realize v' K
  | .imp a c =>
      ∀ v' : V → M, (∀ x, x ∉ a.referents → v' x = v x) → DRS.Realize v' a →
        ∃ v'' : V → M, (∀ x, x ∉ c.referents → v'' x = v' x) ∧ DRS.Realize v'' c
  | .dis l r =>
      (∃ v' : V → M, (∀ x, x ∉ l.referents → v' x = v x) ∧ DRS.Realize v' l) ∨
      (∃ v' : V → M, (∀ x, x ∉ r.referents → v' x = v x) ∧ DRS.Realize v' r)
/-- Every condition in the list is verified by `v`. A `List` helper (not
`List.Forall (Condition.Realize v)`) because Lean's structural-recursion checker
for the nested `List (Condition …)` rejects the higher-order argument. -/
def Condition.RealizeAll (v : V → M) : List (Condition L V) → Prop
  | [] => True
  | c :: cs => Condition.Realize v c ∧ Condition.RealizeAll v cs
end

end DRT
