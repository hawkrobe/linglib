import Linglib.Semantics.Dynamic.DRS.Defs

/-!
# Model-theoretic semantics of DRSs

DRS verification via *embeddings* into a mathlib `FirstOrder.Language.Structure`
— [kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering. An
embedding is an assignment `v : V → M` of discourse referents to the model
domain; a sub-DRS is entered by existentially (re)assigning the referents of
its universe, which is what `∀ x ∉ K.referents, v' x = v x` expresses (`v'`
extends `v` on `K`'s universe). For `imp`, the consequent witness extends the
*antecedent* embedding, not the host one — antecedent referents stay visible
in the consequent, the `⇒` accessibility asymmetry. The atomic and `¬` clauses
are Def. 1.4.4(ii); the `⇒`/`∨` clauses are the Chapter 2 conditional and
disjunction semantics. Truth (Def. 1.4.5) is the existential closure of
verification over the outer universe; it is delivered downstream as
`DRS.trueRel` (`DRS/Dynamics.lean`) and as the first-order translation's
realization (`DRS/Reduction.lean`).

**Deviation** ([muskens-1996], fn. 4): K&R's embeddings are *partial* functions
that sub-DRSs strictly *extend*, so a re-declared referent keeps its value; here
embeddings are total and a re-declared referent is freely reassigned. The two
agree on DRSs that declare each referent once — the construction algorithm never
re-declares — but diverge on re-declaration: `[ | [x | man x] ⇒ [x | mortal x]]`
says "every man is mortal" for K&R, "if there is a man there is a mortal" here.

## Main declarations

* `DRS.Realize` / `Condition.Realize` — the verifying-embedding relation,
  reusing mathlib's `Structure.RelMap` for atomic conditions.
* `DRS.realize_perm` — verification reads the condition list as a set, cashing
  the `List`-representation note in `DRS/Defs.lean`.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

mutual
/-- `K.Realize v`: the embedding `v` *verifies* `K` — every condition of `K`
holds under `v`. -/
def DRS.Realize : DRS L V → (V → M) → Prop
  | .mk _ conds, v => Condition.RealizeAll conds v
/-- `c.Realize v`: the embedding `v` verifies the condition `c`; sub-DRSs are
entered by existentially (re)assigning the referents of their universes. -/
def Condition.Realize : Condition L V → (V → M) → Prop
  | .rel R args, v => Structure.RelMap R (fun i => v (args i))
  | .eq a b, v => v a = v b
  | .neg K, v => ¬ ∃ v' : V → M, (∀ x ∉ K.referents, v' x = v x) ∧ DRS.Realize K v'
  | .imp a c, v =>
      ∀ v' : V → M, (∀ x ∉ a.referents, v' x = v x) → DRS.Realize a v' →
        ∃ v'' : V → M, (∀ x ∉ c.referents, v'' x = v' x) ∧ DRS.Realize c v''
  | .dis l r, v =>
      (∃ v' : V → M, (∀ x ∉ l.referents, v' x = v x) ∧ DRS.Realize l v') ∨
      (∃ v' : V → M, (∀ x ∉ r.referents, v' x = v x) ∧ DRS.Realize r v')
/-- Every condition in the list is verified by `v`. A `List` helper — the
higher-order `List.Forall (·.Realize v)` form fails the nested-inductive
structural-recursion checker; `realizeAll_iff_forall_mem` is the membership
characterization. -/
def Condition.RealizeAll : List (Condition L V) → (V → M) → Prop
  | [], _ => True
  | c :: cs, v => Condition.Realize c v ∧ Condition.RealizeAll cs v
end

/-! ### Structural simp API -/

variable {v : V → M}

@[simp] theorem DRS.realize_mk (U : Finset V) (conds : List (Condition L V)) :
    (DRS.mk U conds).Realize v ↔ Condition.RealizeAll conds v := Iff.rfl

@[simp] theorem Condition.realize_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).Realize v ↔ Structure.RelMap R (fun i => v (args i)) := Iff.rfl

@[simp] theorem Condition.realize_eq (a b : V) :
    (Condition.eq a b : Condition L V).Realize v ↔ v a = v b := Iff.rfl

@[simp] theorem Condition.realize_neg (K : DRS L V) :
    (Condition.neg K).Realize v ↔
      ¬ ∃ v', (∀ x ∉ K.referents, v' x = v x) ∧ K.Realize v' := Iff.rfl

@[simp] theorem Condition.realize_imp (a c : DRS L V) :
    (Condition.imp a c).Realize v ↔
      ∀ v', (∀ x ∉ a.referents, v' x = v x) → a.Realize v' →
        ∃ v'', (∀ x ∉ c.referents, v'' x = v' x) ∧ c.Realize v'' := Iff.rfl

@[simp] theorem Condition.realize_dis (l r : DRS L V) :
    (Condition.dis l r).Realize v ↔
      (∃ v', (∀ x ∉ l.referents, v' x = v x) ∧ l.Realize v') ∨
      (∃ v', (∀ x ∉ r.referents, v' x = v x) ∧ r.Realize v') := Iff.rfl

@[simp] theorem Condition.realizeAll_nil :
    Condition.RealizeAll ([] : List (Condition L V)) v := trivial

@[simp] theorem Condition.realizeAll_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.RealizeAll (c :: cs) v ↔ c.Realize v ∧ Condition.RealizeAll cs v := Iff.rfl

/-! ### Verification reads the condition list as a set -/

/-- Membership characterization of `RealizeAll`. -/
theorem Condition.realizeAll_iff_forall_mem {cs : List (Condition L V)} :
    Condition.RealizeAll cs v ↔ ∀ c ∈ cs, c.Realize v := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- Verification of a condition list is invariant under permutation. -/
theorem Condition.realizeAll_perm {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    Condition.RealizeAll cs v ↔ Condition.RealizeAll ds v := by
  simp only [Condition.realizeAll_iff_forall_mem, h.mem_iff]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem DRS.realize_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    (DRS.mk U cs).Realize v ↔ (DRS.mk U ds).Realize v :=
  Condition.realizeAll_perm h

end DRT
