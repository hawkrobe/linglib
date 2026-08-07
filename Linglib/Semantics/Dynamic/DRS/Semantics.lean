import Linglib.Semantics.Dynamic.DRS.Basic

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
* `DRS.realize_map` — renaming along a bijection transports verification:
  alphabetic variants (Def. 1.4.8, via `DRS.map` in `DRS/Basic.lean`) have the
  same semantics.
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

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

/-- Precomposition with `e` is a bijection between the embeddings extending `v`
on `U.image e` and those extending `v ∘ e` on `U`. -/
private theorem exists_precomp_extend_iff (e : V ≃ W) (U : Finset V) (v : W → M)
    (P : (V → M) → Prop) :
    (∃ v' : W → M, (∀ y ∉ U.image e, v' y = v y) ∧ P (v' ∘ e)) ↔
      ∃ w' : V → M, (∀ x ∉ U, w' x = v (e x)) ∧ P w' := by
  constructor
  · rintro ⟨v', h, hp⟩
    exact ⟨v' ∘ e, fun x hx => h (e x) (by simpa using hx), hp⟩
  · rintro ⟨w', h, hp⟩
    refine ⟨w' ∘ e.symm, fun y hy => ?_, ?_⟩
    · have hx : e.symm y ∉ U := fun hmem => hy (by simpa using Finset.mem_image_of_mem e hmem)
      simpa using h _ hx
    · have key : (w' ∘ e.symm) ∘ e = w' := by funext x; simp
      exact key.symm ▸ hp

/-- The `∀` analogue of `exists_precomp_extend_iff`. -/
private theorem forall_precomp_extend_iff (e : V ≃ W) (U : Finset V) (v : W → M)
    (P : (V → M) → Prop) :
    (∀ v' : W → M, (∀ y ∉ U.image e, v' y = v y) → P (v' ∘ e)) ↔
      ∀ w' : V → M, (∀ x ∉ U, w' x = v (e x)) → P w' := by
  constructor
  · intro H w' h
    have key : (w' ∘ e.symm) ∘ e = w' := by funext x; simp
    refine key ▸ H (w' ∘ e.symm) fun y hy => ?_
    have hx : e.symm y ∉ U := fun hmem => hy (by simpa using Finset.mem_image_of_mem e hmem)
    simpa using h _ hx
  · intro H v' h
    exact H (v' ∘ e) fun x hx => h (e x) (by simpa using hx)

mutual
/-- Renaming along a bijection transports verification: `v` verifies `K.map e`
iff `v ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem DRS.realize_map (e : V ≃ W) (K : DRS L V) (v : W → M) :
    (K.map e).Realize v ↔ K.Realize (v ∘ e) := by
  match K with
  | .mk U conds =>
    simp only [DRS.map, DRS.realize_mk]
    exact Condition.realizeAll_mapList e conds v
/-- The condition analogue of `DRS.realize_map`. -/
theorem Condition.realize_map (e : V ≃ W) (c : Condition L V) (v : W → M) :
    (c.map e).Realize v ↔ c.Realize (v ∘ e) := by
  match c with
  | .rel R args => exact Iff.rfl
  | .eq a b => exact Iff.rfl
  | .neg K =>
    simp only [Condition.map, Condition.realize_neg, DRS.referents_map]
    exact not_congr ((exists_congr fun v' => and_congr_right fun _ =>
      DRS.realize_map e K v').trans (exists_precomp_extend_iff e K.referents v K.Realize))
  | .imp ante cons =>
    simp only [Condition.map, Condition.realize_imp, DRS.referents_map]
    refine Iff.trans (forall_congr' fun v' => imp_congr_right fun _ => imp_congr
      (DRS.realize_map e ante v')
      ((exists_congr fun v'' => and_congr_right fun _ => DRS.realize_map e cons v'').trans
        (exists_precomp_extend_iff e cons.referents v' cons.Realize))) ?_
    exact forall_precomp_extend_iff e ante.referents v
      (fun u => ante.Realize u → ∃ w'', (∀ x ∉ cons.referents, w'' x = u x) ∧ cons.Realize w'')
  | .dis l r =>
    simp only [Condition.map, Condition.realize_dis, DRS.referents_map]
    exact or_congr
      ((exists_congr fun v' => and_congr_right fun _ => DRS.realize_map e l v').trans
        (exists_precomp_extend_iff e l.referents v l.Realize))
      ((exists_congr fun v' => and_congr_right fun _ => DRS.realize_map e r v').trans
        (exists_precomp_extend_iff e r.referents v r.Realize))
/-- The list analogue of `Condition.realize_map`. -/
theorem Condition.realizeAll_mapList (e : V ≃ W) (cs : List (Condition L V)) (v : W → M) :
    Condition.RealizeAll (Condition.mapList e cs) v ↔ Condition.RealizeAll cs (v ∘ e) := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.mapList, Condition.realizeAll_cons]
    exact and_congr (Condition.realize_map e c v) (Condition.realizeAll_mapList e cs v)
end

end Map

end DRT
