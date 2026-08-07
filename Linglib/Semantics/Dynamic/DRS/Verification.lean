import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

DRS verification via *embeddings* into a mathlib `FirstOrder.Language.Structure`
— [kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering. An
embedding is an assignment `v : V → M` of discourse referents to the model
domain; `DRS.Extends K v v'` is K&R's extension relation `v [K] v'` — the
output `v'` differs from `v` at most on `K`'s universe — and a sub-DRS is
entered by existentially (re)assigning along it. For `imp`, the consequent
witness extends the *antecedent* embedding, not the host one — antecedent
referents stay visible in the consequent, the `⇒` accessibility asymmetry.
The atomic and `¬` clauses are Def. 1.4.4(ii); the `⇒`/`∨` clauses are the
Chapter 2 conditional and disjunction semantics. Truth (Def. 1.4.5) is the
existential closure of verification over the outer universe; it is delivered
downstream as `DRS.trueRel` (`DRS/Dynamics.lean`) and as the first-order
translation's realization (`DRS/Reduction.lean`).

**Deviation** ([muskens-1996], fn. 4): K&R's embeddings are *partial* functions
that sub-DRSs strictly *extend*, so a re-declared referent keeps its value; here
embeddings are total and a re-declared referent is freely reassigned. The two
agree on DRSs that declare each referent once — the construction algorithm never
re-declares — but diverge on re-declaration: `[ | [x | man x] ⇒ [x | mortal x]]`
says "every man is mortal" for K&R, "if there is a man there is a mortal" here.

## Main declarations

* `DRS.Extends` — K&R's extension relation `v [K] v'`.
* `DRS.Realize` / `Condition.Realize` — the verifying-embedding relation. A DRS
  is verified when every condition is (`∀ c ∈ K.conditions`, the `Theory.Model`
  idiom), so there is no mutual recursion and no list helper.
* `DRS.realize_perm` — verification reads the condition list as a set, cashing
  the `List`-representation note in `DRS/Defs.lean`.
* `DRS.realize_map` — renaming along a bijection transports verification:
  alphabetic variants (Def. 1.4.8, via `DRS.map` in `DRS/Basic.lean`) have the
  same semantics.

## Implementation notes

`Condition.Realize` recurses into sub-DRSs through the nested
`List (Condition L V)` by well-founded recursion on `sizeOf`, so its clause
characterizations (`realize_neg`, …) are equation-lemma rewrites rather than
`Iff.rfl`.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-- `K.Extends v v'` (K&R's `v [K] v'`): the output embedding `v'` differs from
the input `v` at most on `K`'s universe. -/
def DRS.Extends (K : DRS L V) (v v' : V → M) : Prop := ∀ x ∉ K.referents, v' x = v x

private theorem sizeOf_lt_of_mem_conditions {K : DRS L V} {c : Condition L V}
    (h : c ∈ K.conditions) : sizeOf c < sizeOf K := by
  cases K with
  | mk U conds =>
    simp only [DRS.conditions_mk] at h
    have := List.sizeOf_lt_of_mem h
    simp only [DRS.mk.sizeOf_spec]
    omega

/-- `c.Realize v`: the embedding `v` *verifies* the condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along
its extension relation and verifying each of its conditions. -/
def Condition.Realize : Condition L V → (V → M) → Prop
  | .rel R args, v => Structure.RelMap R (fun i => v (args i))
  | .eq a b, v => v a = v b
  | .neg K, v => ¬ ∃ v', K.Extends v v' ∧ ∀ c ∈ K.conditions, c.Realize v'
  | .imp a c, v =>
      ∀ v', a.Extends v v' → (∀ d ∈ a.conditions, d.Realize v') →
        ∃ v'', c.Extends v' v'' ∧ ∀ d ∈ c.conditions, d.Realize v''
  | .dis l r, v =>
      (∃ v', l.Extends v v' ∧ ∀ c ∈ l.conditions, c.Realize v') ∨
      (∃ v', r.Extends v v' ∧ ∀ c ∈ r.conditions, c.Realize v')
decreasing_by all_goals
  have := sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- `K.Realize v`: the embedding `v` *verifies* `K` — every condition of `K`
holds under `v` (Def. 1.4.4). -/
def DRS.Realize (K : DRS L V) (v : V → M) : Prop := ∀ c ∈ K.conditions, c.Realize v

/-! ### Structural simp API -/

variable {v : V → M}

@[simp] theorem DRS.realize_mk (U : Finset V) (conds : List (Condition L V)) :
    (DRS.mk U conds).Realize v ↔ ∀ c ∈ conds, c.Realize v := Iff.rfl

@[simp] theorem Condition.realize_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).Realize v ↔ Structure.RelMap R (fun i => v (args i)) := by
  simp only [Condition.Realize]

@[simp] theorem Condition.realize_eq (a b : V) :
    (Condition.eq a b : Condition L V).Realize v ↔ v a = v b := by
  simp only [Condition.Realize]

@[simp] theorem Condition.realize_neg (K : DRS L V) :
    (Condition.neg K).Realize v ↔ ¬ ∃ v', K.Extends v v' ∧ K.Realize v' := by
  simp only [Condition.Realize, DRS.Realize]

@[simp] theorem Condition.realize_imp (a c : DRS L V) :
    (Condition.imp a c).Realize v ↔
      ∀ v', a.Extends v v' → a.Realize v' →
        ∃ v'', c.Extends v' v'' ∧ c.Realize v'' := by
  simp only [Condition.Realize, DRS.Realize]

@[simp] theorem Condition.realize_dis (l r : DRS L V) :
    (Condition.dis l r).Realize v ↔
      (∃ v', l.Extends v v' ∧ l.Realize v') ∨
      (∃ v', r.Extends v v' ∧ r.Realize v') := by
  simp only [Condition.Realize, DRS.Realize]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem DRS.realize_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    (DRS.mk U cs).Realize v ↔ (DRS.mk U ds).Realize v := by
  simp only [DRS.realize_mk, h.mem_iff]

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

/-- A renamed DRS is verified iff the original is under the precomposed
embedding, given the transport for each of its conditions. -/
private theorem realize_map_all (e : V ≃ W) (K : DRS L V) (v' : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M, (c.map e).Realize u ↔ c.Realize (u ∘ e)) :
    (K.map e).Realize v' ↔ K.Realize (v' ∘ e) := by
  simp only [DRS.Realize, DRS.conditions_map, Condition.mapList_eq_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc v'

/-- Renaming along a bijection transports verification (the condition form of
`DRS.realize_map`). -/
theorem Condition.realize_map (e : V ≃ W) : ∀ (c : Condition L V) (v : W → M),
    (c.map e).Realize v ↔ c.Realize (v ∘ e)
  | .rel R args, v => by
    simp [Condition.map, Function.comp]
  | .eq a b, v => by
    simp [Condition.map, Function.comp]
  | .neg K, v => by
    have hK := fun v' : W → M =>
      realize_map_all e K v' (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_neg, DRS.Extends, DRS.referents_map]
    exact not_congr ((exists_congr fun v' => and_congr_right fun _ => hK v').trans
      (exists_precomp_extend_iff e K.referents v K.Realize))
  | .imp a c, v => by
    have hA := fun v' : W → M =>
      realize_map_all e a v' (fun d hd u => Condition.realize_map e d u)
    have hC := fun v' : W → M =>
      realize_map_all e c v' (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_imp, DRS.Extends, DRS.referents_map]
    refine Iff.trans (forall_congr' fun v' => imp_congr_right fun _ => imp_congr (hA v')
      ((exists_congr fun v'' => and_congr_right fun _ => hC v'').trans
        (exists_precomp_extend_iff e c.referents v' c.Realize))) ?_
    exact forall_precomp_extend_iff e a.referents v
      (fun u => a.Realize u → ∃ w'', (∀ x ∉ c.referents, w'' x = u x) ∧ c.Realize w'')
  | .dis l r, v => by
    have hL := fun v' : W → M =>
      realize_map_all e l v' (fun d hd u => Condition.realize_map e d u)
    have hR := fun v' : W → M =>
      realize_map_all e r v' (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_dis, DRS.Extends, DRS.referents_map]
    exact or_congr
      ((exists_congr fun v' => and_congr_right fun _ => hL v').trans
        (exists_precomp_extend_iff e l.referents v l.Realize))
      ((exists_congr fun v' => and_congr_right fun _ => hR v').trans
        (exists_precomp_extend_iff e r.referents v r.Realize))
decreasing_by all_goals
  have := sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming along a bijection transports verification: `v` verifies `K.map e`
iff `v ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem DRS.realize_map (e : V ≃ W) (K : DRS L V) (v : W → M) :
    (K.map e).Realize v ↔ K.Realize (v ∘ e) :=
  realize_map_all e K v (fun c _ u => Condition.realize_map e c u)

end Map

end DRT
