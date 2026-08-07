import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

DRS verification via *embeddings* into a mathlib `FirstOrder.Language.Structure`
— [kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering. An
embedding is an assignment `f : V → M` of discourse referents to the model
domain; `DRS.Extends K f g` is K&R's extension relation `f [K] g` — the
output `g` differs from `f` at most on `K`'s universe — and a sub-DRS is
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

/-- `c.Realize f`: the embedding `f` *verifies* the condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along
its extension relation and verifying each of its conditions. -/
def Condition.Realize : Condition L V → (V → M) → Prop
  | .rel R args, f => Structure.RelMap R (fun i => f (args i))
  | .eq a b, f => f a = f b
  | .neg K, f => ¬ ∃ g, K.Extends f g ∧ ∀ c ∈ K.conditions, c.Realize g
  | .imp a c, f =>
      ∀ g, a.Extends f g → (∀ d ∈ a.conditions, d.Realize g) →
        ∃ h, c.Extends g h ∧ ∀ d ∈ c.conditions, d.Realize h
  | .dis l r, f =>
      (∃ g, l.Extends f g ∧ ∀ c ∈ l.conditions, c.Realize g) ∨
      (∃ g, r.Extends f g ∧ ∀ c ∈ r.conditions, c.Realize g)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- `K.Realize f`: the embedding `f` *verifies* `K` — every condition of `K`
holds under `f` (Def. 1.4.4). -/
def DRS.Realize (K : DRS L V) (f : V → M) : Prop := ∀ c ∈ K.conditions, c.Realize f

/-! ### Structural simp API -/

variable {f : V → M}

@[simp] theorem DRS.realize_mk (U : Finset V) (conds : List (Condition L V)) :
    (DRS.mk U conds).Realize f ↔ ∀ c ∈ conds, c.Realize f := Iff.rfl

@[simp] theorem Condition.realize_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).Realize f ↔ Structure.RelMap R (fun i => f (args i)) := by
  simp only [Condition.Realize]

@[simp] theorem Condition.realize_eq (a b : V) :
    (Condition.eq a b : Condition L V).Realize f ↔ f a = f b := by
  simp only [Condition.Realize]

@[simp] theorem Condition.realize_neg (K : DRS L V) :
    (Condition.neg K).Realize f ↔ ¬ ∃ g, K.Extends f g ∧ K.Realize g := by
  simp only [Condition.Realize, DRS.Realize]

@[simp] theorem Condition.realize_imp (a c : DRS L V) :
    (Condition.imp a c).Realize f ↔
      ∀ g, a.Extends f g → a.Realize g →
        ∃ h, c.Extends g h ∧ c.Realize h := by
  simp only [Condition.Realize, DRS.Realize]

@[simp] theorem Condition.realize_dis (l r : DRS L V) :
    (Condition.dis l r).Realize f ↔
      (∃ g, l.Extends f g ∧ l.Realize g) ∨
      (∃ g, r.Extends f g ∧ r.Realize g) := by
  simp only [Condition.Realize, DRS.Realize]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem DRS.realize_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    (DRS.mk U cs).Realize f ↔ (DRS.mk U ds).Realize f := by
  simp only [DRS.realize_mk, h.mem_iff]

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

/-- Precomposition with `e` is a bijection between the embeddings extending `f`
on `U.image e` and those extending `f ∘ e` on `U`. -/
private theorem exists_precomp_extend_iff (e : V ≃ W) (U : Finset V) (f : W → M)
    (P : (V → M) → Prop) :
    (∃ g : W → M, (∀ y ∉ U.image e, g y = f y) ∧ P (g ∘ e)) ↔
      ∃ w' : V → M, (∀ x ∉ U, w' x = f (e x)) ∧ P w' := by
  constructor
  · rintro ⟨g, h, hp⟩
    exact ⟨g ∘ e, fun x hx => h (e x) (by simpa using hx), hp⟩
  · rintro ⟨w', h, hp⟩
    refine ⟨w' ∘ e.symm, fun y hy => ?_, ?_⟩
    · have hx : e.symm y ∉ U := fun hmem => hy (by simpa using Finset.mem_image_of_mem e hmem)
      simpa using h _ hx
    · have key : (w' ∘ e.symm) ∘ e = w' := by funext x; simp
      exact key.symm ▸ hp

/-- The `∀` analogue of `exists_precomp_extend_iff`. -/
private theorem forall_precomp_extend_iff (e : V ≃ W) (U : Finset V) (f : W → M)
    (P : (V → M) → Prop) :
    (∀ g : W → M, (∀ y ∉ U.image e, g y = f y) → P (g ∘ e)) ↔
      ∀ w' : V → M, (∀ x ∉ U, w' x = f (e x)) → P w' := by
  constructor
  · intro H w' h
    have key : (w' ∘ e.symm) ∘ e = w' := by funext x; simp
    refine key ▸ H (w' ∘ e.symm) fun y hy => ?_
    have hx : e.symm y ∉ U := fun hmem => hy (by simpa using Finset.mem_image_of_mem e hmem)
    simpa using h _ hx
  · intro H g h
    exact H (g ∘ e) fun x hx => h (e x) (by simpa using hx)

/-- A renamed DRS is verified iff the original is under the precomposed
embedding, given the transport for each of its conditions. -/
private theorem realize_map_all (e : V ≃ W) (K : DRS L V) (g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M, (c.map e).Realize u ↔ c.Realize (u ∘ e)) :
    (K.map e).Realize g ↔ K.Realize (g ∘ e) := by
  simp only [DRS.Realize, DRS.conditions_map, Condition.mapList_eq_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

/-- Renaming along a bijection transports verification (the condition form of
`DRS.realize_map`). -/
theorem Condition.realize_map (e : V ≃ W) : ∀ (c : Condition L V) (f : W → M),
    (c.map e).Realize f ↔ c.Realize (f ∘ e)
  | .rel R args, f => by
    simp [Condition.map, Function.comp]
  | .eq a b, f => by
    simp [Condition.map, Function.comp]
  | .neg K, f => by
    have hK := fun g : W → M =>
      realize_map_all e K g (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_neg, DRS.Extends, DRS.referents_map]
    exact not_congr ((exists_congr fun g => and_congr_right fun _ => hK g).trans
      (exists_precomp_extend_iff e K.referents f K.Realize))
  | .imp a c, f => by
    have hA := fun g : W → M =>
      realize_map_all e a g (fun d hd u => Condition.realize_map e d u)
    have hC := fun g : W → M =>
      realize_map_all e c g (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_imp, DRS.Extends, DRS.referents_map]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr (hA g)
      ((exists_congr fun h => and_congr_right fun _ => hC h).trans
        (exists_precomp_extend_iff e c.referents g c.Realize))) ?_
    exact forall_precomp_extend_iff e a.referents f
      (fun u => a.Realize u → ∃ w'', (∀ x ∉ c.referents, w'' x = u x) ∧ c.Realize w'')
  | .dis l r, f => by
    have hL := fun g : W → M =>
      realize_map_all e l g (fun d hd u => Condition.realize_map e d u)
    have hR := fun g : W → M =>
      realize_map_all e r g (fun d hd u => Condition.realize_map e d u)
    simp only [Condition.map, Condition.realize_dis, DRS.Extends, DRS.referents_map]
    exact or_congr
      ((exists_congr fun g => and_congr_right fun _ => hL g).trans
        (exists_precomp_extend_iff e l.referents f l.Realize))
      ((exists_congr fun g => and_congr_right fun _ => hR g).trans
        (exists_precomp_extend_iff e r.referents f r.Realize))
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming along a bijection transports verification: `f` verifies `K.map e`
iff `f ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem DRS.realize_map (e : V ≃ W) (K : DRS L V) (f : W → M) :
    (K.map e).Realize f ↔ K.Realize (f ∘ e) :=
  realize_map_all e K f (fun c _ u => Condition.realize_map e c u)

end Map

end DRT
