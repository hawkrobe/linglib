import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

DRS verification via *embeddings* into a mathlib `FirstOrder.Language.Structure`
— [kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering. An
embedding is an assignment `f : V → M` of discourse referents to the model
domain; `DRS.Extends K f g` is K&R's extension relation `f [K] g`
(`DRS/Basic.lean`), and a sub-DRS is entered by existentially (re)assigning
along it. For `imp`, the consequent witness extends the *antecedent*
embedding, not the host one — antecedent referents stay visible in the
consequent, the `⇒` accessibility asymmetry. The atomic and `¬` clauses are
Def. 1.4.4(ii); the `⇒`/`∨` clauses are the Chapter 2 conditional and
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

* `DRS.Verifies` / `Condition.Verifies` — `Verifies f K` is the field's
  "`f` verifies `K`": every condition of `K` holds under `f`
  (`∀ c ∈ K.conditions`, the `Theory.Model` idiom — no mutual recursion, no
  list helper).
* `DRS.verifies_perm` — verification reads the condition list as a set, cashing
  the `List`-representation note in `DRS/Defs.lean`.
* `DRS.verifies_map` — renaming along a bijection transports verification:
  alphabetic variants (Def. 1.4.8, via `DRS.map` in `DRS/Basic.lean`) have the
  same semantics.

## Implementation notes

`Condition.Verifies` recurses into sub-DRSs through the nested
`List (Condition L V)` by well-founded recursion on `sizeOf`, so its clause
characterizations (`verifies_neg`, …) are equation-lemma rewrites rather than
`Iff.rfl`; they restate the clauses with `DRS.Verifies`, as the textbook
states them.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-- `Condition.Verifies f c`: the embedding `f` *verifies* the condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along
its extension relation and verifying each of its conditions. -/
def Condition.Verifies : (V → M) → Condition L V → Prop
  | f, .rel R args => Structure.RelMap R (fun i => f (args i))
  | f, .eq a b => f a = f b
  | f, .neg K => ¬ ∃ g, K.Extends f g ∧ ∀ c ∈ K.conditions, Condition.Verifies g c
  | f, .imp a c =>
      ∀ g, a.Extends f g → (∀ d ∈ a.conditions, Condition.Verifies g d) →
        ∃ h, c.Extends g h ∧ ∀ d ∈ c.conditions, Condition.Verifies h d
  | f, .dis l r =>
      (∃ g, l.Extends f g ∧ ∀ c ∈ l.conditions, Condition.Verifies g c) ∨
      (∃ g, r.Extends f g ∧ ∀ c ∈ r.conditions, Condition.Verifies g c)
termination_by f c => sizeOf c
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- `DRS.Verifies f K`: the embedding `f` *verifies* `K` — `f` verifies every
condition of `K` (Def. 1.4.4). -/
def DRS.Verifies (f : V → M) (K : DRS L V) : Prop :=
  ∀ c ∈ K.conditions, Condition.Verifies f c

/-! ### Structural simp API -/

variable {f : V → M}

@[simp] theorem DRS.verifies_mk (U : Finset V) (conds : List (Condition L V)) :
    DRS.Verifies f (.mk U conds) ↔ ∀ c ∈ conds, Condition.Verifies f c := Iff.rfl

@[simp] theorem Condition.verifies_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    Condition.Verifies f (.rel R args) ↔ Structure.RelMap R (fun i => f (args i)) := by
  simp only [Condition.Verifies]

@[simp] theorem Condition.verifies_eq (a b : V) :
    Condition.Verifies f (.eq a b : Condition L V) ↔ f a = f b := by
  simp only [Condition.Verifies]

@[simp] theorem Condition.verifies_neg (K : DRS L V) :
    Condition.Verifies f (.neg K) ↔ ¬ ∃ g, K.Extends f g ∧ DRS.Verifies g K := by
  simp only [Condition.Verifies, DRS.Verifies]

@[simp] theorem Condition.verifies_imp (a c : DRS L V) :
    Condition.Verifies f (.imp a c) ↔
      ∀ g, a.Extends f g → DRS.Verifies g a →
        ∃ h, c.Extends g h ∧ DRS.Verifies h c := by
  simp only [Condition.Verifies, DRS.Verifies]

@[simp] theorem Condition.verifies_dis (l r : DRS L V) :
    Condition.Verifies f (.dis l r) ↔
      (∃ g, l.Extends f g ∧ DRS.Verifies g l) ∨
      (∃ g, r.Extends f g ∧ DRS.Verifies g r) := by
  simp only [Condition.Verifies, DRS.Verifies]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem DRS.verifies_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    DRS.Verifies f (.mk U cs) ↔ DRS.Verifies f (.mk U ds) := by
  simp only [DRS.verifies_mk, h.mem_iff]

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

/-- An embedding verifies a renamed DRS iff its precomposition verifies the
original, given the transport for each of the DRS's conditions. -/
private theorem verifies_map_all (e : V ≃ W) (K : DRS L V) (g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      Condition.Verifies u (c.map e) ↔ Condition.Verifies (u ∘ e) c) :
    DRS.Verifies g (K.map e) ↔ DRS.Verifies (g ∘ e) K := by
  simp only [DRS.Verifies, DRS.conditions_map, Condition.mapList_eq_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

/-- Renaming along a bijection transports verification (the condition form of
`DRS.verifies_map`). -/
theorem Condition.verifies_map (e : V ≃ W) : ∀ (f : W → M) (c : Condition L V),
    Condition.Verifies f (c.map e) ↔ Condition.Verifies (f ∘ e) c
  | f, .rel R args => by
    simp [Condition.map, Function.comp]
  | f, .eq a b => by
    simp [Condition.map, Function.comp]
  | f, .neg K => by
    have hK := fun g : W → M =>
      verifies_map_all e K g (fun d hd u => Condition.verifies_map e u d)
    simp only [Condition.map, Condition.verifies_neg, DRS.Extends, DRS.referents_map]
    exact not_congr ((exists_congr fun g => and_congr_right fun _ => hK g).trans
      (exists_precomp_extend_iff e K.referents f (DRS.Verifies · K)))
  | f, .imp a c => by
    have hA := fun g : W → M =>
      verifies_map_all e a g (fun d hd u => Condition.verifies_map e u d)
    have hC := fun g : W → M =>
      verifies_map_all e c g (fun d hd u => Condition.verifies_map e u d)
    simp only [Condition.map, Condition.verifies_imp, DRS.Extends, DRS.referents_map]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr (hA g)
      ((exists_congr fun h => and_congr_right fun _ => hC h).trans
        (exists_precomp_extend_iff e c.referents g (DRS.Verifies · c)))) ?_
    exact forall_precomp_extend_iff e a.referents f
      (fun u => DRS.Verifies u a →
        ∃ w'', (∀ x ∉ c.referents, w'' x = u x) ∧ DRS.Verifies w'' c)
  | f, .dis l r => by
    have hL := fun g : W → M =>
      verifies_map_all e l g (fun d hd u => Condition.verifies_map e u d)
    have hR := fun g : W → M =>
      verifies_map_all e r g (fun d hd u => Condition.verifies_map e u d)
    simp only [Condition.map, Condition.verifies_dis, DRS.Extends, DRS.referents_map]
    exact or_congr
      ((exists_congr fun g => and_congr_right fun _ => hL g).trans
        (exists_precomp_extend_iff e l.referents f (DRS.Verifies · l)))
      ((exists_congr fun g => and_congr_right fun _ => hR g).trans
        (exists_precomp_extend_iff e r.referents f (DRS.Verifies · r)))
termination_by f c => sizeOf c
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming along a bijection transports verification: `f` verifies `K.map e`
iff `f ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem DRS.verifies_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    DRS.Verifies f (K.map e) ↔ DRS.Verifies (f ∘ e) K :=
  verifies_map_all e K f (fun c _ u => Condition.verifies_map e u c)

end Map

end DRT
