import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

[kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering, over a
mathlib `FirstOrder.Language.Structure`. An *embedding function*
`f : Embedding V M` assigns discourse referents to individuals in the model;
`DRS.Extends K f g` is K&R's extension relation `f [K] g` (both in
`DRS/Basic.lean`); `f.Verifies K` says the embedding `f` *verifies* the DRS
`K` — it verifies every condition of `K` — and `f.VerifiesCond c` that it
verifies the DRS-condition `c`. A sub-DRS is entered by existentially
(re)assigning along its extension relation. For `imp`, the consequent witness
extends the *antecedent* embedding, not the host one — antecedent referents
stay visible in the consequent, the `⇒` accessibility asymmetry. The atomic
and `¬` clauses are Def. 1.4.4(ii); the `⇒`/`∨` clauses are the Chapter 2
conditional and disjunction semantics. Truth (Def. 1.4.5) is the existential
closure of verification over the outer universe; it is delivered downstream
as `DRS.trueRel` (`DRS/Dynamics.lean`) and as the first-order translation's
realization (`DRS/Reduction.lean`).

**Deviation** ([muskens-1996], fn. 4): K&R's embeddings are *partial* functions
that sub-DRSs strictly *extend*, so a re-declared referent keeps its value; here
embeddings are total and a re-declared referent is freely reassigned. The two
agree on DRSs that declare each referent once — the construction algorithm never
re-declares — but diverge on re-declaration: `[ | [x | man x] ⇒ [x | mortal x]]`
says "every man is mortal" for K&R, "if there is a man there is a mortal" here.

## Main declarations

* `Embedding.Verifies` / `Embedding.VerifiesCond` — `f.Verifies K` is the
  field's "`f` verifies `K`": `f` verifies every condition of `K`
  (`∀ c ∈ K.conditions`, the `Theory.Model` idiom — no mutual recursion, no
  list helper).
* `Embedding.verifies_perm` — verification reads the condition list as a set,
  cashing the `List`-representation note in `DRS/Defs.lean`.
* `Embedding.verifies_map` — renaming along a bijection transports
  verification: alphabetic variants (Def. 1.4.8, via `DRS.map` in
  `DRS/Basic.lean`) have the same semantics.

## Implementation notes

`VerifiesCond` descends into sub-DRSs through the nested
`List (Condition L V)` by well-founded recursion on `sizeOf`, so its clause
characterizations (`verifies_neg`, …) are equation-lemma rewrites rather than
`Iff.rfl`; they restate the clauses with `Verifies` of the sub-DRS, as the
textbook states them.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-- `f.VerifiesCond c`: the embedding `f` *verifies* the DRS-condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along
its extension relation and verifying each of its conditions. -/
def Embedding.VerifiesCond : Embedding V M → Condition L V → Prop
  | f, .rel R args => Structure.RelMap R (fun i => f (args i))
  | f, .eq a b => f a = f b
  | f, .neg K => ¬ ∃ g, K.Extends f g ∧ ∀ c ∈ K.conditions, g.VerifiesCond c
  | f, .imp a c =>
      ∀ g, a.Extends f g → (∀ d ∈ a.conditions, g.VerifiesCond d) →
        ∃ h, c.Extends g h ∧ ∀ d ∈ c.conditions, h.VerifiesCond d
  | f, .dis l r =>
      (∃ g, l.Extends f g ∧ ∀ c ∈ l.conditions, g.VerifiesCond c) ∨
      (∃ g, r.Extends f g ∧ ∀ c ∈ r.conditions, g.VerifiesCond c)
termination_by _ c => sizeOf c
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- `f.Verifies K`: the embedding `f` *verifies* the DRS `K` — `f` verifies
every condition of `K` (Def. 1.4.4). -/
def Embedding.Verifies (f : Embedding V M) (K : DRS L V) : Prop :=
  ∀ c ∈ K.conditions, f.VerifiesCond c

namespace Embedding

/-! ### Structural simp API -/

variable {f : Embedding V M}

@[simp] theorem verifies_mk (U : Finset V) (conds : List (Condition L V)) :
    f.Verifies (.mk U conds) ↔ ∀ c ∈ conds, f.VerifiesCond c := Iff.rfl

theorem verifies_iff {K : DRS L V} :
    f.Verifies K ↔ ∀ c ∈ K.conditions, f.VerifiesCond c := Iff.rfl

@[simp] theorem verifies_empty : f.Verifies (.empty : DRS L V) := by
  simp [DRS.empty]

@[simp] theorem verifies_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    f.Verifies (K₁.merge K₂) ↔ f.Verifies K₁ ∧ f.Verifies K₂ := by
  simp only [verifies_iff, DRS.conditions_merge, List.forall_mem_append]

@[simp] theorem verifies_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    f.VerifiesCond (.rel R args) ↔ Structure.RelMap R (fun i => f (args i)) := by
  simp only [VerifiesCond]

@[simp] theorem verifies_eq (a b : V) :
    f.VerifiesCond (.eq a b : Condition L V) ↔ f a = f b := by
  simp only [VerifiesCond]

@[simp] theorem verifies_neg (K : DRS L V) :
    f.VerifiesCond (.neg K) ↔ ¬ ∃ g, K.Extends f g ∧ g.Verifies K := by
  simp only [VerifiesCond, Verifies]

@[simp] theorem verifies_imp (a c : DRS L V) :
    f.VerifiesCond (.imp a c) ↔
      ∀ g, a.Extends f g → g.Verifies a →
        ∃ h, c.Extends g h ∧ h.Verifies c := by
  simp only [VerifiesCond, Verifies]

@[simp] theorem verifies_dis (l r : DRS L V) :
    f.VerifiesCond (.dis l r) ↔
      (∃ g, l.Extends f g ∧ g.Verifies l) ∨
      (∃ g, r.Extends f g ∧ g.Verifies r) := by
  simp only [VerifiesCond, Verifies]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem verifies_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    f.Verifies (.mk U cs) ↔ f.Verifies (.mk U ds) := by
  simp only [verifies_mk, h.mem_iff]

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

/-- Precomposition with `e` is a bijection between the embeddings extending `f`
on `U.image e` and those extending `f ∘ e` on `U`. -/
private theorem exists_precomp_extend_iff (e : V ≃ W) (U : Finset V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∃ g : Embedding W M, (∀ y ∉ U.image e, g y = f y) ∧ P (g ∘ e)) ↔
      ∃ w' : Embedding V M, (∀ x ∉ U, w' x = f (e x)) ∧ P w' := by
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
private theorem forall_precomp_extend_iff (e : V ≃ W) (U : Finset V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∀ g : Embedding W M, (∀ y ∉ U.image e, g y = f y) → P (g ∘ e)) ↔
      ∀ w' : Embedding V M, (∀ x ∉ U, w' x = f (e x)) → P w' := by
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
private theorem verifies_map_all (e : V ≃ W) (K : DRS L V) (g : Embedding W M)
    (ih : ∀ c ∈ K.conditions, ∀ u : Embedding W M,
      u.VerifiesCond (c.map e) ↔ VerifiesCond (u ∘ e) c) :
    g.Verifies (K.map e) ↔ Verifies (g ∘ e) K := by
  simp only [Verifies, DRS.conditions_map, Condition.mapList_eq_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

/-- Renaming along a bijection transports verification (the condition form of
`verifies_map`). -/
theorem verifies_map_cond (e : V ≃ W) : ∀ (f : Embedding W M) (c : Condition L V),
    f.VerifiesCond (c.map e) ↔ VerifiesCond (f ∘ e) c
  | f, .rel R args => by
    simp [Condition.map, Function.comp]
  | f, .eq a b => by
    simp [Condition.map, Function.comp]
  | f, .neg K => by
    have hK := fun g : Embedding W M =>
      verifies_map_all e K g (fun d hd u => verifies_map_cond e u d)
    simp only [Condition.map, verifies_neg, DRS.Extends, DRS.referents_map]
    exact not_congr ((exists_congr fun g => and_congr_right fun _ => hK g).trans
      (exists_precomp_extend_iff e K.referents f (Verifies · K)))
  | f, .imp a c => by
    have hA := fun g : Embedding W M =>
      verifies_map_all e a g (fun d hd u => verifies_map_cond e u d)
    have hC := fun g : Embedding W M =>
      verifies_map_all e c g (fun d hd u => verifies_map_cond e u d)
    simp only [Condition.map, verifies_imp, DRS.Extends, DRS.referents_map]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr (hA g)
      ((exists_congr fun h => and_congr_right fun _ => hC h).trans
        (exists_precomp_extend_iff e c.referents g (Verifies · c)))) ?_
    exact forall_precomp_extend_iff e a.referents f
      (fun u => Verifies u a →
        ∃ w'', (∀ x ∉ c.referents, w'' x = u x) ∧ Verifies w'' c)
  | f, .dis l r => by
    have hL := fun g : Embedding W M =>
      verifies_map_all e l g (fun d hd u => verifies_map_cond e u d)
    have hR := fun g : Embedding W M =>
      verifies_map_all e r g (fun d hd u => verifies_map_cond e u d)
    simp only [Condition.map, verifies_dis, DRS.Extends, DRS.referents_map]
    exact or_congr
      ((exists_congr fun g => and_congr_right fun _ => hL g).trans
        (exists_precomp_extend_iff e l.referents f (Verifies · l)))
      ((exists_congr fun g => and_congr_right fun _ => hR g).trans
        (exists_precomp_extend_iff e r.referents f (Verifies · r)))
termination_by _ c => sizeOf c
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming along a bijection transports verification: `f` verifies `K.map e`
iff `f ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem verifies_map (e : V ≃ W) (f : Embedding W M) (K : DRS L V) :
    f.Verifies (K.map e) ↔ Verifies (f ∘ e) K :=
  verifies_map_all e K f (fun c _ u => verifies_map_cond e u c)

end Map

end Embedding

end DRT
