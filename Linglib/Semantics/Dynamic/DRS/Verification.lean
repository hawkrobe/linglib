import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

[kamp-reyle-1993]'s Def. 1.4.4 in the *total-assignment* rendering, over a
mathlib `FirstOrder.Language.Structure`. An *embedding function*
`f : Embedding V M` assigns discourse referents to individuals in the model;
`Box.Extends K f g` is the extension relation `f [K] g` (both in
`DRS/Basic.lean`); `f.Verifies K` says the embedding `f` *verifies* the DRS
`K` — it verifies every condition of `K` — and `f.VerifiesCondition c` that it
verifies the DRS-condition `c`. A sub-DRS is entered by existentially
(re)assigning along its extension relation. For `imp`, the consequent witness
extends the *antecedent* embedding, not the host one — antecedent referents
stay visible in the consequent, the `⇒` accessibility asymmetry. The atomic
and `¬` clauses are Def. 1.4.4(ii); the `⇒`/`∨` clauses are the Chapter 2
conditional and disjunction semantics. Truth (Def. 1.4.5) is the existential
closure of verification over the outer universe; it is delivered downstream
as `DRS.trueRel` (`DRS/Dynamics.lean`) and as the first-order translation's
realization (`DRS/Reduction.lean`).

**Deviation** ([muskens-1996], fn. 4): the book's embeddings are *partial*
functions that sub-DRSs strictly *extend*, so a re-declared referent keeps its
value; here embeddings are total and a re-declared referent is freely
reassigned. The two agree on DRSs that declare each referent once — the
construction algorithm never re-declares — but diverge on re-declaration:
`[ | [x | man x] ⇒ [x | mortal x]]` says "every man is mortal" there, "if
there is a man there is a mortal" here.

## Main declarations

* `Embedding.Verifies` / `Embedding.VerifiesCondition` — `f.Verifies K` is the
  field's "`f` verifies `K`": `f` verifies every condition of `K`
  (`∀ c ∈ K.conditions`, the `Theory.Model` idiom — no mutual recursion, no
  list helper).
* `Embedding.verifies_perm` — verification reads the condition list as a set,
  cashing the `List`-representation note in `DRS/Defs.lean`.
* `Embedding.verifies_map` — renaming along a bijection transports
  verification: alphabetic variants (Def. 1.4.8, via `DRS.map` in
  `DRS/Basic.lean`) have the same semantics.

## Implementation notes

`VerifiesCondition` descends into sub-DRSs through the nested
`List (Condition L V)` by well-founded recursion on `sizeOf`, so its clause
characterizations (`verifies_neg`, …) are equation-lemma rewrites rather than
`Iff.rfl`; they restate the clauses with `Verifies` of the sub-DRS, as the
textbook states them.
-/

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

namespace Embedding

/-- `f.VerifiesCondition c`: the embedding `f` *verifies* the DRS-condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along
its extension relation and verifying each of its conditions. -/
def VerifiesCondition : Embedding V M → Condition L V → Prop
  | f, .rel R args => Structure.RelMap R (fun i => f (args i))
  | f, .eq a b => f a = f b
  | f, .neg K => ¬ ∃ g, K.Extends f g ∧ ∀ c ∈ K.conditions, g.VerifiesCondition c
  | f, .imp a c =>
      ∀ g, a.Extends f g → (∀ d ∈ a.conditions, g.VerifiesCondition d) →
        ∃ h, c.Extends g h ∧ ∀ d ∈ c.conditions, h.VerifiesCondition d
  | f, .dis l r =>
      (∃ g, l.Extends f g ∧ ∀ c ∈ l.conditions, g.VerifiesCondition c) ∨
      (∃ g, r.Extends f g ∧ ∀ c ∈ r.conditions, g.VerifiesCondition c)

/-- `f.Verifies K`: the embedding `f` *verifies* the DRS `K` — `f` verifies
every condition of `K` (Def. 1.4.4). -/
def Verifies (f : Embedding V M) (K : DRS L V) : Prop :=
  ∀ c ∈ K.conditions, f.VerifiesCondition c

/-! ### Structural simp API -/

variable {f : Embedding V M}

@[simp] theorem verifies_mk (U : Finset V) (conds : List (Condition L V)) :
    f.Verifies (.mk U conds) ↔ ∀ c ∈ conds, f.VerifiesCondition c := Iff.rfl

theorem verifies_iff {K : DRS L V} :
    f.Verifies K ↔ ∀ c ∈ K.conditions, f.VerifiesCondition c := Iff.rfl

@[simp] theorem verifies_empty : f.Verifies (.empty : DRS L V) := by
  simp [DRS.empty]

@[simp] theorem verifies_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    f.Verifies (K₁.merge K₂) ↔ f.Verifies K₁ ∧ f.Verifies K₂ := by
  simp only [verifies_iff, DRS.conditions_merge, List.forall_mem_append]

@[simp] theorem verifies_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    f.VerifiesCondition (.rel R args) ↔ Structure.RelMap R (fun i => f (args i)) := by
  simp only [VerifiesCondition]

@[simp] theorem verifies_eq (a b : V) :
    f.VerifiesCondition (.eq a b : Condition L V) ↔ f a = f b := by
  simp only [VerifiesCondition]

@[simp] theorem verifies_neg (K : DRS L V) :
    f.VerifiesCondition (.neg K) ↔ ¬ ∃ g, K.Extends f g ∧ g.Verifies K := by
  simp only [VerifiesCondition, Verifies]

@[simp] theorem verifies_imp (a c : DRS L V) :
    f.VerifiesCondition (.imp a c) ↔
      ∀ g, a.Extends f g → g.Verifies a →
        ∃ h, c.Extends g h ∧ h.Verifies c := by
  simp only [VerifiesCondition, Verifies]

@[simp] theorem verifies_dis (l r : DRS L V) :
    f.VerifiesCondition (.dis l r) ↔
      (∃ g, l.Extends f g ∧ g.Verifies l) ∨
      (∃ g, r.Extends f g ∧ g.Verifies r) := by
  simp only [VerifiesCondition, Verifies]

/-- Verification is invariant under permutation of the conditions — the set
semantics the `List`-valued `conditions` field promises (`DRS/Defs.lean`). -/
theorem verifies_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    f.Verifies (.mk U cs) ↔ f.Verifies (.mk U ds) := by
  simp only [verifies_mk, h.mem_iff]

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

/-- An embedding verifies a renamed DRS iff its precomposition verifies the
original, given the transport for each of the DRS's conditions. -/
private theorem verifies_map_all (e : V ≃ W) (K : DRS L V) (g : Embedding W M)
    (ih : ∀ c ∈ K.conditions, ∀ u : Embedding W M,
      u.VerifiesCondition (c.map e) ↔ VerifiesCondition (u ∘ e) c) :
    g.Verifies (K.map e) ↔ Verifies (g ∘ e) K := by
  simp only [Verifies, DRS.conditions_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

/-- "Some extension of `f` verifies `K`" transported along renaming, given the
transport for each condition of `K`. -/
private theorem exists_extends_verifies_map_aux (e : V ≃ W) (K : DRS L V) (f : Embedding W M)
    (ih : ∀ c ∈ K.conditions, ∀ u : Embedding W M,
      u.VerifiesCondition (c.map e) ↔ VerifiesCondition (u ∘ e) c) :
    (∃ g, (K.map e).Extends f g ∧ g.Verifies (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ g.Verifies K :=
  (exists_congr fun g => and_congr_right fun _ => verifies_map_all e K g ih).trans
    (DRS.exists_extends_map e K f (Verifies · K))

/-- Renaming along a bijection transports verification (the condition form of
`verifies_map`). -/
theorem verifies_map_condition (e : V ≃ W) (f : Embedding W M) (c : Condition L V) :
    f.VerifiesCondition (c.map e) ↔ VerifiesCondition (f ∘ e) c := by
  induction c generalizing f with
  | rel R args => simp [Condition.map, Function.comp]
  | eq a b => simp [Condition.map, Function.comp]
  | neg K ih =>
    simp only [Condition.map, verifies_neg]
    exact not_congr (exists_extends_verifies_map_aux e K f ih)
  | imp a c iha ihc =>
    simp only [Condition.map, verifies_imp]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr
      (verifies_map_all e a g iha) (exists_extends_verifies_map_aux e c g ihc)) ?_
    exact DRS.forall_extends_map e a f
      (fun u => Verifies u a → ∃ h', c.Extends u h' ∧ Verifies h' c)
  | dis l r ihl ihr =>
    simp only [Condition.map, verifies_dis]
    exact or_congr (exists_extends_verifies_map_aux e l f ihl)
      (exists_extends_verifies_map_aux e r f ihr)

/-- Renaming along a bijection transports verification: `f` verifies `K.map e`
iff `f ∘ e` verifies `K` — alphabetic variants have the same semantics. -/
theorem verifies_map (e : V ≃ W) (f : Embedding W M) (K : DRS L V) :
    f.Verifies (K.map e) ↔ Verifies (f ∘ e) K :=
  verifies_map_all e K f (fun c _ u => verifies_map_condition e u c)

/-- "Some extension verifies", transported along renaming: `f` has a verifying
`K.map e`-extension iff `f ∘ e` has a verifying `K`-extension. -/
theorem exists_extends_verifies_map (e : V ≃ W) (f : Embedding W M) (K : DRS L V) :
    (∃ g, (K.map e).Extends f g ∧ g.Verifies (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ g.Verifies K :=
  (exists_congr fun g => and_congr_right fun _ => verifies_map e g K).trans
    (DRS.exists_extends_map e K f (Verifies · K))

end Map

/-! ### Coincidence -/

section Coincidence

variable [DecidableEq V]

/-- "Some extension of `f₁` verifies `K`" survives changing `f₁` at
non-occurring referents, given coincidence for each condition of `K`. -/
private theorem exists_extends_verifies_congr_aux (K : DRS L V) {f₁ f₂ : Embedding V M}
    (h : Set.EqOn f₁ f₂ ↑K.occ)
    (ih : ∀ c ∈ K.conditions, ∀ {g₁ g₂ : Embedding V M},
      Set.EqOn g₁ g₂ ↑(Condition.occ c) → (g₁.VerifiesCondition c ↔ g₂.VerifiesCondition c)) :
    (∃ g, K.Extends f₁ g ∧ g.Verifies K) → ∃ g, K.Extends f₂ g ∧ g.Verifies K := by
  obtain ⟨U, conds⟩ := K
  rintro ⟨g, hag, hh⟩
  refine ⟨(Condition.occL conds).piecewise g f₂, ?_, ?_⟩
  · intro x hx
    by_cases hxc : x ∈ Condition.occL conds
    · rw [Finset.piecewise_eq_of_mem _ _ _ hxc, hag x hx]
      refine h ?_
      simp only [DRS.occ, Finset.coe_union]
      exact Or.inr (Finset.mem_coe.mpr hxc)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hxc]
  · intro c hc
    refine (ih c hc (g₂ := g) fun x hx => ?_).mpr (hh c hc)
    exact Finset.piecewise_eq_of_mem _ _ _
      (Condition.occ_subset_occL hc (Finset.mem_coe.mp hx))

/-- Verification of a condition reads the embedding only at its occurring
referents. -/
theorem verifiesCondition_congr (c : Condition L V) {f₁ f₂ : Embedding V M}
    (h : Set.EqOn f₁ f₂ ↑(Condition.occ c)) :
    f₁.VerifiesCondition c ↔ f₂.VerifiesCondition c := by
  induction c generalizing f₁ f₂ with
  | rel R args =>
    simp only [verifies_rel]
    rw [show (fun i => f₁ (args i)) = fun i => f₂ (args i) from
      funext fun i => h (by simp)]
  | eq a b =>
    simp only [verifies_eq]
    rw [h (show a ∈ ↑(Condition.occ (.eq a b : Condition L V)) by simp),
      h (show b ∈ ↑(Condition.occ (.eq a b : Condition L V)) by simp)]
  | neg K ih =>
    simp only [verifies_neg]
    rw [Condition.occ_neg] at h
    exact not_congr ⟨exists_extends_verifies_congr_aux K h ih,
      exists_extends_verifies_congr_aux K h.symm ih⟩
  | imp a c iha ihc =>
    simp only [verifies_imp]
    rw [Condition.occ_imp] at h
    have key : ∀ b₁ b₂ : Embedding V M,
        Set.EqOn b₁ b₂ ↑(DRS.occ a ∪ DRS.occ c) →
        (∀ g, a.Extends b₁ g → g.Verifies a →
          ∃ h', c.Extends g h' ∧ h'.Verifies c) →
        ∀ g, a.Extends b₂ g → g.Verifies a →
          ∃ h', c.Extends g h' ∧ h'.Verifies c := by
      rintro b₁ b₂ hb hL g hag hv
      have hpg : Set.EqOn ((DRS.occ a ∪ DRS.occ c).piecewise g b₁) g ↑(DRS.occ a) :=
        fun x hx =>
          Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_union_left _ (Finset.mem_coe.mp hx))
      have hExt : a.Extends b₁ ((DRS.occ a ∪ DRS.occ c).piecewise g b₁) := by
        intro x hx
        by_cases hxS : x ∈ DRS.occ a ∪ DRS.occ c
        · rw [Finset.piecewise_eq_of_mem _ _ _ hxS, hag x hx]
          exact (hb (Finset.mem_coe.mpr hxS)).symm
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hxS]
      have hVer : Verifies ((DRS.occ a ∪ DRS.occ c).piecewise g b₁) a := fun d hd =>
        (iha d hd (hpg.mono (Finset.coe_subset.mpr
          ((Condition.occ_subset_occL hd).trans (DRS.occL_subset_occ a))))).mpr (hv d hd)
      obtain ⟨h', hch', hvh'⟩ := hL _ hExt hVer
      have hpc : Set.EqOn ((DRS.occ a ∪ DRS.occ c).piecewise g b₁) g ↑(DRS.occ c) :=
        fun x hx =>
          Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_union_right _ (Finset.mem_coe.mp hx))
      exact exists_extends_verifies_congr_aux c hpc ihc ⟨h', hch', hvh'⟩
    exact ⟨key f₁ f₂ h, key f₂ f₁ h.symm⟩
  | dis l r ihl ihr =>
    simp only [verifies_dis]
    have hl : Set.EqOn f₁ f₂ ↑(DRS.occ l) :=
      h.mono (by simp only [Condition.occ_dis, Finset.coe_union]; exact Set.subset_union_left)
    have hr : Set.EqOn f₁ f₂ ↑(DRS.occ r) :=
      h.mono (by simp only [Condition.occ_dis, Finset.coe_union]; exact Set.subset_union_right)
    exact or_congr
      ⟨exists_extends_verifies_congr_aux l hl ihl,
       exists_extends_verifies_congr_aux l hl.symm ihl⟩
      ⟨exists_extends_verifies_congr_aux r hr ihr,
       exists_extends_verifies_congr_aux r hr.symm ihr⟩

/-- Verification reads the embedding only at the DRS's occurring referents. -/
theorem verifies_congr {K : DRS L V} {f₁ f₂ : Embedding V M}
    (h : Set.EqOn f₁ f₂ ↑K.occ) : f₁.Verifies K ↔ f₂.Verifies K := by
  simp only [verifies_iff]
  exact forall_congr' fun c => imp_congr_right fun hc =>
    verifiesCondition_congr c (h.mono (Finset.coe_subset.mpr
      ((Condition.occ_subset_occL hc).trans (DRS.occL_subset_occ K))))

/-- "Some extension verifies" reads the input embedding only at the occurring
referents. -/
theorem exists_extends_verifies_congr {K : DRS L V} {f₁ f₂ : Embedding V M}
    (h : Set.EqOn f₁ f₂ ↑K.occ) :
    (∃ g, K.Extends f₁ g ∧ g.Verifies K) ↔ ∃ g, K.Extends f₂ g ∧ g.Verifies K :=
  ⟨exists_extends_verifies_congr_aux K h fun c _ => verifiesCondition_congr c,
   exists_extends_verifies_congr_aux K h.symm fun c _ => verifiesCondition_congr c⟩

end Coincidence

end Embedding

end DRT
