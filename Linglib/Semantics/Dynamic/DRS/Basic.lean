import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.Data.Finset.Image

/-!
# Structural operations on DRSs

This file develops the structural theory of the `DRS` type of `DRS/Defs.lean`:
functorial renaming of discourse referents (`DRS.map`), the merge algebra,
embedding functions (`Embedding`) with the extension relation `f [K] g`
(`Box.Extends`), and the referent predicates `occ`, `fv` and `IsProper`,
`ReuseFreeAt`, and `Accessible`. Renaming along a bijection is
[kamp-reyle-1993]'s *alphabetic variant* (the prose preceding Def. 1.4.8).
-/

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x}

/-! ### Functorial renaming -/

/-- Rename discourse referents along `f` throughout a condition. -/
def Condition.map [DecidableEq W] (f : V → W) : Condition L V → Condition L W
  | .rel R args => .rel R (fun i => f (args i))
  | .eq a b => .eq (f a) (f b)
  | .neg K => .neg ⟨K.referents.image f, K.conditions.map (Condition.map f)⟩
  | .imp a c =>
      .imp ⟨a.referents.image f, a.conditions.map (Condition.map f)⟩
        ⟨c.referents.image f, c.conditions.map (Condition.map f)⟩
  | .dis l r =>
      .dis ⟨l.referents.image f, l.conditions.map (Condition.map f)⟩
        ⟨r.referents.image f, r.conditions.map (Condition.map f)⟩
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Rename discourse referents along `f : V → W` throughout a DRS. -/
def DRS.map [DecidableEq W] (f : V → W) (K : DRS L V) : DRS L W :=
  ⟨K.referents.image f, K.conditions.map (Condition.map f)⟩

@[simp] theorem DRS.referents_map [DecidableEq W] (f : V → W) (K : DRS L V) :
    (K.map f).referents = K.referents.image f := rfl

@[simp] theorem DRS.conditions_map [DecidableEq W] (f : V → W) (K : DRS L V) :
    (K.map f).conditions = K.conditions.map (Condition.map f) := rfl

/-- Renaming a condition along the identity is the identity. -/
@[simp] theorem Condition.map_id [DecidableEq V] : ∀ c : Condition L V, Condition.map id c = c
  | .rel R args => by simp only [Condition.map, id_eq]
  | .eq a b => by simp only [Condition.map, id_eq]
  | .neg K => by
    have ih : ∀ d ∈ K.conditions, Condition.map id d = d := fun d _ => Condition.map_id d
    simp only [Condition.map, Finset.image_id, List.map_congr_left ih, List.map_id']
  | .imp a c => by
    have iha : ∀ d ∈ a.conditions, Condition.map id d = d := fun d _ => Condition.map_id d
    have ihc : ∀ d ∈ c.conditions, Condition.map id d = d := fun d _ => Condition.map_id d
    simp only [Condition.map, Finset.image_id, List.map_congr_left iha,
      List.map_congr_left ihc, List.map_id']
  | .dis l r => by
    have ihl : ∀ d ∈ l.conditions, Condition.map id d = d := fun d _ => Condition.map_id d
    have ihr : ∀ d ∈ r.conditions, Condition.map id d = d := fun d _ => Condition.map_id d
    simp only [Condition.map, Finset.image_id, List.map_congr_left ihl,
      List.map_congr_left ihr, List.map_id']
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming a DRS along the identity is the identity. -/
@[simp] theorem DRS.map_id [DecidableEq V] (K : DRS L V) : DRS.map id K = K := by
  obtain ⟨U, conds⟩ := K
  have ih : ∀ d ∈ conds, Condition.map id d = d := fun d _ => Condition.map_id d
  simp only [DRS.map, Finset.image_id, List.map_congr_left ih, List.map_id']

variable {X : Type*}

/-- Renaming a condition along a composite is the composite of the renamings. -/
theorem Condition.map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W) :
    ∀ c : Condition L V, Condition.map g (Condition.map f c) = Condition.map (g ∘ f) c
  | .rel R args => by simp only [Condition.map]; rfl
  | .eq a b => by simp only [Condition.map]; rfl
  | .neg K => by
    have ih : ∀ d ∈ K.conditions,
        (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
      fun d _ => Condition.map_map g f d
    simp only [Condition.map, Finset.image_image, List.map_map, List.map_congr_left ih]
  | .imp a c => by
    have iha : ∀ d ∈ a.conditions,
        (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
      fun d _ => Condition.map_map g f d
    have ihc : ∀ d ∈ c.conditions,
        (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
      fun d _ => Condition.map_map g f d
    simp only [Condition.map, Finset.image_image, List.map_map, List.map_congr_left iha,
      List.map_congr_left ihc]
  | .dis l r => by
    have ihl : ∀ d ∈ l.conditions,
        (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
      fun d _ => Condition.map_map g f d
    have ihr : ∀ d ∈ r.conditions,
        (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
      fun d _ => Condition.map_map g f d
    simp only [Condition.map, Finset.image_image, List.map_map, List.map_congr_left ihl,
      List.map_congr_left ihr]
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Renaming a DRS along a composite is the composite of the renamings. -/
theorem DRS.map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W) (K : DRS L V) :
    DRS.map g (DRS.map f K) = DRS.map (g ∘ f) K := by
  have ih : ∀ d ∈ K.conditions,
      (Condition.map g ∘ Condition.map f) d = Condition.map (g ∘ f) d :=
    fun d _ => Condition.map_map g f d
  simp only [DRS.map, Finset.image_image, List.map_map, List.map_congr_left ih]

/-! ### Merge algebra -/

namespace DRS

variable [DecidableEq V]

@[simp] theorem empty_merge (K : DRS L V) : (empty : DRS L V).merge K = K := by
  cases K with
  | mk r c => simp [merge, empty]

@[simp] theorem merge_empty (K : DRS L V) : K.merge (empty : DRS L V) = K := by
  cases K with
  | mk r c => simp [merge, empty]

theorem merge_assoc (K₁ K₂ K₃ : DRS L V) :
    (K₁.merge K₂).merge K₃ = K₁.merge (K₂.merge K₃) := by
  cases K₁; cases K₂; cases K₃
  simp only [merge, referents_mk, conditions_mk]
  rw [Finset.union_assoc, List.append_assoc]

end DRS

/-! ### Embeddings and the extension relation -/

/-- An *embedding function*: an assignment of discourse referents to
individuals in a given model, in the total-assignment rendering (deviation
note in `DRS/Verification.lean`). `M` is the model's domain of individuals;
the model itself — `M` together with an interpretation of the relation
symbols — is the `L.Structure M` instance that verification
(`Embedding.Verifies`) requires, so embeddings and the extension relation
need no model theory, while `f.Verifies K` only exists in a given model. -/
abbrev Embedding (V : Type w) (M : Type*) := V → M

section Extends

variable {M : Type*} {C : Type x}

/-- `K.Extends f g` (written `f [K] g`): the output embedding `g` differs from
the input `f` at most on `K`'s universe — the total-assignment rendering of
"`f ⊆ g` and `Dom g = Dom f ∪ U_K`". Stated for any box, since only the
universe is read. -/
def Box.Extends (K : Box V C) (f g : Embedding V M) : Prop := ∀ x ∉ K.referents, g x = f x

/-- Extension along a renamed DRS is extension of the precompositions. -/
theorem DRS.extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f g : Embedding W M) :
    (K.map e).Extends f g ↔ K.Extends (f ∘ e) (g ∘ e) := by
  simp only [Box.Extends, DRS.referents_map, Function.comp_apply]
  constructor
  · intro h x hx
    exact h (e x) (by simpa using hx)
  · intro h y hy
    have hx : e.symm y ∉ K.referents := fun hm =>
      hy (by simpa using Finset.mem_image_of_mem e hm)
    simpa using h (e.symm y) hx

/-- The extensions of `f` at `K.map e` are the extensions of `f ∘ e` at `K`,
via precomposition. -/
theorem DRS.exists_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∃ g, (K.map e).Extends f g ∧ P (g ∘ e)) ↔ ∃ g, K.Extends (f ∘ e) g ∧ P g := by
  simp only [DRS.extends_map]
  constructor
  · rintro ⟨g, hg, hp⟩
    exact ⟨g ∘ e, hg, hp⟩
  · rintro ⟨g, hg, hp⟩
    have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
    exact ⟨g ∘ e.symm, key.symm ▸ hg, key.symm ▸ hp⟩

/-- The `∀` analogue of `DRS.exists_extends_map`. -/
theorem DRS.forall_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∀ g, (K.map e).Extends f g → P (g ∘ e)) ↔ ∀ g, K.Extends (f ∘ e) g → P g := by
  simp only [DRS.extends_map]
  constructor
  · intro H g hg
    have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
    exact key ▸ H (g ∘ e.symm) (key.symm ▸ hg)
  · intro H g hg
    exact H (g ∘ e) hg

end Extends

/-! ### Occurring referents -/

section Occ
variable [DecidableEq V]

/-- Occurring referents (free or bound) in a condition, as a `Finset` — the DRS
analogue of mathlib's `Term.varFinset`. Membership `x ∈ occ c` is decidable, so
downstream consumers get decidable occurrence for free. -/
def Condition.occ : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => K.referents ∪ (K.conditions.map Condition.occ).foldr (· ∪ ·) ∅
  | .imp a c => (a.referents ∪ (a.conditions.map Condition.occ).foldr (· ∪ ·) ∅) ∪
      (c.referents ∪ (c.conditions.map Condition.occ).foldr (· ∪ ·) ∅)
  | .dis l r => (l.referents ∪ (l.conditions.map Condition.occ).foldr (· ∪ ·) ∅) ∪
      (r.referents ∪ (r.conditions.map Condition.occ).foldr (· ∪ ·) ∅)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Occurring referents in a list of conditions. -/
def Condition.occL (cs : List (Condition L V)) : Finset V :=
  (cs.map Condition.occ).foldr (· ∪ ·) ∅

/-- Occurring referents in a DRS (its universe and those of its conditions). -/
def DRS.occ (K : DRS L V) : Finset V := K.referents ∪ Condition.occL K.conditions

@[simp] theorem Condition.occL_nil : Condition.occL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem Condition.occL_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.occL (c :: cs) = c.occ ∪ Condition.occL cs := rfl
@[simp] theorem DRS.occ_mk (U : Finset V) (conds : List (Condition L V)) :
    DRS.occ ⟨U, conds⟩ = U ∪ Condition.occL conds := rfl
@[simp] theorem Condition.occ_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).occ = Finset.image args Finset.univ := by
  simp only [Condition.occ]
@[simp] theorem Condition.occ_eq (u v : V) :
    (Condition.eq u v : Condition L V).occ = {u, v} := by simp only [Condition.occ]
@[simp] theorem Condition.occ_neg (K : DRS L V) : (Condition.neg K).occ = K.occ := by
  simp only [Condition.occ]; rfl
@[simp] theorem Condition.occ_imp (a c : DRS L V) :
    (Condition.imp a c).occ = a.occ ∪ c.occ := by simp only [Condition.occ]; rfl
@[simp] theorem Condition.occ_dis (l r : DRS L V) :
    (Condition.dis l r).occ = l.occ ∪ r.occ := by simp only [Condition.occ]; rfl

@[simp] theorem Condition.occL_append (cs ds : List (Condition L V)) :
    Condition.occL (cs ++ ds) = Condition.occL cs ∪ Condition.occL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

/-- A DRS's conditions' occurring referents are among the DRS's. -/
theorem DRS.occL_subset_occ (K : DRS L V) : Condition.occL K.conditions ⊆ K.occ :=
  Finset.subset_union_right

/-- A condition's occurring referents are among its list's. -/
theorem Condition.occ_subset_occL {c : Condition L V} {cs : List (Condition L V)}
    (hc : c ∈ cs) : c.occ ⊆ Condition.occL cs := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with h | h
    · exact h ▸ Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

end Occ

/-! ### Free discourse referents and properness -/

section Fv
variable [DecidableEq V]

/-- The free discourse referents of a condition. -/
def Condition.fv : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => (K.conditions.map Condition.fv).foldr (· ∪ ·) ∅ \ K.referents
  | .imp a c => ((a.conditions.map Condition.fv).foldr (· ∪ ·) ∅ \ a.referents) ∪
      (((c.conditions.map Condition.fv).foldr (· ∪ ·) ∅ \ c.referents) \ a.referents)
  | .dis l r => ((l.conditions.map Condition.fv).foldr (· ∪ ·) ∅ \ l.referents) ∪
      ((r.conditions.map Condition.fv).foldr (· ∪ ·) ∅ \ r.referents)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Free referents of a list of conditions. -/
def Condition.fvL (cs : List (Condition L V)) : Finset V :=
  (cs.map Condition.fv).foldr (· ∪ ·) ∅

/-- The free discourse referents of a DRS: referents occurring in its
conditions and not bound by its universe or by an ancestor reachable "left
and up" (the antecedent of a `⇒` threads its referents into the consequent).
`K.fv ⊆ b` says every referent of `K` is bound in context `b`. -/
def DRS.fv (K : DRS L V) : Finset V := Condition.fvL K.conditions \ K.referents

@[simp] theorem DRS.fv_mk (U : Finset V) (conds : List (Condition L V)) :
    DRS.fv ⟨U, conds⟩ = Condition.fvL conds \ U := rfl
@[simp] theorem Condition.fv_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).fv = Finset.image args Finset.univ := by simp only [Condition.fv]
@[simp] theorem Condition.fv_eq (u v : V) :
    (Condition.eq u v : Condition L V).fv = {u, v} := by simp only [Condition.fv]
@[simp] theorem Condition.fv_neg (K : DRS L V) : (Condition.neg K).fv = K.fv := by
  simp only [Condition.fv]; rfl
@[simp] theorem Condition.fv_imp (a c : DRS L V) :
    (Condition.imp a c).fv = a.fv ∪ (c.fv \ a.referents) := by simp only [Condition.fv]; rfl
@[simp] theorem Condition.fv_dis (l r : DRS L V) :
    (Condition.dis l r).fv = l.fv ∪ r.fv := by simp only [Condition.fv]; rfl
@[simp] theorem Condition.fvL_nil : Condition.fvL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem Condition.fvL_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.fvL (c :: cs) = c.fv ∪ Condition.fvL cs := rfl

/-- The characteristic form of the referential presupposition: a box's free
referents are supplied by `X` iff its conditions' are supplied by the grown
base. -/
theorem DRS.fv_subset_iff {U X : Finset V} {conds : List (Condition L V)} :
    DRS.fv ⟨U, conds⟩ ⊆ X ↔ Condition.fvL conds ⊆ X ∪ U := by
  rw [DRS.fv_mk, sdiff_le_iff, sup_comm, Finset.sup_eq_union]

private theorem Condition.fvL_subset_occL_of_forall {cs : List (Condition L V)}
    (h : ∀ c ∈ cs, c.fv ⊆ c.occ) : Condition.fvL cs ⊆ Condition.occL cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [Condition.fvL_cons, Condition.occL_cons]
    exact Finset.union_subset_union (h c (by simp))
      (ih fun d hd => h d (List.mem_cons_of_mem c hd))

private theorem DRS.fv_subset_occ_of_forall {K : DRS L V}
    (h : ∀ c ∈ K.conditions, c.fv ⊆ c.occ) : K.fv ⊆ K.occ :=
  Finset.sdiff_subset.trans ((Condition.fvL_subset_occL_of_forall h).trans
    Finset.subset_union_right)

/-- Free referents of a condition occur. -/
theorem Condition.fv_subset_occ (c : Condition L V) : c.fv ⊆ c.occ := by
  match c with
  | .rel R args => simp
  | .eq u v => simp
  | .neg K =>
    have ih : ∀ d ∈ K.conditions, d.fv ⊆ d.occ := fun d _ => Condition.fv_subset_occ d
    simpa using DRS.fv_subset_occ_of_forall ih
  | .imp a c =>
    have iha : ∀ d ∈ a.conditions, d.fv ⊆ d.occ := fun d _ => Condition.fv_subset_occ d
    have ihc : ∀ d ∈ c.conditions, d.fv ⊆ d.occ := fun d _ => Condition.fv_subset_occ d
    simp only [Condition.fv_imp, Condition.occ_imp]
    exact Finset.union_subset_union (DRS.fv_subset_occ_of_forall iha)
      (Finset.sdiff_subset.trans (DRS.fv_subset_occ_of_forall ihc))
  | .dis l r =>
    have ihl : ∀ d ∈ l.conditions, d.fv ⊆ d.occ := fun d _ => Condition.fv_subset_occ d
    have ihr : ∀ d ∈ r.conditions, d.fv ⊆ d.occ := fun d _ => Condition.fv_subset_occ d
    simp only [Condition.fv_dis, Condition.occ_dis]
    exact Finset.union_subset_union (DRS.fv_subset_occ_of_forall ihl)
      (DRS.fv_subset_occ_of_forall ihr)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Free referents occur. -/
theorem DRS.fv_subset_occ (K : DRS L V) : K.fv ⊆ K.occ :=
  DRS.fv_subset_occ_of_forall fun c _ => Condition.fv_subset_occ c

/-- The list analogue of `Condition.fv_subset_occ`. -/
theorem Condition.fvL_subset_occL (cs : List (Condition L V)) :
    Condition.fvL cs ⊆ Condition.occL cs :=
  Condition.fvL_subset_occL_of_forall fun c _ => Condition.fv_subset_occ c

@[simp] theorem Condition.fvL_append (cs ds : List (Condition L V)) :
    Condition.fvL (cs ++ ds) = Condition.fvL cs ∪ Condition.fvL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

/-- Merging preserves boundedness: the merge's free referents are supplied by
`X` when the context's are and the increment's are supplied by the grown base. -/
theorem DRS.fv_merge_subset {X : Finset V} {K₁ K₂ : DRS L V} (h₁ : K₁.fv ⊆ X)
    (h₂ : K₂.fv ⊆ X ∪ K₁.referents) : (K₁.merge K₂).fv ⊆ X := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  rw [DRS.referents_mk] at h₂
  rw [DRS.fv_subset_iff] at h₁ h₂
  rw [DRS.merge, DRS.referents_mk, DRS.conditions_mk, DRS.fv_subset_iff,
    Condition.fvL_append, ← Finset.union_assoc]
  exact Finset.union_subset (h₁.trans Finset.subset_union_left) h₂

/-- A DRS is *proper* iff it has no free discourse referent
(Def. 1.4.2–1.4.3). -/
def DRS.IsProper (K : DRS L V) : Prop := K.fv = ∅

/-- Merging preserves properness when the increment's free referents are
supplied by the context DRS's universe. -/
theorem DRS.isProper_merge {K₁ K₂ : DRS L V} (h₁ : K₁.IsProper)
    (h₂ : K₂.fv ⊆ K₁.referents) : (K₁.merge K₂).IsProper :=
  Finset.subset_empty.mp (DRS.fv_merge_subset (Finset.subset_empty.mpr h₁)
    (h₂.trans Finset.subset_union_right))

end Fv

/-! ### Reuse-freeness

No discourse referent is declared twice along a nesting path: each universe is
fresh for the ambient declarations, threaded through sub-boxes the way
verification threads the base (the antecedent of a `⇒` feeds its referents
into the consequent). This is the hypothesis under which the total
agree-off-universe semantics and the persistence semantics coincide
(`DRS.trueRel_iff_toRelAt` in `DRS/Indexed.lean`). -/

section ReuseFree
variable [DecidableEq V]

/-- A condition is reuse-free at ambient declarations `X`: each sub-box
universe is fresh for the declarations in scope, threaded the way verification
threads the base (the antecedent of a `⇒` feeds its referents into the
consequent). -/
def Condition.ReuseFreeAt (X : Finset V) : Condition L V → Prop
  | .rel _ _ => True
  | .eq _ _ => True
  | .neg K => Disjoint X K.referents ∧
      ∀ c ∈ K.conditions, Condition.ReuseFreeAt (X ∪ K.referents) c
  | .imp a c =>
      (Disjoint X a.referents ∧
        ∀ d ∈ a.conditions, Condition.ReuseFreeAt (X ∪ a.referents) d) ∧
      (Disjoint (X ∪ a.referents) c.referents ∧
        ∀ d ∈ c.conditions, Condition.ReuseFreeAt (X ∪ a.referents ∪ c.referents) d)
  | .dis l r =>
      (Disjoint X l.referents ∧
        ∀ d ∈ l.conditions, Condition.ReuseFreeAt (X ∪ l.referents) d) ∧
      (Disjoint X r.referents ∧
        ∀ d ∈ r.conditions, Condition.ReuseFreeAt (X ∪ r.referents) d)
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Reuse-freeness for a list of conditions. -/
def Condition.ReuseFreeAllAt (X : Finset V) (cs : List (Condition L V)) : Prop :=
  ∀ c ∈ cs, Condition.ReuseFreeAt X c

/-- A DRS is *reuse-free* at ambient declarations `X`: its universe avoids `X`
and its conditions are reuse-free at the grown set. -/
def DRS.ReuseFreeAt (X : Finset V) (K : DRS L V) : Prop :=
  Disjoint X K.referents ∧ Condition.ReuseFreeAllAt (X ∪ K.referents) K.conditions

@[simp] theorem DRS.reuseFreeAt_mk (X U : Finset V) (conds : List (Condition L V)) :
    DRS.ReuseFreeAt X (.mk U conds) ↔
      Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) conds := Iff.rfl

@[simp] theorem Condition.reuseFreeAt_rel (X : Finset V) {n : ℕ} (R : L.Relations n)
    (args : Fin n → V) : Condition.ReuseFreeAt X (.rel R args) := by
  simp only [Condition.ReuseFreeAt]

@[simp] theorem Condition.reuseFreeAt_eq (X : Finset V) (u v : V) :
    Condition.ReuseFreeAt X (.eq u v : Condition L V) := by
  simp only [Condition.ReuseFreeAt]

@[simp] theorem Condition.reuseFreeAt_neg (X : Finset V) (K : DRS L V) :
    Condition.ReuseFreeAt X (.neg K) ↔ DRS.ReuseFreeAt X K := by
  simp only [Condition.ReuseFreeAt]; rfl

@[simp] theorem Condition.reuseFreeAt_imp (X : Finset V) (a c : DRS L V) :
    Condition.ReuseFreeAt X (.imp a c) ↔
      DRS.ReuseFreeAt X a ∧ DRS.ReuseFreeAt (X ∪ a.referents) c := by
  simp only [Condition.ReuseFreeAt]; rfl

@[simp] theorem Condition.reuseFreeAt_dis (X : Finset V) (l r : DRS L V) :
    Condition.ReuseFreeAt X (.dis l r) ↔
      DRS.ReuseFreeAt X l ∧ DRS.ReuseFreeAt X r := by
  simp only [Condition.ReuseFreeAt]; rfl

@[simp] theorem Condition.reuseFreeAllAt_nil (X : Finset V) :
    Condition.ReuseFreeAllAt X ([] : List (Condition L V)) := by
  simp [Condition.ReuseFreeAllAt]

@[simp] theorem Condition.reuseFreeAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) :
    Condition.ReuseFreeAllAt X (c :: cs) ↔
      Condition.ReuseFreeAt X c ∧ Condition.ReuseFreeAllAt X cs := by
  simp only [Condition.ReuseFreeAllAt, List.forall_mem_cons]

end ReuseFree

/-! ### Accessibility (decidable, host-relative)

Accessibility (Def. 1.4.11) is intrinsically *relative to a
host DRS*: "`u` accessible at box `B`" means `u` lies in the universe of `B` or of
a box on the path from the host down to `B`. A host-free `∃ D, WeakSubordinate K D
∧ u ∈ D.referents` is **vacuous** — a superordinate `D` introducing any referent
can always be manufactured. So accessibility is computed *top-down*, threading the
in-scope referents (the same threading as `DRS.Bound`), which is also decidable. -/

section Accessibility
variable [DecidableEq V]

/-- Accessibility threading through a condition. -/
def Condition.accScope (s : Finset V) : Condition L V → V → Option (Finset V)
  | .rel _ _, _ => none
  | .eq _ _, _ => none
  | .neg K, x =>
      if x ∈ K.referents then some (s ∪ K.referents)
      else (K.conditions.map fun c => Condition.accScope (s ∪ K.referents) c x).foldr
        (fun r acc => r.orElse fun _ => acc) none
  | .imp a c, x =>
      (if x ∈ a.referents then some (s ∪ a.referents)
       else (a.conditions.map fun d => Condition.accScope (s ∪ a.referents) d x).foldr
         (fun r acc => r.orElse fun _ => acc) none).orElse fun _ =>
      if x ∈ c.referents then some (s ∪ a.referents ∪ c.referents)
      else (c.conditions.map fun d =>
          Condition.accScope (s ∪ a.referents ∪ c.referents) d x).foldr
        (fun r acc => r.orElse fun _ => acc) none
  | .dis l r, x =>
      (if x ∈ l.referents then some (s ∪ l.referents)
       else (l.conditions.map fun d => Condition.accScope (s ∪ l.referents) d x).foldr
         (fun r acc => r.orElse fun _ => acc) none).orElse fun _ =>
      if x ∈ r.referents then some (s ∪ r.referents)
      else (r.conditions.map fun d => Condition.accScope (s ∪ r.referents) d x).foldr
        (fun r acc => r.orElse fun _ => acc) none
decreasing_by all_goals
  have := DRS.sizeOf_lt_of_mem_conditions (by assumption)
  simp_wf
  omega

/-- Accessibility threading through a list of conditions: the first hit wins. -/
def Condition.accScopeL (s : Finset V) (cs : List (Condition L V)) (x : V) :
    Option (Finset V) :=
  (cs.map fun c => Condition.accScope s c x).foldr (fun r acc => r.orElse fun _ => acc) none

/-- Descend `K`, accumulating in-scope referents `s` ("left and up"); on reaching
the box introducing `x`, return that box's in-scope set `s ∪ U`. The `⇒`-consequent
additionally sees the antecedent's universe. -/
def DRS.accScope (s : Finset V) (K : DRS L V) (x : V) : Option (Finset V) :=
  if x ∈ K.referents then some (s ∪ K.referents)
  else Condition.accScopeL (s ∪ K.referents) K.conditions x

theorem Condition.accScope_neg (s : Finset V) (K : DRS L V) (x : V) :
    Condition.accScope s (.neg K) x = DRS.accScope s K x := by
  simp only [Condition.accScope]; rfl

theorem Condition.accScope_imp (s : Finset V) (a c : DRS L V) (x : V) :
    Condition.accScope s (.imp a c) x =
      (DRS.accScope s a x).orElse fun _ => DRS.accScope (s ∪ a.referents) c x := by
  simp only [Condition.accScope]; rfl

theorem Condition.accScope_dis (s : Finset V) (l r : DRS L V) (x : V) :
    Condition.accScope s (.dis l r) x =
      (DRS.accScope s l x).orElse fun _ => DRS.accScope s r x := by
  simp only [Condition.accScope]; rfl

/-- The referents accessible from `u`'s introduction in `T`, as a decidable
`Finset`; `∅` if `u` is not introduced in `T`. (Def. 1.4.11 defines
accessibility of a referent from a *condition*; this is the derived
referent-to-referent relation of the surrounding prose.) -/
def DRS.accessibleFrom (T : DRS L V) (u : V) : Finset V := (DRS.accScope ∅ T u).getD ∅

/-- `v` is accessible from `u`'s position in `T`. Decidable (Finset membership). -/
def DRS.Accessible (T : DRS L V) (u v : V) : Prop := v ∈ DRS.accessibleFrom T u

instance (T : DRS L V) (u v : V) : Decidable (DRS.Accessible T u v) :=
  inferInstanceAs (Decidable (v ∈ _))

end Accessibility

open FirstOrder in
/-- Non-vacuity guard: in `[1 | ¬[2 | ]]`, `1` is accessible from `2` but `2` is
not accessible from `1` — the subordination asymmetry, now decidable (contrast the
old host-free `Accessible`, which was provable for *all* referents). -/
example :
    DRS.Accessible (L := Language.empty) (.mk {1} [.neg (.mk {2} [])]) 2 1 ∧
      ¬ DRS.Accessible (L := Language.empty) (.mk {1} [.neg (.mk {2} [])]) 1 2 := by
  simp [DRS.Accessible, DRS.accessibleFrom, DRS.accScope, Condition.accScopeL,
    Condition.accScope_neg]

end DRT
