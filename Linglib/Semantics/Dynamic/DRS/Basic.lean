import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.Data.Finset.Image

/-!
# DRS structural API: functorial renaming and merge algebra

Structural operations and lemmas over the faithful `DRS` core (`DRS/Defs.lean`):

* `DRS.map` / `Condition.map` — functorial renaming of discourse referents along
  `f : V → W`. When `f` is a bijection this is [kamp-reyle-1993]'s *alphabetic
  variant* (the prose preceding Def. 1.4.8); `map_id` makes "renaming to the
  identity is the identity" a free corollary, and `Embedding.verifies_map`
  (`DRS/Verification.lean`) shows variants have the same semantics.
* `merge` algebra — identity (`empty`) and associativity.
* `Embedding` and `Box.Extends` — embedding functions and K&R's extension
  relation `f [K] g` between them.
* `DRS.fv` / `DRS.IsProper` — free discourse referents (as a `Finset`) and
  properness (`fv K = ∅`, Def. 1.4.2–1.4.3).
* `Condition.occ` / `DRS.occ` — occurring referents, as a decidable `Finset`.
* `DRS.accessibleFrom` / `DRS.Accessible` — decidable, host-relative
  accessibility (Def. 1.4.11).
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

/-- `K.Extends f g` (K&R's `f [K] g`): the output embedding `g` differs from
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

mutual
/-- Occurring referents (free or bound) in a condition, as a `Finset` — the DRS
analogue of mathlib's `Term.varFinset`. Membership `x ∈ occ c` is decidable, so
downstream consumers get decidable occurrence for free. -/
def Condition.occ : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => DRS.occ K
  | .imp a c => DRS.occ a ∪ DRS.occ c
  | .dis l r => DRS.occ l ∪ DRS.occ r
/-- Occurring referents in a DRS (its universe and those of its conditions). -/
def DRS.occ : DRS L V → Finset V
  | .mk U conds => U ∪ Condition.occL conds
/-- Occurring referents in a list of conditions. -/
def Condition.occL : List (Condition L V) → Finset V
  | [] => ∅
  | c :: cs => Condition.occ c ∪ Condition.occL cs
end

@[simp] theorem Condition.occL_append (cs ds : List (Condition L V)) :
    Condition.occL (cs ++ ds) = Condition.occL cs ∪ Condition.occL ds := by
  induction cs with
  | nil => simp [Condition.occL]
  | cons c cs ih => simp [Condition.occL, ih, Finset.union_assoc]

/-- A DRS's conditions' occurring referents are among the DRS's. -/
theorem DRS.occL_subset_occ (K : DRS L V) : Condition.occL K.conditions ⊆ K.occ := by
  cases K; exact Finset.subset_union_right

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

mutual
/-- The free discourse referents of a DRS: referents occurring in its
conditions and not bound by its universe or by an ancestor reachable "left
and up" (the antecedent of a `⇒` threads its referents into the consequent).
`K.fv ⊆ b` says every referent of `K` is bound in context `b`. -/
def DRS.fv : DRS L V → Finset V
  | .mk U conds => Condition.fvL conds \ U
/-- The free discourse referents of a condition. -/
def Condition.fv : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => DRS.fv K
  | .imp a c => DRS.fv a ∪ (DRS.fv c \ a.referents)
  | .dis l r => DRS.fv l ∪ DRS.fv r
/-- Free referents of a list of conditions. A `List` helper — the
higher-order form fails the nested-inductive structural-recursion checker. -/
def Condition.fvL : List (Condition L V) → Finset V
  | [] => ∅
  | c :: cs => Condition.fv c ∪ Condition.fvL cs
end

@[simp] theorem DRS.fv_mk (U : Finset V) (conds : List (Condition L V)) :
    DRS.fv ⟨U, conds⟩ = Condition.fvL conds \ U := rfl
@[simp] theorem Condition.fv_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (Condition.rel R args).fv = Finset.image args Finset.univ := rfl
@[simp] theorem Condition.fv_eq (u v : V) :
    (Condition.eq u v : Condition L V).fv = {u, v} := rfl
@[simp] theorem Condition.fv_neg (K : DRS L V) : (Condition.neg K).fv = K.fv := rfl
@[simp] theorem Condition.fv_imp (a c : DRS L V) :
    (Condition.imp a c).fv = a.fv ∪ (c.fv \ a.referents) := rfl
@[simp] theorem Condition.fv_dis (l r : DRS L V) :
    (Condition.dis l r).fv = l.fv ∪ r.fv := rfl
@[simp] theorem Condition.fvL_nil : Condition.fvL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem Condition.fvL_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.fvL (c :: cs) = c.fv ∪ Condition.fvL cs := rfl

/-- The characteristic form of the referential presupposition: a box's free
referents are supplied by `X` iff its conditions' are supplied by the grown
base. -/
theorem DRS.fv_subset_iff {U X : Finset V} {conds : List (Condition L V)} :
    DRS.fv ⟨U, conds⟩ ⊆ X ↔ Condition.fvL conds ⊆ X ∪ U := by
  rw [DRS.fv_mk, sdiff_le_iff, sup_comm, Finset.sup_eq_union]

mutual
/-- Free referents occur. -/
theorem DRS.fv_subset_occ (K : DRS L V) : K.fv ⊆ K.occ := by
  match K with
  | .mk U conds =>
    simp only [DRS.fv_mk, DRS.occ]
    exact (Finset.sdiff_subset).trans (Condition.fvL_subset_occL conds) |>.trans
      Finset.subset_union_right
/-- Free referents of a condition occur. -/
theorem Condition.fv_subset_occ (c : Condition L V) : c.fv ⊆ c.occ := by
  match c with
  | .rel R args => simp [Condition.occ]
  | .eq u v => simp [Condition.occ]
  | .neg K => simpa [Condition.occ] using DRS.fv_subset_occ K
  | .imp a c =>
    simp only [Condition.fv_imp, Condition.occ]
    exact Finset.union_subset_union (DRS.fv_subset_occ a)
      ((Finset.sdiff_subset).trans (DRS.fv_subset_occ c))
  | .dis l r =>
    simp only [Condition.fv_dis, Condition.occ]
    exact Finset.union_subset_union (DRS.fv_subset_occ l) (DRS.fv_subset_occ r)
/-- The list analogue of `Condition.fv_subset_occ`. -/
theorem Condition.fvL_subset_occL (cs : List (Condition L V)) :
    Condition.fvL cs ⊆ Condition.occL cs := by
  match cs with
  | [] => simp
  | c :: cs =>
    simp only [Condition.fvL_cons, Condition.occL]
    exact Finset.union_subset_union (Condition.fv_subset_occ c)
      (Condition.fvL_subset_occL cs)
end

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

mutual
/-- A DRS is *reuse-free* at ambient declarations `X`: its universe avoids `X`
and its conditions are reuse-free at the grown set. -/
def DRS.ReuseFreeAt (X : Finset V) : DRS L V → Prop
  | .mk U conds => Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) conds
/-- A condition is reuse-free at ambient declarations `X`. -/
def Condition.ReuseFreeAt (X : Finset V) : Condition L V → Prop
  | .rel _ _ => True
  | .eq _ _ => True
  | .neg K => DRS.ReuseFreeAt X K
  | .imp a c => DRS.ReuseFreeAt X a ∧ DRS.ReuseFreeAt (X ∪ a.referents) c
  | .dis l r => DRS.ReuseFreeAt X l ∧ DRS.ReuseFreeAt X r
/-- Reuse-freeness for a list of conditions. -/
def Condition.ReuseFreeAllAt (X : Finset V) : List (Condition L V) → Prop
  | [] => True
  | c :: cs => Condition.ReuseFreeAt X c ∧ Condition.ReuseFreeAllAt X cs
end

@[simp] theorem DRS.reuseFreeAt_mk (X U : Finset V) (conds : List (Condition L V)) :
    DRS.ReuseFreeAt X (.mk U conds) ↔
      Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) conds := Iff.rfl

@[simp] theorem Condition.reuseFreeAt_rel (X : Finset V) {n : ℕ} (R : L.Relations n)
    (args : Fin n → V) : Condition.ReuseFreeAt X (.rel R args) := trivial

@[simp] theorem Condition.reuseFreeAt_eq (X : Finset V) (u v : V) :
    Condition.ReuseFreeAt X (.eq u v : Condition L V) := trivial

@[simp] theorem Condition.reuseFreeAt_neg (X : Finset V) (K : DRS L V) :
    Condition.ReuseFreeAt X (.neg K) ↔ DRS.ReuseFreeAt X K := Iff.rfl

@[simp] theorem Condition.reuseFreeAt_imp (X : Finset V) (a c : DRS L V) :
    Condition.ReuseFreeAt X (.imp a c) ↔
      DRS.ReuseFreeAt X a ∧ DRS.ReuseFreeAt (X ∪ a.referents) c := Iff.rfl

@[simp] theorem Condition.reuseFreeAt_dis (X : Finset V) (l r : DRS L V) :
    Condition.ReuseFreeAt X (.dis l r) ↔
      DRS.ReuseFreeAt X l ∧ DRS.ReuseFreeAt X r := Iff.rfl

@[simp] theorem Condition.reuseFreeAllAt_nil (X : Finset V) :
    Condition.ReuseFreeAllAt X ([] : List (Condition L V)) := trivial

@[simp] theorem Condition.reuseFreeAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) :
    Condition.ReuseFreeAllAt X (c :: cs) ↔
      Condition.ReuseFreeAt X c ∧ Condition.ReuseFreeAllAt X cs := Iff.rfl

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

mutual
/-- Descend `T`, accumulating in-scope referents `s` ("left and up"); on reaching
the box introducing `x`, return that box's in-scope set `s ∪ U`. The `⇒`-consequent
additionally sees the antecedent's universe. -/
def DRS.accScope (s : Finset V) : DRS L V → V → Option (Finset V)
  | .mk U conds, x => if x ∈ U then some (s ∪ U) else Condition.accScopeL (s ∪ U) conds x
/-- Accessibility threading through a condition. -/
def Condition.accScope (s : Finset V) : Condition L V → V → Option (Finset V)
  | .rel _ _, _ => none
  | .eq _ _, _ => none
  | .neg K, x => DRS.accScope s K x
  | .imp a c, x =>
      match DRS.accScope s a x with
      | some r => some r
      | none => DRS.accScope (s ∪ a.referents) c x
  | .dis l r, x =>
      match DRS.accScope s l x with
      | some r => some r
      | none => DRS.accScope s r x
/-- Accessibility threading through a list of conditions (mutual helper). -/
def Condition.accScopeL (s : Finset V) : List (Condition L V) → V → Option (Finset V)
  | [], _ => none
  | c :: cs, x =>
      match Condition.accScope s c x with
      | some r => some r
      | none => Condition.accScopeL s cs x
end

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
      ¬ DRS.Accessible (L := Language.empty) (.mk {1} [.neg (.mk {2} [])]) 1 2 := by decide

end DRT
