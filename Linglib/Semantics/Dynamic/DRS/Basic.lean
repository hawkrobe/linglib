import Linglib.Semantics.Dynamic.DRS.Defs

/-!
# Structural operations on DRSs

This file develops the structural theory of the `DRS` type of `DRS/Defs.lean`:
functorial renaming of discourse referents (`DRS.map`), the merge algebra,
transport of the extension relation along renaming, and the referent
predicates `varFinset`, `freeVarFinset` and `IsProper`, `ReuseFreeAt`, and
`Accessible`. Renaming along a bijection is [kamp-reyle-1993]'s *alphabetic
variant* (the prose preceding Def. 1.4.8).
-/

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x} {M X : Type*}

/-! ## Conditions -/

namespace Condition

/-! ### Renaming -/

/-- Rename discourse referents along `f` throughout a condition. -/
def map [DecidableEq W] (f : V → W) : Condition L V → Condition L W
  | .rel R args => .rel R (fun i => f (args i))
  | .eq a b => .eq (f a) (f b)
  | .neg K => .neg (K.map f (map f))
  | .imp a c => .imp (a.map f (map f)) (c.map f (map f))
  | .dis l r => .dis (l.map f (map f)) (r.map f (map f))

/-- Renaming a condition along the identity is the identity. -/
@[simp] theorem map_id [DecidableEq V] (c : Condition L V) : map id c = c := by
  induction c with
  | rel R args => simp [map]
  | eq u v => simp [map]
  | neg K ih => simp [map, Box.map_eq_self ih]
  | imp a c iha ihc => simp [map, Box.map_eq_self iha, Box.map_eq_self ihc]
  | dis l r ihl ihr => simp [map, Box.map_eq_self ihl, Box.map_eq_self ihr]

/-- Renaming a condition along a composite is the composite of the renamings. -/
theorem map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W)
    (c : Condition L V) : map g (map f c) = map (g ∘ f) c := by
  induction c with
  | rel R args => simp [map]
  | eq u v => simp [map]
  | neg K ih => simp [map, Box.map_map_of_forall f g ih]
  | imp a c iha ihc => simp [map, Box.map_map_of_forall f g iha, Box.map_map_of_forall f g ihc]
  | dis l r ihl ihr => simp [map, Box.map_map_of_forall f g ihl, Box.map_map_of_forall f g ihr]

variable [DecidableEq V]

/-! ### Occurring referents -/

/-- Occurring referents (free or bound) in a condition, as a `Finset` — the DRS
analogue of mathlib's `Term.varFinset`. Membership `x ∈ varFinset c` is
decidable, so downstream consumers get decidable occurrence for free. -/
def varFinset : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => K.referents ∪ (K.conditions.map varFinset).foldr (· ∪ ·) ∅
  | .imp a c => (a.referents ∪ (a.conditions.map varFinset).foldr (· ∪ ·) ∅) ∪
      (c.referents ∪ (c.conditions.map varFinset).foldr (· ∪ ·) ∅)
  | .dis l r => (l.referents ∪ (l.conditions.map varFinset).foldr (· ∪ ·) ∅) ∪
      (r.referents ∪ (r.conditions.map varFinset).foldr (· ∪ ·) ∅)

/-- Occurring referents in a list of conditions. -/
def varFinsetL (cs : List (Condition L V)) : Finset V := (cs.map varFinset).foldr (· ∪ ·) ∅

@[simp] theorem varFinsetL_nil : varFinsetL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem varFinsetL_cons (c : Condition L V) (cs : List (Condition L V)) :
    varFinsetL (c :: cs) = c.varFinset ∪ varFinsetL cs := rfl
@[simp] theorem varFinset_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (rel R args).varFinset = Finset.image args Finset.univ := by simp only [varFinset]
@[simp] theorem varFinset_eq (u v : V) :
    (eq u v : Condition L V).varFinset = {u, v} := by simp only [varFinset]

@[simp] theorem varFinsetL_append (cs ds : List (Condition L V)) :
    varFinsetL (cs ++ ds) = varFinsetL cs ∪ varFinsetL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

/-- A condition's occurring referents are among its list's. -/
theorem varFinset_subset_varFinsetL {c : Condition L V} {cs : List (Condition L V)}
    (hc : c ∈ cs) : c.varFinset ⊆ varFinsetL cs := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with h | h
    · exact h ▸ Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-! ### Free discourse referents -/

/-- The free discourse referents of a condition. -/
def freeVarFinset : Condition L V → Finset V
  | .rel _ args => Finset.image args Finset.univ
  | .eq u v => {u, v}
  | .neg K => (K.conditions.map freeVarFinset).foldr (· ∪ ·) ∅ \ K.referents
  | .imp a c => ((a.conditions.map freeVarFinset).foldr (· ∪ ·) ∅ \ a.referents) ∪
      (((c.conditions.map freeVarFinset).foldr (· ∪ ·) ∅ \ c.referents) \ a.referents)
  | .dis l r => ((l.conditions.map freeVarFinset).foldr (· ∪ ·) ∅ \ l.referents) ∪
      ((r.conditions.map freeVarFinset).foldr (· ∪ ·) ∅ \ r.referents)

/-- Free referents of a list of conditions. -/
def freeVarFinsetL (cs : List (Condition L V)) : Finset V :=
  (cs.map freeVarFinset).foldr (· ∪ ·) ∅

@[simp] theorem freeVarFinset_rel {n : ℕ} (R : L.Relations n) (args : Fin n → V) :
    (rel R args).freeVarFinset = Finset.image args Finset.univ := by simp only [freeVarFinset]
@[simp] theorem freeVarFinset_eq (u v : V) :
    (eq u v : Condition L V).freeVarFinset = {u, v} := by simp only [freeVarFinset]
@[simp] theorem freeVarFinsetL_nil : freeVarFinsetL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem freeVarFinsetL_cons (c : Condition L V) (cs : List (Condition L V)) :
    freeVarFinsetL (c :: cs) = c.freeVarFinset ∪ freeVarFinsetL cs := rfl

@[simp] theorem freeVarFinsetL_append (cs ds : List (Condition L V)) :
    freeVarFinsetL (cs ++ ds) = freeVarFinsetL cs ∪ freeVarFinsetL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

private theorem freeVarFinsetL_subset_varFinsetL_of_forall {cs : List (Condition L V)}
    (h : ∀ c ∈ cs, c.freeVarFinset ⊆ c.varFinset) : freeVarFinsetL cs ⊆ varFinsetL cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [freeVarFinsetL_cons, varFinsetL_cons]
    exact Finset.union_subset_union (h c (by simp))
      (ih fun d hd => h d (List.mem_cons_of_mem c hd))

/-! ### Reuse-freeness

No discourse referent is declared twice along a nesting path: each universe is
fresh for the ambient declarations, threaded through sub-boxes the way
verification threads the base (the antecedent of a `⇒` feeds its referents
into the consequent). This is the hypothesis under which the total
agree-off-universe semantics and the persistence semantics coincide
(`DRS.trueRel_iff_toRelAt` in `DRS/Indexed.lean`). -/

/-- A condition is reuse-free at ambient declarations `X`: each sub-box
universe is fresh for the declarations in scope, threaded the way verification
threads the base (the antecedent of a `⇒` feeds its referents into the
consequent). -/
def ReuseFreeAt (X : Finset V) : Condition L V → Prop
  | .rel _ _ => True
  | .eq _ _ => True
  | .neg K => Disjoint X K.referents ∧
      ∀ c ∈ K.conditions, ReuseFreeAt (X ∪ K.referents) c
  | .imp a c =>
      (Disjoint X a.referents ∧
        ∀ d ∈ a.conditions, ReuseFreeAt (X ∪ a.referents) d) ∧
      (Disjoint (X ∪ a.referents) c.referents ∧
        ∀ d ∈ c.conditions, ReuseFreeAt (X ∪ a.referents ∪ c.referents) d)
  | .dis l r =>
      (Disjoint X l.referents ∧
        ∀ d ∈ l.conditions, ReuseFreeAt (X ∪ l.referents) d) ∧
      (Disjoint X r.referents ∧
        ∀ d ∈ r.conditions, ReuseFreeAt (X ∪ r.referents) d)

/-- Reuse-freeness for a list of conditions. -/
def ReuseFreeAllAt (X : Finset V) (cs : List (Condition L V)) : Prop :=
  ∀ c ∈ cs, ReuseFreeAt X c

@[simp] theorem reuseFreeAt_rel (X : Finset V) {n : ℕ} (R : L.Relations n)
    (args : Fin n → V) : ReuseFreeAt X (.rel R args) := by
  simp only [ReuseFreeAt]

@[simp] theorem reuseFreeAt_eq (X : Finset V) (u v : V) :
    ReuseFreeAt X (.eq u v : Condition L V) := by
  simp only [ReuseFreeAt]

@[simp] theorem reuseFreeAllAt_nil (X : Finset V) :
    ReuseFreeAllAt X ([] : List (Condition L V)) := by
  simp [ReuseFreeAllAt]

@[simp] theorem reuseFreeAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) :
    ReuseFreeAllAt X (c :: cs) ↔ ReuseFreeAt X c ∧ ReuseFreeAllAt X cs := by
  simp only [ReuseFreeAllAt, List.forall_mem_cons]

/-! ### Accessibility threading

Accessibility (Def. 1.4.11) is intrinsically *relative to a
host DRS*: "`u` accessible at box `B`" means `u` lies in the universe of `B` or of
a box on the path from the host down to `B`. A host-free `∃ D, WeakSubordinate K D
∧ u ∈ D.referents` is **vacuous** — a superordinate `D` introducing any referent
can always be manufactured. So accessibility is computed *top-down*, threading the
in-scope referents (the same threading as `DRS.Bound`), which is also decidable. -/

/-- Accessibility threading through a condition. -/
def accScope (s : Finset V) : Condition L V → V → Option (Finset V)
  | .rel _ _, _ => none
  | .eq _ _, _ => none
  | .neg K, x =>
      if x ∈ K.referents then some (s ∪ K.referents)
      else (K.conditions.map fun c => accScope (s ∪ K.referents) c x).foldr
        (fun r acc => r.orElse fun _ => acc) none
  | .imp a c, x =>
      (if x ∈ a.referents then some (s ∪ a.referents)
       else (a.conditions.map fun d => accScope (s ∪ a.referents) d x).foldr
         (fun r acc => r.orElse fun _ => acc) none).orElse fun _ =>
      if x ∈ c.referents then some (s ∪ a.referents ∪ c.referents)
      else (c.conditions.map fun d =>
          accScope (s ∪ a.referents ∪ c.referents) d x).foldr
        (fun r acc => r.orElse fun _ => acc) none
  | .dis l r, x =>
      (if x ∈ l.referents then some (s ∪ l.referents)
       else (l.conditions.map fun d => accScope (s ∪ l.referents) d x).foldr
         (fun r acc => r.orElse fun _ => acc) none).orElse fun _ =>
      if x ∈ r.referents then some (s ∪ r.referents)
      else (r.conditions.map fun d => accScope (s ∪ r.referents) d x).foldr
        (fun r acc => r.orElse fun _ => acc) none

/-- Accessibility threading through a list of conditions: the first hit wins. -/
def accScopeL (s : Finset V) (cs : List (Condition L V)) (x : V) : Option (Finset V) :=
  (cs.map fun c => accScope s c x).foldr (fun r acc => r.orElse fun _ => acc) none

end Condition

/-! ## DRSs -/

namespace DRS

/-! ### Renaming -/

/-- Rename discourse referents along `f : V → W` throughout a DRS. -/
def map [DecidableEq W] (f : V → W) : DRS L V → DRS L W :=
  Box.map f (Condition.map f)

@[simp] theorem referents_map [DecidableEq W] (f : V → W) (K : DRS L V) :
    (K.map f).referents = K.referents.image f := rfl

@[simp] theorem conditions_map [DecidableEq W] (f : V → W) (K : DRS L V) :
    (K.map f).conditions = K.conditions.map (Condition.map f) := rfl

/-- Renaming a DRS along the identity is the identity. -/
@[simp] theorem map_id [DecidableEq V] (K : DRS L V) : map id K = K := by
  simp [map]

/-- Renaming a DRS along a composite is the composite of the renamings. -/
theorem map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W) (K : DRS L V) :
    map g (map f K) = map (g ∘ f) K := by
  simp [map, Box.map_map, Condition.map_map g f]

/-- Extension along a renamed DRS is extension of the precompositions. -/
theorem extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f g : Embedding W M) :
    (K.map e).Extends f g ↔ K.Extends (f ∘ e) (g ∘ e) := by
  simp only [Box.Extends, referents_map, Function.comp_apply]
  refine ⟨fun h x hx => h (e x) (by simpa using hx), fun h y hy => ?_⟩
  have hx : e.symm y ∉ K.referents := fun hm =>
    hy (by simpa using Finset.mem_image_of_mem e hm)
  simpa using h (e.symm y) hx

/-- The extensions of `f` at `K.map e` are the extensions of `f ∘ e` at `K`,
via precomposition. -/
theorem exists_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∃ g, (K.map e).Extends f g ∧ P (g ∘ e)) ↔ ∃ g, K.Extends (f ∘ e) g ∧ P g := by
  simp only [extends_map]
  refine ⟨fun ⟨g, hg, hp⟩ => ⟨g ∘ e, hg, hp⟩, fun ⟨g, hg, hp⟩ => ⟨g ∘ e.symm, ?_⟩⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key.symm ▸ ⟨hg, hp⟩

/-- The `∀` analogue of `DRS.exists_extends_map`. -/
theorem forall_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : Embedding W M)
    (P : Embedding V M → Prop) :
    (∀ g, (K.map e).Extends f g → P (g ∘ e)) ↔ ∀ g, K.Extends (f ∘ e) g → P g := by
  simp only [extends_map]
  refine ⟨fun H g hg => ?_, fun H g hg => H (g ∘ e) hg⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key ▸ H (g ∘ e.symm) (key.symm ▸ hg)

variable [DecidableEq V]

/-! ### Merge algebra -/

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

/-! ### Occurring and free referents -/

/-- Occurring referents in a DRS (its universe and those of its conditions). -/
def varFinset (K : DRS L V) : Finset V := K.referents ∪ Condition.varFinsetL K.conditions

@[simp] theorem varFinset_mk (U : Finset V) (conds : List (Condition L V)) :
    varFinset ⟨U, conds⟩ = U ∪ Condition.varFinsetL conds := rfl

/-- A DRS's conditions' occurring referents are among the DRS's. -/
theorem varFinsetL_subset_varFinset (K : DRS L V) :
    Condition.varFinsetL K.conditions ⊆ K.varFinset :=
  Finset.subset_union_right

/-- The free discourse referents of a DRS: referents occurring in its
conditions and not bound by its universe or by an ancestor reachable "left
and up" (the antecedent of a `⇒` threads its referents into the consequent).
`K.freeVarFinset ⊆ b` says every referent of `K` is bound in context `b`. -/
def freeVarFinset (K : DRS L V) : Finset V :=
  Condition.freeVarFinsetL K.conditions \ K.referents

@[simp] theorem freeVarFinset_mk (U : Finset V) (conds : List (Condition L V)) :
    freeVarFinset ⟨U, conds⟩ = Condition.freeVarFinsetL conds \ U := rfl

/-- The characteristic form of the referential presupposition: a box's free
referents are supplied by `X` iff its conditions' are supplied by the grown
base. -/
theorem freeVarFinset_subset_iff {U X : Finset V} {conds : List (Condition L V)} :
    freeVarFinset ⟨U, conds⟩ ⊆ X ↔ Condition.freeVarFinsetL conds ⊆ X ∪ U := by
  rw [freeVarFinset_mk, sdiff_le_iff, sup_comm, Finset.sup_eq_union]

private theorem freeVarFinset_subset_varFinset_of_forall {K : DRS L V}
    (h : ∀ c ∈ K.conditions, c.freeVarFinset ⊆ c.varFinset) :
    K.freeVarFinset ⊆ K.varFinset :=
  Finset.sdiff_subset.trans
    ((Condition.freeVarFinsetL_subset_varFinsetL_of_forall h).trans Finset.subset_union_right)

/-- Merging preserves boundedness: the merge's free referents are supplied by
`X` when the context's are and the increment's are supplied by the grown base. -/
theorem freeVarFinset_merge_subset {X : Finset V} {K₁ K₂ : DRS L V}
    (h₁ : K₁.freeVarFinset ⊆ X) (h₂ : K₂.freeVarFinset ⊆ X ∪ K₁.referents) :
    (K₁.merge K₂).freeVarFinset ⊆ X := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  rw [referents_mk] at h₂
  rw [freeVarFinset_subset_iff] at h₁ h₂
  rw [merge, referents_mk, conditions_mk, freeVarFinset_subset_iff,
    Condition.freeVarFinsetL_append, ← Finset.union_assoc]
  exact Finset.union_subset (h₁.trans Finset.subset_union_left) h₂

/-- A DRS is *proper* iff it has no free discourse referent
(Def. 1.4.2–1.4.3). -/
def IsProper (K : DRS L V) : Prop := K.freeVarFinset = ∅

/-- Merging preserves properness when the increment's free referents are
supplied by the context DRS's universe. -/
theorem isProper_merge {K₁ K₂ : DRS L V} (h₁ : K₁.IsProper)
    (h₂ : K₂.freeVarFinset ⊆ K₁.referents) : (K₁.merge K₂).IsProper :=
  Finset.subset_empty.mp (freeVarFinset_merge_subset (Finset.subset_empty.mpr h₁)
    (h₂.trans Finset.subset_union_right))

/-! ### Reuse-freeness -/

/-- A DRS is *reuse-free* at ambient declarations `X`: its universe avoids `X`
and its conditions are reuse-free at the grown set. -/
def ReuseFreeAt (X : Finset V) (K : DRS L V) : Prop :=
  Disjoint X K.referents ∧ Condition.ReuseFreeAllAt (X ∪ K.referents) K.conditions

@[simp] theorem reuseFreeAt_mk (X U : Finset V) (conds : List (Condition L V)) :
    ReuseFreeAt X (.mk U conds) ↔
      Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) conds := Iff.rfl

/-! ### Accessibility -/

/-- Descend `K`, accumulating in-scope referents `s` ("left and up"); on reaching
the box introducing `x`, return that box's in-scope set `s ∪ U`. The `⇒`-consequent
additionally sees the antecedent's universe. -/
def accScope (s : Finset V) (K : DRS L V) (x : V) : Option (Finset V) :=
  if x ∈ K.referents then some (s ∪ K.referents)
  else Condition.accScopeL (s ∪ K.referents) K.conditions x

/-- The referents accessible from `u`'s introduction in `T`, as a decidable
`Finset`; `∅` if `u` is not introduced in `T`. (Def. 1.4.11 defines
accessibility of a referent from a *condition*; this is the derived
referent-to-referent relation of the surrounding prose.) -/
def accessibleFrom (T : DRS L V) (u : V) : Finset V := (accScope ∅ T u).getD ∅

/-- `v` is accessible from `u`'s position in `T`. Decidable (Finset membership). -/
def Accessible (T : DRS L V) (u v : V) : Prop := v ∈ accessibleFrom T u

instance (T : DRS L V) (u v : V) : Decidable (Accessible T u v) :=
  inferInstanceAs (Decidable (v ∈ _))

end DRS

/-! ## Sub-box characterizations

The per-constructor forms of the condition-level predicates, phrased through
the corresponding DRS-level notion of the sub-boxes, and the subset relations
tying free to occurring referents. -/

variable [DecidableEq V]

@[simp] theorem Condition.varFinset_neg (K : DRS L V) :
    (Condition.neg K).varFinset = K.varFinset := by
  simp only [Condition.varFinset]; rfl
@[simp] theorem Condition.varFinset_imp (a c : DRS L V) :
    (Condition.imp a c).varFinset = a.varFinset ∪ c.varFinset := by
  simp only [Condition.varFinset]; rfl
@[simp] theorem Condition.varFinset_dis (l r : DRS L V) :
    (Condition.dis l r).varFinset = l.varFinset ∪ r.varFinset := by
  simp only [Condition.varFinset]; rfl

@[simp] theorem Condition.freeVarFinset_neg (K : DRS L V) :
    (Condition.neg K).freeVarFinset = K.freeVarFinset := by
  simp only [Condition.freeVarFinset]; rfl
@[simp] theorem Condition.freeVarFinset_imp (a c : DRS L V) :
    (Condition.imp a c).freeVarFinset
      = a.freeVarFinset ∪ (c.freeVarFinset \ a.referents) := by
  simp only [Condition.freeVarFinset]; rfl
@[simp] theorem Condition.freeVarFinset_dis (l r : DRS L V) :
    (Condition.dis l r).freeVarFinset = l.freeVarFinset ∪ r.freeVarFinset := by
  simp only [Condition.freeVarFinset]; rfl

/-- Free referents of a condition occur. -/
theorem Condition.freeVarFinset_subset_varFinset (c : Condition L V) :
    c.freeVarFinset ⊆ c.varFinset := by
  induction c with
  | rel R args => simp
  | eq u v => simp
  | neg K ih => simpa using DRS.freeVarFinset_subset_varFinset_of_forall ih
  | imp a c iha ihc =>
    simp only [Condition.freeVarFinset_imp, Condition.varFinset_imp]
    exact Finset.union_subset_union (DRS.freeVarFinset_subset_varFinset_of_forall iha)
      (Finset.sdiff_subset.trans (DRS.freeVarFinset_subset_varFinset_of_forall ihc))
  | dis l r ihl ihr =>
    simp only [Condition.freeVarFinset_dis, Condition.varFinset_dis]
    exact Finset.union_subset_union (DRS.freeVarFinset_subset_varFinset_of_forall ihl)
      (DRS.freeVarFinset_subset_varFinset_of_forall ihr)

/-- Free referents occur. -/
theorem DRS.freeVarFinset_subset_varFinset (K : DRS L V) : K.freeVarFinset ⊆ K.varFinset :=
  DRS.freeVarFinset_subset_varFinset_of_forall fun c _ =>
    Condition.freeVarFinset_subset_varFinset c

/-- The list analogue of `Condition.freeVarFinset_subset_varFinset`. -/
theorem Condition.freeVarFinsetL_subset_varFinsetL (cs : List (Condition L V)) :
    Condition.freeVarFinsetL cs ⊆ Condition.varFinsetL cs :=
  Condition.freeVarFinsetL_subset_varFinsetL_of_forall fun c _ =>
    Condition.freeVarFinset_subset_varFinset c

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

end DRT
