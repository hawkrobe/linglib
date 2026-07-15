import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.Data.Finset.Image

/-!
# DRS structural API: functorial renaming and merge algebra
[kamp-reyle-1993]

Structural operations and lemmas over the faithful `DRS` core (`DRS/Defs.lean`):

* `DRS.map` / `Condition.map` — functorial renaming of discourse referents along
  `f : V → W`. When `f` is a bijection this is Kamp & Reyle's *alphabetic
  variant* (the prose preceding Def. 1.4.8); `map_id` makes "renaming to the
  identity is the identity" a free corollary.
* `merge` algebra — identity (`empty`) and associativity.
* `DRS.Bound` / `DRS.IsProper` — properness (no free discourse referent,
  Def. 1.4.2–1.4.3).
* `Condition.occ` / `DRS.occ` — occurring referents, as a decidable `Finset`.
* `DRS.accessibleFrom` / `DRS.Accessible` — decidable, host-relative
  accessibility (Def. 1.4.11).
-/

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x}

/-! ### Functorial renaming -/

mutual
/-- Rename discourse referents along `f : V → W` throughout a DRS. -/
def DRS.map [DecidableEq W] (f : V → W) : DRS L V → DRS L W
  | .mk refs conds => .mk (refs.image f) (Condition.mapList f conds)
/-- Rename discourse referents along `f` throughout a condition. -/
def Condition.map [DecidableEq W] (f : V → W) : Condition L V → Condition L W
  | .rel R args => .rel R (fun i => f (args i))
  | .eq a b => .eq (f a) (f b)
  | .neg K => .neg (DRS.map f K)
  | .imp a c => .imp (DRS.map f a) (DRS.map f c)
  | .dis l r => .dis (DRS.map f l) (DRS.map f r)
/-- Rename along `f` throughout a list of conditions. A `List` helper (not
`conds.map (Condition.map f)`) because the higher-order form fails the
nested-inductive structural-recursion checker. -/
def Condition.mapList [DecidableEq W] (f : V → W) : List (Condition L V) → List (Condition L W)
  | [] => []
  | c :: cs => Condition.map f c :: Condition.mapList f cs
end

mutual
/-- Renaming along the identity is the identity. -/
@[simp] theorem DRS.map_id [DecidableEq V] (K : DRS L V) : DRS.map id K = K := by
  match K with
  | .mk refs conds =>
      simp only [DRS.map, Condition.mapList_id]
      congr 1
      ext x
      simp
/-- Renaming a condition along the identity is the identity. -/
@[simp] theorem Condition.map_id [DecidableEq V] (c : Condition L V) :
    Condition.map id c = c := by
  match c with
  | .rel R args => simp only [Condition.map, id_eq]
  | .eq a b => simp only [Condition.map, id_eq]
  | .neg K => simp only [Condition.map, DRS.map_id K]
  | .imp a c => simp only [Condition.map, DRS.map_id a, DRS.map_id c]
  | .dis l r => simp only [Condition.map, DRS.map_id l, DRS.map_id r]
theorem Condition.mapList_id [DecidableEq V] (cs : List (Condition L V)) :
    Condition.mapList id cs = cs := by
  match cs with
  | [] => rfl
  | c :: cs => simp only [Condition.mapList, Condition.map_id c, Condition.mapList_id cs]
end

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

/-! ### Properness (no free discourse referent) -/

section Proper
variable [DecidableEq V]

mutual
/-- `Bound b K`: every discourse referent occurring in `K` is bound — present in
`b` or introduced by `K`'s universe or by an ancestor reachable "left and up"
(the antecedent of a `⇒` threads its referents into the consequent). -/
def DRS.Bound (b : Finset V) : DRS L V → Prop
  | .mk U conds => Condition.BoundAll (b ∪ U) conds
/-- `b`-boundedness of a condition. -/
def Condition.Bound (b : Finset V) : Condition L V → Prop
  | .rel _ args => ∀ i, args i ∈ b
  | .eq u v => u ∈ b ∧ v ∈ b
  | .neg K => DRS.Bound b K
  | .imp a c => DRS.Bound b a ∧ DRS.Bound (b ∪ a.referents) c
  | .dis l r => DRS.Bound b l ∧ DRS.Bound b r
/-- `b`-boundedness of a list of conditions. A `List` helper (not
`List.Forall (Condition.Bound b)`) — the higher-order form fails the
nested-inductive structural-recursion checker. -/
def Condition.BoundAll (b : Finset V) : List (Condition L V) → Prop
  | [] => True
  | c :: cs => Condition.Bound b c ∧ Condition.BoundAll b cs
end

/-- A DRS is *proper* iff it has no free discourse referent
([kamp-reyle-1993], Def. 1.4.2–1.4.3): every occurring referent is bound at
its position. -/
def DRS.IsProper (K : DRS L V) : Prop := DRS.Bound ∅ K

end Proper

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

end Occ

/-! ### Accessibility (decidable, host-relative)

Accessibility ([kamp-reyle-1993], Def. 1.4.11) is intrinsically *relative to a
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
`Finset`; `∅` if `u` is not introduced in `T`. ([kamp-reyle-1993] Def. 1.4.11
defines accessibility of a referent from a *condition*; this is the derived
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
