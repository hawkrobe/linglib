import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.Data.Finset.Image

/-!
# DRS structural API: functorial renaming and merge algebra
@cite{kamp-reyle-1993}

Structural operations and lemmas over the faithful `DRS` core (`DRS/Defs.lean`):

* `DRS.map` / `Condition.map` — functorial renaming of discourse referents along
  `f : V → W`. When `f` is a bijection this is Kamp & Reyle's *alphabetic
  variant* (Def. 1.4.7); `map_id` makes "renaming to the identity is the
  identity" a free corollary.
* `merge` algebra — identity (`empty`) and associativity.
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
/-- Rename along `f` throughout a list of conditions (mutual helper). -/
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
/-- `b`-boundedness of a list of conditions (mutual helper). -/
def Condition.BoundAll (b : Finset V) : List (Condition L V) → Prop
  | [] => True
  | c :: cs => Condition.Bound b c ∧ Condition.BoundAll b cs
end

/-- A DRS is *proper* iff it has no free discourse referent
(@cite{kamp-reyle-1993}, Def. 1.4.2–1.4.3): every occurring referent is bound at
its position. -/
def DRS.IsProper (K : DRS L V) : Prop := DRS.Bound ∅ K

end Proper

end DRT
