import Linglib.Semantics.Dynamic.DRS.Defs
import Mathlib.Data.Finset.Image

/-!
# DRS structural API: functorial renaming, merge algebra, properness
@cite{kamp-reyle-1993}

Structural operations and lemmas over the faithful `DRS` core (`DRS/Defs.lean`):

* `DRS.map` / `Condition.map` — functorial renaming of discourse referents along
  `f : V → W`. `map_id` makes "rename a referent to itself is the identity" a
  free corollary, replacing the legacy bespoke `rename` + `rename_self`.
* `merge` algebra — identity (`empty`) and associativity.
* `IsProper` — the decidable, top-down "left and up" properness check (every
  occurring referent is bound at its position), the faithful counterpart of the
  legacy `allBound`.
-/

namespace DRT

universe u v w

variable {R : Type u} {V : Type v} {W : Type w}

/-! ### Functorial renaming -/

mutual
/-- Rename discourse referents along `f : V → W` throughout a DRS. -/
def DRS.map [DecidableEq W] (f : V → W) : DRS R V → DRS R W
  | .mk refs conds => .mk (refs.image f) (Condition.mapList f conds)
/-- Rename discourse referents along `f` throughout a condition. -/
def Condition.map [DecidableEq W] (f : V → W) : Condition R V → Condition R W
  | .rel r args => .rel r (args.map f)
  | .eq a b => .eq (f a) (f b)
  | .neg K => .neg (DRS.map f K)
  | .imp a c => .imp (DRS.map f a) (DRS.map f c)
  | .dis l r => .dis (DRS.map f l) (DRS.map f r)
/-- Rename along `f` throughout a list of conditions (mutual helper). -/
def Condition.mapList [DecidableEq W] (f : V → W) : List (Condition R V) → List (Condition R W)
  | [] => []
  | c :: cs => Condition.map f c :: Condition.mapList f cs
end

mutual
/-- Renaming along the identity is the identity. -/
@[simp] theorem DRS.map_id [DecidableEq V] (K : DRS R V) : DRS.map id K = K := by
  match K with
  | .mk refs conds =>
      simp only [DRS.map, Condition.mapList_id]
      congr 1
      ext x
      simp
/-- Renaming a condition along the identity is the identity. -/
@[simp] theorem Condition.map_id [DecidableEq V] (c : Condition R V) :
    Condition.map id c = c := by
  match c with
  | .rel r args => simp only [Condition.map, List.map_id]
  | .eq a b => rfl
  | .neg K => simp only [Condition.map, DRS.map_id K]
  | .imp a c => simp only [Condition.map, DRS.map_id a, DRS.map_id c]
  | .dis l r => simp only [Condition.map, DRS.map_id l, DRS.map_id r]
theorem Condition.mapList_id [DecidableEq V] (cs : List (Condition R V)) :
    Condition.mapList id cs = cs := by
  match cs with
  | [] => rfl
  | c :: cs => simp only [Condition.mapList, Condition.map_id c, Condition.mapList_id cs]
end

/-! ### Merge algebra -/

namespace DRS

variable [DecidableEq V]

@[simp] theorem empty_merge (K : DRS R V) : (empty : DRS R V).merge K = K := by
  cases K with
  | mk r c => simp [merge, empty]

@[simp] theorem merge_empty (K : DRS R V) : K.merge (empty : DRS R V) = K := by
  cases K with
  | mk r c => simp [merge, empty]

theorem merge_assoc (K₁ K₂ K₃ : DRS R V) :
    (K₁.merge K₂).merge K₃ = K₁.merge (K₂.merge K₃) := by
  cases K₁; cases K₂; cases K₃
  simp only [merge, referents_mk, conditions_mk]
  rw [Finset.union_assoc, List.append_assoc]

end DRS

end DRT
