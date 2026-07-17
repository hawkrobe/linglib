import Linglib.Core.Order.PartialUnify
import Mathlib.Data.Part
import Mathlib.Data.Set.Function

/-!
# Possibilities

This file defines a *possibility* — a world paired with an assignment
of discourse referents — and the structure of its partial points, with
`Part`-valued assignments: the descent order, compatibility and union,
restriction, and the classification of each stratum as
world–assignment pairs.

## References

- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [kamp-vangenabith-reyle-2011], Def. 0.22
- [heim-1982]
-/

namespace DynamicSemantics

/-- A possibility is a world paired with an assignment of discourse
referents to individuals. -/
@[ext] structure Possibility (W V M : Type*) where
  /-- The world coordinate. -/
  world : W
  /-- The assignment of discourse referents. -/
  assignment : V → M

namespace Possibility

variable {W V M : Type*} (p : Possibility W V M)

section Update

variable [DecidableEq V] (x : V) (e : M)

/-- Update the assignment at a single referent. -/
def update : Possibility W V M :=
  { p with assignment := Function.update p.assignment x e }

@[simp] theorem update_world : (p.update x e).world = p.world := rfl

@[simp] theorem update_assignment :
    (p.update x e).assignment = Function.update p.assignment x e := rfl

end Update

/-! ### Partial points -/

variable {p q u : Possibility W V (Part M)}

/-- `p ≤ q` iff `p` and `q` share their world and the assignments grow
pointwise in the order of partial values. -/
instance : PartialOrder (Possibility W V (Part M)) where
  le p q := p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x
  le_refl _ := ⟨rfl, fun _ => le_rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, fun x => (hpq.2 x).trans (hqr.2 x)⟩
  le_antisymm _ _ hpq hqp :=
    Possibility.ext hpq.1 (funext fun x => (hpq.2 x).antisymm (hqp.2 x))

theorem le_def : p ≤ q ↔ p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x :=
  Iff.rfl

/-- The domain of a partial point is the set of referents it defines. -/
def domain (p : Possibility W V (Part M)) : Set V :=
  {v | (p.assignment v).Dom}

@[simp] theorem mem_domain {v : V} :
    v ∈ p.domain ↔ (p.assignment v).Dom := Iff.rfl

/-- Descent grows the domain. -/
theorem domain_mono (h : p ≤ q) : p.domain ⊆ q.domain := fun v hd =>
  Part.dom_iff_mem.mpr ⟨_, h.2 v _ (Part.get_mem hd)⟩

/-- On a shared domain, descent is equality — there is no room to grow. -/
theorem eq_of_le_of_domain_eq (h : p ≤ q) (hdom : p.domain = q.domain) : p = q :=
  Possibility.ext h.1 <| funext fun v => le_antisymm (h.2 v) fun e he => by
    have hd : (p.assignment v).Dom := hdom.superset (Part.dom_iff_mem.mpr ⟨e, he⟩)
    obtain rfl := Part.mem_unique (h.2 v _ (Part.get_mem hd)) he
    exact Part.get_mem hd

open Classical in
/-- The union of two points, defined wherever either is, with the left
taking precedence; on compatible points the precedence is immaterial
(`union_comm`). -/
noncomputable def union (p q : Possibility W V (Part M)) : Possibility W V (Part M) :=
  ⟨p.world, fun v => if (p.assignment v).Dom then p.assignment v else q.assignment v⟩

theorem le_union_left (p q : Possibility W V (Part M)) : p ≤ p.union q :=
  ⟨rfl, fun v e he => by
    simp only [union]
    split
    · exact he
    · next h => exact absurd (Part.dom_iff_mem.mpr ⟨e, he⟩) h⟩

private theorem le_union_right_of_agree (hw : p.world = q.world)
    (hag : ∀ v e e', e ∈ p.assignment v → e' ∈ q.assignment v → e = e') :
    q ≤ p.union q :=
  ⟨hw.symm, fun v e he => by
    simp only [union]
    split
    · next hd => exact hag v _ e (Part.get_mem hd) he ▸ Part.get_mem hd
    · exact he⟩

theorem union_le (hp : p ≤ u) (hq : q ≤ u) : p.union q ≤ u :=
  ⟨hp.1, fun v e he => by
    simp only [union] at he
    split at he
    · exact hp.2 v e he
    · exact hq.2 v e he⟩

/-- Two partial points are compatible (`Compat`: bounded above in the
descent order) exactly when they share their world and agree wherever
both are defined — the requirement in [kamp-vangenabith-reyle-2011],
Def. 0.26, that the union of chosen points be a function. -/
theorem compat_iff : Compat p q ↔
    p.world = q.world ∧
      ∀ v e e', e ∈ p.assignment v → e' ∈ q.assignment v → e = e' := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hp, hq⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    exact ⟨hp.1.trans hq.1.symm,
      fun v e e' he he' => Part.mem_unique (hp.2 v e he) (hq.2 v e' he')⟩
  · rintro ⟨hw, hag⟩
    exact ⟨p.union q, PartialUnify.mem_upperBounds_pair.mpr
      ⟨le_union_left p q, le_union_right_of_agree hw hag⟩⟩

theorem le_union_right (h : Compat p q) : q ≤ p.union q :=
  have h' := compat_iff.mp h
  le_union_right_of_agree h'.1 h'.2

/-- The union of compatible points is their least upper bound. -/
theorem isLUB_union (h : Compat p q) : IsLUB {p, q} (p.union q) :=
  ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨le_union_left p q, le_union_right h⟩,
    fun _ hu =>
      have h := PartialUnify.mem_upperBounds_pair.mp hu
      union_le h.1 h.2⟩

/-- The union of two points defines the union of their domains. -/
theorem domain_union (p q : Possibility W V (Part M)) :
    (p.union q).domain = p.domain ∪ q.domain := by
  ext v
  by_cases h : (p.assignment v).Dom <;> simp [union, domain, h]

/-- On a shared domain, compatibility is equality. -/
theorem eq_of_compat_of_domain_eq (h : Compat p q) (hdom : p.domain = q.domain) :
    p = q :=
  have hu : (p.union q).domain = p.domain := by rw [domain_union, ← hdom, Set.union_self]
  (eq_of_le_of_domain_eq (le_union_left p q) hu.symm).trans
    (eq_of_le_of_domain_eq (le_union_right h) (hdom.symm.trans hu.symm)).symm

theorem union_assoc (p q v : Possibility W V (Part M)) :
    (p.union q).union v = p.union (q.union v) :=
  Possibility.ext rfl <| funext fun x => by
    by_cases hp : (p.assignment x).Dom <;> by_cases hq : (q.assignment x).Dom <;>
      simp [union, hp, hq]

/-- On compatible points the left precedence of `union` is immaterial. -/
theorem union_comm (h : Compat p q) : p.union q = q.union p :=
  (isLUB_union h).unique (Set.pair_comm p q ▸ isLUB_union h.symm)

/-- A union is compatible with whatever both components are compatible
with. -/
theorem compat_union_left (hpu : Compat p u) (hqu : Compat q u) :
    Compat (p.union q) u := by
  obtain ⟨hpw, hpa⟩ := compat_iff.mp hpu
  obtain ⟨hqw, hqa⟩ := compat_iff.mp hqu
  refine compat_iff.mpr ⟨hpw, fun x e e' he he' => ?_⟩
  simp only [union] at he
  split at he
  · exact hpa x e e' he he'
  · exact hqa x e e' he he'

/-- The left component of a compatible union is compatible. -/
theorem compat_of_union_left (h : Compat (p.union q) u) : Compat p u :=
  h.mono (le_union_left p q) le_rfl

/-- The right component of a compatible union is compatible, given the
components agree. -/
theorem compat_of_union_right (hpq : Compat p q) (h : Compat (p.union q) u) :
    Compat q u :=
  h.mono (le_union_right hpq) le_rfl

/-! ### Restriction and the indexed classification -/

section Restrict

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Set V) (p : Possibility W V (Part M)) : Possibility W V (Part M) :=
  ⟨p.world, fun v => ⟨v ∈ X ∧ (p.assignment v).Dom, fun h => (p.assignment v).get h.2⟩⟩

@[simp] theorem restrict_world (X : Set V) (p : Possibility W V (Part M)) :
    (p.restrict X).world = p.world := rfl

/-- Restriction descends. -/
theorem restrict_le (X : Set V) (p : Possibility W V (Part M)) : p.restrict X ≤ p :=
  ⟨rfl, fun v e he => by
    obtain ⟨⟨-, hd⟩, rfl⟩ := he
    exact Part.get_mem hd⟩

/-- Restriction intersects the domain. -/
theorem domain_restrict (X : Set V) (p : Possibility W V (Part M)) :
    (p.restrict X).domain = X ∩ p.domain :=
  rfl

/-- A point with domain `X` descends into `q` exactly when it is `q`
restricted to `X`. -/
theorem le_iff_eq_restrict {X : Set V} (hp : p.domain = X) :
    p ≤ q ↔ p = q.restrict X := by
  refine ⟨fun h => Possibility.ext h.1 (funext fun v => ?_), fun h => h ▸ restrict_le X q⟩
  refine Part.ext' ⟨fun hd => ⟨hp.subset hd, domain_mono h hd⟩, fun hd => hp.superset hd.1⟩
    fun hd hd' => ?_
  exact Part.mem_unique (h.2 v _ (Part.get_mem hd)) (Part.get_mem hd'.2)

/-- Consecutive restrictions restrict to the intersection. -/
theorem restrict_restrict (X Y : Set V) (p : Possibility W V (Part M)) :
    (p.restrict Y).restrict X = p.restrict (X ∩ Y) :=
  Possibility.ext rfl <| funext fun v =>
    Part.ext' (by simp [restrict, Set.mem_inter_iff, and_assoc]) fun _ _ => rfl

/-- Partial points with domain `X` are exactly world–`X`-assignment
pairs. -/
def domainEquiv (X : Set V) :
    {p : Possibility W V (Part M) // p.domain = X} ≃ W × (X → M) where
  toFun p := (p.1.world, fun v => (p.1.assignment v.1).get (p.2.superset v.2))
  invFun e := ⟨⟨e.1, fun v => ⟨v ∈ X, fun h => e.2 ⟨v, h⟩⟩⟩, rfl⟩
  left_inv p := Subtype.ext <| Possibility.ext rfl <| funext fun _ =>
    Part.ext' ⟨fun hx => p.2.superset hx, fun hd => p.2.subset hd⟩ fun _ _ => rfl
  right_inv _ := rfl

theorem domainEquiv_symm_val (X : Set V) (e : W × (X → M)) :
    ((domainEquiv X).symm e).1 = ⟨e.1, fun v => ⟨v ∈ X, fun h => e.2 ⟨v, h⟩⟩⟩ :=
  rfl

/-- Restricting a classified point restricts its chart. -/
theorem restrict_domainEquiv_symm {Y X : Set V} (h : Y ⊆ X) (e : W × (X → M)) :
    ((domainEquiv X).symm e).1.restrict Y =
      ((domainEquiv Y).symm (e.1, fun v => e.2 ⟨v.1, h v.2⟩)).1 :=
  Possibility.ext rfl <| funext fun _ =>
    Part.ext' ⟨fun hd => hd.1, fun hy => ⟨hy, h hy⟩⟩ fun _ _ =>
      congrArg e.2 (Subtype.ext rfl)

end Restrict

/-! ### Instantiations

Update systems share one form — states are sets of points, updates act
on states — and differ in the point. The parameters select the system:
worlds only gives propositional update semantics ([veltman-1996]; the
`∅`-fiber), assignments only gives lifted DPL, and the general form is
FCS/DRT's pairs. Propositional inquisitive semantics instead *iterates*
the construction — its points are sets of worlds — a level shift, not a
parameter choice. -/

/-- Worlds-only points are bare worlds — the points of propositional
update semantics. -/
def worldEquiv (W M : Type*) : Possibility W Empty M ≃ W where
  toFun p := p.world
  invFun w := ⟨w, Empty.elim⟩
  left_inv _ := Possibility.ext rfl (funext fun v => v.elim)
  right_inv _ := rfl

/-- Assignment-only points are bare assignments — the points of lifted
DPL. -/
def assignmentEquiv (V M : Type*) : Possibility Unit V M ≃ (V → M) where
  toFun p := p.assignment
  invFun g := ⟨(), g⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Possibility

end DynamicSemantics
