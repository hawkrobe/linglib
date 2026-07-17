import Linglib.Core.Data.Part
import Linglib.Core.Order.PartialUnify
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Basic

/-!
# Possibilities

This file defines a *possibility* — a world paired with an assignment
of discourse referents — and the structure of its partial points, with
`Part`-valued assignments (partial functions `V →. M`): the descent
order, compatibility and union, restriction, and the classification of
each stratum as world–assignment pairs.

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

variable {p q r u : Possibility W V (Part M)}

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
  PFun.Dom p.assignment

@[simp] theorem mem_domain {v : V} :
    v ∈ p.domain ↔ (p.assignment v).Dom := Iff.rfl

/-- Descent grows the domain. -/
theorem domain_mono (h : p ≤ q) : p.domain ⊆ q.domain := fun v =>
  Part.dom_mono (h.2 v)

/-- On a shared domain, descent is equality — there is no room to grow. -/
theorem eq_of_le_of_domain_eq (h : p ≤ q) (hdom : p.domain = q.domain) : p = q :=
  Possibility.ext h.1 <| funext fun v =>
    Part.eq_of_le_of_dom (h.2 v) fun hd => hdom.superset hd

/-- A point defines no referent exactly when its assignment is nowhere
defined. -/
theorem domain_eq_empty_iff : p.domain = ∅ ↔ ∀ v, p.assignment v = ⊥ := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_domain]
  exact forall_congr' fun v => Part.eq_none_iff'.symm

/-- The union of two points, defined wherever either is, with the left
taking precedence; on compatible points the precedence is immaterial
(`union_comm`). -/
noncomputable def union (p q : Possibility W V (Part M)) : Possibility W V (Part M) :=
  ⟨p.world, fun v => (p.assignment v).or (q.assignment v)⟩

@[simp] theorem union_world : (p.union q).world = p.world := rfl

@[simp] theorem union_assignment (v : V) :
    (p.union q).assignment v = (p.assignment v).or (q.assignment v) := rfl

theorem le_union_left : p ≤ p.union q :=
  ⟨rfl, fun _ => Part.le_or_left⟩

theorem union_le (hp : p ≤ u) (hq : q ≤ u) : p.union q ≤ u :=
  ⟨hp.1, fun v => Part.or_le (hp.2 v) (hq.2 v)⟩

/-- Compatibility of partial points is worldwise and pointwise. -/
theorem compat_iff_forall : Compat p q ↔
    p.world = q.world ∧ ∀ v, Compat (p.assignment v) (q.assignment v) :=
  ⟨fun ⟨_, hu⟩ =>
    have ⟨hp, hq⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    ⟨hp.1.trans hq.1.symm, fun v => .of_le (hp.2 v) (hq.2 v)⟩,
   fun ⟨hw, hc⟩ => .of_le le_union_left
    ⟨hw.symm, fun v => Part.le_or_right (hc v)⟩⟩

/-- Two partial points are compatible (`Compat`: bounded above in the
descent order) exactly when they share their world and agree wherever
both are defined — the requirement in [kamp-vangenabith-reyle-2011],
Def. 0.26, that the union of chosen points be a function. -/
theorem compat_iff : Compat p q ↔
    p.world = q.world ∧
      ∀ v e e', e ∈ p.assignment v → e' ∈ q.assignment v → e = e' := by
  simp only [compat_iff_forall, Part.compat_iff]

theorem le_union_right (h : Compat p q) : q ≤ p.union q :=
  have h' := compat_iff_forall.mp h
  ⟨h'.1.symm, fun v => Part.le_or_right (h'.2 v)⟩

/-- The union of compatible points is their least upper bound. -/
theorem isLUB_union (h : Compat p q) : IsLUB {p, q} (p.union q) :=
  ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨le_union_left, le_union_right h⟩,
    fun _ hu =>
      have h := PartialUnify.mem_upperBounds_pair.mp hu
      union_le h.1 h.2⟩

/-- The joins of pairs of points: `u` bounds `{p, q}` least exactly when
the pair is compatible and `u` is its union. -/
theorem isLUB_pair_iff : IsLUB {p, q} u ↔ Compat p q ∧ u = p.union q :=
  ⟨fun h =>
    have hc : Compat p q := ⟨u, h.1⟩
    ⟨hc, ((isLUB_union hc).unique h).symm⟩,
   fun ⟨hc, hu⟩ => hu ▸ isLUB_union hc⟩

/-- The union of two points defines the union of their domains. -/
theorem domain_union : (p.union q).domain = p.domain ∪ q.domain := by
  ext v; simp

/-- On a shared domain, compatibility is equality. -/
theorem eq_of_compat_of_domain_eq (h : Compat p q) (hdom : p.domain = q.domain) :
    p = q :=
  have hu : (p.union q).domain = p.domain := by rw [domain_union, ← hdom, Set.union_self]
  (eq_of_le_of_domain_eq le_union_left hu.symm).trans
    (eq_of_le_of_domain_eq (le_union_right h) (hdom.symm.trans hu.symm)).symm

theorem union_assoc : (p.union q).union r = p.union (q.union r) :=
  Possibility.ext rfl <| funext fun _ => Part.or_assoc

@[simp] theorem union_self : p.union p = p :=
  Possibility.ext rfl <| funext fun _ => Part.or_self

/-- On compatible points the left precedence of `union` is immaterial. -/
theorem union_comm (h : Compat p q) : p.union q = q.union p :=
  (isLUB_union h).unique (Set.pair_comm p q ▸ isLUB_union h.symm)

/-! ### The empty point -/

/-- The empty point at a world: no referent defined. -/
def bot (w : W) : Possibility W V (Part M) :=
  ⟨w, fun _ => ⊥⟩

theorem bot_le : bot p.world ≤ p :=
  ⟨rfl, fun _ => _root_.bot_le⟩

/-- An empty point compatible with `p` shares its world, hence sits
below it. -/
theorem bot_le_of_compat {w : W} (h : Compat p (bot w)) : bot w ≤ p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨hpu, hbu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
  rw [show w = p.world from hbu.1.trans hpu.1.symm]
  exact bot_le

@[simp] theorem union_bot {w : W} : p.union (bot w) = p :=
  Possibility.ext rfl <| funext fun _ => Part.or_bot

@[simp] theorem domain_bot {w : W} : (bot w : Possibility W V (Part M)).domain = ∅ :=
  domain_eq_empty_iff.mpr fun _ => rfl

/-! ### Restriction and the indexed classification -/

section Restrict

variable {X Y : Set V}

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Set V) (p : Possibility W V (Part M)) : Possibility W V (Part M) :=
  ⟨p.world, fun v => ⟨v ∈ X ∧ (p.assignment v).Dom, fun h => (p.assignment v).get h.2⟩⟩

@[simp] theorem restrict_world : (p.restrict X).world = p.world := rfl

/-- Restriction descends. -/
theorem restrict_le : p.restrict X ≤ p :=
  ⟨rfl, fun v e he => by
    obtain ⟨⟨-, hd⟩, rfl⟩ := he
    exact Part.get_mem hd⟩

/-- Restriction intersects the domain. -/
theorem domain_restrict : (p.restrict X).domain = X ∩ p.domain :=
  rfl

/-- A point with domain `X` descends into `q` exactly when it is `q`
restricted to `X`. -/
theorem le_iff_eq_restrict (hp : p.domain = X) :
    p ≤ q ↔ p = q.restrict X := by
  refine ⟨fun h => Possibility.ext h.1 (funext fun v => ?_), fun h => h ▸ restrict_le⟩
  refine Part.ext' ⟨fun hd => ⟨hp.subset hd, domain_mono h hd⟩, fun hd => hp.superset hd.1⟩
    fun hd hd' => ?_
  exact Part.mem_unique (h.2 v _ (Part.get_mem hd)) (Part.get_mem hd'.2)

/-- Consecutive restrictions restrict to the intersection. -/
theorem restrict_restrict : (p.restrict Y).restrict X = p.restrict (X ∩ Y) :=
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

/-- Restricting a classified point restricts its chart. -/
theorem restrict_domainEquiv_symm (h : Y ⊆ X) (e : W × (X → M)) :
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
