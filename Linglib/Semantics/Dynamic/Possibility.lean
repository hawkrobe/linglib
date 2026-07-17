import Linglib.Core.Order.Flat
import Mathlib.Data.Set.Function

/-!
# Possibilities

This file defines a *possibility* — a world paired with an assignment
of discourse referents — and the structure of its partial points: the
descent order, compatibility and union, restriction, and the
classification of each stratum as world–assignment pairs.

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

variable {p q u : Possibility W V (Option M)}

/-- A partial point lies below another in the *descent* order when they
share their world and the assignments grow pointwise in the flat
information order ([elliott-sudo-2025], Def. 3.3). -/
instance : PartialOrder (Possibility W V (Option M)) where
  le p q := p.world = q.world ∧ ∀ x, (p.assignment x).FlatLE (q.assignment x)
  le_refl _ := ⟨rfl, fun _ => .refl _⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, fun x => (hpq.2 x).trans (hqr.2 x)⟩
  le_antisymm _ _ hpq hqp :=
    Possibility.ext hpq.1 (funext fun x => (hpq.2 x).antisymm (hqp.2 x))

theorem le_def : p ≤ q ↔ p.world = q.world ∧ ∀ x, (p.assignment x).FlatLE (q.assignment x) :=
  Iff.rfl

/-- The domain of a partial point is the set of referents it defines. -/
def domain (p : Possibility W V (Option M)) : Set V :=
  {v | (p.assignment v).isSome}

@[simp] theorem mem_domain {v : V} :
    v ∈ p.domain ↔ (p.assignment v).isSome := Iff.rfl

/-- Descent grows the domain. -/
theorem domain_mono (h : p ≤ q) : p.domain ⊆ q.domain := fun v => (h.2 v).isSome_mono

/-- On a shared domain, descent is equality — there is no room to grow. -/
theorem eq_of_le_of_domain_eq (h : p ≤ q) (hdom : p.domain = q.domain) : p = q :=
  Possibility.ext h.1 <| funext fun v => (h.2 v).eq_of_isSome fun hv => hdom.superset hv

/-- Two partial points are *compatible* if they share their world and
agree wherever both are defined — the requirement in
[kamp-vangenabith-reyle-2011], Def. 0.26, that the union of chosen
points be a function. Equivalently, the pair is bounded above in the
descent order (`compatible_iff_bddAbove`). -/
def Compatible (p q : Possibility W V (Option M)) : Prop :=
  p.world = q.world ∧
    ∀ v e e', p.assignment v = some e → q.assignment v = some e' → e = e'

theorem Compatible.symm (h : p.Compatible q) : q.Compatible p :=
  ⟨h.1.symm, fun v e e' hq hp => (h.2 v e' e hp hq).symm⟩

/-- The union of two points, defined wherever either is, with the left
taking precedence; on compatible points the precedence is immaterial
(`Compatible.union_comm`). -/
def union (p q : Possibility W V (Option M)) : Possibility W V (Option M) :=
  ⟨p.world, fun v => (p.assignment v).or (q.assignment v)⟩

theorem le_union_left (p q : Possibility W V (Option M)) : p ≤ p.union q :=
  ⟨rfl, fun v e h => by simp [union, Option.mem_def.mp h]⟩

theorem Compatible.le_union_right (h : p.Compatible q) : q ≤ p.union q :=
  ⟨h.1.symm, fun v e hq => by
    rcases hp : p.assignment v with _ | e'
    · simpa [union, hp] using hq
    · simpa [union, hp] using h.2 v e' e hp (Option.mem_def.mp hq)⟩

theorem union_le (hp : p ≤ u) (hq : q ≤ u) : p.union q ≤ u :=
  ⟨hp.1, fun v e h => by
    rcases hpv : p.assignment v with _ | e'
    · exact hq.2 v e (by simpa [union, hpv] using h)
    · obtain rfl : e' = e := by simpa [union, hpv] using h
      exact hp.2 v e' hpv⟩

/-- Points below a common point are compatible. -/
theorem compatible_of_le_of_le (hp : p ≤ u) (hq : q ≤ u) : p.Compatible q :=
  ⟨hp.1.trans hq.1.symm, fun v e e' he he' =>
    Option.some_injective M ((Option.mem_def.mp (hp.2 v e he)).symm.trans
      (Option.mem_def.mp (hq.2 v e' he')))⟩

/-- The union of compatible points is their least upper bound. -/
theorem Compatible.isLUB_union (h : p.Compatible q) : IsLUB {p, q} (p.union q) :=
  ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨le_union_left p q, h.le_union_right⟩,
    fun _ hu =>
      have h := PartialUnify.mem_upperBounds_pair.mp hu
      union_le h.1 h.2⟩

/-- Compatibility is boundedness above in the descent order — the
consistency relation `Compat` of the unification substrate. -/
theorem compatible_iff_bddAbove : p.Compatible q ↔ BddAbove {p, q} :=
  ⟨fun h => ⟨p.union q, h.isLUB_union.1⟩, fun ⟨_, hu⟩ =>
    have h := PartialUnify.mem_upperBounds_pair.mp hu
    compatible_of_le_of_le h.1 h.2⟩

/-- On a shared domain, compatibility is equality. -/
theorem Compatible.eq_of_domain_eq (h : p.Compatible q)
    (hdom : p.domain = q.domain) : p = q :=
  eq_of_le_of_domain_eq
    ⟨h.1, fun v e hv => by
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
        (hdom.subset (Option.isSome_iff_exists.mpr ⟨e, hv⟩))
      exact (h.2 v e e' hv he').symm ▸ he'⟩
    hdom

/-- The union of two points defines the union of their domains. -/
theorem domain_union (p q : Possibility W V (Option M)) :
    (p.union q).domain = p.domain ∪ q.domain := by
  ext v
  rcases hp : p.assignment v with _ | e <;> simp [union, domain, hp]

theorem union_assoc (p q v : Possibility W V (Option M)) :
    (p.union q).union v = p.union (q.union v) :=
  Possibility.ext rfl (funext fun _ => Option.or_assoc ..)

/-- On compatible points the left precedence of `union` is immaterial. -/
theorem Compatible.union_comm (h : p.Compatible q) : p.union q = q.union p :=
  Possibility.ext h.1 <| funext fun v => by
    rcases hp : p.assignment v with _ | e <;> rcases hq : q.assignment v with _ | e' <;>
      simp [union, hp, hq]
    exact h.2 v e e' hp hq

/-- A union is compatible with whatever both components are compatible
with. -/
theorem Compatible.union_left (hpu : p.Compatible u) (hqu : q.Compatible u) :
    (p.union q).Compatible u :=
  ⟨hpu.1, fun x e e' he he' => by
    rcases hp : p.assignment x with _ | c
    · exact hqu.2 x e e' (by simpa [union, hp] using he) he'
    · obtain rfl : c = e := by simpa [union, hp] using he
      exact hpu.2 x c e' hp he'⟩

/-- The left component of a compatible union is compatible. -/
theorem Compatible.left_of_union
    (h : (p.union q).Compatible u) : p.Compatible u :=
  ⟨h.1, fun x e e' hp hu => h.2 x e e' (by simp [union, hp]) hu⟩

/-- The right component of a compatible union is compatible, given the
components agree. -/
theorem Compatible.right_of_union
    (hpq : p.Compatible q) (h : (p.union q).Compatible u) :
    q.Compatible u :=
  ⟨hpq.1.symm.trans h.1, fun x e e' hq hu => by
    rcases hp : p.assignment x with _ | c
    · exact h.2 x e e' (by simp [union, hp, hq]) hu
    · exact hpq.2 x c e hp hq ▸ h.2 x c e' (by simp [union, hp]) hu⟩

/-! ### Restriction and the indexed classification -/

section Restrict

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Set V) [∀ v, Decidable (v ∈ X)]
    (p : Possibility W V (Option M)) : Possibility W V (Option M) :=
  ⟨p.world, fun v => if v ∈ X then p.assignment v else none⟩

@[simp] theorem restrict_world (X : Set V) [∀ v, Decidable (v ∈ X)]
    (p : Possibility W V (Option M)) :
    (p.restrict X).world = p.world := rfl

/-- Restriction descends. -/
theorem restrict_le (X : Set V) [∀ v, Decidable (v ∈ X)]
    (p : Possibility W V (Option M)) : p.restrict X ≤ p :=
  ⟨rfl, fun x e h => by
    by_cases hx : x ∈ X
    · simpa [restrict, hx] using h
    · simp [restrict, hx] at h⟩

/-- Restriction intersects the domain. -/
theorem domain_restrict (X : Set V) [∀ v, Decidable (v ∈ X)]
    (p : Possibility W V (Option M)) :
    (p.restrict X).domain = X ∩ p.domain := by
  ext v
  by_cases hv : v ∈ X <;> simp [restrict, domain, hv]

/-- A point with domain `X` descends into `q` exactly when it is `q`
restricted to `X`. -/
theorem le_iff_eq_restrict {X : Set V} [∀ v, Decidable (v ∈ X)]
    (hp : p.domain = X) :
    p ≤ q ↔ p = q.restrict X := by
  refine ⟨fun h => Possibility.ext h.1 (funext fun v => ?_), fun h => h ▸ restrict_le X q⟩
  by_cases hv : v ∈ X
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hp.superset hv)
    simp only [restrict, if_pos hv]
    exact he.trans (Option.mem_def.mp (h.2 v e he)).symm
  · rw [Option.not_isSome_iff_eq_none.mp fun hs => hv (hp.subset hs)]
    simp [restrict, hv]

/-- Consecutive restrictions restrict to the intersection. -/
theorem restrict_restrict (X Y : Set V) [∀ v, Decidable (v ∈ X)]
    [∀ v, Decidable (v ∈ Y)] (p : Possibility W V (Option M)) :
    (p.restrict Y).restrict X = p.restrict (X ∩ Y) :=
  Possibility.ext rfl <| funext fun v => by
    by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [restrict, hx, hy]

/-- Partial points with domain `X` are exactly world–`X`-assignment
pairs. -/
def domainEquiv (X : Set V) [∀ v, Decidable (v ∈ X)] :
    {p : Possibility W V (Option M) // p.domain = X} ≃ W × (X → M) where
  toFun p := (p.1.world, fun v => (p.1.assignment v.1).get (p.2.superset v.2))
  invFun e :=
    ⟨⟨e.1, fun v => if h : v ∈ X then some (e.2 ⟨v, h⟩) else none⟩, by
      ext v
      by_cases h : v ∈ X <;> simp [domain, h]⟩
  left_inv p := Subtype.ext <| Possibility.ext rfl <| funext fun v => by
    by_cases h : v ∈ X
    · simp only [dif_pos h, Option.some_get]
    · exact (dif_neg h).trans
        (Option.not_isSome_iff_eq_none.mp fun hs => h (p.2.subset hs)).symm
  right_inv e := Prod.ext rfl (funext fun v => by simp)

theorem domainEquiv_symm_val (X : Set V) [∀ v, Decidable (v ∈ X)]
    (e : W × (X → M)) :
    ((domainEquiv X).symm e).1 =
      ⟨e.1, fun v => if h : v ∈ X then some (e.2 ⟨v, h⟩) else none⟩ :=
  rfl

/-- Restricting a classified point restricts its chart. -/
theorem restrict_domainEquiv_symm {Y X : Set V} [∀ v, Decidable (v ∈ X)]
    [∀ v, Decidable (v ∈ Y)] (h : Y ⊆ X) (e : W × (X → M)) :
    ((domainEquiv X).symm e).1.restrict Y =
      ((domainEquiv Y).symm (e.1, fun v => e.2 ⟨v.1, h v.2⟩)).1 := by
  rw [domainEquiv_symm_val, domainEquiv_symm_val]
  refine Possibility.ext rfl (funext fun v => ?_)
  by_cases hv : v ∈ Y
  · simp [restrict, hv, h hv]
  · simp [restrict, hv]

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
