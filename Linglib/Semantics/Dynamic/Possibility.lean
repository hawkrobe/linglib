import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Function

/-!
# Possibilities

This file defines a *possibility* — a world paired with an assignment
of discourse referents — and the structure of its partial points: the
descent order, compatibility and union, restriction, and the
classification of each stratum as world–assignment pairs.

## References

- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [kamp-vangenabith-reyle-2011], Def. 22
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

/-- Descent is the canonical order on partial points ([elliott-sudo-2025]
Def. 3.3's descendance, [groenendijk-stokhof-veltman-1996]'s
graph-extension — pointwise, the information order mathlib gives
`Part`): same world, and the larger assignment defined wherever the
smaller is. Every point lies over its own domain, so under descent the
points form the total space of `Category.lean`'s possibilities family. -/
instance : Preorder (Possibility W V (Option M)) where
  le p q := p.world = q.world ∧
    ∀ x e, p.assignment x = some e → q.assignment x = some e
  le_refl _ := ⟨rfl, fun _ _ h => h⟩
  le_trans _ _ _ hpq hqr :=
    ⟨hpq.1.trans hqr.1, fun x e h => hqr.2 x e (hpq.2 x e h)⟩

theorem le_def :
    p ≤ q ↔ p.world = q.world ∧
      ∀ x e, p.assignment x = some e → q.assignment x = some e := Iff.rfl

/-- The domain of a partial point is the set of referents it defines. -/
def dom (p : Possibility W V (Option M)) : Set V :=
  {v | (p.assignment v).isSome}

@[simp] theorem mem_dom {v : V} :
    v ∈ p.dom ↔ (p.assignment v).isSome := Iff.rfl

/-- Descent grows the domain. -/
theorem dom_mono (h : p ≤ q) : p.dom ⊆ q.dom := fun v hv => by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hv
  exact Option.isSome_iff_exists.mpr ⟨e, h.2 v e he⟩

/-- On a shared domain, descent is equality: there is no room to
grow. -/
theorem eq_of_le_of_dom_eq (h : p ≤ q) (hdom : p.dom = q.dom) : p = q := by
  refine Possibility.ext h.1 (funext fun v => ?_)
  rcases hp : p.assignment v with _ | e
  · rcases hq : q.assignment v with _ | e
    · rfl
    · have : v ∈ p.dom := hdom ▸ Option.isSome_iff_exists.mpr ⟨e, hq⟩
      rw [Possibility.mem_dom, hp] at this
      exact absurd this (by simp)
  · exact (h.2 v e hp).symm ▸ rfl

/-- Two partial points are *compatible*: same world, agreeing wherever
both are defined — [kamp-vangenabith-reyle-2011] Def. 26's condition
that the union of chosen points be a function. -/
def Compatible (p q : Possibility W V (Option M)) : Prop :=
  p.world = q.world ∧
    ∀ v e e', p.assignment v = some e → q.assignment v = some e' → e = e'

/-- The union of two points: defined wherever either is, the left
taking precedence (agreement makes the choice immaterial). -/
def union (p q : Possibility W V (Option M)) :
    Possibility W V (Option M) :=
  ⟨p.world, fun v => (p.assignment v).or (q.assignment v)⟩

theorem le_union_left (p q : Possibility W V (Option M)) :
    p ≤ p.union q :=
  ⟨rfl, fun v e h => by simp [union, h]⟩

theorem Compatible.le_union_right (h : p.Compatible q) :
    q ≤ p.union q :=
  ⟨h.1.symm, fun v e hq => by
    rcases hp : p.assignment v with _ | e'
    · simp [union, hp, hq]
    · simp [union, hp, h.2 v e' e hp hq]⟩

/-- On a shared domain, compatibility is equality. -/
theorem Compatible.eq_of_dom_eq (h : p.Compatible q) (hdom : p.dom = q.dom) : p = q := by
  refine Possibility.ext h.1 (funext fun v => ?_)
  rcases hp : p.assignment v with _ | e
  · rcases hq : q.assignment v with _ | e
    · rfl
    · have : v ∈ p.dom := hdom ▸ Option.isSome_iff_exists.mpr ⟨e, hq⟩
      rw [Possibility.mem_dom, hp] at this
      exact absurd this (by simp)
  · rcases hq : q.assignment v with _ | e'
    · have : v ∈ q.dom := hdom ▸ Option.isSome_iff_exists.mpr ⟨e, hp⟩
      rw [Possibility.mem_dom, hq] at this
      exact absurd this (by simp)
    · exact congrArg some (h.2 v e e' hp hq)

/-- Union of points unites domains. -/
theorem dom_union (p q : Possibility W V (Option M)) :
    (p.union q).dom = p.dom ∪ q.dom := by
  ext v
  rcases hp : p.assignment v with _ | e <;> simp [union, dom, hp]

/-- Points below a common point are compatible. -/
theorem compatible_of_le_of_le (hp : p ≤ u) (hq : q ≤ u) : p.Compatible q :=
  ⟨hp.1.trans hq.1.symm, fun v e e' he he' => by
    have h1 := hp.2 v e he
    have h2 := hq.2 v e' he'
    rw [h1] at h2
    exact (Option.some.injEq .. ▸ h2 :)⟩

/-- The union of two lower bounds is a lower bound. -/
theorem union_le (hp : p ≤ u) (hq : q ≤ u) :
    p.union q ≤ u :=
  ⟨hp.1, fun v e h => by
    rcases hpv : p.assignment v with _ | e'
    · exact hq.2 v e (by simpa [union, hpv] using h)
    · have : e' = e := by simpa [union, hpv] using h
      exact this ▸ hp.2 v e' hpv⟩

theorem Compatible.symm (h : p.Compatible q) : q.Compatible p :=
  ⟨h.1.symm, fun v e e' hq hp => (h.2 v e' e hp hq).symm⟩

/-- Union of points is associative. -/
theorem union_assoc (p q v : Possibility W V (Option M)) :
    (p.union q).union v = p.union (q.union v) :=
  Possibility.ext rfl (funext fun _ => Option.or_assoc ..)

/-- On compatible points the left precedence of `union` is
immaterial. -/
theorem Compatible.union_comm (h : p.Compatible q) : p.union q = q.union p :=
  Possibility.ext h.1 (funext fun v => by
    rcases hp : p.assignment v with _ | e <;>
      rcases hq : q.assignment v with _ | e' <;> simp [union, hp, hq]
    exact h.2 v e e' hp hq)

/-- A union is compatible with whatever both components are compatible
with. -/
theorem Compatible.union_left (hpu : p.Compatible u) (hqu : q.Compatible u) :
    (p.union q).Compatible u :=
  ⟨hpu.1, fun x e e' he he' => by
    rcases hp : p.assignment x with _ | c
    · exact hqu.2 x e e' (by simpa [union, hp] using he) he'
    · have hce : c = e := by simpa [union, hp] using he
      exact hce ▸ hpu.2 x c e' hp he'⟩

/-- The left component of a compatible union is compatible. -/
theorem Compatible.left_of_union
    (h : (p.union q).Compatible u) : p.Compatible u :=
  ⟨h.1, fun x e e' hp hv => h.2 x e e' (by simp [union, hp]) hv⟩

/-- The right component of a compatible union is compatible, given the
components agree. -/
theorem Compatible.right_of_union
    (hpq : p.Compatible q) (h : (p.union q).Compatible u) :
    q.Compatible u :=
  ⟨hpq.1.symm.trans h.1, fun x e e' hq hv => by
    rcases hp : p.assignment x with _ | c
    · exact h.2 x e e' (by simp [union, hp, hq]) hv
    · exact hpq.2 x c e hp hq ▸ h.2 x c e' (by simp [union, hp]) hv⟩

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
theorem dom_restrict (X : Set V) [∀ v, Decidable (v ∈ X)]
    (p : Possibility W V (Option M)) :
    (p.restrict X).dom = X ∩ p.dom := by
  ext v
  by_cases hv : v ∈ X <;> simp [restrict, dom, hv]

/-- Descent out of a stratum is *being the restriction*: for `p` at
`X`, `p` grows into `q` exactly when `p` is `q` cut to `X`. The
hom-characterization of the fibred order. -/
theorem le_iff_eq_restrict {X : Set V} [∀ v, Decidable (v ∈ X)]
    (hp : p.dom = X) :
    p ≤ q ↔ p = q.restrict X := by
  constructor
  · intro h
    refine Possibility.ext h.1 (funext fun v => ?_)
    by_cases hv : v ∈ X
    · have hsome : (p.assignment v).isSome :=
        (Set.ext_iff.mp hp v).mpr hv
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
      rw [he]
      simp only [restrict, if_pos hv]
      exact (h.2 v e he).symm
    · have hnone : p.assignment v = none :=
        Option.not_isSome_iff_eq_none.mp
          fun hs => hv ((Set.ext_iff.mp hp v).mp hs)
      rw [hnone]
      simp [restrict, hv]
  · rintro rfl
    exact restrict_le X q

/-- Restriction is pointwise idempotent along intersections. -/
theorem restrict_restrict (X Y : Set V) [∀ v, Decidable (v ∈ X)]
    [∀ v, Decidable (v ∈ Y)] (p : Possibility W V (Option M)) :
    (p.restrict Y).restrict X = p.restrict (X ∩ Y) := by
  refine Possibility.ext rfl (funext fun v => ?_)
  by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;>
    simp [restrict, hx, hy]

/-- Partial points with domain `X` are world–`X`-assignment pairs —
constructively: the classification that the total-assignment rendering
recovered only with choice and an inhabitant of `M`. -/
def domEquiv (X : Set V) [∀ v, Decidable (v ∈ X)] :
    {p : Possibility W V (Option M) // p.dom = X} ≃ W × (X → M) where
  toFun p :=
    (p.1.world, fun v => (p.1.assignment v.1).get
      ((Set.ext_iff.mp p.2 v.1).mpr v.2))
  invFun e :=
    ⟨⟨e.1, fun v => if h : v ∈ X then some (e.2 ⟨v, h⟩)
      else none⟩, by
      ext v
      by_cases h : v ∈ X <;> simp [dom, h]⟩
  left_inv p := by
    obtain ⟨⟨w, g⟩, hp⟩ := p
    refine Subtype.ext (Possibility.ext rfl (funext fun v => ?_))
    by_cases h : v ∈ X
    · simp only [dif_pos h, Option.some_get]
    · have hnone : g v = none := Option.not_isSome_iff_eq_none.mp
        fun hs => h ((Set.ext_iff.mp hp v).mp hs)
      simp only [dif_neg h]
      exact hnone.symm
  right_inv e := by
    refine Prod.ext rfl (funext fun v => ?_)
    simp

theorem domEquiv_symm_val (X : Set V) [∀ v, Decidable (v ∈ X)]
    (e : W × (X → M)) :
    ((domEquiv X).symm e).1 =
      ⟨e.1, fun v => if h : v ∈ X then some (e.2 ⟨v, h⟩)
        else none⟩ :=
  rfl

/-- The charts commute with restriction: restricting a classified point
is weakening its chart. -/
theorem restrict_domEquiv_symm {Y X : Set V} [∀ v, Decidable (v ∈ X)]
    [∀ v, Decidable (v ∈ Y)] (h : Y ⊆ X) (e : W × (X → M)) :
    ((domEquiv X).symm e).1.restrict Y =
      ((domEquiv Y).symm (e.1, fun v => e.2 ⟨v.1, h v.2⟩)).1 := by
  rw [domEquiv_symm_val, domEquiv_symm_val]
  refine Possibility.ext rfl (funext fun v => ?_)
  by_cases hv : v ∈ Y
  · have hvX : v ∈ X := h hv
    simp [restrict, hv, hvX]
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

/-- Worlds-only points: propositional update semantics. -/
def worldEquiv (W M : Type*) : Possibility W Empty M ≃ W where
  toFun p := p.world
  invFun w := ⟨w, Empty.elim⟩
  left_inv _ := Possibility.ext rfl (funext fun v => v.elim)
  right_inv _ := rfl

/-- Assignments-only points: lifted DPL. -/
def assignmentEquiv (V M : Type*) : Possibility Unit V M ≃ (V → M) where
  toFun p := p.assignment
  invFun g := ⟨(), g⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Possibility

end DynamicSemantics
