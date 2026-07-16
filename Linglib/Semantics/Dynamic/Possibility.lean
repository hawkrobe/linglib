import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Setoid.Basic

/-!
# Possibilities

A *possibility* is a world paired with an assignment of discourse
referents — the point type of dynamic semantics. Indexed information
states over possibilities live in `State.lean`; unindexed states are plain
sets of possibilities, with the generic level-0 CCP algebra in
`Update.lean`.

*Possibility* is the update-semantics tradition's word:
[groenendijk-stokhof-veltman-1996]'s possibilities are triples carrying a
referent system ([vermeulen-1995]) we do not; [elliott-sudo-2025]'s are
world–assignment pairs like ours. [kamp-vangenabith-reyle-2011] leaves the
pairs of its Def. 22 unnamed — DRT's word for the assignment is
*(verifying) embedding*, a partial function on referents with one
universe across worlds — and the monadic tradition calls the same points
*indices* ([charlow-2025-staged-updates]).

## Main definitions

- `Possibility W V M`: the point object; `Possibility.update` rewrites
  one referent.
- `Possibility.agreeSetoid X`: agreement at granularity `X`, as the
  kernel of the projection `Possibility.proj X`; quotienting by it is
  the state space at granularity `X` (`Collapse.lean`).
- `Possibility.dom`, `Possibility.Descendant`, `Possibility.Compatible`,
  `Possibility.union`: partial points (`Option`-valued assignments) —
  their defined referents, growth order, and consistent union.
- `Possibility.restrict`, `Possibility.domEquiv`: domain restriction and
  the constructive classification of the domain-`X` points as
  world–`X`-environment pairs.

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

variable {W V M : Type*} (X : Set V)

/-- The projection of a possibility to granularity `X` is its world
together with its assignment of the `X`-referents. -/
def proj (p : Possibility W V M) : W × (X → M) :=
  (p.world, X.restrict p.assignment)

/-- Two possibilities agree at granularity `X` when their projections to
`X` coincide. -/
def agreeSetoid : Setoid (Possibility W V M) :=
  Setoid.ker (proj X)

variable {X} in
/-- Possibilities agree at `X` exactly when they share their world and
their assignments agree on `X`. -/
theorem agreeSetoid_iff {p q : Possibility W V M} :
    agreeSetoid X p q ↔
      p.world = q.world ∧ Set.EqOn p.assignment q.assignment X :=
  Prod.ext_iff.trans (and_congr Iff.rfl Set.restrict_eq_restrict_iff)

/-- Coarser granularities identify more possibilities. -/
theorem agreeSetoid_anti :
    Antitone (agreeSetoid : Set V → Setoid (Possibility W V M)) :=
  fun _ _ hXY _ _ h =>
    have h' := agreeSetoid_iff.mp h
    agreeSetoid_iff.mpr ⟨h'.1, h'.2.mono hXY⟩

/-- A possibility up to agreement at `X` is a world together with an
assignment of the `X`-referents. -/
noncomputable def agreeQuotientEquiv [Nonempty M] :
    Quotient (agreeSetoid (W := W) (M := M) X) ≃ W × (X → M) :=
  Setoid.quotientKerEquivOfRightInverse (proj X)
    (fun wf => ⟨wf.1,
      Function.extend Subtype.val wf.2 fun _ => Classical.arbitrary M⟩)
    fun wf => Prod.ext rfl (funext fun x => by
      exact Subtype.val_injective.extend_apply wf.2
        (fun _ => Classical.arbitrary M) x)

@[simp] theorem agreeQuotientEquiv_mk [Nonempty M]
    (p : Possibility W V M) :
    agreeQuotientEquiv X (Quotient.mk _ p) = (p.world, X.restrict p.assignment) :=
  rfl

/-- Update the assignment at a single referent. -/
def update [DecidableEq V] (p : Possibility W V M) (x : V) (e : M) :
    Possibility W V M :=
  { p with assignment := Function.update p.assignment x e }

@[simp] theorem update_self [DecidableEq V] (p : Possibility W V M)
    (x : V) (e : M) : (p.update x e).assignment x = e :=
  Function.update_self ..

@[simp] theorem update_of_ne [DecidableEq V] (p : Possibility W V M)
    {x y : V} (e : M) (h : y ≠ x) :
    (p.update x e).assignment y = p.assignment y :=
  Function.update_of_ne h ..

@[simp] theorem update_world [DecidableEq V] (p : Possibility W V M)
    (x : V) (e : M) : (p.update x e).world = p.world := rfl

/-! ### Partial points -/

/-- The referents a partial point defines —
[kamp-vangenabith-reyle-2011] Def. 23's `Dom(f)`. -/
def dom (p : Possibility W V (Option M)) : Set V :=
  {v | (p.assignment v).isSome}

@[simp] theorem mem_dom {p : Possibility W V (Option M)} {v : V} :
    v ∈ p.dom ↔ (p.assignment v).isSome := Iff.rfl

/-- `q` is a *descendant* of `p` ([elliott-sudo-2025], Def. 3.3): same
world, and `q`'s assignment extends `p`'s wherever the latter is defined
([groenendijk-stokhof-veltman-1996]'s graph-extension — pointwise, the
information order mathlib gives `Part`). -/
def Descendant (p q : Possibility W V (Option M)) : Prop :=
  p.world = q.world ∧ ∀ x e, p.assignment x = some e → q.assignment x = some e

theorem Descendant.refl (p : Possibility W V (Option M)) :
    p.Descendant p :=
  ⟨rfl, fun _ _ h => h⟩

theorem Descendant.trans {p q r : Possibility W V (Option M)}
    (hpq : p.Descendant q) (hqr : q.Descendant r) : p.Descendant r :=
  ⟨hpq.1.trans hqr.1, fun x e h => hqr.2 x e (hpq.2 x e h)⟩

/-- Descendance grows the domain. -/
theorem Descendant.dom_subset {p q : Possibility W V (Option M)}
    (h : p.Descendant q) : p.dom ⊆ q.dom := fun v hv => by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hv
  exact Option.isSome_iff_exists.mpr ⟨e, h.2 v e he⟩

/-- On a shared domain, descendance is equality: there is no room to
grow. -/
theorem Descendant.eq_of_dom_eq {p q : Possibility W V (Option M)}
    (h : p.Descendant q) (hdom : p.dom = q.dom) : p = q := by
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

theorem left_descendant_union (p q : Possibility W V (Option M)) :
    p.Descendant (p.union q) :=
  ⟨rfl, fun v e h => by simp [union, h]⟩

theorem Compatible.right_descendant_union
    {p q : Possibility W V (Option M)} (h : p.Compatible q) :
    q.Descendant (p.union q) :=
  ⟨h.1.symm, fun v e hq => by
    rcases hp : p.assignment v with _ | e'
    · simp [union, hp, hq]
    · simp [union, hp, h.2 v e' e hp hq]⟩

/-- On a shared domain, compatibility is equality. -/
theorem Compatible.eq_of_dom_eq {p q : Possibility W V (Option M)}
    (h : p.Compatible q) (hdom : p.dom = q.dom) : p = q := by
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

/-- Common ancestors are compatible. -/
theorem Descendant.compatible {p q u : Possibility W V (Option M)}
    (hp : p.Descendant u) (hq : q.Descendant u) : p.Compatible q :=
  ⟨hp.1.trans hq.1.symm, fun v e e' he he' => by
    have h1 := hp.2 v e he
    have h2 := hq.2 v e' he'
    rw [h1] at h2
    exact (Option.some.injEq .. ▸ h2 :)⟩

/-- The union of two ancestors is an ancestor. -/
theorem Descendant.union_descendant {p q u : Possibility W V (Option M)}
    (hp : p.Descendant u) (hq : q.Descendant u) :
    (p.union q).Descendant u :=
  ⟨hp.1, fun v e h => by
    rcases hpv : p.assignment v with _ | e'
    · exact hq.2 v e (by simpa [union, hpv] using h)
    · have : e' = e := by simpa [union, hpv] using h
      exact this ▸ hp.2 v e' hpv⟩

theorem Compatible.symm {p q : Possibility W V (Option M)}
    (h : p.Compatible q) : q.Compatible p :=
  ⟨h.1.symm, fun v e e' hq hp => (h.2 v e' e hp hq).symm⟩

/-- Union of points is associative. -/
theorem union_assoc (p q v : Possibility W V (Option M)) :
    (p.union q).union v = p.union (q.union v) :=
  Possibility.ext rfl (funext fun _ => Option.or_assoc ..)

/-- On compatible points the left precedence of `union` is
immaterial. -/
theorem Compatible.union_comm {p q : Possibility W V (Option M)}
    (h : p.Compatible q) : p.union q = q.union p :=
  Possibility.ext h.1 (funext fun v => by
    rcases hp : p.assignment v with _ | e <;>
      rcases hq : q.assignment v with _ | e' <;> simp [union, hp, hq]
    exact h.2 v e e' hp hq)

/-- A union is compatible with whatever both components are compatible
with. -/
theorem Compatible.union_left {p q v : Possibility W V (Option M)}
    (hpv : p.Compatible v) (hqv : q.Compatible v) :
    (p.union q).Compatible v :=
  ⟨hpv.1, fun x e e' he he' => by
    rcases hp : p.assignment x with _ | c
    · exact hqv.2 x e e' (by simpa [union, hp] using he) he'
    · have hce : c = e := by simpa [union, hp] using he
      exact hce ▸ hpv.2 x c e' hp he'⟩

/-- The left component of a compatible union is compatible. -/
theorem Compatible.left_of_union {p q v : Possibility W V (Option M)}
    (h : (p.union q).Compatible v) : p.Compatible v :=
  ⟨h.1, fun x e e' hp hv => h.2 x e e' (by simp [union, hp]) hv⟩

/-- The right component of a compatible union is compatible, given the
components agree. -/
theorem Compatible.right_of_union {p q v : Possibility W V (Option M)}
    (hpq : p.Compatible q) (h : (p.union q).Compatible v) :
    q.Compatible v :=
  ⟨hpq.1.symm.trans h.1, fun x e e' hq hv => by
    rcases hp : p.assignment x with _ | c
    · exact h.2 x e e' (by simp [union, hp, hq]) hv
    · exact hpq.2 x c e hp hq ▸ h.2 x c e' (by simp [union, hp]) hv⟩

/-! ### Restriction and the indexed classification -/

section Restrict

variable [DecidableEq V]

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Finset V) (p : Possibility W V (Option M)) :
    Possibility W V (Option M) :=
  ⟨p.world, fun v => if v ∈ X then p.assignment v else none⟩

@[simp] theorem restrict_world (X : Finset V)
    (p : Possibility W V (Option M)) :
    (p.restrict X).world = p.world := rfl

/-- Restriction is an ancestor. -/
theorem restrict_descendant (X : Finset V)
    (p : Possibility W V (Option M)) : (p.restrict X).Descendant p :=
  ⟨rfl, fun x e h => by
    by_cases hx : x ∈ X
    · simpa [restrict, hx] using h
    · simp [restrict, hx] at h⟩

/-- Restriction intersects the domain. -/
theorem dom_restrict (X : Finset V) (p : Possibility W V (Option M)) :
    (p.restrict X).dom = ↑X ∩ p.dom := by
  ext v
  by_cases hv : v ∈ X <;> simp [restrict, dom, hv]

/-- Descendance out of a stratum is *being the restriction*: for `p` at
`X`, `p` grows into `q` exactly when `p` is `q` cut to `X`. The
hom-characterization of the fibred order. -/
theorem descendant_iff_eq_restrict {X : Finset V}
    {p q : Possibility W V (Option M)} (hp : p.dom = (↑X : Set V)) :
    p.Descendant q ↔ p = q.restrict X := by
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
    exact restrict_descendant X q

/-- Restriction is pointwise idempotent along intersections. -/
theorem restrict_restrict (X Y : Finset V)
    (p : Possibility W V (Option M)) :
    (p.restrict Y).restrict X = p.restrict (X ∩ Y) := by
  refine Possibility.ext rfl (funext fun v => ?_)
  by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;>
    simp [restrict, hx, hy]

/-- Partial points with domain `X` are world–`X`-environment pairs —
constructively: the classification that the total-assignment rendering
recovered only with choice and an inhabitant of `M`. -/
def domEquiv (X : Finset V) :
    {p : Possibility W V (Option M) // p.dom = (↑X : Set V)} ≃
      W × ((↑X : Set V) → M) where
  toFun p :=
    (p.1.world, fun v => (p.1.assignment v.1).get
      ((Set.ext_iff.mp p.2 v.1).mpr v.2))
  invFun e :=
    ⟨⟨e.1, fun v => if h : v ∈ (↑X : Set V) then some (e.2 ⟨v, h⟩)
      else none⟩, by
      ext v
      by_cases h : v ∈ (↑X : Set V) <;> simp [dom, h]⟩
  left_inv p := by
    obtain ⟨⟨w, g⟩, hp⟩ := p
    refine Subtype.ext (Possibility.ext rfl (funext fun v => ?_))
    by_cases h : v ∈ (↑X : Set V)
    · simp only [dif_pos h, Option.some_get]
    · have hnone : g v = none := Option.not_isSome_iff_eq_none.mp
        fun hs => h ((Set.ext_iff.mp hp v).mp hs)
      simp only [dif_neg h]
      exact hnone.symm
  right_inv e := by
    refine Prod.ext rfl (funext fun v => ?_)
    simp

end Restrict

end Possibility

end DynamicSemantics
