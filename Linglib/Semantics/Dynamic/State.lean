import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function

/-!
# Information states

An *information state* is a set of world–assignment pairs, with the
assignments partial — [kamp-vangenabith-reyle-2011]'s Def. 23 (sets of
pairs of a world and an embedding), the form the field standardly
assumes: the absurd state is `∅`, the initial state is `W × {g_⊤}`
(`initial`), and the lattice of states is `Set`'s. Partiality is by
`Option` ([elliott-sudo-2025]'s Def. 3.1: total functions into
`D ∪ {∗}`), so no component of a state carries a proof obligation.

There is no base field: Def. 23's "Dom(f) = X" is the *uniform* stratum
(`UniformAt`), and a base is the index of a fiber, not part of the data.
Points with domain `X` are world–`X`-environment pairs, constructively
(`Possibility.domEquiv` — the total-assignment rendering needed choice
and an inhabitant of `M` to recover this). Two preorders run through states, and they are
dual on shared strata. *Informativeness* (`⊑`,
[kamp-vangenabith-reyle-2011] Def. 25) quantifies over the stronger
state: every point of the stronger has an ancestor in the weaker — the
absurd state `∅` is maximally informative, the eliminative direction.
*Subsistence* (`⪯`, [elliott-sudo-2025] Def. 3.3, after
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) quantifies over the
weaker: every point survives, extended, into the stronger — the
anaphoric-support direction, with `∅` at the bottom. On a uniform
stratum they reduce to `⊇` and `⊆` respectively
(`infoLe_iff_superset`, `subsistsIn_iff_subset`).

## Main definitions

- `Possibility.dom`, `Possibility.Descendant`: the defined referents of
  a partial point, and same-world graph-extension.
- `State W V M`: information states; `initial`, with `∅` the absurd
  state.
- `infoLe` (`⊑`): informativeness (Def. 25); `Subsists` (`≺`),
  `subsistsIn` (`⪯`): subsistence.
- `worlds`, `Familiar`: worldly content and familiarity.
- `State.UniformAt`, `Possibility.domEquiv`: the indexed stratum and its
  constructive classification.
- `Possibility.restrict`, `State.restrict`, `State.randomAssign`:
  domain restriction (pointwise, by direct image) and random assignment.

## Main results

- `Possibility.Descendant.eq_of_dom_eq`: on a shared domain, descendance
  is equality — so both preorders are partial orders on each uniform
  stratum (`infoLe_iff_superset`, `subsistsIn_iff_subset`).
- `subsistsIn_restrict`: restriction only forgets — the restricted state
  subsists in the original.
- `uniformAt_restrict`, `restrict_restrict`: restriction meets the
  stratification.
- `uniformAt_initial`: the initial state is the empty-base fiber.

## Implementation notes

`State` is an abbreviation, so `Set`'s complete lattice is available and
`⊑`/`⪯` are scoped relations rather than instances. Neither is
antisymmetric on raw sets (adding a comparable point is invisible — an
ancestor for `⪯`, a descendant for `⊑`); antisymmetry holds on each
uniform stratum, where they coincide with `⊇`/`⊆`. The predecessor of this file classified its
fibers as `(Set (W × (↑X → M)))ᵒᵈ` — the dual lands here because its
order was Def. 25's, matching `⊑`, not `⪯`.

## References

- [kamp-vangenabith-reyle-2011], Defs. 23, 25
- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [heim-1982]
-/

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Partial points -/

namespace Possibility

/-- The referents a partial point defines — Def. 23's `Dom(f)`. -/
def dom (p : Possibility W V (Option M)) : Set V :=
  {v | (p.assignment v).isSome}

@[simp] theorem mem_dom {p : Possibility W V (Option M)} {v : V} :
    v ∈ p.dom ↔ (p.assignment v).isSome := Iff.rfl

/-- `q` is a *descendant* of `p` ([elliott-sudo-2025], Def. 3.3): same
world, and `q`'s assignment extends `p`'s wherever the latter is defined
([groenendijk-stokhof-veltman-1996]'s graph-extension). -/
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

end Possibility

/-! ### Information states -/

/-- An information state: a set of world–assignment pairs, the
assignments partial (Def. 23). The absurd state is `∅`; the lattice of
states is `Set`'s. -/
abbrev State (W V M : Type*) := Set (Possibility W V (Option M))

/-- The initial information state `W × {g_⊤}`: every world live, no
referent defined. -/
def State.initial : State W V M := {p | ∀ v, p.assignment v = none}

/-- `p` *subsists* in `s` ([elliott-sudo-2025], Def. 3.3): it has a
descendant in `s`. -/
def Subsists (p : Possibility W V (Option M)) (s : State W V M) : Prop :=
  ∃ q ∈ s, p.Descendant q

@[inherit_doc] scoped notation:50 p " ≺ " s => Subsists p s

theorem Subsists.of_mem {p : Possibility W V (Option M)} {s : State W V M}
    (h : p ∈ s) : p ≺ s :=
  ⟨p, h, Possibility.Descendant.refl p⟩

/-- `s` subsists in `s'`: the informativeness order, Def. 25's
projection form — every point of the weaker state has a descendant in
the stronger. -/
def subsistsIn (s s' : State W V M) : Prop :=
  ∀ p ∈ s, p ≺ s'

@[inherit_doc] scoped notation:50 s " ⪯ " s' => subsistsIn s s'

theorem subsistsIn_refl (s : State W V M) : s ⪯ s :=
  fun _ hp => Subsists.of_mem hp

theorem subsistsIn_trans {s t u : State W V M} (hst : s ⪯ t)
    (htu : t ⪯ u) : s ⪯ u := fun p hp => by
  obtain ⟨q, hq, hpq⟩ := hst p hp
  obtain ⟨r, hr, hqr⟩ := htu q hq
  exact ⟨r, hr, hpq.trans hqr⟩

/-- Informativeness ([kamp-vangenabith-reyle-2011] Def. 25): `s'` carries
at least as much information as `s` — every point of the stronger state
has an ancestor in the weaker. The absurd state is maximally
informative; the eliminative direction, dual to `⪯` on shared strata. -/
def infoLe (s s' : State W V M) : Prop :=
  ∀ q ∈ s', ∃ p ∈ s, p.Descendant q

@[inherit_doc] scoped notation:50 s " ⊑ " s' => infoLe s s'

theorem infoLe_refl (s : State W V M) : s ⊑ s :=
  fun q hq => ⟨q, hq, Possibility.Descendant.refl q⟩

theorem infoLe_trans {s t u : State W V M} (hst : s ⊑ t) (htu : t ⊑ u) :
    s ⊑ u := fun r hr => by
  obtain ⟨q, hq, hqr⟩ := htu r hr
  obtain ⟨p, hp, hpq⟩ := hst q hq
  exact ⟨p, hp, hpq.trans hqr⟩

/-- The absurd state is maximally informative. -/
theorem infoLe_empty (s : State W V M) : s ⊑ (∅ : State W V M) :=
  fun q hq => absurd hq (Set.notMem_empty q)

/-! ### Consistent merge -/

/-- Consistent merge ([kamp-vangenabith-reyle-2011] Def. 26, binary):
the points assembled from compatible pairs. Across strata this is the
descendant-mediated join — plain intersection of point-sets is empty
between distinct strata. -/
def State.merge (s s' : State W V M) : State W V M :=
  {r | ∃ p ∈ s, ∃ q ∈ s', p.Compatible q ∧ r = p.union q}

/-- The merge is above the left component in informativeness. -/
theorem infoLe_merge_left (s s' : State W V M) : s ⊑ s.merge s' := by
  rintro r ⟨p, hp, q, hq, hpq, rfl⟩
  exact ⟨p, hp, Possibility.left_descendant_union p q⟩

/-- The merge is above the right component in informativeness. -/
theorem infoLe_merge_right (s s' : State W V M) : s' ⊑ s.merge s' := by
  rintro r ⟨p, hp, q, hq, hpq, rfl⟩
  exact ⟨q, hq, hpq.right_descendant_union⟩

/-- **The merge is the least upper bound** (Def. 26's universal
property, in the informativeness preorder): anything above both
components is above their merge. -/
theorem merge_infoLe {s s' t : State W V M} (hs : s ⊑ t)
    (hs' : s' ⊑ t) : s.merge s' ⊑ t := fun u hu => by
  obtain ⟨p, hp, hpu⟩ := hs u hu
  obtain ⟨q, hq, hqu⟩ := hs' u hu
  exact ⟨p.union q, ⟨p, hp, q, hq, hpu.compatible hqu, rfl⟩,
    hpu.union_descendant hqu⟩

/-- The worldly content of a state ([elliott-sudo-2025] Def. 3.1's 𝒲). -/
def worlds (s : State W V M) : Set W :=
  Possibility.world '' s

@[simp] theorem mem_worlds {s : State W V M} {w : W} :
    w ∈ worlds s ↔ ∃ p ∈ s, Possibility.world p = w := Iff.rfl

/-- A referent is *familiar* at a state ([elliott-sudo-2025], Def. 3.2;
[heim-1982]'s files): defined at every point. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, p.assignment x ≠ none

/-! ### Restriction and random assignment -/

namespace Possibility

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

end Possibility

namespace State

/-! ### The uniform stratum -/

/-- The state is uniform at `X`: every point defines exactly the
referents in `X` — Def. 23's "Dom(f) = X", as a stratum rather than a
component. -/
def UniformAt (X : Finset V) (I : State W V M) : Prop :=
  ∀ p ∈ I, Possibility.dom p = (↑X : Set V)

/-- The initial state is uniform at the empty base. -/
theorem uniformAt_initial : UniformAt ∅ (initial : State W V M) :=
  fun p hp => by
    ext v
    simp [Possibility.dom, hp v]

/-- On a uniform stratum, subsistence is inclusion. -/
theorem subsistsIn_iff_subset {X : Finset V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    (s ⪯ s') ↔ s ⊆ s' := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, hpq⟩ := h p hp
    rwa [hpq.eq_of_dom_eq ((hs p hp).trans (hs' q hq).symm)]
  · exact fun h p hp => Subsists.of_mem (h hp)

/-- On a uniform stratum, informativeness is reverse inclusion — the
eliminative direction. -/
theorem infoLe_iff_superset {X : Finset V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    (s ⊑ s') ↔ s' ⊆ s := by
  constructor
  · intro h q hq
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← hpq.eq_of_dom_eq ((hs p hp).trans (hs' q hq).symm)]
  · exact fun h q hq => ⟨q, h hq, Possibility.Descendant.refl q⟩

/-- Within one stratum, merge is intersection: compatibility on a shared
domain forces equality. -/
theorem merge_eq_inter_of_uniform {X : Finset V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    s.merge s' = s ∩ s' := by
  have hself : ∀ r : Possibility W V (Option M), r.union r = r := fun r =>
    Possibility.ext rfl (funext fun v => by
      rcases h : r.assignment v with _ | e <;> simp [Possibility.union, h])
  ext r
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    obtain rfl := hpq.eq_of_dom_eq ((hs p hp).trans (hs' q hq).symm)
    rw [hself p]
    exact ⟨hp, hq⟩
  · rintro ⟨hr, hr'⟩
    refine ⟨r, hr, r, hr', ⟨rfl, fun v e e' he he' => ?_⟩, (hself r).symm⟩
    rw [he] at he'
    exact (Option.some.injEq .. ▸ he' :)

section Fibred
variable [DecidableEq V]

/-- Merge unites strata. -/
theorem uniformAt_merge {X Y : Finset V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s.merge s') := by
  rintro r ⟨p, hp, q, hq, -, rfl⟩
  rw [Possibility.dom_union, hs p hp, hs' q hq, Finset.coe_union]

/-- Subsistence out of a stratum factors through reindexing: the weaker
state includes into the restricted image of the stronger — the fibred
order, glued from within-stratum `⊆` along `restrict`. -/
theorem subsistsIn_iff_subset_restrict {X : Finset V}
    {s s' : State W V M} (hs : UniformAt X s) :
    (s ⪯ s') ↔ s ⊆ Possibility.restrict X '' s' := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, hpq⟩ := h p hp
    exact ⟨q, hq,
      ((Possibility.descendant_iff_eq_restrict (hs p hp)).mp hpq).symm⟩
  · rintro h p hp
    obtain ⟨q, hq, rfl⟩ := h hp
    exact ⟨q, hq, Possibility.restrict_descendant X q⟩

/-- Informativeness out of a stratum factors through reindexing: the
restricted image of the stronger is included in the weaker — the
eliminative direction of the fibred order. -/
theorem infoLe_iff_restrict_subset {X : Finset V}
    {s s' : State W V M} (hs : UniformAt X s) :
    (s ⊑ s') ↔ Possibility.restrict X '' s' ⊆ s := by
  constructor
  · rintro h r ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← (Possibility.descendant_iff_eq_restrict (hs p hp)).mp hpq]
  · intro h q hq
    exact ⟨q.restrict X, h ⟨q, hq, rfl⟩,
      Possibility.restrict_descendant X q⟩

end Fibred

variable [DecidableEq V]

/-- Restriction of a state: pointwise, by direct image. -/
def restrict (X : Finset V) (I : State W V M) : State W V M :=
  Possibility.restrict X '' I

/-- Restriction only forgets: the restricted state subsists in the
original. -/
theorem subsistsIn_restrict (X : Finset V) (I : State W V M) :
    I.restrict X ⪯ I := by
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, hq, Possibility.restrict_descendant X q⟩

/-- Restriction meets the stratification. -/
theorem uniformAt_restrict {X Y : Finset V} {I : State W V M}
    (h : UniformAt Y I) : UniformAt (X ∩ Y) (I.restrict X) := by
  rintro p ⟨q, hq, rfl⟩
  rw [Possibility.dom_restrict, h q hq, Finset.coe_inter]

/-- Restriction composes along intersections. -/
theorem restrict_restrict (X Y : Finset V) (I : State W V M) :
    (I.restrict Y).restrict X = I.restrict (X ∩ Y) := by
  unfold restrict
  rw [← Set.image_comp]
  exact congrFun (congrArg _ (funext (Possibility.restrict_restrict X Y))) I

/-- Random assignment ([elliott-sudo-2025], (43);
[groenendijk-stokhof-1991]'s `x := random`): indeterministically extend
each point to a defined value at `x`. -/
def randomAssign (I : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ I, ∃ m : M, p = q.extend x (some m)}

end State

/-! ### The indexed classification -/

namespace Possibility

variable [DecidableEq V]

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

end Possibility

end DynamicSemantics
