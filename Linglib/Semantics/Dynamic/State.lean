import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Hom.Basic

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
Points with domain `X` are world–`X`-assignment pairs, constructively
(`Possibility.domainEquiv` — the total-assignment rendering needed choice
and an inhabitant of `M` to recover this). Two preorders run through states, and they are
dual on shared strata. *Informativeness* (`⊑`,
[kamp-vangenabith-reyle-2011] Def. 25) quantifies over the stronger
state: every point of the stronger lies above a point of the weaker — the
absurd state `∅` is maximally informative, the eliminative direction.
*Subsistence* (`⪯`, [elliott-sudo-2025] Def. 3.3, after
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) quantifies over the
weaker: every point survives, extended, into the stronger — the
anaphoric-support direction, with `∅` at the bottom. On a uniform
stratum they reduce to `⊇` and `⊆` respectively
(`infoLe_iff_superset`, `subsistsIn_iff_subset`).

## Main definitions

- `State W V M`: information states; `initial`, with `∅` the absurd
  state.
- `infoLe` (`⊑`): informativeness (Def. 25); `Subsists` (`≺`),
  `subsistsIn` (`⪯`): subsistence.
- `State.merge`: Def. 26's consistent merge.
- `worlds`, `Familiar`: worldly content and familiarity.
- `State.UniformAt`: the indexed stratum (Def. 23's `Dom(f) = X`).
- `State.restrict`, `State.randomAssign`: domain restriction (by direct
  image of `Possibility.restrict`) and random assignment.

## Main results

- `merge_infoLe`: the merge is the `⊑`-least upper bound.
- `merge_assoc`, `merge_comm`, `merge_initial`: states form a
  commutative monoid under consistent merge — the content half of
  [visser-vermeulen-1996]'s monoidal processing.
- `infoLe_iff_superset`, `subsistsIn_iff_subset`: on a uniform stratum
  both preorders are partial orders, coinciding with `⊇`/`⊆` (via
  `Possibility.eq_of_le_of_domain_eq`).
- `subsistsIn_restrict`: restriction only forgets — the restricted state
  subsists in the original.
- `uniformAt_restrict`, `restrict_restrict`: restriction meets the
  stratification.
- `uniformAt_initial`: the initial state is the empty-base fiber.

## Implementation notes

`State` is an abbreviation, so `Set`'s complete lattice is available and
`⊑`/`⪯` are scoped relations rather than instances. Neither is
antisymmetric on raw sets (adding a comparable point is invisible —
below for `⪯`, above for `⊑`); antisymmetry holds on each
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

/-! ### Information states -/

/-- An information state: a set of world–assignment pairs, the
assignments partial (Def. 23). The absurd state is `∅`; the lattice of
states is `Set`'s. -/
abbrev State (W V M : Type*) := Set (Possibility W V (Option M))

/-- The initial information state `W × {g_⊤}`: every world live, no
referent defined. -/
def State.initial : State W V M := {p | ∀ v, p.assignment v = none}

/-- `p` *subsists* in `s` ([elliott-sudo-2025], Def. 3.3): it has a
point above it in `s`. -/
def Subsists (p : Possibility W V (Option M)) (s : State W V M) : Prop :=
  ∃ q ∈ s, p ≤ q

@[inherit_doc] scoped notation:50 p " ≺ " s => Subsists p s

theorem Subsists.of_mem {p : Possibility W V (Option M)} {s : State W V M}
    (h : p ∈ s) : p ≺ s :=
  ⟨p, h, le_refl p⟩

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
lies above a point of the weaker. The absurd state is maximally
informative; the eliminative direction, dual to `⪯` on shared strata. -/
def infoLe (s s' : State W V M) : Prop :=
  ∀ q ∈ s', ∃ p ∈ s, p ≤ q

@[inherit_doc] scoped notation:50 s " ⊑ " s' => infoLe s s'

theorem infoLe_refl (s : State W V M) : s ⊑ s :=
  fun q hq => ⟨q, hq, le_refl q⟩

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
  exact ⟨p, hp, Possibility.le_union_left p q⟩

/-- The merge is above the right component in informativeness. -/
theorem infoLe_merge_right (s s' : State W V M) : s' ⊑ s.merge s' := by
  rintro r ⟨p, hp, q, hq, hpq, rfl⟩
  exact ⟨q, hq, hpq.le_union_right⟩

/-- **The merge is the least upper bound** (Def. 26's universal
property, in the informativeness preorder): anything above both
components is above their merge. -/
theorem merge_infoLe {s s' t : State W V M} (hs : s ⊑ t)
    (hs' : s' ⊑ t) : s.merge s' ⊑ t := fun u hu => by
  obtain ⟨p, hp, hpu⟩ := hs u hu
  obtain ⟨q, hq, hqu⟩ := hs' u hu
  exact ⟨p.union q, ⟨p, hp, q, hq, Possibility.compatible_of_le_of_le hpu hqu, rfl⟩,
    Possibility.union_le hpu hqu⟩

/-- Consistent merge is commutative. -/
theorem merge_comm (s s' : State W V M) : s.merge s' = s'.merge s := by
  ext r
  constructor <;> rintro ⟨p, hp, q, hq, h, rfl⟩ <;>
    exact ⟨q, hq, p, hp, h.symm, h.union_comm⟩

/-- Consistent merge is associative. -/
theorem merge_assoc (s t u : State W V M) :
    (s.merge t).merge u = s.merge (t.merge u) := by
  ext r
  constructor
  · rintro ⟨a, ⟨p, hp, q, hq, hpq, rfl⟩, v, hv, hav, rfl⟩
    have hpv := hav.left_of_union
    have hqv := hpq.right_of_union hav
    exact ⟨p, hp, q.union v, ⟨q, hq, v, hv, hqv, rfl⟩,
      (Possibility.Compatible.union_left hpq.symm hpv.symm).symm,
      Possibility.union_assoc p q v⟩
  · rintro ⟨p, hp, a, ⟨q, hq, v, hv, hqv, rfl⟩, hpa, rfl⟩
    have hpq := hpa.symm.left_of_union.symm
    have hpv := (hqv.right_of_union hpa.symm).symm
    exact ⟨p.union q, ⟨p, hp, q, hq, hpq, rfl⟩, v, hv,
      Possibility.Compatible.union_left hpv hqv,
      (Possibility.union_assoc p q v).symm⟩

/-- The initial state is a unit for consistent merge: with `merge_comm`,
`merge_assoc`, and `merge_infoLe`, updating is joining in a commutative
monoid of information — the content half of
[visser-vermeulen-1996]'s monoidal processing. -/
@[simp] theorem merge_initial (s : State W V M) : s.merge State.initial = s := by
  ext r
  constructor
  · rintro ⟨p, hp, q, hq, -, rfl⟩
    have hq' : p.union q = p :=
      Possibility.ext rfl (funext fun v => by simp [Possibility.union, hq v])
    rwa [hq']
  · intro hr
    exact ⟨r, hr, ⟨r.world, fun _ => none⟩, fun _ => rfl,
      ⟨rfl, fun _ _ _ _ h => by simp at h⟩,
      Possibility.ext rfl (funext fun v => by simp [Possibility.union])⟩

@[simp] theorem initial_merge (s : State W V M) : State.merge State.initial s = s := by
  rw [merge_comm, merge_initial]

/-- The worldly content of a state ([elliott-sudo-2025] Def. 3.1's 𝒲). -/
def worlds (s : State W V M) : Set W :=
  Possibility.world '' s

@[simp] theorem mem_worlds {s : State W V M} {w : W} :
    w ∈ worlds s ↔ ∃ p ∈ s, Possibility.world p = w := Iff.rfl

/-- A referent is *familiar* at a state ([elliott-sudo-2025], Def. 3.2;
[heim-1982]'s files): defined at every point. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, p.assignment x ≠ none

namespace State

/-! ### The uniform stratum -/

/-- The state is uniform at `X`: every point defines exactly the
referents in `X` — Def. 23's "Dom(f) = X", as a stratum rather than a
component. -/
def UniformAt (X : Set V) (I : State W V M) : Prop :=
  ∀ p ∈ I, Possibility.domain p = X

/-- The initial state is uniform at the empty base. -/
theorem uniformAt_initial : UniformAt ∅ (initial : State W V M) :=
  fun p hp => by
    ext v
    simp [Possibility.domain, hp v]

/-- Into a uniform stratum, subsistence is membership: a point already
at the stratum's domain has no room to grow. -/
theorem subsists_iff_mem {X : Set V} {s : State W V M}
    (hs : UniformAt X s) {p : Possibility W V (Option M)}
    (hp : p.domain = X) : (p ≺ s) ↔ p ∈ s :=
  ⟨fun ⟨q, hq, hpq⟩ =>
    (Possibility.eq_of_le_of_domain_eq hpq (hp.trans (hs q hq).symm)).symm ▸ hq,
    Subsists.of_mem⟩

/-- On a uniform stratum, subsistence is inclusion. -/
theorem subsistsIn_iff_subset {X : Set V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    (s ⪯ s') ↔ s ⊆ s' :=
  forall₂_congr fun p hp => subsists_iff_mem hs' (hs p hp)

/-- On a uniform stratum, informativeness is reverse inclusion — the
eliminative direction. -/
theorem infoLe_iff_superset {X : Set V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    (s ⊑ s') ↔ s' ⊆ s := by
  constructor
  · intro h q hq
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← Possibility.eq_of_le_of_domain_eq hpq ((hs p hp).trans (hs' q hq).symm)]
  · exact fun h q hq => ⟨q, h hq, le_refl q⟩

/-- Within one stratum, merge is intersection: compatibility on a shared
domain forces equality. -/
theorem merge_eq_inter_of_uniform {X : Set V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt X s') :
    s.merge s' = s ∩ s' := by
  have hself : ∀ r : Possibility W V (Option M), r.union r = r := fun r =>
    Possibility.ext rfl (funext fun v => by
      rcases h : r.assignment v with _ | e <;> simp [Possibility.union, h])
  ext r
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    obtain rfl := hpq.eq_of_domain_eq ((hs p hp).trans (hs' q hq).symm)
    rw [hself p]
    exact ⟨hp, hq⟩
  · rintro ⟨hr, hr'⟩
    refine ⟨r, hr, r, hr', ⟨rfl, fun v e e' he he' => ?_⟩, (hself r).symm⟩
    rw [he] at he'
    exact (Option.some.injEq .. ▸ he' :)

section Fibred

/-- Merge unites strata. -/
theorem uniformAt_merge {X Y : Set V} {s s' : State W V M}
    (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s.merge s') := by
  rintro r ⟨p, hp, q, hq, -, rfl⟩
  rw [Possibility.domain_union, hs p hp, hs' q hq]

/-- Subsistence out of a stratum factors through reindexing: the weaker
state includes into the restricted image of the stronger — the fibred
order, glued from within-stratum `⊆` along `restrict`. -/
theorem subsistsIn_iff_subset_restrict {X : Set V}
    [∀ v, Decidable (v ∈ X)]
    {s s' : State W V M} (hs : UniformAt X s) :
    (s ⪯ s') ↔ s ⊆ Possibility.restrict X '' s' := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, hpq⟩ := h p hp
    exact ⟨q, hq,
      ((Possibility.le_iff_eq_restrict (hs p hp)).mp hpq).symm⟩
  · rintro h p hp
    obtain ⟨q, hq, rfl⟩ := h hp
    exact ⟨q, hq, Possibility.restrict_le X q⟩

/-- Informativeness out of a stratum factors through reindexing: the
restricted image of the stronger is included in the weaker — the
eliminative direction of the fibred order. -/
theorem infoLe_iff_restrict_subset {X : Set V}
    [∀ v, Decidable (v ∈ X)]
    {s s' : State W V M} (hs : UniformAt X s) :
    (s ⊑ s') ↔ Possibility.restrict X '' s' ⊆ s := by
  constructor
  · rintro h r ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← (Possibility.le_iff_eq_restrict (hs p hp)).mp hpq]
  · intro h q hq
    exact ⟨q.restrict X, h ⟨q, hq, rfl⟩,
      Possibility.restrict_le X q⟩

end Fibred

/-- Restriction of a state: pointwise, by direct image. -/
def restrict (X : Set V) [∀ v, Decidable (v ∈ X)] (I : State W V M) :
    State W V M :=
  Possibility.restrict X '' I

/-- Restriction only forgets: the restricted state subsists in the
original. -/
theorem subsistsIn_restrict (X : Set V) [∀ v, Decidable (v ∈ X)]
    (I : State W V M) : I.restrict X ⪯ I := by
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, hq, Possibility.restrict_le X q⟩

/-- Restriction meets the stratification. -/
theorem uniformAt_restrict {X Y : Set V} [∀ v, Decidable (v ∈ X)]
    {I : State W V M}
    (h : UniformAt Y I) : UniformAt (X ∩ Y) (I.restrict X) := by
  rintro p ⟨q, hq, rfl⟩
  rw [Possibility.domain_restrict, h q hq]

/-- Restriction composes along intersections. -/
theorem restrict_restrict (X Y : Set V) [∀ v, Decidable (v ∈ X)]
    [∀ v, Decidable (v ∈ Y)] (I : State W V M) :
    (I.restrict Y).restrict X = I.restrict (X ∩ Y) := by
  unfold restrict
  rw [← Set.image_comp]
  exact congrFun (congrArg _ (funext (Possibility.restrict_restrict X Y))) I

variable [DecidableEq V]

/-- Random assignment ([elliott-sudo-2025], (43);
[groenendijk-stokhof-1991]'s `x := random`): indeterministically extend
each point to a defined value at `x`. -/
def randomAssign (I : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ I, ∃ m : M, p = q.update x (some m)}

/-- Random assignment makes its referent familiar. -/
theorem familiar_randomAssign (I : State W V M) (x : V) :
    Familiar (I.randomAssign x) x := by
  rintro p ⟨q, -, m, rfl⟩
  simp

/-! ### The uniform classification -/

/-- Uniform states at `X` are sets of world–`X`-assignment pairs — the
state-level face of `Possibility.domainEquiv`, and the comparison to the
predecessor's fibers: an order isomorphism for `⊆` (which is `⪯` on the
stratum, `subsistsIn_iff_subset`), hence an anti-isomorphism for `⊑`
(`infoLe_iff_superset`). -/
def uniformEquiv (X : Set V) [∀ v, Decidable (v ∈ X)] :
    {I : State W V M // UniformAt X I} ≃o Set (W × (X → M)) where
  toFun I := {e | ((Possibility.domainEquiv X).symm e).1 ∈ I.1}
  invFun S :=
    ⟨{p | ∃ h : p.domain = X, Possibility.domainEquiv X ⟨p, h⟩ ∈ S},
      fun _ ⟨h, _⟩ => h⟩
  left_inv I := by
    refine Subtype.ext (Set.ext fun p => ?_)
    constructor
    · rintro ⟨h, hmem⟩
      simpa using hmem
    · intro hp
      exact ⟨I.2 p hp, by simpa using hp⟩
  right_inv S := Set.ext fun e => by
    constructor
    · rintro ⟨h, hmem⟩
      simpa using hmem
    · intro he
      exact ⟨((Possibility.domainEquiv X).symm e).2, by simpa using he⟩
  map_rel_iff' {I J} := by
    constructor
    · intro h p hp
      simpa using h (a := Possibility.domainEquiv X ⟨p, I.2 p hp⟩)
        (by simpa using hp)
    · exact fun h _ he => h he

end State

end DynamicSemantics
