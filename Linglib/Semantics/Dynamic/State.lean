import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.Hom.Basic

/-!
# Information states

An *information state* is a set of world–assignment pairs with the
assignments partial ([kamp-vangenabith-reyle-2011], Def. 0.23;
partiality by `Part`, after [elliott-sudo-2025], Def. 3.1). `State`
carries *informativeness* (Def. 0.25) as its preorder, lifted along the
upper closure of the point set: `s ≤ s'` iff every point of the
stronger state lies above a point of the weaker. The initial state is
`⊥`, the absurd state is `⊤ = ∅`, and consistent merge (Def. 0.26) is
the least upper bound.

Def. 0.23's base `X` is not a component: `State.UniformAt X` carves it
out as a stratum, whose states are sets of world–`X`-assignment pairs
(`State.uniformEquiv`). *Subsistence* (`subsistsIn`,
[elliott-sudo-2025], Def. 3.3, after
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) is the dual closure
kernel, lifted along the lower closure. On a uniform stratum both
orders are partial orders, coinciding with `⊇` and `⊆`.

## Main definitions

- `State`: information states, preordered by informativeness; `⊥` is
  the initial state (Def. 0.23's Λ), `⊤ = ∅` the absurd state.
- `Subsists` (`≺`), `subsistsIn`: point- and state-level subsistence.
- `State.merge`: consistent merge (Def. 0.26, binary), as `Set.lubs`.
- `State.UniformAt`, `State.restrict`: the base-`X` stratum; domain
  restriction.
- `worlds`, `Familiar`, `State.randomAssign`: worldly content,
  familiarity, random assignment ([elliott-sudo-2025]).

## Main results

- `State.isLUB_merge`: merge is the least upper bound — with
  `merge_comm`, `merge_assoc`, `merge_bot`, the content half of
  [visser-vermeulen-1996]'s monoidal processing.
- `State.le_iff_superset`, `State.subsistsIn_iff_subset`,
  `State.merge_eq_inter_of_uniform`: on a uniform stratum the orders
  are `⊇`/`⊆` and merge is intersection.
- `State.uniformEquiv`: uniform states at `X` are `Set (W × (X → M))`.

## Implementation notes

`State` is a type synonym for the point-set, in the `Lex`/`OrderDual`
mold: membership and the set operations are re-exposed, while `≤` is
informativeness — the kernel of `upperClosure` — rather than `⊆`, which
remains available with its literal meaning. Neither closure kernel is
antisymmetric on point sets (adding a comparable point is invisible),
so `State` is a `Preorder` only; antisymmetry holds on each uniform
stratum.

## References

- [kamp-vangenabith-reyle-2011], Defs. 0.23–0.26
- [elliott-sudo-2025], [groenendijk-stokhof-veltman-1996], [heim-1982]
-/

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Information states -/

/-- An information state: a set of world–assignment pairs, the
assignments partial ([kamp-vangenabith-reyle-2011], Def. 0.23), ordered
by informativeness rather than inclusion. -/
def State (W V M : Type*) := Set (Possibility W V (Part M))

namespace State

@[reducible] instance : Membership (Possibility W V (Part M)) (State W V M) :=
  inferInstanceAs (Membership _ (Set _))

/-- Point-set inclusion between states. Deliberately `HasSubset`, not the
order: `≤` is informativeness, and the two coincide only stratum-wise
(`le_iff_superset`). -/
instance : HasSubset (State W V M) := ⟨fun s s' => ∀ ⦃p⦄, p ∈ s → p ∈ s'⟩

@[reducible] instance : EmptyCollection (State W V M) :=
  inferInstanceAs (EmptyCollection (Set _))

@[reducible] instance : Union (State W V M) := inferInstanceAs (Union (Set _))

@[reducible] instance : Inter (State W V M) := inferInstanceAs (Inter (Set _))

@[reducible] instance : SDiff (State W V M) := inferInstanceAs (SDiff (Set _))

@[ext] theorem ext {s s' : State W V M} (h : ∀ p, p ∈ s ↔ p ∈ s') : s = s' :=
  Set.ext h

/-- Informativeness ([kamp-vangenabith-reyle-2011], Def. 0.25): `s ≤ s'`
iff `s'` carries at least as much information as `s` — the preorder
lifted along the upper closure of the point set. -/
instance : Preorder (State W V M) :=
  .lift fun s => upperClosure (s : Set (Possibility W V (Part M)))

/-- Def. 0.25 in projection form: every point of the stronger state lies
above a point of the weaker. -/
theorem le_def {s s' : State W V M} : s ≤ s' ↔ ∀ q ∈ s', ∃ p ∈ s, p ≤ q := by
  change upperClosure _ ≤ upperClosure _ ↔ _
  rw [← UpperSet.coe_subset_coe]
  constructor
  · intro h q hq
    exact h (subset_upperClosure hq)
  · rintro h x ⟨q, hq, hqx⟩
    obtain ⟨p, hp, hpq⟩ := h q hq
    exact ⟨p, hp, hpq.trans hqx⟩

/-- The initial information state `⊥ = W × {g_⊤}` (Def. 0.23's Λ):
every world live, no referent defined — the range of the empty points,
the bottom of the informativeness order. -/
instance : OrderBot (State W V M) where
  bot := Set.range Possibility.bot
  bot_le _ := le_def.mpr fun q _ => ⟨.bot q.world, ⟨q.world, rfl⟩, Possibility.bot_le⟩

/-- Membership in the initial state: no referent defined. -/
theorem mem_bot {p : Possibility W V (Part M)} :
    p ∈ (⊥ : State W V M) ↔ ∀ v, p.assignment v = ⊥ :=
  ⟨fun ⟨_, hw⟩ _ => hw ▸ rfl, fun h =>
    ⟨p.world, Possibility.ext rfl (funext fun v => (h v).symm)⟩⟩

/-- The absurd state is maximally informative: no live point. -/
instance : OrderTop (State W V M) where
  top := ∅
  le_top _ := le_def.mpr fun _ hq => hq.elim

@[simp] theorem top_eq_empty : (⊤ : State W V M) = ∅ := rfl

end State

/-! ### Subsistence -/

/-- `p` *subsists* in `s` ([elliott-sudo-2025], Def. 3.3): it survives,
possibly extended, into `s` — membership in the lower closure of the
point set. -/
def Subsists (p : Possibility W V (Part M)) (s : State W V M) : Prop :=
  p ∈ lowerClosure (s : Set (Possibility W V (Part M)))

@[inherit_doc] scoped notation:50 p " ≺ " s => Subsists p s

/-- Subsistence unfolded: a point of `s` lies above `p`. -/
theorem subsists_iff {p : Possibility W V (Part M)} {s : State W V M} :
    (p ≺ s) ↔ ∃ q ∈ s, p ≤ q :=
  Iff.rfl

theorem Subsists.of_mem {p : Possibility W V (Part M)} {s : State W V M}
    (h : p ∈ s) : p ≺ s :=
  ⟨p, h, le_rfl⟩

/-- `s` subsists in `s'` ([elliott-sudo-2025], Def. 3.3, state-level;
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9): every point survives,
extended, into `s'` — the preorder lifted along the lower closure, dual
to `≤` on shared strata, with `⊤ = ∅` at the bottom. -/
def subsistsIn (s s' : State W V M) : Prop :=
  lowerClosure (s : Set (Possibility W V (Part M))) ≤
    lowerClosure (s' : Set (Possibility W V (Part M)))

/-- Subsistence in projection form: every point subsists. -/
theorem subsistsIn_iff {s s' : State W V M} :
    subsistsIn s s' ↔ ∀ p ∈ s, p ≺ s' :=
  lowerClosure_le

/-! ### Consistent merge -/

namespace State

variable {s s' t : State W V M} {r : Possibility W V (Part M)}

/-- Consistent merge ([kamp-vangenabith-reyle-2011] Def. 0.26, binary):
the joins of pairs of points, one from each state (`Set.lubs`). Across
strata this is the descendant-mediated join — plain intersection of
point-sets is empty between distinct strata. -/
def merge (s s' : State W V M) : State W V M :=
  Set.lubs s s'

/-- Membership in a merge, in union form. -/
theorem mem_merge :
    r ∈ s.merge s' ↔ ∃ p ∈ s, ∃ q ∈ s', Compat p q ∧ r = p.union q := by
  show r ∈ Set.lubs (s : Set (Possibility W V (Part M))) s' ↔ _
  simp only [Set.mem_lubs, Possibility.isLUB_pair_iff]
  rfl

/-- The Smyth face of the merge: upper closures compose by join. -/
theorem upperClosure_merge :
    upperClosure (s.merge s' : Set (Possibility W V (Part M))) =
      upperClosure (s : Set (Possibility W V (Part M))) ⊔
        upperClosure (s' : Set (Possibility W V (Part M))) :=
  Set.upperClosure_lubs (fun _ _ h => ⟨_, Possibility.isLUB_union h⟩) _ _

/-- The merge is above the left component. -/
theorem le_merge_left : s ≤ s.merge s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_merge]
  exact le_sup_left

/-- The merge is above the right component. -/
theorem le_merge_right : s' ≤ s.merge s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_merge]
  exact le_sup_right

/-- Def. 0.26's universal property: anything above both components is
above their merge. -/
theorem merge_le (h : s ≤ t) (h' : s' ≤ t) : s.merge s' ≤ t := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_merge]
  exact sup_le h h'

/-- **The merge is the least upper bound** of its components in the
informativeness preorder. -/
theorem isLUB_merge : IsLUB {s, s'} (s.merge s') :=
  ⟨by rintro x (rfl | rfl); exacts [le_merge_left, le_merge_right],
   fun _ hu => merge_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-- Consistent merge is commutative. -/
theorem merge_comm (s s' : State W V M) : s.merge s' = s'.merge s :=
  Set.lubs_comm s s'

/-- Consistent merge is associative. -/
theorem merge_assoc (s t u : State W V M) :
    (s.merge t).merge u = s.merge (t.merge u) :=
  Set.lubs_assoc (fun _ _ h => ⟨_, Possibility.isLUB_union h⟩) s t u

/-- The initial state is a unit for consistent merge: with `merge_comm`,
`merge_assoc`, and `isLUB_merge`, updating is joining in a commutative
monoid of information — the content half of [visser-vermeulen-1996]'s
monoidal processing. -/
@[simp] theorem merge_bot (s : State W V M) : s.merge ⊥ = s := by
  ext r
  constructor
  · rintro ⟨p, hp, q, ⟨w, rfl⟩, hlub⟩
    obtain ⟨-, rfl⟩ := Possibility.isLUB_pair_iff.mp hlub
    rwa [Possibility.union_bot]
  · intro hr
    exact ⟨r, hr, Possibility.bot r.world, ⟨r.world, rfl⟩,
      Possibility.isLUB_pair_iff.mpr
        ⟨.of_le le_rfl Possibility.bot_le, Possibility.union_bot.symm⟩⟩

@[simp] theorem bot_merge (s : State W V M) : merge ⊥ s = s := by
  rw [merge_comm, merge_bot]

end State

/-! ### Worldly content and familiarity -/

/-- The worldly content of a state ([elliott-sudo-2025] Def. 3.1's 𝒲). -/
def worlds (s : State W V M) : Set W :=
  Possibility.world '' s

@[simp] theorem mem_worlds {s : State W V M} {w : W} :
    w ∈ worlds s ↔ ∃ p ∈ s, Possibility.world p = w := Iff.rfl

/-- A referent is *familiar* at a state ([elliott-sudo-2025], Def. 3.2;
[heim-1982]'s files): defined at every point. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, (p.assignment x).Dom

namespace State

/-! ### The uniform stratum -/

variable {s s' : State W V M}

/-- The state is uniform at `X`: every point defines exactly the
referents in `X` — Def. 0.23's "Dom(f) = X", as a stratum rather than a
component. -/
def UniformAt (X : Set V) (I : State W V M) : Prop :=
  ∀ p ∈ I, Possibility.domain p = X

/-- The initial state is uniform at the empty base. -/
theorem uniformAt_bot : UniformAt ∅ (⊥ : State W V M) := fun _ hp =>
  Possibility.domain_eq_empty_iff.mpr (mem_bot.mp hp)

/-- Into a uniform stratum, subsistence is membership: a point already
at the stratum's domain has no room to grow. -/
theorem subsists_iff_mem {X : Set V} (hs : UniformAt X s)
    {p : Possibility W V (Part M)} (hp : p.domain = X) : (p ≺ s) ↔ p ∈ s :=
  ⟨fun ⟨q, hq, hpq⟩ =>
    (Possibility.eq_of_le_of_domain_eq hpq (hp.trans (hs q hq).symm)).symm ▸ hq,
    Subsists.of_mem⟩

/-- On a uniform stratum, subsistence is inclusion. -/
theorem subsistsIn_iff_subset {X : Set V} (hs : UniformAt X s)
    (hs' : UniformAt X s') : subsistsIn s s' ↔ s ⊆ s' :=
  subsistsIn_iff.trans (forall₂_congr fun p hp => subsists_iff_mem hs' (hs p hp))

/-- On a uniform stratum, informativeness is reverse inclusion — the
eliminative direction. -/
theorem le_iff_superset {X : Set V} (hs : UniformAt X s) (hs' : UniformAt X s') :
    s ≤ s' ↔ s' ⊆ s := by
  rw [le_def]
  constructor
  · intro h q hq
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← Possibility.eq_of_le_of_domain_eq hpq ((hs p hp).trans (hs' q hq).symm)]
  · exact fun h q hq => ⟨q, h hq, le_rfl⟩

/-- Within one stratum, merge is intersection: compatibility on a shared
domain forces equality. -/
theorem merge_eq_inter_of_uniform {X : Set V} (hs : UniformAt X s)
    (hs' : UniformAt X s') : s.merge s' = s ∩ s' := by
  ext r
  rw [mem_merge]
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    obtain rfl := Possibility.eq_of_compat_of_domain_eq hpq ((hs p hp).trans (hs' q hq).symm)
    rw [Possibility.union_self]
    exact ⟨hp, hq⟩
  · rintro ⟨hr, hr'⟩
    exact ⟨r, hr, r, hr', compat_self r, Possibility.union_self.symm⟩

/-- Restriction of a state: pointwise, by direct image. -/
def restrict (X : Set V) (I : State W V M) : State W V M :=
  Possibility.restrict X '' I

/-- Membership in a restriction. -/
theorem mem_restrict {X : Set V} {I : State W V M} {p : Possibility W V (Part M)} :
    p ∈ I.restrict X ↔ ∃ q ∈ I, q.restrict X = p :=
  Iff.rfl

section Fibred

/-- Merge unites strata. -/
theorem uniformAt_merge {X Y : Set V} (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s.merge s') := by
  intro r hr
  obtain ⟨p, hp, q, hq, -, rfl⟩ := mem_merge.mp hr
  rw [Possibility.domain_union, hs p hp, hs' q hq]

/-- Subsistence out of a stratum factors through reindexing: the weaker
state includes into the restricted image of the stronger — the fibred
order, glued from within-stratum `⊆` along `restrict`. -/
theorem subsistsIn_iff_subset_restrict {X : Set V} (hs : UniformAt X s) :
    subsistsIn s s' ↔ s ⊆ s'.restrict X := by
  rw [subsistsIn_iff]
  constructor
  · intro h p hp
    obtain ⟨q, hq, hpq⟩ := h p hp
    exact ⟨q, hq, ((Possibility.le_iff_eq_restrict (hs p hp)).mp hpq).symm⟩
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := h hp
    exact ⟨q, hq, Possibility.restrict_le⟩

/-- Informativeness out of a stratum factors through reindexing: the
restricted image of the stronger is included in the weaker — the
eliminative direction of the fibred order. -/
theorem le_iff_restrict_subset {X : Set V} (hs : UniformAt X s) :
    s ≤ s' ↔ s'.restrict X ⊆ s := by
  rw [le_def]
  constructor
  · rintro h r ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := h q hq
    rwa [← (Possibility.le_iff_eq_restrict (hs p hp)).mp hpq]
  · intro h q hq
    exact ⟨q.restrict X, h ⟨q, hq, rfl⟩, Possibility.restrict_le⟩

end Fibred

/-- Restriction only forgets: the restricted state subsists in the
original. -/
theorem subsistsIn_restrict (X : Set V) (I : State W V M) :
    subsistsIn (I.restrict X) I := by
  rw [subsistsIn_iff]
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, hq, Possibility.restrict_le⟩

/-- Restriction meets the stratification. -/
theorem uniformAt_restrict {X Y : Set V} {I : State W V M}
    (h : UniformAt Y I) : UniformAt (X ∩ Y) (I.restrict X) := by
  rintro p ⟨q, hq, rfl⟩
  rw [Possibility.domain_restrict, h q hq]

/-- Restriction composes along intersections. -/
theorem restrict_restrict (X Y : Set V) (I : State W V M) :
    (I.restrict Y).restrict X = I.restrict (X ∩ Y) := by
  simp only [restrict, Set.image_image, Possibility.restrict_restrict]

variable [DecidableEq V]

/-- Random assignment ([elliott-sudo-2025], (43);
[groenendijk-stokhof-1991]'s `x := random`): indeterministically extend
each point to a defined value at `x`. -/
def randomAssign (I : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ I, ∃ m : M, p = q.update x (Part.some m)}

/-- Random assignment makes its referent familiar. -/
theorem familiar_randomAssign (I : State W V M) (x : V) :
    Familiar (I.randomAssign x) x := by
  rintro p ⟨q, -, m, rfl⟩
  simp

/-! ### The uniform classification -/

/-- Uniform states at `X` are sets of world–`X`-assignment pairs — the
state-level face of `Possibility.domainEquiv`. Informativeness on the
stratum is reverse inclusion (`le_iff_superset`), so the isomorphism
lands in the dual order. -/
def uniformEquiv (X : Set V) :
    {I : State W V M // UniformAt X I} ≃o (Set (W × (X → M)))ᵒᵈ where
  toFun I := OrderDual.toDual {e | ((Possibility.domainEquiv X).symm e).1 ∈ I.1}
  invFun S :=
    ⟨{p | ∃ h : p.domain = X, Possibility.domainEquiv X ⟨p, h⟩ ∈ OrderDual.ofDual S},
      fun _ ⟨h, _⟩ => h⟩
  left_inv I := by
    refine Subtype.ext (State.ext fun p => ?_)
    constructor
    · rintro ⟨h, hmem⟩
      simpa using hmem
    · intro hp
      exact ⟨I.2 p hp, by simpa using hp⟩
  right_inv S := OrderDual.ofDual.injective <| Set.ext fun e => by
    constructor
    · rintro ⟨h, hmem⟩
      simpa using hmem
    · intro he
      exact ⟨((Possibility.domainEquiv X).symm e).2, by simpa using he⟩
  map_rel_iff' {I J} := by
    rw [← Subtype.coe_le_coe, le_iff_superset I.2 J.2]
    show ({e | ((Possibility.domainEquiv X).symm e).1 ∈ J.1} : Set (W × (X → M))) ⊆
        {e | ((Possibility.domainEquiv X).symm e).1 ∈ I.1} ↔ _
    constructor
    · intro h p hp
      simpa using h (show Possibility.domainEquiv X ⟨p, J.2 p hp⟩ ∈
        {e | ((Possibility.domainEquiv X).symm e).1 ∈ J.1} by simpa using hp)
    · exact fun h _ he => h he

end State

end DynamicSemantics
