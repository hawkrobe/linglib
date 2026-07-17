import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
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
the monoid multiplication and the least upper bound.

Def. 0.23's base `X` is not a component: `State.UniformAt X` carves it
out as a stratum, whose states are sets of world–`X`-assignment pairs
(`State.uniformEquiv`). *Subsistence* ([elliott-sudo-2025], Def. 3.3,
after [groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) is not a new
relation: a point subsists in a state iff it lies in `lowerClosure` of
its point set, a state subsists in another iff the lower closures are
ordered — the dual closure kernel. On a uniform stratum both kernels
are partial orders, coinciding with `⊇` and `⊆`.

## Main definitions

- `State`: information states, preordered by informativeness; `⊥` is
  the initial state (Def. 0.23's Λ), `⊤ = ∅` the absurd state.
- the `CommMonoid` instance: `*` is consistent merge (Def. 0.26,
  binary, as `Set.lubs`) and `1 = ⊥`, so `Multiset.prod` is the finite
  n-ary merge.
- `State.UniformAt`, `State.restrict`: the base-`X` stratum; domain
  restriction.
- `Familiar`, `State.randomAssign`: familiarity and random assignment
  ([elliott-sudo-2025]); worldly content (Def. 0.23(v)'s proposition,
  [elliott-sudo-2025]'s 𝒲) is the image `Possibility.world '' s`.

## Main results

- `State.isLUB_mul`, `State.isGLB_union`: merge is the least upper
  bound and union the greatest lower bound — with the `CommMonoid` and
  `CovariantClass` instances, the content half of
  [visser-vermeulen-1996]'s monoidal processing.
- `State.le_iff_superset`, `State.lowerClosure_le_iff`,
  `State.mul_eq_inter_of_uniform`: on a uniform stratum the orders
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

/-- Interpret a point set as an information state — the type-synonym
retyping (`OrderDual.toDual`'s analogue), for positions whose binder is
`Set`-typed. -/
def _root_.Set.toState (s : Set (Possibility W V (Part M))) : State W V M := s

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

/-! ### Subsistence

*Subsistence* ([elliott-sudo-2025], Def. 3.3, after
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) is not a new
relation: a point subsists in a state iff it lies in the lower closure
of its point set (`mem_lowerClosure`: some point of the state extends
it), and a state subsists in another iff `lowerClosure s ≤
lowerClosure s'` — the closure kernel dual to `≤`, with `⊤ = ∅` at the
bottom. -/

/-! ### Consistent merge as multiplication -/

namespace State

variable {s s' t : State W V M} {r : Possibility W V (Part M)}

private theorem lubs_bot (s : State W V M) :
    (Set.lubs s (⊥ : State W V M) : State W V M) = s := by
  ext r
  constructor
  · rintro ⟨p, hp, q, ⟨w, rfl⟩, hlub⟩
    obtain ⟨-, rfl⟩ := Possibility.isLUB_pair_iff.mp hlub
    rwa [Possibility.union_bot]
  · intro hr
    exact ⟨r, hr, Possibility.bot r.world, ⟨r.world, rfl⟩,
      Possibility.isLUB_pair_iff.mpr
        ⟨.of_le le_rfl Possibility.bot_le, Possibility.union_bot.symm⟩⟩

/-- States form a commutative monoid: `*` is consistent merge
([kamp-vangenabith-reyle-2011] Def. 0.26, binary) — the joins of pairs
of points, one from each state (`Set.lubs`) — and `1` is the initial
state `⊥`. Updating is joining in a commutative monoid of information
([visser-vermeulen-1996]'s monoidal processing); `Multiset.prod` is
Def. 0.26's finite n-ary merge. -/
instance : CommMonoid (State W V M) where
  mul s s' := Set.lubs s s'
  mul_assoc := Set.lubs_assoc fun _ _ h => ⟨_, Possibility.isLUB_union h⟩
  one := ⊥
  one_mul s := (Set.lubs_comm _ _).trans (lubs_bot s)
  mul_one := lubs_bot
  mul_comm := Set.lubs_comm

theorem one_eq_bot : (1 : State W V M) = ⊥ := rfl

/-- Membership in the merge, in union form. -/
theorem mem_mul :
    r ∈ s * s' ↔ ∃ p ∈ s, ∃ q ∈ s', Compat p q ∧ r = p.union q := by
  show r ∈ Set.lubs (s : Set (Possibility W V (Part M))) s' ↔ _
  simp only [Set.mem_lubs, Possibility.isLUB_pair_iff]
  rfl

/-- The Smyth face of the merge: upper closures compose by join. -/
theorem upperClosure_mul :
    upperClosure ((s * s' : State W V M) : Set (Possibility W V (Part M))) =
      upperClosure (s : Set (Possibility W V (Part M))) ⊔
        upperClosure (s' : Set (Possibility W V (Part M))) :=
  Set.upperClosure_lubs (fun _ _ h => ⟨_, Possibility.isLUB_union h⟩) _ _

/-- The merge is above the left factor. -/
theorem left_le_mul : s ≤ s * s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_mul]
  exact le_sup_left

/-- The merge is above the right factor. -/
theorem right_le_mul : s' ≤ s * s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_mul]
  exact le_sup_right

/-- Def. 0.26's universal property: anything above both factors is
above their merge. -/
theorem mul_le (h : s ≤ t) (h' : s' ≤ t) : s * s' ≤ t := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_mul]
  exact sup_le h h'

/-- **The merge is the least upper bound** of its factors in the
informativeness preorder. -/
theorem isLUB_mul : IsLUB {s, s'} (s * s') :=
  ⟨by rintro x (rfl | rfl); exacts [left_le_mul, right_le_mul],
   fun _ hu => mul_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-- Merge is monotone: the ordered-monoid law, [kamp-vangenabith-reyle-2011]
Def. 0.27's ascent composes across updates. -/
instance : CovariantClass (State W V M) (State W V M) (· * ·) (· ≤ ·) :=
  ⟨fun _ _ _ h => mul_le left_le_mul (h.trans right_le_mul)⟩

instance : CovariantClass (State W V M) (State W V M)
    (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun _ _ _ h => mul_le (h.trans left_le_mul) right_le_mul⟩

/-! ### Union is the meet

Merge is the join of the informativeness order; plain union is its
meet — pooling two states keeps exactly their common information. `∪`
is **not** merge: within a stratum merge is intersection
(`mul_eq_inter_of_uniform`), the eliminative regime. -/

/-- The Smyth face of the union: upper closures compose by meet. -/
theorem upperClosure_union :
    upperClosure ((s ∪ s' : State W V M) : Set (Possibility W V (Part M))) =
      upperClosure (s : Set (Possibility W V (Part M))) ⊓
        upperClosure (s' : Set (Possibility W V (Part M))) :=
  _root_.upperClosure_union _ _

/-- The union is below the left component. -/
theorem union_le_left : s ∪ s' ≤ s := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_union]
  exact inf_le_left

/-- The union is below the right component. -/
theorem union_le_right : s ∪ s' ≤ s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_union]
  exact inf_le_right

/-- Anything below both components is below their union. -/
theorem le_union (h : t ≤ s) (h' : t ≤ s') : t ≤ s ∪ s' := by
  change upperClosure _ ≤ upperClosure _
  rw [upperClosure_union]
  exact le_inf h h'

/-- **The union is the greatest lower bound** of its components in the
informativeness preorder — the meet dual to `isLUB_mul`. -/
theorem isGLB_union : IsGLB {s, s'} (s ∪ s') :=
  ⟨by rintro x (rfl | rfl); exacts [union_le_left, union_le_right],
   fun _ hu => le_union (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

end State

/-! ### Familiarity

The worldly content of a state — Def. 0.23(v)'s proposition,
[elliott-sudo-2025] Def. 3.1's 𝒲 — is the image `Possibility.world '' s`. -/

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
theorem mem_lowerClosure_iff {X : Set V} (hs : UniformAt X s)
    {p : Possibility W V (Part M)} (hp : p.domain = X) :
    p ∈ lowerClosure s ↔ p ∈ s :=
  ⟨fun ⟨q, hq, hpq⟩ =>
    (Possibility.eq_of_le_of_domain_eq hpq (hp.trans (hs q hq).symm)).symm ▸ hq,
    fun h => subset_lowerClosure h⟩

/-- On a uniform stratum, subsistence is inclusion. -/
theorem lowerClosure_le_iff {X : Set V} (hs : UniformAt X s)
    (hs' : UniformAt X s') :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s' :=
  lowerClosure_le.trans (forall₂_congr fun p hp => mem_lowerClosure_iff hs' (hs p hp))

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
theorem mul_eq_inter_of_uniform {X : Set V} (hs : UniformAt X s)
    (hs' : UniformAt X s') : s * s' = s ∩ s' := by
  ext r
  rw [mem_mul]
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
theorem uniformAt_mul {X Y : Set V} (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s * s') := by
  intro r hr
  obtain ⟨p, hp, q, hq, -, rfl⟩ := mem_mul.mp hr
  rw [Possibility.domain_union, hs p hp, hs' q hq]

/-- Subsistence out of a stratum factors through reindexing: the weaker
state includes into the restricted image of the stronger — the fibred
order, glued from within-stratum `⊆` along `restrict`. -/
theorem lowerClosure_le_iff_subset_restrict {X : Set V} (hs : UniformAt X s) :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s'.restrict X := by
  rw [lowerClosure_le]
  constructor
  · intro h p hp
    obtain ⟨q, hq, hpq⟩ := h hp
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
theorem lowerClosure_restrict_le (X : Set V) (I : State W V M) :
    lowerClosure (I.restrict X) ≤ lowerClosure I := by
  rw [lowerClosure_le]
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
