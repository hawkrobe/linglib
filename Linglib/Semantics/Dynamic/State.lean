module

public import Linglib.Semantics.Dynamic.Possibility
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Hom.Basic

/-!
# Information states

This file defines an *information state* — a set of possibilities with
partial assignments — and its order and algebra: informativeness as
the preorder lifted along `upperClosure`, with initial state `⊤` and
absurd state `⊥ = ∅`; consistent merge as the monoid `*` and greatest
lower bound, dually union as least upper bound; subsistence as the
dual `lowerClosure` kernel; the strata `State.stratum X`, the least
informative states at each domain, which carry the union of domains to
the merge and through which merging with a uniform state factors as
extension then filtering (`State.mul_eq_sep_of_uniformAt`); the uniform
states, where both kernels collapse to inclusion; and the
classifications of a stratum as world–assignment pairs
(`State.uniformEquiv`) and of states up to informational equivalence as
the complete lattice of upper sets (`State.antisymmetrizationOrderIso`).

`State` is a type synonym whose `≤` is informativeness, oriented like the
inclusion order of `Set` and of `DynamicSemantics.CCP`: a more informed state
lies lower, and discarding points descends (`le_of_subset`). The order is the
one mathlib's Galois connection `gc_upperClosure_coe` induces on sets, and
since neither kernel is antisymmetric, `State` is a `Preorder` only.
[kamp-vangenabith-reyle-2011] orient informativeness the other way, with the
initial state at the bottom, and the content is the same.

## References

- [kamp-vangenabith-reyle-2011], Defs. 0.23 (information states),
  0.25 (informativeness), 0.26 (consistent merge)
- [elliott-sudo-2025], Def. 3.3 (subsistence);
  [groenendijk-stokhof-veltman-1996]
- [visser-vermeulen-1996] (monoidal processing); [heim-1982]
-/

@[expose] public section

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Information states -/

/-- An information state is a set of world–assignment pairs. -/
def State (W V M : Type*) := Set (Possibility W V (Part M))

namespace State

variable {s s' t : State W V M} {p q r : Possibility W V (Part M)} {X Y : Set V}

@[reducible] instance : Membership (Possibility W V (Part M)) (State W V M) :=
  inferInstanceAs (Membership _ (Set _))

instance : HasSubset (State W V M) := ⟨fun s s' => ∀ ⦃p⦄, p ∈ s → p ∈ s'⟩

@[reducible] instance : EmptyCollection (State W V M) :=
  inferInstanceAs (EmptyCollection (Set _))

@[reducible] instance : Union (State W V M) := inferInstanceAs (Union (Set _))

@[reducible] instance : Inter (State W V M) := inferInstanceAs (Inter (Set _))

@[reducible] instance : SDiff (State W V M) := inferInstanceAs (SDiff (Set _))

@[ext] theorem ext (h : ∀ p, p ∈ s ↔ p ∈ s') : s = s' :=
  Set.ext h

/-- `s ≤ s'` iff `s` carries at least as much information as `s'`. -/
instance : Preorder (State W V M) :=
  .lift (OrderDual.toDual ∘ upperClosure :
    State W V M → (UpperSet (Possibility W V (Part M)))ᵒᵈ)

/-- Every point of the stronger state lies above a point of the weaker. -/
theorem le_def : s ≤ s' ↔ ∀ p ∈ s, ∃ q ∈ s', q ≤ p :=
  le_upperClosure

/-- The initial information state `⊤ = W × {g_⊤}`. -/
instance : OrderTop (State W V M) where
  top := Set.range Possibility.bot
  le_top _ := le_def.mpr fun p _ => ⟨.bot p.world, ⟨p.world, rfl⟩, Possibility.bot_le⟩

/-- Membership in the initial state: no referent defined. -/
theorem mem_top : r ∈ (⊤ : State W V M) ↔ ∀ v, r.assignment v = ⊥ :=
  ⟨fun ⟨_, hw⟩ _ => hw ▸ rfl, fun h =>
    ⟨r.world, Possibility.ext rfl (funext fun v => (h v).symm)⟩⟩

/-- The absurd state `⊥ = ∅` is maximally informative. -/
instance : OrderBot (State W V M) where
  bot := ∅
  bot_le _ := le_def.mpr fun _ hq => hq.elim

@[simp] theorem bot_eq_empty : (⊥ : State W V M) = ∅ := rfl

/-- Discarding points only adds information. -/
theorem le_of_subset (h : s ⊆ s') : s ≤ s' :=
  le_def.mpr fun p hp ↦ ⟨p, h hp, le_rfl⟩

/-- Only the absurd state is at least as informative as the absurd state. -/
theorem eq_empty_of_le_bot (h : s ≤ ⊥) : s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp ↦ let ⟨_, hq, _⟩ := le_def.mp h p hp; hq.elim

/-! ### Subsistence

*Subsistence* ([elliott-sudo-2025], Def. 3.3, after
[groenendijk-stokhof-veltman-1996] Defs. 2.8–2.9) is not a new
relation: a point subsists in a state iff it lies in the lower closure
of its point set (`mem_lowerClosure`: some point of the state extends
it), and a state subsists in another iff `lowerClosure s ≤
lowerClosure s'` — the closure kernel dual to `≤`, with `⊥ = ∅` at the
bottom of both. -/

/-! ### Consistent merge as multiplication -/

open PartialUnify (unify unify_comm unify_assoc sup_coe_eq_coe_iff coe_sup_eq_coe_iff
  unify_eq_left unify_eq_right unify_le_coe_iff unify_ne_top_iff_bddAbove)

/-- `s * s'` is consistent merge, the unifications of pairs of points, one from each state. -/
instance : Mul (State W V M) := ⟨fun s s' ↦ {r | ∃ p ∈ s, ∃ q ∈ s', unify p q = ↑r}⟩

/-- The unit of merge is the initial state. -/
instance : One (State W V M) := ⟨⊤⟩

theorem one_eq_top : (1 : State W V M) = ⊤ := rfl

/-- A point is in the merge when it is the unification of a point of each state. -/
theorem mem_mul_iff_unify : r ∈ s * s' ↔ ∃ p ∈ s, ∃ q ∈ s', unify p q = ↑r := Iff.rfl

/-- Membership in the merge, in union form. -/
theorem mem_mul : r ∈ s * s' ↔ ∃ p ∈ s, ∃ q ∈ s', Compat p q ∧ r = p.union q := by
  simp only [mem_mul_iff_unify, Possibility.unify_eq_coe_iff]

instance : CommMonoid (State W V M) where
  mul_assoc s t u := Set.ext fun r ↦
    ⟨fun ⟨v, ⟨p, hp, q, hq, hv⟩, w, hw, hr⟩ ↦
      let ⟨v', hv', hr'⟩ :=
        coe_sup_eq_coe_iff.mp (unify_assoc p q w ▸ sup_coe_eq_coe_iff.mpr ⟨v, hv, hr⟩)
      ⟨p, hp, v', ⟨q, hq, w, hw, hv'⟩, hr'⟩,
     fun ⟨p, hp, v, ⟨q, hq, w, hw, hv⟩, hr⟩ ↦
      let ⟨v', hv', hr'⟩ :=
        sup_coe_eq_coe_iff.mp ((unify_assoc p q w).symm ▸ coe_sup_eq_coe_iff.mpr ⟨v, hv, hr⟩)
      ⟨v', ⟨p, hp, q, hq, hv'⟩, w, hw, hr'⟩⟩
  one_mul s := Set.ext fun r ↦
    ⟨fun ⟨_, ⟨w, rfl⟩, p, hp, h⟩ ↦
      have hw : Possibility.bot w ≤ p := Possibility.bot_le_of_compat
        (Compat.symm (unify_ne_top_iff_bddAbove.mp (h ▸ WithTop.coe_ne_top)))
      WithTop.coe_inj.mp ((unify_eq_right.mpr hw).symm.trans h) ▸ hp,
     fun hr ↦ ⟨_, ⟨r.world, rfl⟩, r, hr, unify_eq_right.mpr Possibility.bot_le⟩⟩
  mul_one s := Set.ext fun r ↦
    ⟨fun ⟨p, hp, _, ⟨w, rfl⟩, h⟩ ↦
      have hw : Possibility.bot w ≤ p :=
        Possibility.bot_le_of_compat (unify_ne_top_iff_bddAbove.mp (h ▸ WithTop.coe_ne_top))
      WithTop.coe_inj.mp ((unify_eq_left.mpr hw).symm.trans h) ▸ hp,
     fun hr ↦ ⟨r, hr, _, ⟨r.world, rfl⟩, unify_eq_left.mpr Possibility.bot_le⟩⟩
  mul_comm s s' := Set.ext fun _ ↦
    ⟨fun ⟨p, hp, q, hq, h⟩ ↦ ⟨q, hq, p, hp, (unify_comm q p).trans h⟩,
     fun ⟨q, hq, p, hp, h⟩ ↦ ⟨p, hp, q, hq, (unify_comm p q).trans h⟩⟩

/-- The absurd state absorbs merge. -/
@[simp] theorem empty_mul : (∅ : State W V M) * s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hr ↦ let ⟨_, hp, _⟩ := mem_mul.mp hr; Set.notMem_empty _ hp

@[simp] theorem mul_empty : s * (∅ : State W V M) = ∅ := by rw [mul_comm, empty_mul]

/-- The Smyth face of the merge: upper closures compose by join. -/
theorem upperClosure_mul :
    upperClosure (s * s') = upperClosure s ⊔ upperClosure s' := by
  ext x
  simp only [SetLike.mem_coe, UpperSet.mem_sup_iff, mem_upperClosure]
  exact ⟨fun ⟨r, ⟨p, hp, q, hq, h⟩, hrx⟩ ↦
      have := unify_le_coe_iff.mp (h ▸ WithTop.coe_le_coe.mpr hrx)
      ⟨⟨p, hp, this.1⟩, q, hq, this.2⟩,
    fun ⟨⟨p, hp, hpx⟩, q, hq, hqx⟩ ↦
      let ⟨r, hr, hrx⟩ := WithTop.le_coe_iff.mp (unify_le_coe_iff.mpr ⟨hpx, hqx⟩)
      ⟨r, ⟨p, hp, q, hq, hr⟩, hrx⟩⟩

/-- The merge is below the left factor. -/
theorem mul_le_left : s * s' ≤ s :=
  le_sup_left.trans_eq upperClosure_mul.symm

/-- The merge is below the right factor. -/
theorem mul_le_right : s * s' ≤ s' :=
  le_sup_right.trans_eq upperClosure_mul.symm

/-- Anything below both factors is below their merge. -/
theorem le_mul (h : t ≤ s) (h' : t ≤ s') : t ≤ s * s' :=
  upperClosure_mul.trans_le (sup_le h h')

/-- The merge is the greatest lower bound of its factors. -/
theorem isGLB_mul : IsGLB {s, s'} (s * s') :=
  ⟨by rintro x (rfl | rfl); exacts [mul_le_left, mul_le_right],
   fun _ hu => le_mul (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-- Merge is monotone in the informativeness order. -/
instance : CovariantClass (State W V M) (State W V M) (· * ·) (· ≤ ·) :=
  ⟨fun _ _ _ h => le_mul mul_le_left (mul_le_right.trans h)⟩

/-! ### Union is the join

Merge is the meet of the informativeness order; plain union is its
join — pooling two states keeps exactly their common information. `∪`
is **not** merge: within a stratum merge is intersection
(`mul_eq_inter_of_uniform`), the eliminative regime. -/

/-- The Smyth face of the union: upper closures compose by meet. -/
theorem upperClosure_union :
    upperClosure (s ∪ s') = upperClosure s ⊓ upperClosure s' :=
  _root_.upperClosure_union _ _

/-- The union is above the left component. -/
theorem left_le_union : s ≤ s ∪ s' :=
  upperClosure_union.trans_le inf_le_left

/-- The union is above the right component. -/
theorem right_le_union : s' ≤ s ∪ s' :=
  upperClosure_union.trans_le inf_le_right

/-- Anything above both components is above their union. -/
theorem union_le (h : s ≤ t) (h' : s' ≤ t) : s ∪ s' ≤ t :=
  (le_inf h h').trans_eq upperClosure_union.symm

/-- The union is the least upper bound of its components. -/
theorem isLUB_union : IsLUB {s, s'} (s ∪ s') :=
  ⟨by rintro x (rfl | rfl); exacts [left_le_union, right_le_union],
   fun _ hu => union_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-! ### States up to informational equivalence

The Smyth kernel is full: `UpperSet`'s complete lattice is the algebra
of states up to equivalence, and Def. 0.26's unrestricted
(arbitrary-family) merge is `sSup` there. -/

/-- Up to informational equivalence, states are exactly the upper sets
of possibilities, ordered by inclusion. -/
def antisymmetrizationOrderIso :
    Antisymmetrization (State W V M) (· ≤ ·) ≃o
      (UpperSet (Possibility W V (Part M)))ᵒᵈ where
  toFun := Quotient.lift (fun s : State W V M => OrderDual.toDual (upperClosure s))
    fun _ _ h => le_antisymm (α := (UpperSet _)ᵒᵈ) h.1 h.2
  invFun U := toAntisymmetrization (· ≤ ·)
    (↑(OrderDual.ofDual U) : Set (Possibility W V (Part M)))
  left_inv := by
    refine Quotient.ind fun s => Quotient.sound ?_
    have key : upperClosure ↑(upperClosure (s : Set (Possibility W V (Part M)))) =
        upperClosure (s : Set (Possibility W V (Part M))) :=
      SetLike.coe_injective (upperClosure _).upper'.upperClosure
    exact ⟨le_of_eq (α := UpperSet _) key.symm, le_of_eq (α := UpperSet _) key⟩
  right_inv U :=
    congrArg OrderDual.toDual (SetLike.coe_injective (OrderDual.ofDual U).upper'.upperClosure)
  map_rel_iff' {a b} := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Iff.rfl

/-! ### Familiarity

The worldly content of a state — Def. 0.23(v)'s proposition,
[elliott-sudo-2025] Def. 3.1's 𝒲 — is the image `Possibility.world '' s`. -/

/-- A referent is *familiar* at a state: defined at every point. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, (p.assignment x).Dom

/-- A referent is *novel* at a state: defined at no point. -/
def Novel (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, ¬(p.assignment x).Dom

theorem Familiar.mono {s s' : State W V M} {x : V} (h : Familiar s' x) (hs : s ⊆ s') :
    Familiar s x := fun p hp => h p (hs hp)

theorem Novel.mono {s s' : State W V M} {x : V} (h : Novel s' x) (hs : s ⊆ s') :
    Novel s x := fun p hp => h p (hs hp)

/-- Familiarity ascends in informativeness: a card established in a state is
established in every more informative one. -/
theorem Familiar.of_le {x : V} (h : Familiar s x) (hs : s' ≤ s) : Familiar s' x := fun q hq ↦
  let ⟨p, hp, hpq⟩ := le_def.mp hs q hq
  Possibility.domain_mono hpq (h p hp)

theorem Familiar.mul_left {x : V} (h : Familiar s x) : Familiar (s * s') x :=
  h.of_le mul_le_left

theorem Familiar.mul_right {x : V} (h : Familiar s' x) : Familiar (s * s') x :=
  h.of_le mul_le_right

/-- A card novel at both factors is novel at their merge. -/
theorem Novel.mul {x : V} (h : Novel s x) (h' : Novel s' x) : Novel (s * s') x := by
  intro r hr
  obtain ⟨p, hp, q, hq, -, rfl⟩ := mem_mul.mp hr
  simpa [Part.or_dom] using not_or.mpr ⟨h p hp, h' q hq⟩

/-! ### Strata

The stratum at `X` is the least informative state defining exactly the
referents in `X`; the states uniform at `X` are its subsets, and strata
multiply as their bases unite, so `stratum` carries the union of bases
to the merge. Merging with a state uniform at `X` factors through the
stratum: extension along `X`, then filtering by restriction to `X`
(`mul_eq_sep_of_uniformAt`) — [heim-1982]'s atomic rule, whose
satisfaction clause filters and whose domain clause extends. -/

/-- The stratum at `X`: every point defining exactly the referents in `X`. -/
def stratum (X : Set V) : State W V M := {p | p.domain = X}

@[simp] theorem mem_stratum : p ∈ (stratum X : State W V M) ↔ p.domain = X := Iff.rfl

/-- The state is uniform at `X`: every point defines exactly the
referents in `X`. -/
def UniformAt (X : Set V) (s : State W V M) : Prop :=
  ∀ p ∈ s, Possibility.domain p = X

theorem uniformAt_iff_subset_stratum : UniformAt X s ↔ s ⊆ stratum X := Iff.rfl

theorem uniformAt_stratum : UniformAt X (stratum X : State W V M) := fun _ hp ↦ hp

/-- The initial state is the empty stratum. -/
theorem stratum_empty : (stratum ∅ : State W V M) = ⊤ :=
  ext fun _ ↦ by rw [mem_stratum, Possibility.domain_eq_empty_iff, mem_top]

/-- The initial state is uniform at the empty base. -/
theorem uniformAt_top : UniformAt ∅ (⊤ : State W V M) :=
  stratum_empty ▸ uniformAt_stratum

/-- Extension along no referents changes nothing. -/
@[simp] theorem mul_stratum_empty : s * stratum ∅ = s := by
  rw [stratum_empty, ← one_eq_top, mul_one]

/-- The merge with a stratum: the points above a point of `s` whose domain
adds exactly `X`. -/
theorem mem_mul_stratum :
    r ∈ s * stratum X ↔ ∃ p ∈ s, p ≤ r ∧ r.domain = p.domain ∪ X := by
  rw [mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, -, rfl⟩
    exact ⟨p, hp, Possibility.le_union_left, by rw [Possibility.domain_union, mem_stratum.mp hq]⟩
  · rintro ⟨p, hp, hpr, hdom⟩
    refine ⟨p, hp, r.restrict X, ?_, .of_le hpr Possibility.restrict_le,
      Possibility.eq_union_restrict hpr hdom⟩
    show (r.restrict X).domain = X
    rw [Possibility.domain_restrict, hdom, Set.inter_eq_left.mpr Set.subset_union_right]

/-- Strata multiply as their bases unite. -/
theorem stratum_union : (stratum (X ∪ Y) : State W V M) = stratum X * stratum Y := by
  ext r
  rw [mem_mul_stratum, mem_stratum]
  constructor
  · intro hr
    have hX : (r.restrict X).domain = X := by
      rw [Possibility.domain_restrict, hr, Set.inter_eq_left.mpr Set.subset_union_left]
    exact ⟨r.restrict X, hX, Possibility.restrict_le, by rw [hX, hr]⟩
  · rintro ⟨p, hp, -, hdom⟩
    rw [hdom, mem_stratum.mp hp]

/-- Extension along referents every point already defines changes nothing. -/
theorem mul_stratum_eq_self (h : ∀ p ∈ s, X ⊆ p.domain) : s * stratum X = s := by
  ext r
  rw [mem_mul_stratum]
  constructor
  · rintro ⟨p, hp, hpr, hdom⟩
    rw [Set.union_eq_left.mpr (h p hp)] at hdom
    exact Possibility.eq_of_le_of_domain_eq hpr hdom.symm ▸ hp
  · exact fun hr ↦ ⟨r, hr, le_rfl, (Set.union_eq_left.mpr (h r hr)).symm⟩

/-- Extension along `X` establishes every card in `X`. -/
theorem familiar_mul_stratum {x : V} (hx : x ∈ X) : Familiar (s * stratum X) x := fun r hr ↦ by
  obtain ⟨_, _, _, hdom⟩ := mem_mul_stratum.mp hr
  show x ∈ r.domain
  rw [hdom]
  exact Set.mem_union_right _ hx

/-- Extension along an established card changes nothing. -/
theorem Familiar.mul_stratum_singleton {x : V} (h : Familiar s x) : s * stratum {x} = s :=
  mul_stratum_eq_self fun p hp ↦ Set.singleton_subset_iff.mpr (h p hp)

/-- Merging with a state uniform at `X` is extension along `X` followed by
filtering through restriction to `X`. -/
theorem mul_eq_sep_of_uniformAt (hs' : UniformAt X s') :
    s * s' = {r ∈ s * stratum X | r.restrict X ∈ s'} := by
  ext r
  rw [mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    refine ⟨mem_mul.mpr ⟨p, hp, q, hs' q hq, hpq, rfl⟩, ?_⟩
    rwa [← (Possibility.le_iff_eq_restrict (hs' q hq)).mp (Possibility.le_union_right hpq)]
  · rintro ⟨hr, hq⟩
    obtain ⟨p, hp, hpr, hdom⟩ := mem_mul_stratum.mp hr
    exact ⟨p, hp, _, hq, .of_le hpr Possibility.restrict_le,
      Possibility.eq_union_restrict hpr hdom⟩

/-- The proposition state of an atomic predicate at card `x`: the points of
the stratum `{x}` whose value at `x` satisfies the predicate at their world. -/
def atomAt (x : V) (pred : W → M → Prop) : State W V M :=
  {q ∈ (stratum {x} : State W V M) | ∃ m ∈ q.assignment x, pred q.world m}

theorem uniformAt_atomAt {x : V} {pred : W → M → Prop} :
    UniformAt {x} (atomAt x pred : State W V M) := fun _ h ↦ h.1

/-- Merging with an atom extends along its card, then filters by its
predicate: the satisfaction clause and the domain clause of [heim-1982]'s
atomic rule, per point. -/
theorem mul_atomAt {x : V} {pred : W → M → Prop} :
    s * atomAt x pred = {r ∈ s * stratum {x} | ∃ m ∈ r.assignment x, pred r.world m} := by
  rw [mul_eq_sep_of_uniformAt uniformAt_atomAt]
  ext r
  refine and_congr_right fun hr ↦ ?_
  have hx : x ∈ r.domain := familiar_mul_stratum (Set.mem_singleton x) r hr
  show ((r.restrict {x}).domain = {x} ∧
    ∃ m ∈ (r.restrict {x}).assignment x, pred (r.restrict {x}).world m) ↔ _
  rw [Possibility.restrict_assignment_of_mem (Set.mem_singleton x), Possibility.domain_restrict,
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx)]
  exact and_iff_right rfl

/-- A uniform stratum is an antichain: comparable points with one
domain are equal. -/
theorem UniformAt.isAntichain (hs : UniformAt X s) :
    IsAntichain (· ≤ ·) (s : Set (Possibility W V (Part M))) :=
  fun p hp q hq hne hpq =>
    hne (Possibility.eq_of_le_of_domain_eq hpq ((hs p hp).trans (hs q hq).symm))

/-- Within one stratum, merge is intersection. -/
theorem UniformAt.mul_eq_inter (hs : UniformAt X s) (hs' : UniformAt X s') :
    s * s' = s ∩ s' := by
  rw [mul_eq_sep_of_uniformAt hs', mul_stratum_eq_self fun p hp ↦ (hs p hp).symm.subset]
  exact ext fun r ↦ and_congr_right fun hr ↦ by rw [Possibility.restrict_eq_self (hs r hr)]

/-- Restriction of a state: pointwise, by direct image. -/
def restrict (X : Set V) (s : State W V M) : State W V M :=
  Possibility.restrict X '' s

/-- Membership in a restriction. -/
theorem mem_restrict : p ∈ s.restrict X ↔ ∃ q ∈ s, q.restrict X = p :=
  Iff.rfl

/-- Restriction fixes its stratum. -/
theorem UniformAt.restrict_eq (hs : UniformAt X s) : s.restrict X = s :=
  ext fun p =>
    ⟨fun ⟨q, hq, hqp⟩ => (hqp.symm.trans (Possibility.restrict_eq_self (hs q hq))) ▸ hq,
     fun hp => ⟨p, hp, Possibility.restrict_eq_self (hs p hp)⟩⟩

/-- A point at the stratum's domain lies below `s` iff it lies in the
restriction of `s`. -/
theorem mem_lowerClosure_iff_mem_restrict (hp : p.domain = X) :
    p ∈ lowerClosure s ↔ p ∈ s.restrict X :=
  ⟨fun ⟨q, hq, hpq⟩ => ⟨q, hq, ((Possibility.le_iff_eq_restrict hp).mp hpq).symm⟩,
   fun ⟨q, hq, hqp⟩ => ⟨q, hq, hqp ▸ Possibility.restrict_le⟩⟩

/-- A point lies above a uniform `s` iff its restriction is a point
of `s`. -/
theorem UniformAt.mem_upperClosure_iff_restrict_mem (hs : UniformAt X s) :
    q ∈ upperClosure s ↔ q.restrict X ∈ s :=
  ⟨fun ⟨p, hp, hpq⟩ => (Possibility.le_iff_eq_restrict (hs p hp)).mp hpq ▸ hp,
   fun h => ⟨q.restrict X, h, Possibility.restrict_le⟩⟩

/-- Into a uniform stratum, subsistence is membership. -/
theorem UniformAt.mem_lowerClosure (hs : UniformAt X s) (hp : p.domain = X) :
    p ∈ lowerClosure s ↔ p ∈ s :=
  (mem_lowerClosure_iff_mem_restrict hp).trans (by rw [hs.restrict_eq])

/-- On a uniform stratum, subsistence is inclusion. -/
theorem UniformAt.lowerClosure_le_iff (hs : UniformAt X s) (hs' : UniformAt X s') :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s' :=
  lowerClosure_le.trans (forall₂_congr fun p hp => hs'.mem_lowerClosure (hs p hp))

/-- Into a uniform stratum, domination is membership. -/
theorem UniformAt.mem_upperClosure (hs : UniformAt X s) (hq : q.domain = X) :
    q ∈ upperClosure s ↔ q ∈ s :=
  hs.mem_upperClosure_iff_restrict_mem.trans (by rw [Possibility.restrict_eq_self hq])

/-- On a uniform stratum, informativeness is inclusion. -/
theorem UniformAt.le_iff_subset (hs : UniformAt X s) (hs' : UniformAt X s') :
    s ≤ s' ↔ s ⊆ s' :=
  le_def.trans (forall₂_congr fun p hp => hs'.mem_upperClosure (hs p hp))

section Fibred

/-- Merge unites strata. -/
theorem UniformAt.mul (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s * s') := by
  intro r hr
  obtain ⟨p, hp, q, hq, -, rfl⟩ := mem_mul.mp hr
  rw [Possibility.domain_union, hs p hp, hs' q hq]

/-- Subsistence out of a stratum is inclusion into the restricted image. -/
theorem UniformAt.lowerClosure_le_iff_restrict (hs : UniformAt X s) :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s'.restrict X :=
  lowerClosure_le.trans
    (forall₂_congr fun p hp => mem_lowerClosure_iff_mem_restrict (hs p hp))

/-- Informativeness over a stratum is inclusion of the restricted image. -/
theorem UniformAt.le_iff_restrict_subset (hs : UniformAt X s) :
    s' ≤ s ↔ s'.restrict X ⊆ s :=
  le_def.trans <|
    (forall₂_congr fun _ _ => hs.mem_upperClosure_iff_restrict_mem).trans
      Set.forall_mem_image.symm

end Fibred

/-- Restriction only forgets: the restricted state subsists in the
original. -/
theorem lowerClosure_restrict_le :
    lowerClosure (s.restrict X) ≤ lowerClosure s :=
  lowerClosure_le.mpr <|
    Set.forall_mem_image.mpr fun q hq => ⟨q, hq, Possibility.restrict_le⟩

/-- Restriction meets the stratification. -/
theorem UniformAt.restrict (hs : UniformAt Y s) :
    UniformAt (X ∩ Y) (s.restrict X) := by
  rintro p ⟨q, hq, rfl⟩
  rw [Possibility.domain_restrict, hs q hq]

/-- Restriction composes along intersections. -/
theorem restrict_restrict :
    (s.restrict Y).restrict X = s.restrict (X ∩ Y) := by
  simp only [restrict, Set.image_image, Possibility.restrict_restrict]

/-! ### The uniform classification -/

/-- Uniform states at `X` are sets of world–`X`-assignment pairs. -/
def uniformEquiv (X : Set V) :
    {I : State W V M // UniformAt X I} ≃ Set (W × (X → M)) :=
  (Equiv.Set.powerset {p : Possibility W V (Part M) | p.domain = X}).trans
    (Equiv.setCongr (Possibility.domainEquiv X))

@[simp] theorem mem_uniformEquiv {I : {I : State W V M // UniformAt X I}}
    {e : W × (X → M)} :
    e ∈ uniformEquiv X I ↔ ((Possibility.domainEquiv X).symm e).1 ∈ I.1 :=
  Set.mem_image_equiv

variable [DecidableEq V]

/-- Random assignment: indeterministically extend each point to a
defined value at `x`. -/
def randomAssign (s : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ s, ∃ m : M, p = q.update x (Part.some m)}

/-- Random assignment makes its referent familiar. -/
theorem familiar_randomAssign (s : State W V M) (x : V) :
    Familiar (s.randomAssign x) x := by
  rintro p ⟨q, -, m, rfl⟩
  simp

/-- Random assignment keeps the other referents familiar. -/
theorem Familiar.randomAssign {s : State W V M} {y : V} (h : Familiar s y) (x : V) :
    Familiar (s.randomAssign x) y := by
  rintro p ⟨q, hq, m, rfl⟩
  by_cases hyx : y = x
  · subst hyx; simp
  · simpa [Possibility.update, Function.update_of_ne hyx] using h q hq

/-- Random assignment keeps the other referents novel. -/
theorem Novel.randomAssign {s : State W V M} {y : V} (h : Novel s y) {x : V} (hyx : y ≠ x) :
    Novel (s.randomAssign x) y := by
  rintro p ⟨q, hq, m, rfl⟩
  simpa [Possibility.update, Function.update_of_ne hyx] using h q hq

/-- Every point of a random assignment extends a point of the state when the
referent was novel. -/
theorem randomAssign_le {s : State W V M} {x : V} (h : Novel s x) : s.randomAssign x ≤ s :=
  le_def.mpr fun _ ⟨p, hp, _, hq⟩ ↦ ⟨p, hp, hq ▸ Possibility.le_update_of_not_dom (h p hp) _⟩

/-- Extension along a novel card is random assignment. -/
theorem Novel.mul_stratum_singleton {s : State W V M} {x : V} (h : Novel s x) :
    s * stratum {x} = s.randomAssign x := by
  ext r
  rw [mem_mul_stratum]
  constructor
  · rintro ⟨p, hp, hpr, hdom⟩
    rw [Set.union_singleton] at hdom
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp (show x ∈ r.domain from hdom ▸ Set.mem_insert x _)
    exact ⟨p, hp, m, Possibility.eq_update_of_le hpr hdom hm⟩
  · rintro ⟨p, hp, m, rfl⟩
    exact ⟨p, hp, Possibility.le_update_of_not_dom (h p hp) _,
      by rw [Possibility.domain_update_some, Set.union_singleton]⟩

end State

end DynamicSemantics
