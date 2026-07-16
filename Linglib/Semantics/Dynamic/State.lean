import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.DependsOn
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Lattice

/-!
# Indexed information states

An *information state* relative to a *base* `X` — a finite set of live
discourse referents — is an `X`-supported set of possibilities
(`Possibility.lean`). The base is the "context as storage" dimension of
dynamic meaning: finer than a proposition, coarser than syntax
([kamp-vangenabith-reyle-2011]'s Partee-marbles argument). Level-0 states are plain,
unindexed sets of possibilities (`Update.lean`); the transitions
acting on states live in `Transition.lean`.

## Main definitions

- `BaseSupported X S`: membership in `S` depends on assignments only
  through their values at `X` (mathlib's `DependsOn`, per world).
- `State W V M`: a base with an `X`-supported carrier, ordered by
  informativeness, with the minimal state Λ as `⊥` and consistent merge
  as `⊔`.
- `State.prop`: the proposition a state determines.
- `State.restrict`, `State.weaken`, `State.kernRestrict`: the transports
  along base inclusion — [lawvere-1969]'s quantifier triple.
- `State.fiberEquiv`, `State.fiberOrderIso`: the states indexed at `X`, as
  propositions over the `X`-collapsed state space.

## Main results

- `le_iff_projection`, `mem_sup_iff_projection`: the chapter's projection
  and choice-function forms of order and merge coincide with the
  componentwise ones — support supplies the witnesses.
- `baseSupported_iff`, `BaseSupported.preimage_image_mk`: support is
  *saturation* for `Possibility.agreeSetoid ↑X`.
- `prop_restrict`, `le_restrict_iff`: restriction never changes the
  proposition, and is the universal `Y`-supported approximation.
- `Compatible.restrict_sup_left`, `sup_le_of_restrict_eq`: consistent
  merge is sheaf gluing for the presheaf of states
  ([abramsky-sadrzadeh-2014]'s semantic unification), and the least one;
  `exists_ne_of_restrict_eq`: the gluing is not unique — restriction
  forgets cross-referent correlation.
- `weaken_le_iff`, `kernRestrict_le_iff`, `restrict_weaken`,
  `restrict_sup_weaken`: the adjunctions `kernRestrict ⊣ weaken ⊣
  restrict`, Beck–Chevalley, and Frobenius — the fibers form a
  hyperdoctrine over the category of contexts ([jacobs-1999]).
- `baseSupported_iff_exists_preimage`: supported sets are the cylinders —
  preimages along the projection to environments.
- `fiberOrderIsoProd`, `fiberEmptyOrderIso`: the fiber at `X` classified
  as propositions over world–`X`-assignment pairs ([heim-1982]'s
  satisfaction sets), degenerating at `X = ∅` to bare propositions
  ([veltman-1996]'s update-semantics states).

## Implementation notes

*Indexed* is Jacobs' term, via [visser-1998]'s "indexed" treatment of
predicate-logic semantics: meanings carry their variable declaration —
the pair ⟨base, carrier⟩ — rather than living over one global assignment
space. The chapter calls the declaration a *base*; type theory calls it
a basis.

The chapter's partial embeddings with domain `X` are rendered as total
assignments with `X`-supported membership; Def. 25's informativeness
order, Def. 26's consistent merge, and Def. 23(iv)'s minimal state then
collapse to order theory (`PartialOrder`, `SemilatticeSup`, `OrderBot`).

`State` gets a `Membership` instance rather than `SetLike`: the coe to
carriers is not injective (`Set.univ` is supported at every base), and
`Filter` is the precedent. The projection ladder carrier → agreement
classes (`fiberEquiv`) → worlds (`prop`) forgets in two documented steps;
[muskens-van-benthem-visser-2011]'s propositions-over-a-state-space
picture is the middle rung, at granularity `X`.

## References

- [kamp-vangenabith-reyle-2011], Defs. 22–26
- [heim-1982]
- [muskens-van-benthem-visser-2011], [abramsky-sadrzadeh-2014]
- [lawvere-1969], [jacobs-1999]
-/

namespace DynamicSemantics

variable {W V M : Type*} {X Y : Finset V} {S T : Set (Possibility W V M)}

/-! ### Base-supported sets -/

/-- A set of possibilities is *supported* on `X` when membership depends on
the assignment only through its values at `X`: for each world, the
membership predicate `DependsOn` the coordinates in `X`. -/
def BaseSupported (X : Finset V) (S : Set (Possibility W V M)) : Prop :=
  ∀ w : W, DependsOn (fun f => (⟨w, f⟩ : Possibility W V M) ∈ S) ↑X

/-- Introduction form: supply the membership-invariance iff. -/
theorem baseSupported_of_iff
    (h : ∀ ⦃w : W⦄ ⦃f g : V → M⦄, Set.EqOn f g ↑X →
      ((⟨w, f⟩ : Possibility W V M) ∈ S ↔ ⟨w, g⟩ ∈ S)) :
    BaseSupported X S :=
  fun _ _ _ hfg => propext (h hfg)

/-- Elimination form: membership is invariant under agreement on the base. -/
theorem BaseSupported.mem_iff (h : BaseSupported X S) {w : W} {f g : V → M} (hfg : Set.EqOn f g ↑X) :
    (⟨w, f⟩ : Possibility W V M) ∈ S ↔ ⟨w, g⟩ ∈ S :=
  iff_of_eq (h w hfg)

theorem BaseSupported.mono (h : BaseSupported X S) (hXY : X ⊆ Y) : BaseSupported Y S :=
  fun w => (h w).mono (Finset.coe_subset.mpr hXY)

theorem BaseSupported.inter (hS : BaseSupported X S) (hT : BaseSupported X T) : BaseSupported X (S ∩ T) :=
  baseSupported_of_iff fun _ _ _ hfg =>
    and_congr (hS.mem_iff hfg) (hT.mem_iff hfg)

/-- A set is supported on `X` iff membership is invariant under agreement on
`X`: `BaseSupported X` is saturation for `Possibility.agreeSetoid ↑X`. -/
theorem baseSupported_iff :
    BaseSupported X S ↔
      ∀ ⦃p q⦄, Possibility.agreeSetoid (↑X : Set V) p q → (p ∈ S ↔ q ∈ S) := by
  constructor
  · rintro h ⟨w, f⟩ ⟨w', g⟩ ⟨rfl, hfg⟩
    exact h.mem_iff hfg
  · intro h
    exact baseSupported_of_iff fun _ _ _ hfg => h ⟨rfl, hfg⟩

/-- Point form of `BaseSupported.mem_iff`: membership is invariant on
agreement classes. -/
theorem BaseSupported.mem_congr (h : BaseSupported X S) {p q : Possibility W V M}
    (hpq : Possibility.agreeSetoid (↑X : Set V) p q) : p ∈ S ↔ q ∈ S :=
  baseSupported_iff.mp h hpq

/-- The saturation round trip: a supported set is the preimage of its image
in the collapsed state space. -/
theorem BaseSupported.preimage_image_mk (h : BaseSupported X S) :
    Quotient.mk (Possibility.agreeSetoid ↑X) ⁻¹' (Quotient.mk _ '' S) = S :=
  Set.Subset.antisymm (fun _ ⟨_, hq, hqp⟩ => (h.mem_congr (Quotient.exact hqp)).mp hq)
    (Set.subset_preimage_image _ _)

/-- Supported sets are exactly the *cylinders*: preimages along the
projection to `X`-environments (`Category.lean`'s `environments`). -/
theorem baseSupported_iff_exists_preimage :
    BaseSupported X S ↔ ∃ T : Set (W × ((↑X : Set V) → M)),
      S = (fun p : Possibility W V M =>
        (p.world, (↑X : Set V).restrict p.assignment)) ⁻¹' T := by
  constructor
  · intro h
    refine ⟨(fun p : Possibility W V M =>
      (p.world, (↑X : Set V).restrict p.assignment)) '' S,
      Set.Subset.antisymm (Set.subset_preimage_image _ _) ?_⟩
    rintro ⟨w, g⟩ ⟨⟨w', f⟩, hf, heq⟩
    obtain ⟨rfl, h2⟩ := Prod.mk.injEq .. |>.mp heq
    exact (h.mem_iff (Set.restrict_eq_restrict_iff.mp h2)).mp hf
  · rintro ⟨T, rfl⟩
    exact baseSupported_of_iff fun w f g hfg => by
      simp only [Set.mem_preimage]
      rw [Set.restrict_eq_restrict_iff.mpr hfg]

/-! ### Information states -/

/-- An information state ([kamp-vangenabith-reyle-2011], Defs. 22–23): a base
`X` of live discourse referents together with an `X`-supported set of
possibilities. -/
@[ext] structure State (W V M : Type*) where
  /-- The live discourse referents (the chapter's base `X`). -/
  base : Finset V
  /-- The possibilities compatible with the information. -/
  carrier : Set (Possibility W V M)
  /-- Membership depends on assignments only through their values at `base`. -/
  supported : BaseSupported base carrier

namespace State

variable {I I' J : State W V M} {p : Possibility W V M}

instance : Membership (Possibility W V M) (State W V M) :=
  ⟨fun I p => p ∈ I.carrier⟩

@[simp] theorem mem_carrier :
    p ∈ I.carrier ↔ p ∈ I := Iff.rfl

/-! ### The informativeness order -/

/-- Informativeness ([kamp-vangenabith-reyle-2011], Def. 25): `I ≤ I'` iff
`I'` carries at least as much information — the base grows and the carrier
shrinks. -/
instance : PartialOrder (State W V M) where
  le I I' := I.base ⊆ I'.base ∧ I'.carrier ⊆ I.carrier
  le_refl _ := ⟨subset_rfl, subset_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h'.2.trans h.2⟩
  le_antisymm _ _ h h' :=
    State.ext (Finset.Subset.antisymm h.1 h'.1) (Set.Subset.antisymm h'.2 h.2)

theorem le_def :
    I ≤ I' ↔ I.base ⊆ I'.base ∧ I'.carrier ⊆ I.carrier := Iff.rfl

/-- The chapter's projection form of Def. 25 — every possibility of the
stronger state restricts to one of the weaker — coincides with `≤`: support
makes the projected witness the possibility itself. -/
theorem le_iff_projection :
    I ≤ I' ↔ I.base ⊆ I'.base ∧
      ∀ ⦃w g⦄, (⟨w, g⟩ : Possibility W V M) ∈ I' →
        ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I ∧ Set.EqOn f g ↑I.base := by
  constructor
  · rintro ⟨hb, hc⟩
    exact ⟨hb, fun w g hg => ⟨g, hc hg, Set.eqOn_refl g _⟩⟩
  · rintro ⟨hb, hproj⟩
    refine ⟨hb, fun p hp => ?_⟩
    obtain ⟨w, g⟩ := p
    obtain ⟨f, hf, hfg⟩ := hproj hp
    exact (I.supported.mem_iff hfg).mp hf

/-- The minimal information state Λ ([kamp-vangenabith-reyle-2011],
Def. 23(iv)): empty base, no information. -/
instance : OrderBot (State W V M) where
  bot := ⟨∅, Set.univ, fun _ _ _ _ => rfl⟩
  bot_le _ := ⟨Finset.empty_subset _, Set.subset_univ _⟩

@[simp] theorem base_bot : (⊥ : State W V M).base = ∅ := rfl
@[simp] theorem carrier_bot : (⊥ : State W V M).carrier = Set.univ := rfl

@[simp] theorem mem_bot : p ∈ (⊥ : State W V M) := trivial

/-! ### Consistent merge is the join -/

section Merge
variable [DecidableEq V]

/-- Consistent merge ([kamp-vangenabith-reyle-2011], Def. 26) is the join of
the informativeness order: union the bases, intersect the carriers. -/
instance : SemilatticeSup (State W V M) where
  sup I I' :=
    ⟨I.base ∪ I'.base, I.carrier ∩ I'.carrier,
      (I.supported.mono Finset.subset_union_left).inter
        (I'.supported.mono Finset.subset_union_right)⟩
  le_sup_left _ _ := ⟨Finset.subset_union_left, Set.inter_subset_left⟩
  le_sup_right _ _ := ⟨Finset.subset_union_right, Set.inter_subset_right⟩
  sup_le _ _ _ h h' :=
    ⟨Finset.union_subset h.1 h'.1, Set.subset_inter h.2 h'.2⟩

@[simp] theorem base_sup (I I' : State W V M) :
    (I ⊔ I').base = I.base ∪ I'.base := rfl
@[simp] theorem carrier_sup (I I' : State W V M) :
    (I ⊔ I').carrier = I.carrier ∩ I'.carrier := rfl

@[simp] theorem mem_sup :
    p ∈ I ⊔ I' ↔ p ∈ I ∧ p ∈ I' := Iff.rfl

/-- The chapter's choice-function form of Def. 26: a possibility belongs to
the merge iff it restricts into each component — support makes the choice
functions the possibility itself. -/
theorem mem_sup_iff_projection {w : W} {k : V → M} :
    (⟨w, k⟩ : Possibility W V M) ∈ I ⊔ I' ↔
      (∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I ∧ Set.EqOn f k ↑I.base) ∧
      (∃ g, (⟨w, g⟩ : Possibility W V M) ∈ I' ∧ Set.EqOn g k ↑I'.base) := by
  constructor
  · rintro ⟨hI, hI'⟩
    exact ⟨⟨k, hI, Set.eqOn_refl k _⟩, ⟨k, hI', Set.eqOn_refl k _⟩⟩
  · rintro ⟨⟨f, hf, hfk⟩, ⟨g, hg, hgk⟩⟩
    exact ⟨(I.supported.mem_iff hfk).mp hf, (I'.supported.mem_iff hgk).mp hg⟩

end Merge

/-! ### The proposition determined by a state -/

/-- The proposition a state determines ([kamp-vangenabith-reyle-2011],
Def. 23(v)): the worlds compatible with some assignment. -/
def prop (I : State W V M) : Set W := {w | ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I}

@[simp] theorem mem_prop {w : W} :
    w ∈ I.prop ↔ ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I := Iff.rfl

theorem prop_eq_image (I : State W V M) : I.prop = Possibility.world '' I.carrier :=
  Set.ext fun _ => ⟨fun ⟨f, hf⟩ => ⟨⟨_, f⟩, hf, rfl⟩, fun ⟨⟨_, f⟩, hp, hw⟩ => ⟨f, hw ▸ hp⟩⟩

/-- Stronger states determine stronger propositions. -/
theorem prop_anti : Antitone (prop : State W V M → Set W) :=
  fun _ _ h _ ⟨f, hf⟩ => ⟨f, h.2 hf⟩

@[simp] theorem prop_bot [Nonempty M] : (⊥ : State W V M).prop = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨fun _ => Classical.arbitrary M, trivial⟩

/-! ### Restriction to a smaller base -/

/-- Restrict a state to base `Y`: the best `Y`-supported approximation — a
possibility survives iff some carrier member agrees with it on `Y`. -/
def restrict (I : State W V M) (Y : Finset V) : State W V M where
  base := Y
  carrier :=
    {p | ∃ f, (⟨p.world, f⟩ : Possibility W V M) ∈ I.carrier ∧
      Set.EqOn f p.assignment ↑Y}
  supported := baseSupported_of_iff fun _ _ _ hgg' =>
    exists_congr fun _ => and_congr_right fun _ =>
      ⟨fun h => h.trans hgg', fun h => h.trans hgg'.symm⟩

@[simp] theorem base_restrict (I : State W V M) (Y : Finset V) :
    (I.restrict Y).base = Y := rfl

@[simp] theorem mem_restrict {w : W} {g : V → M} :
    (⟨w, g⟩ : Possibility W V M) ∈ I.restrict Y ↔
      ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I ∧ Set.EqOn f g ↑Y := Iff.rfl

/-- Restricting to the state's own base is the identity. -/
@[simp] theorem restrict_base (I : State W V M) : I.restrict I.base = I := by
  ext1
  · rfl
  · ext ⟨w, g⟩
    exact ⟨fun ⟨f, hf, hfg⟩ => (I.supported.mem_iff hfg).mp hf,
      fun h => ⟨g, h, Set.eqOn_refl g _⟩⟩

/-- Restriction is transitive along shrinking bases. -/
theorem restrict_restrict (I : State W V M) {Z : Finset V} (hZY : Z ⊆ Y) :
    (I.restrict Y).restrict Z = I.restrict Z := by
  ext1
  · rfl
  · ext ⟨w, g⟩
    constructor
    · rintro ⟨f, ⟨f', hf', hf'f⟩, hfg⟩
      exact ⟨f', hf', (hf'f.mono (Finset.coe_subset.mpr hZY)).trans hfg⟩
    · rintro ⟨f, hf, hfg⟩
      exact ⟨f, ⟨f, hf, Set.eqOn_refl f _⟩, hfg⟩

/-- Restriction to a sub-base weakens the state. -/
theorem restrict_le (h : Y ⊆ I.base) :
    I.restrict Y ≤ I :=
  ⟨h, fun p hp => ⟨p.assignment, hp, Set.eqOn_refl p.assignment _⟩⟩

/-- Restriction is the *best* `Y`-supported approximation: for states indexed
below `Y`, lying below `I.restrict Y` is lying below `I`. -/
theorem le_restrict_iff (hJ : J.base ⊆ Y) (hY : Y ⊆ I.base) : J ≤ I.restrict Y ↔ J ≤ I := by
  constructor
  · exact fun h => h.trans (restrict_le hY)
  · rintro ⟨hb, hc⟩
    refine ⟨hJ, fun p hp => ?_⟩
    obtain ⟨w, g⟩ := p
    obtain ⟨f, hf, hfg⟩ := hp
    exact (J.supported.mem_iff (hfg.mono (Finset.coe_subset.mpr hJ))).mp (hc hf)

/-- Restriction never changes the proposition — only anaphoric potential. -/
@[simp] theorem prop_restrict (I : State W V M) (Y : Finset V) :
    (I.restrict Y).prop = I.prop :=
  Set.ext fun _ =>
    ⟨fun ⟨_, f, hf, _⟩ => ⟨f, hf⟩, fun ⟨f, hf⟩ => ⟨f, f, hf, Set.eqOn_refl f _⟩⟩

/-! ### Weakening and the quantifier adjoints

The three transports along a base inclusion — `kernRestrict`, `weaken`,
`restrict` — are [lawvere-1969]'s quantifier triple `∀ ⊣ w* ⊣ ∃`
(mathlib's `Set.kernImage`, `Set.preimage`, `Set.image` along environment
projections; `Category.lean`'s `fiberOrderIsoProd_restrict` computes the
`restrict` leg). The informativeness order reverses inclusion, so here
the ∃-leg is the *right* adjoint: `kernRestrict ⊣ weaken ⊣ restrict`.
Beck–Chevalley (`restrict_weaken`) commutes the adjoints across the
poset's pullback squares: the fibers form a hyperdoctrine over the
category of contexts ([jacobs-1999]). -/

/-- Weakening: grow the base, keep the carrier — supported carriers are
already cylindric off the base. Semantically vacuous, anaphorically not:
the new referents are live. [jacobs-1999]'s weakening. -/
def weaken (I : State W V M) (h : I.base ⊆ Y) : State W V M where
  base := Y
  carrier := I.carrier
  supported := I.supported.mono h

@[simp] theorem base_weaken (h : I.base ⊆ Y) : (I.weaken h).base = Y := rfl

@[simp] theorem carrier_weaken (h : I.base ⊆ Y) :
    (I.weaken h).carrier = I.carrier := rfl

@[simp] theorem weaken_self (I : State W V M) : I.weaken subset_rfl = I := rfl

theorem weaken_weaken {Z : Finset V} (h : I.base ⊆ Y) (h' : Y ⊆ Z) :
    (I.weaken h).weaken h' = I.weaken (h.trans h') := rfl

/-- The universal counterpart of restriction: a possibility survives iff
*every* variant agreeing with it on `Y` is in the carrier. The ∀-leg of
the quantifier triple (`Set.kernImage` where `restrict` is `Set.image`),
and the transport for universal quantification and the DRS conditional. -/
def kernRestrict (I : State W V M) (Y : Finset V) : State W V M where
  base := Y
  carrier := {p | ∀ f, Set.EqOn f p.assignment ↑Y →
    (⟨p.world, f⟩ : Possibility W V M) ∈ I.carrier}
  supported := baseSupported_of_iff fun _ _ _ hfg =>
    forall_congr' fun _ =>
      imp_congr_left ⟨fun h => h.trans hfg, fun h => h.trans hfg.symm⟩

@[simp] theorem base_kernRestrict : (I.kernRestrict Y).base = Y := rfl

@[simp] theorem mem_kernRestrict {w : W} {g : V → M} :
    (⟨w, g⟩ : Possibility W V M) ∈ I.kernRestrict Y ↔
      ∀ f, Set.EqOn f g ↑Y → (⟨w, f⟩ : Possibility W V M) ∈ I := Iff.rfl

/-- The universal approximation is at least as informative as the
existential one. -/
theorem restrict_le_kernRestrict (I : State W V M) (Y : Finset V) :
    I.restrict Y ≤ I.kernRestrict Y :=
  ⟨subset_rfl, fun p hp =>
    ⟨p.assignment, hp p.assignment (Set.eqOn_refl _ _), Set.eqOn_refl _ _⟩⟩

/-- Weakening is left adjoint to restriction — `Set.image_preimage` in the
fibers, the informativeness order making the ∃-leg the right adjoint.
`le_restrict_iff` is this connection with the weakening left implicit. -/
theorem weaken_le_iff (hJ : J.base ⊆ Y) (hY : Y ⊆ I.base) :
    J.weaken hJ ≤ I ↔ J ≤ I.restrict Y := by
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨hJ, fun p hp => ?_⟩
    obtain ⟨w, g⟩ := p
    obtain ⟨f, hf, hfg⟩ := hp
    exact (J.supported.mem_iff (hfg.mono (Finset.coe_subset.mpr hJ))).mp (hc hf)
  · rintro ⟨-, hc⟩
    exact ⟨hY, fun p hp => hc ⟨p.assignment, hp, Set.eqOn_refl _ _⟩⟩

/-- `kernRestrict` is left adjoint to weakening — `Set.preimage_kernImage`
in the fibers: `I.kernRestrict J.base` is the strongest `J.base`-supported
consequence of `I`. -/
theorem kernRestrict_le_iff (h : J.base ⊆ I.base) :
    I.kernRestrict J.base ≤ J ↔ I ≤ J.weaken h := by
  constructor
  · rintro ⟨-, hc⟩
    exact ⟨subset_rfl, fun p hp => hc hp p.assignment (Set.eqOn_refl _ _)⟩
  · rintro ⟨-, hc⟩
    refine ⟨subset_rfl, fun p hp => ?_⟩
    obtain ⟨w, g⟩ := p
    intro f hfg
    exact hc ((J.supported.mem_iff hfg).mpr hp)

section BeckChevalley
variable [DecidableEq V]

/-- Beck–Chevalley: weakening then restricting is restricting to the
intersection then weakening — the quantifier adjoints commute across the
poset's pullback squares. -/
theorem restrict_weaken (I : State W V M) (Z : Finset V) :
    (I.weaken (Finset.subset_union_left : I.base ⊆ I.base ∪ Z)).restrict Z =
      (I.restrict (I.base ∩ Z)).weaken Finset.inter_subset_right := by
  refine State.ext rfl (Set.ext fun p => ?_)
  obtain ⟨w, g⟩ := p
  constructor
  · rintro ⟨f, hf, hfg⟩
    exact ⟨f, hf, hfg.mono (by rw [Finset.coe_inter]; exact Set.inter_subset_right)⟩
  · rintro ⟨f, hf, hfg⟩
    refine ⟨I.base.piecewise f g,
      (I.supported.mem_iff fun x hx => I.base.piecewise_eq_of_mem f g hx).mpr hf,
      fun z hz => ?_⟩
    by_cases hzB : z ∈ I.base
    · rw [Finset.piecewise_eq_of_mem _ _ _ hzB]
      exact hfg (by rw [Finset.coe_inter]; exact ⟨hzB, hz⟩)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hzB]

end BeckChevalley

/-! ### Merge is gluing -/

section Gluing
variable [DecidableEq V]

/-- Two states are *compatible* when they agree under restriction to their
common base ([abramsky-sadrzadeh-2014]'s compatible families, for pairs). -/
def Compatible (I J : State W V M) : Prop :=
  I.restrict (I.base ∩ J.base) = J.restrict (I.base ∩ J.base)

@[simp] theorem compatible_refl (I : State W V M) : I.Compatible I := by
  show I.restrict _ = I.restrict _
  rw [Finset.inter_self]

theorem Compatible.symm (h : I.Compatible J) : J.Compatible I := by
  show J.restrict _ = I.restrict _
  rw [Finset.inter_comm]
  exact Eq.symm h

/-- Disjoint-base states determining the same proposition are compatible —
[kamp-vangenabith-reyle-2011] Def. 26's "of particular importance" case. -/
theorem compatible_of_disjoint (hd : Disjoint I.base J.base)
    (hw : I.prop = J.prop) : I.Compatible J := by
  show I.restrict _ = J.restrict _
  rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
  refine State.ext rfl (Set.ext fun p => ?_)
  constructor
  · rintro ⟨f, hf, -⟩
    obtain ⟨g, hg⟩ : p.world ∈ J.prop := hw ▸ ⟨f, hf⟩
    exact ⟨g, hg, fun x hx => absurd hx (by simp)⟩
  · rintro ⟨f, hf, -⟩
    obtain ⟨g, hg⟩ : p.world ∈ I.prop := hw.symm ▸ ⟨f, hf⟩
    exact ⟨g, hg, fun x hx => absurd hx (by simp)⟩

/-- **Merge is gluing**: the join of compatible states restricts back onto
the left component — [abramsky-sadrzadeh-2014]'s semantic unification,
with no disjointness hypothesis. The carrier witness is repaired on
`J.base` only, which support tolerates. -/
theorem Compatible.restrict_sup_left (h : I.Compatible J) :
    (I ⊔ J).restrict I.base = I := by
  refine State.ext rfl (Set.ext fun p => ?_)
  obtain ⟨w, g⟩ := p
  constructor
  · rintro ⟨f, hf, hfg⟩
    exact (I.supported.mem_iff hfg).mp (mem_sup.mp hf).1
  · intro hg
    have hD : (⟨w, g⟩ : Possibility W V M) ∈ I.restrict (I.base ∩ J.base) :=
      ⟨g, hg, Set.eqOn_refl _ _⟩
    rw [show I.restrict (I.base ∩ J.base) = J.restrict (I.base ∩ J.base)
      from h] at hD
    obtain ⟨f, hfJ, hfg⟩ := hD
    have hpw : Set.EqOn (J.base.piecewise f g) g ↑I.base := fun x hx => by
      by_cases hxJ : x ∈ J.base
      · rw [Finset.piecewise_eq_of_mem _ _ _ hxJ]
        exact hfg (by rw [Finset.coe_inter]; exact ⟨hx, hxJ⟩)
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hxJ]
    refine ⟨J.base.piecewise f g, mem_sup.mpr ⟨?_, ?_⟩, hpw⟩
    · exact (I.supported.mem_iff hpw).mpr hg
    · exact (J.supported.mem_iff
        (fun x hx => J.base.piecewise_eq_of_mem f g hx)).mpr hfJ

/-- Merge is gluing, right component. -/
theorem Compatible.restrict_sup_right (h : I.Compatible J) :
    (I ⊔ J).restrict J.base = J := by
  rw [sup_comm]
  exact h.symm.restrict_sup_left

/-- Frobenius reciprocity: restriction distributes over merge with a
weakened state, unconditionally — where the gluing law needs
compatibility, the weakened component needs nothing. -/
theorem restrict_sup_weaken (hJ : J.base ⊆ Y) (hY : Y ⊆ I.base) :
    (I ⊔ J.weaken (hJ.trans hY)).restrict Y = I.restrict Y ⊔ J := by
  refine State.ext (Finset.union_eq_left.mpr hJ).symm (Set.ext fun p => ?_)
  obtain ⟨w, g⟩ := p
  constructor
  · rintro ⟨f, hf, hfg⟩
    obtain ⟨hfI, hfJ⟩ := mem_sup.mp hf
    exact mem_sup.mpr ⟨⟨f, hfI, hfg⟩,
      (J.supported.mem_iff (hfg.mono (Finset.coe_subset.mpr hJ))).mp hfJ⟩
  · intro hp
    obtain ⟨⟨f, hfI, hfg⟩, hpJ⟩ := mem_sup.mp hp
    exact ⟨f, mem_sup.mpr ⟨hfI,
      (J.supported.mem_iff (hfg.mono (Finset.coe_subset.mpr hJ))).mpr hpJ⟩, hfg⟩

/-- The merge is the *least* gluing: any state that restricts onto both
components over the union base lies above it. -/
theorem sup_le_of_restrict_eq {S : State W V M} (hb : S.base = I.base ∪ J.base)
    (hI : S.restrict I.base = I) (hJ : S.restrict J.base = J) : I ⊔ J ≤ S :=
  ⟨le_of_eq hb.symm, fun p hp => mem_sup.mpr
    ⟨by rw [← hI]; exact ⟨p.assignment, hp, Set.eqOn_refl _ _⟩,
     by rw [← hJ]; exact ⟨p.assignment, hp, Set.eqOn_refl _ _⟩⟩⟩

end Gluing

/-- The diagonal state: two referents, correlated. -/
private def diag : State Unit Bool Bool where
  base := {false, true}
  carrier := {p | p.assignment false = p.assignment true}
  supported := baseSupported_of_iff fun _ f g hfg => by
    show f false = f true ↔ g false = g true
    rw [hfg (by simp), hfg (by simp)]

/-- The full state: two referents, unconstrained. -/
private def square : State Unit Bool Bool where
  base := {false, true}
  carrier := Set.univ
  supported := baseSupported_of_iff fun _ _ _ _ => Iff.rfl

/-- **The gluing is not unique**: the diagonal and the full square agree on
every singleton restriction yet differ. Restriction forgets cross-referent
correlation, so a state is not determined by its per-referent
projections — the marbles argument, one referent up. -/
theorem exists_ne_of_restrict_eq :
    ∃ I J : State Unit Bool Bool, I.base = J.base ∧ I ≠ J ∧
      ∀ x, I.restrict {x} = J.restrict {x} := by
  refine ⟨diag, square, rfl, fun h => ?_, fun x => ?_⟩
  · have : (⟨(), id⟩ : Possibility Unit Bool Bool) ∈ diag := by
      rw [h]; trivial
    exact Bool.false_ne_true this
  · refine State.ext rfl (Set.ext fun p => ?_)
    constructor
    · rintro ⟨f, -, hfg⟩
      exact ⟨f, trivial, hfg⟩
    · rintro ⟨f, -, -⟩
      refine ⟨fun _ => p.assignment x, rfl, fun y hy => ?_⟩
      obtain rfl : y = x := by simpa using hy
      rfl

/-! ### Random assignment -/

/-- Random assignment: introduce the discourse referent `x` — the base
grows, and any constraint at `x` is dropped ([heim-1982]'s indefinite
widening, [groenendijk-stokhof-1991]'s random reset). For a novel `x` the
carrier is unchanged (`randomAssign_of_notMem`) — supported carriers are
already cylindric off the base, so introduction is pure base growth; for a
live `x` the update is destructive. -/
def randomAssign [DecidableEq V] (I : State W V M) (x : V) : State W V M :=
  (I.restrict (I.base.erase x)).weaken
    (show I.base.erase x ⊆ insert x I.base from
      (Finset.erase_subset ..).trans (Finset.subset_insert ..))

section RandomAssign
variable [DecidableEq V] {x : V}

@[simp] theorem base_randomAssign (I : State W V M) (x : V) :
    (I.randomAssign x).base = insert x I.base := rfl

theorem mem_randomAssign {w : W} {g : V → M} :
    (⟨w, g⟩ : Possibility W V M) ∈ I.randomAssign x ↔
      ∃ f, (⟨w, f⟩ : Possibility W V M) ∈ I ∧ Set.EqOn f g ↑(I.base.erase x) :=
  Iff.rfl

/-- Introducing a novel referent only grows the base. -/
theorem randomAssign_of_notMem (hx : x ∉ I.base) :
    (I.randomAssign x).carrier = I.carrier := by
  show (I.restrict (I.base.erase x)).carrier = I.carrier
  rw [Finset.erase_eq_of_notMem hx, restrict_base]

end RandomAssign

/-! ### States at a base as collapsed propositions -/

/-- The states indexed at `X`. -/
abbrev fiber (W M : Type*) {V : Type*} (X : Finset V) : Type _ :=
  {I : State W V M // I.base = X}

theorem fiber_supported (I : fiber W M X) :
    BaseSupported X I.1.carrier :=
  (congrArg (fun b => BaseSupported b I.1.carrier) I.2).mp I.1.supported

/-- A state indexed at `X` is a proposition over the `X`-collapsed state
space ([muskens-van-benthem-visser-2011]'s picture at granularity `X`):
support is saturation, so carriers and sets of agreement classes are in
bijection. -/
def fiberEquiv (X : Finset V) :
    fiber W M X ≃ Set (Quotient (Possibility.agreeSetoid (W := W) (M := M) (↑X : Set V))) where
  toFun I := {q | q.liftOn (· ∈ I.1) fun _ _ h => propext ((fiber_supported I).mem_congr h)}
  invFun T :=
    ⟨⟨X, Quotient.mk _ ⁻¹' T, baseSupported_iff.mpr fun _ _ h => by
        rw [Set.mem_preimage, Set.mem_preimage, Quotient.sound h]⟩, rfl⟩
  left_inv I := Subtype.ext (State.ext I.2.symm rfl)
  right_inv T := by
    ext q
    induction q using Quotient.ind
    exact Iff.rfl

@[simp] theorem mem_fiberEquiv {I : fiber W M X} :
    Quotient.mk _ p ∈ fiberEquiv X I ↔ p ∈ I.1 := Iff.rfl

@[simp] theorem mem_fiberEquiv_symm
    {T : Set (Quotient (Possibility.agreeSetoid (W := W) (M := M) (↑X : Set V)))} :
    p ∈ ((fiberEquiv X).symm T).1 ↔ Quotient.mk _ p ∈ T := Iff.rfl

/-- The equivalence is the image of the carrier in the collapsed space —
the sibling of `prop_eq_image`, one rung up the ladder. -/
theorem fiberEquiv_eq_image (I : fiber W M X) :
    fiberEquiv X I = Quotient.mk _ '' I.1.carrier := by
  have h := (fiber_supported I).preimage_image_mk
  ext q
  induction q using Quotient.ind
  rw [mem_fiberEquiv, ← State.mem_carrier, ← Set.mem_preimage, h]

/-- Informativeness at a fixed base is reverse inclusion of collapsed
propositions. -/
def fiberOrderIso (X : Finset V) :
    fiber W M X ≃o (Set (Quotient (Possibility.agreeSetoid (W := W) (M := M) (↑X : Set V))))ᵒᵈ where
  toEquiv := (fiberEquiv X).trans OrderDual.toDual
  map_rel_iff' {I I'} := by
    show OrderDual.toDual (fiberEquiv X I) ≤ OrderDual.toDual (fiberEquiv X I') ↔ I ≤ I'
    rw [OrderDual.toDual_le_toDual]
    constructor
    · intro h
      refine ⟨by rw [I.2, I'.2], fun p hp => ?_⟩
      exact mem_fiberEquiv.mp (h (mem_fiberEquiv.mpr hp))
    · rintro ⟨-, hc⟩ q hq
      induction q using Quotient.ind
      exact mem_fiberEquiv.mpr (hc (mem_fiberEquiv.mp hq))

section Classified
variable [Nonempty M]

/-- The fiber at `X`, classified: a indexed state is a proposition over
world–`X`-assignment pairs, reversed by informativeness — [heim-1982]'s
satisfaction sets of domain-`X` sequences, as a theorem rather than a
gloss. -/
noncomputable def fiberOrderIsoProd (X : Finset V) :
    fiber W M X ≃o (Set (W × ((↑X : Set V) → M)))ᵒᵈ :=
  (fiberOrderIso X).trans
    (Possibility.agreeQuotientEquiv (↑X : Set V)).toOrderIsoSet.dual

/-- Membership form of the classification: a pair lies in the classified
state iff the corresponding possibility does. -/
theorem mem_fiberOrderIsoProd {I : fiber W M X} {w : W} {g : V → M} :
    (w, (↑X : Set V).restrict g) ∈
        OrderDual.ofDual (fiberOrderIsoProd X I) ↔
      (⟨w, g⟩ : Possibility W V M) ∈ I.1 := by
  show (w, (↑X : Set V).restrict g) ∈
    Possibility.agreeQuotientEquiv (↑X : Set V) '' fiberEquiv X I ↔ _
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨p⟩ := q
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
    exact ((fiber_supported I).mem_congr
      ⟨h1, fun v hv => congrFun h2 ⟨v, hv⟩⟩).mp (mem_fiberEquiv.mp hq)
  · intro hg
    exact ⟨Quotient.mk _ ⟨w, g⟩, mem_fiberEquiv.mpr hg, rfl⟩

/-- At the empty context the fiber degenerates to bare propositions:
[veltman-1996]'s update-semantics states are the referent-free fiber. -/
noncomputable def fiberEmptyOrderIso :
    fiber W M (∅ : Finset V) ≃o (Set W)ᵒᵈ :=
  haveI : IsEmpty ((↑(∅ : Finset V) : Set V) : Type _) :=
    ⟨fun x => by simpa using x.2⟩
  (fiberOrderIsoProd ∅).trans (Equiv.prodUnique W _).toOrderIsoSet.dual

/-- Membership form: at the empty context, membership is a fact about the
world alone. -/
theorem mem_fiberEmptyOrderIso {I : fiber W M (∅ : Finset V)} {w : W}
    {g : V → M} :
    w ∈ OrderDual.ofDual (fiberEmptyOrderIso I) ↔
      (⟨w, g⟩ : Possibility W V M) ∈ I.1 := by
  haveI : IsEmpty ((↑(∅ : Finset V) : Set V) : Type _) :=
    ⟨fun x => by simpa using x.2⟩
  rw [← mem_fiberOrderIsoProd (g := g)]
  show w ∈ Equiv.prodUnique W _ '' OrderDual.ofDual (fiberOrderIsoProd ∅ I) ↔ _
  constructor
  · rintro ⟨⟨w', f⟩, hf, rfl⟩
    rwa [Subsingleton.elim ((↑(∅ : Finset V) : Set V).restrict g) f]
  · intro h
    exact ⟨(w, _), h, rfl⟩

end Classified

end State

end DynamicSemantics
