import Linglib.Semantics.Dynamic.Possibility
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.DependsOn
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

/-!
# Possibilities and based information states
[kamp-vangenabith-reyle-2011] (Defs. 22–26), [heim-1982]

A *possibility* is a world paired with an assignment of discourse referents —
the point type of dynamic semantics. An *information state* relative to a
*base* `X` — a finite set of discourse referents — is a set of possibilities
whose membership depends on assignments only through their values at `X`
(mathlib's `DependsOn`, per world). The base is the "context as storage"
dimension of dynamic meaning: finer than a proposition (it records which
referents are live for anaphora — [kamp-vangenabith-reyle-2011]'s Partee
marbles argument), coarser than syntax, and framework-neutral.

Total-assignment rendering: the chapter's partial embeddings with domain `X`
become total assignments with `X`-supported membership (`BaseSupported`).
Under it the chapter's definitions collapse to order theory:

* Def. 25's informativeness order is componentwise — the base grows and the
  carrier shrinks (`le_def`; the chapter's projection form is
  `le_iff_projection`).
* Def. 26's consistent merge is carrier intersection at the union base, and
  it is the *join* of the informativeness order (`SemilatticeSup`;
  `mem_sup_iff_projection` recovers the chapter's choice-function form).
* Def. 23(iv)'s minimal information state Λ (empty base, no information)
  is `⊥`.

`InfoStateOf P` (`ContextChange.lean`) is the unbased, level-0 notion — a
bare set of possibilities; `State` adds the base. The transitions acting on
these states live in `Transition.lean`.

Support is *saturation*: a carrier is supported on `X` iff it is a union of
`Possibility.agreeSetoid ↑X` classes (`baseSupported_iff`), so a state
based at `X` is exactly a proposition over the `X`-collapsed state space
(`fiberEquiv`) — [muskens-van-benthem-visser-2011]'s propositions-over-a-
state-space picture at granularity `X`. The projection ladder carrier →
agreement classes (`fiberEquiv`) → worlds (`prop`) forgets in two
documented steps; the marbles argument lives in the second.

`State` gets a `Membership` instance rather than `SetLike`: the coe to
carriers is not injective (`Set.univ` is supported at every base — same
carrier, different base), and `Filter` is the precedent.

## Main declarations

* `BaseSupported` — membership depends only on assignment values at `X`
  (`DependsOn`, per world); equivalently, saturation for the agreement
  setoid (`baseSupported_iff`).
* `State` — a base together with a supported carrier of possibilities.
* `State.prop` — the proposition determined by a state (Def. 23(v)).
* `State.restrict` — the best approximation supported on a smaller base
  (presheaf restriction along base inclusion; `le_restrict_iff`).
* `State.fiberEquiv` / `fiberOrderIso` — the states based at `X` are the
  propositions over the `X`-collapsed state space, reversing the order.
-/

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Base-supported sets -/

/-- A set of possibilities is *supported* on `X` when membership depends on
the assignment only through its values at `X`: for each world, the
membership predicate `DependsOn` the coordinates in `X`. -/
def BaseSupported (X : Finset V) (S : Set (Possibility W V M)) : Prop :=
  ∀ w : W, DependsOn (fun f => (⟨w, f⟩ : Possibility W V M) ∈ S) ↑X

/-- Introduction form: supply the membership-invariance iff. -/
theorem baseSupported_of_iff {X : Finset V} {S : Set (Possibility W V M)}
    (h : ∀ ⦃w : W⦄ ⦃f g : V → M⦄, Set.EqOn f g ↑X →
      ((⟨w, f⟩ : Possibility W V M) ∈ S ↔ ⟨w, g⟩ ∈ S)) :
    BaseSupported X S :=
  fun _ _ _ hfg => propext (h hfg)

/-- Elimination form: membership is invariant under agreement on the base. -/
theorem BaseSupported.mem_iff {X : Finset V} {S : Set (Possibility W V M)}
    (h : BaseSupported X S) {w : W} {f g : V → M} (hfg : Set.EqOn f g ↑X) :
    (⟨w, f⟩ : Possibility W V M) ∈ S ↔ ⟨w, g⟩ ∈ S :=
  iff_of_eq (h w hfg)

theorem BaseSupported.mono {X Y : Finset V} {S : Set (Possibility W V M)}
    (h : BaseSupported X S) (hXY : X ⊆ Y) : BaseSupported Y S :=
  fun w => (h w).mono (Finset.coe_subset.mpr hXY)

theorem BaseSupported.inter {X : Finset V} {S T : Set (Possibility W V M)}
    (hS : BaseSupported X S) (hT : BaseSupported X T) : BaseSupported X (S ∩ T) :=
  baseSupported_of_iff fun _ _ _ hfg =>
    and_congr (hS.mem_iff hfg) (hT.mem_iff hfg)

/-- A set is supported on `X` iff membership is invariant under agreement on
`X`: `BaseSupported X` is saturation for `Possibility.agreeSetoid ↑X`. -/
theorem baseSupported_iff {X : Finset V} {S : Set (Possibility W V M)} :
    BaseSupported X S ↔
      ∀ ⦃p q⦄, Possibility.agreeSetoid (↑X : Set V) p q → (p ∈ S ↔ q ∈ S) := by
  constructor
  · rintro h ⟨w, f⟩ ⟨w', g⟩ ⟨rfl, hfg⟩
    exact h.mem_iff hfg
  · intro h
    exact baseSupported_of_iff fun _ _ _ hfg => h ⟨rfl, hfg⟩

/-- Point form of `BaseSupported.mem_iff`: membership is invariant on
agreement classes. -/
theorem BaseSupported.mem_congr {X : Finset V} {S : Set (Possibility W V M)}
    (h : BaseSupported X S) {p q : Possibility W V M}
    (hpq : Possibility.agreeSetoid (↑X : Set V) p q) : p ∈ S ↔ q ∈ S :=
  baseSupported_iff.mp h hpq

/-- The saturation round trip: a supported set is the preimage of its image
in the collapsed state space. -/
theorem BaseSupported.preimage_image_mk {X : Finset V} {S : Set (Possibility W V M)}
    (h : BaseSupported X S) :
    Quotient.mk (Possibility.agreeSetoid ↑X) ⁻¹' (Quotient.mk _ '' S) = S :=
  Set.Subset.antisymm (fun _ ⟨_, hq, hqp⟩ => (h.mem_congr (Quotient.exact hqp)).mp hq)
    (Set.subset_preimage_image _ _)

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

instance : Membership (Possibility W V M) (State W V M) :=
  ⟨fun I p => p ∈ I.carrier⟩

@[simp] theorem mem_carrier {I : State W V M} {p : Possibility W V M} :
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

theorem le_def {I I' : State W V M} :
    I ≤ I' ↔ I.base ⊆ I'.base ∧ I'.carrier ⊆ I.carrier := Iff.rfl

/-- The chapter's projection form of Def. 25 — every possibility of the
stronger state restricts to one of the weaker — coincides with `≤`: support
makes the projected witness the possibility itself. -/
theorem le_iff_projection {I I' : State W V M} :
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

@[simp] theorem mem_bot {p : Possibility W V M} : p ∈ (⊥ : State W V M) := trivial

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

@[simp] theorem mem_sup {I I' : State W V M} {p : Possibility W V M} :
    p ∈ I ⊔ I' ↔ p ∈ I ∧ p ∈ I' := Iff.rfl

/-- The chapter's choice-function form of Def. 26: a possibility belongs to
the merge iff it restricts into each component — support makes the choice
functions the possibility itself. -/
theorem mem_sup_iff_projection {I I' : State W V M} {w : W} {k : V → M} :
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

@[simp] theorem mem_prop {I : State W V M} {w : W} :
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

@[simp] theorem mem_restrict {I : State W V M} {Y : Finset V} {w : W}
    {g : V → M} :
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
theorem restrict_restrict (I : State W V M) {Y Z : Finset V} (hZY : Z ⊆ Y) :
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
theorem restrict_le {I : State W V M} {Y : Finset V} (h : Y ⊆ I.base) :
    I.restrict Y ≤ I :=
  ⟨h, fun p hp => ⟨p.assignment, hp, Set.eqOn_refl p.assignment _⟩⟩

/-- Restriction is the *best* `Y`-supported approximation: for states based
below `Y`, lying below `I.restrict Y` is lying below `I`. -/
theorem le_restrict_iff {I J : State W V M} {Y : Finset V}
    (hJ : J.base ⊆ Y) (hY : Y ⊆ I.base) : J ≤ I.restrict Y ↔ J ≤ I := by
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

/-! ### States at a base as collapsed propositions -/

/-- The states based at `X`. -/
abbrev fiber (W M : Type*) {V : Type*} (X : Finset V) : Type _ :=
  {I : State W V M // I.base = X}

theorem fiber_supported {X : Finset V} (I : fiber W M X) :
    BaseSupported X I.1.carrier :=
  (congrArg (fun b => BaseSupported b I.1.carrier) I.2).mp I.1.supported

/-- A state based at `X` is a proposition over the `X`-collapsed state
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

@[simp] theorem mem_fiberEquiv {X : Finset V} {I : fiber W M X} {p : Possibility W V M} :
    Quotient.mk _ p ∈ fiberEquiv X I ↔ p ∈ I.1 := Iff.rfl

@[simp] theorem mem_fiberEquiv_symm {X : Finset V} {p : Possibility W V M}
    {T : Set (Quotient (Possibility.agreeSetoid (W := W) (M := M) (↑X : Set V)))} :
    p ∈ ((fiberEquiv X).symm T).1 ↔ Quotient.mk _ p ∈ T := Iff.rfl

/-- The equivalence is the image of the carrier in the collapsed space —
the sibling of `prop_eq_image`, one rung up the ladder. -/
theorem fiberEquiv_eq_image {X : Finset V} (I : fiber W M X) :
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

end State

end DynamicSemantics
