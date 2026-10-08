module

public import Linglib.Semantics.Modality.Kratzer.Ordering
public import Linglib.Logic.Modal.Basic

/-!
# Kratzer's modal operators

This file defines necessity and possibility over a modal base and an ordering source,
[kratzer-1981]'s operators, as the box and diamond of `Logic.Modal` over the accessibility
relations the two backgrounds induce, each the relation of a set-valued function
(`SetRel.ofSuccessors`). Simple necessity quantifies over the accessible worlds
(`ModalBase.accessible`, `simpleNecessity`), and necessity over the best accessible worlds
(`bestAccessible`, `necessity`). The paper's own definition needs no Limit Assumption. Human
necessity asks each accessible world to see, at least as good, a witness below which only
`p`-worlds occur (`humanNecessity`), and it is universal quantification over the best worlds
exactly under the Limit Assumption (`humanNecessity_iff_necessity`), which every finite frame
satisfies (`LimitAssumption.of_finite`). The modal axioms follow from the frame conditions the
backgrounds impose (`duality`, `necessity_K`, `ConvBackground.IsTotallyRealistic.necessity_le_id`),
a realistic base being exactly one over which simple necessity is veridical
(`isRealistic_iff_simpleNecessity_le_id`), and a conditional antecedent restricts the modal base
(`ModalBase.restrict`, `accessibleWorlds_restrict`).

## Implementation notes

`necessity` quantifies over `bestWorlds` directly, so studies that treat `necessity` and
`possibility` as the Kratzer pair inherit the Limit Assumption; `humanNecessity` is the
limit-free form. The comparative-possibility scale of [kratzer-2012], good possibility, weak
necessity, and slight possibility, is not formalized.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality

open ModalLogic SetRel

variable {W : Type*}

/-! ### Accessibility relations -/

/-- Under a modal base, `w'` is accessible from `w` when it satisfies every premise of `f w`,
Kratzer's `w' ∈ ⋂f(w)`. -/
def ModalBase.accessible (f : ModalBase W) : SetRel W W := .ofSuccessors f.accessibleWorlds

/-- Under a modal base and an ordering source, `w'` is best-accessible from `w` when it is among
the best worlds accessible from `w`. -/
def bestAccessible (f : ModalBase W) (g : OrderingSource W) : SetRel W W :=
  .ofSuccessors (bestWorlds f g)

@[simp] theorem ModalBase.mem_accessible {f : ModalBase W} {w w' : W} :
    w ~[f.accessible] w' ↔ w' ∈ f.accessibleWorlds w := .rfl

@[simp] theorem mem_bestAccessible {f : ModalBase W} {g : OrderingSource W} {w w' : W} :
    w ~[bestAccessible f g] w' ↔ w' ∈ bestWorlds f g w := .rfl

/-- With the empty ordering source, best-world accessibility is base accessibility. -/
theorem bestAccessible_emptyBackground (f : ModalBase W) :
    bestAccessible f (emptyBackground (W := W)) = f.accessible :=
  congrArg ofSuccessors (funext (bestWorlds_emptyBackground f))

/-! ### Operators -/

/-- Simple necessity holds when `p` holds at every accessible world,
`⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')`, Definition 5 of [kratzer-1977]. -/
def simpleNecessity (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  □[f.accessible] p w

/-- Simple possibility holds when `p` holds at some accessible world,
`⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')`, Definition 6 of [kratzer-1977]. -/
def simplePossibility (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  ◇[f.accessible] p w

/-- Necessity with an ordering source holds when `p` holds at every best world,
`⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')`, the Limit Assumption form of
`humanNecessity`. -/
def necessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  □[bestAccessible f g] p w

/-- Possibility with an ordering source holds when `p` holds at some best world,
`⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')`. -/
def possibility (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  ◇[bestAccessible f g] p w

/-- Necessity is monotone in the prejacent: Kratzer's *must* is closed under entailment,
`box_mono` over the best accessible worlds. -/
theorem necessity_mono {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : necessity f g p w) : necessity f g q w :=
  box_mono (bestAccessible f g) hpq w h

/-- Possibility is monotone in the prejacent. -/
theorem possibility_mono {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : possibility f g p w) : possibility f g q w :=
  diamond_mono (bestAccessible f g) hpq w h

/-- Necessity of a conjunction is the conjunction of necessities, `box_inf` over the best
accessible worlds. -/
theorem necessity_and {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w : W} :
    necessity f g (fun v ↦ p v ∧ q v) w ↔ necessity f g p w ∧ necessity f g q w :=
  iff_of_eq (congrFun (box_inf (bestAccessible f g)) w)

/-- Kratzer's *must* eliminates conjunction. -/
theorem necessity_and_left {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w : W}
    (h : necessity f g (fun v ↦ p v ∧ q v) w) : necessity f g p w :=
  (necessity_and.mp h).1

/-! ### Human necessity

[kratzer-1981]'s official definition needs no Limit Assumption, asking each accessible world to
see, at least as good, a witness below which only `p`-worlds occur. `necessity`, universal
quantification over `bestWorlds`, is its Limit Assumption collapse. -/

/-- Human necessity holds when every accessible world has an accessible world at least as good,
below which `p` holds throughout ([kratzer-1981], restated as necessity in [kratzer-2012]). It is
neutral with respect to the Limit Assumption, after Lewis's counterfactual semantics. -/
def humanNecessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ f.accessibleWorlds w,
    atLeastAsGoodAs (g w) v u ∧ ∀ z ∈ f.accessibleWorlds w, atLeastAsGoodAs (g w) z v → p z

/-- Human necessity implies best-worlds necessity, unconditionally. -/
theorem necessity_of_humanNecessity {f : ModalBase W} {g : OrderingSource W} {p : W → Prop}
    {w : W} (h : humanNecessity f g p w) : necessity f g p w := by
  rintro w' ⟨hacc, hmin⟩
  obtain ⟨v, hvacc, hvle, hall⟩ := h w' hacc
  exact hall w' hacc (hmin hvacc hvle)

/-- The Limit Assumption at `w`: every accessible world sees a best world at least as good. -/
def LimitAssumption (f : ModalBase W) (g : OrderingSource W) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ bestWorlds f g w, atLeastAsGoodAs (g w) v u

/-- The Limit Assumption holds on a finite frame, where every accessible world lies above a best
one. -/
theorem LimitAssumption.of_finite [Finite W] (f : ModalBase W) (g : OrderingSource W) (w : W) :
    LimitAssumption f g w := fun _ hu ↦
  Preorder.exists_le_mem_minimals (letI := premisePreorder (g w); wellFounded_lt) hu

/-- Under the Limit Assumption, best-worlds necessity implies human necessity. -/
theorem humanNecessity_of_necessity {f : ModalBase W} {g : OrderingSource W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) (h : necessity f g p w) :
    humanNecessity f g p w := by
  intro u hu
  obtain ⟨v, hvbest, hvle⟩ := hlim u hu
  refine ⟨v, hvbest.1, hvle, fun z hz hzv ↦ h z ⟨hz, fun z' hz' hz'z ↦ ?_⟩⟩
  exact atLeastAsGoodAs_trans hzv (hvbest.2 hz' (atLeastAsGoodAs_trans hz'z hzv))

/-- Under the Limit Assumption, [kratzer-1981]'s human necessity is exactly universal
quantification over the best worlds. -/
theorem humanNecessity_iff_necessity {f : ModalBase W} {g : OrderingSource W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) :
    humanNecessity f g p w ↔ necessity f g p w :=
  ⟨necessity_of_humanNecessity, humanNecessity_of_necessity hlim⟩

/-- Human possibility, the dual of `humanNecessity`: a possibility is what is not the necessity
of its negation ([kratzer-2012]). -/
def humanPossibility (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  ¬ humanNecessity f g (fun v ↦ ¬ p v) w

/-- Under the Limit Assumption, human possibility is existential quantification over the best
worlds. -/
theorem humanPossibility_iff_possibility {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W} (hlim : LimitAssumption f g w) :
    humanPossibility f g p w ↔ possibility f g p w := by
  rw [humanPossibility, humanNecessity_iff_necessity hlim, necessity, possibility, not_box]
  simp [Diamond]

/-- With the empty ordering source, human necessity is simple necessity, [kratzer-1981]'s
equivalence for arbitrary `f` and empty `g`. -/
theorem humanNecessity_emptyBackground_iff (f : ModalBase W) (p : W → Prop) (w : W) :
    humanNecessity f emptyBackground p w ↔ simpleNecessity f p w := by
  constructor
  · intro h u hu
    obtain ⟨v, _, _, hall⟩ := h u hu
    exact hall u hu (atLeastAsGoodAs_nil u v)
  · intro h u hu
    exact ⟨u, hu, atLeastAsGoodAs_nil u u, fun z hz _ ↦ h z hz⟩

/-! ### Characterization lemmas -/

@[simp]
theorem simpleNecessity_iff (f : ModalBase W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem simplePossibility_iff (f : ModalBase W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem necessity_iff (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

@[simp]
theorem possibility_iff (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Simple necessity is consequence from the premise set at the world, Definition 5 of
[kratzer-1977]. -/
theorem simpleNecessity_iff_followsFrom (f : ModalBase W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ FollowsFrom p (f w) := Iff.rfl

/-- Simple possibility is compatibility with the premise set at the world, Definition 6 of
[kratzer-1977]. -/
theorem simplePossibility_iff_isCompatibleWith (f : ModalBase W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ IsCompatibleWith p (f w) :=
  (simplePossibility_iff f p w).trans isCompatibleWith_iff_exists.symm

/-- Necessity with an empty ordering source is simple necessity. -/
theorem necessity_empty_iff_simple (f : ModalBase W) (p : W → Prop) (w : W) :
    necessity f (emptyBackground (W := W)) p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff, simpleNecessity_iff]
  rw [bestWorlds_emptyBackground]

/-! ### Monotonicity in the modal base -/

/-- Premise growth preserves simple necessity, since more evidence leaves fewer accessible
worlds and so at least as many necessities. This is [kratzer-2012]'s point about epistemic
change over time, the approaching-man dialogue, where one conversational background represents
evidence that grows as time goes by, and what *must* hold on the earlier evidence still must on
the later. -/
theorem simpleNecessity_mono {f f' : ModalBase W} {p : W → Prop} {w : W} (h : f w ⊆ f' w)
    (hNec : simpleNecessity f p w) : simpleNecessity f' p w :=
  fun w' hw' ↦ hNec w' (accessibleWorlds_anti h hw')

/-- Adding `p` to an ordering source that holds a proposition incompatible with `p` makes nothing
necessary that a best world verifying the latter fails. -/
theorem not_necessity_cons {f : ModalBase W} {g : OrderingSource W} {p q r : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u)
    (hur : ¬ r u) : ¬ necessity f (fun v ↦ p :: g v) r w :=
  fun h ↦ hur (h u (mem_bestWorlds_cons hq hpq hu huq))

/-! ### Frame conditions on `ModalBase.accessible` -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem ConvBackground.IsRealistic.refl {f : ModalBase W} (h : f.IsRealistic) :
    f.accessible.IsRefl :=
  ⟨fun w ↦ h w⟩

/-- Over a realistic base the evaluation world is itself accessible. -/
theorem ConvBackground.IsRealistic.mem_accessibleWorlds {f : ModalBase W} (h : f.IsRealistic)
    (w : W) : w ∈ f.accessibleWorlds w :=
  h.refl.refl w

/-- A realistic base gives serial accessibility. -/
theorem ConvBackground.IsRealistic.isSerial {f : ModalBase W} (h : f.IsRealistic) :
    IsSerial f.accessible :=
  ⟨fun w ↦ ⟨w, h.refl.refl w⟩⟩

/-- A modal base is realistic exactly when its accessibility relation is reflexive. -/
theorem isRealistic_iff_refl {f : ModalBase W} : f.IsRealistic ↔ f.accessible.IsRefl :=
  ⟨ConvBackground.IsRealistic.refl, fun h w ↦ h.refl w⟩

/-- A modal base is realistic exactly when simple necessity over it is veridical, what must be
the case being the case, so **T** defines realism. -/
theorem isRealistic_iff_simpleNecessity_le_id {f : ModalBase W} :
    f.IsRealistic ↔ simpleNecessity f ≤ id :=
  isRealistic_iff_refl.trans box_T_iff.symm

/-- Under the empty modal base, every world is accessible. -/
theorem accessible_emptyBackground (w w' : W) :
    w ~[ModalBase.accessible (emptyBackground (W := W))] w' :=
  fun _ hq ↦ (List.not_mem_nil hq).elim

/-- Under a singleton modal base, accessibility is the sole premise. -/
theorem accessible_singleton (p : W → Prop) (w w' : W) :
    w ~[ModalBase.accessible (fun _ ↦ [p])] w' ↔ p w' := by
  rw [ModalBase.mem_accessible, ModalBase.accessibleWorlds, propIntersection_singleton]
  rfl

/-- Under the empty modal base, the accessible worlds are all the worlds. -/
theorem accessibleWorlds_emptyBackground (w : W) :
    ModalBase.accessibleWorlds (emptyBackground (W := W)) w = Set.univ :=
  propIntersection_nil

/-! ### Modal axioms -/

/-- Modal duality, `□p ↔ ¬◇¬p`, is the box-diamond duality (`ModalLogic.not_diamond`), since
`necessity` is `□[bestAccessible f g]`. -/
theorem duality (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' ↦ ¬ p w') w := by
  rw [necessity, possibility, not_diamond]
  simp [Box]

/-- Necessity distributes over implication, the K axiom `□(p → q) → □p → □q`. -/
theorem necessity_K (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' ↦ p w' → q w') w) (hP : necessity f g p w) :
    necessity f g q w :=
  box_K hImpl hP

/-- Over a totally realistic base, necessity is veridical whatever the ordering source, the T
axiom for full necessity. -/
theorem ConvBackground.IsTotallyRealistic.necessity_le_id {f : ModalBase W}
    (hTotal : f.IsTotallyRealistic) (g : OrderingSource W) : necessity f g ≤ id := by
  intro p w hNec
  have hacc : f.accessibleWorlds w = {w} := hTotal w
  refine hNec w ⟨by rw [hacc]; exact Set.mem_singleton w, fun v hv _ ↦ ?_⟩
  rw [hacc, Set.mem_singleton_iff] at hv
  subst hv
  exact atLeastAsGoodAs_refl _ _

/-! ### Conditionals as modal-base restriction -/

/-- The modal base restricted by an antecedent, which prepends the antecedent to the base, so that
*if α, must β* is `must_{f + α} β`. -/
def ModalBase.restrict (f : ModalBase W) (antecedent : W → Prop) : ModalBase W :=
  fun w ↦ antecedent :: f w

/-- The accessible worlds of the restricted base are the antecedent-worlds among the accessible
worlds. -/
theorem accessibleWorlds_restrict (f : ModalBase W) (α : W → Prop) (w : W) :
    (f.restrict α).accessibleWorlds w = {v ∈ f.accessibleWorlds w | α v} :=
  Set.ext fun _ ↦ List.forall_mem_cons.trans and_comm

theorem mem_accessibleWorlds_restrict {f : ModalBase W} {α : W → Prop} {w v : W} :
    v ∈ (f.restrict α).accessibleWorlds w ↔ v ∈ f.accessibleWorlds w ∧ α v :=
  List.forall_mem_cons.trans and_comm

/-- Restricting by a stronger antecedent leaves fewer accessible worlds. -/
theorem accessibleWorlds_restrict_mono (f : ModalBase W) {α₁ α₂ : W → Prop} (w : W)
    (h : ∀ v, α₂ v → α₁ v) :
    (f.restrict α₂).accessibleWorlds w ⊆ (f.restrict α₁).accessibleWorlds w :=
  fun _ hv ↦ mem_accessibleWorlds_restrict.2
    ⟨(mem_accessibleWorlds_restrict.1 hv).1, h _ (mem_accessibleWorlds_restrict.1 hv).2⟩

end Modality
