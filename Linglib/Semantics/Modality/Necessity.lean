module

public import Linglib.Semantics.Modality.ConvBackground
public import Linglib.Logic.Modal.Basic

/-!
# Necessity and possibility over conversational backgrounds

Kratzer's modal operators are the box and diamond of `Logic.Modal` over the accessibility
relations two conversational backgrounds induce. Simple necessity quantifies over the worlds a
modal base makes accessible, and necessity over the best of them under an ordering source.
Kratzer's own definition, human necessity, needs no Limit Assumption: each accessible world must
see, at least as good, a witness below which only `p`-worlds occur. It is universal
quantification over the best worlds exactly under the Limit Assumption, which every finite frame
satisfies.

## Main definitions

* `simpleNecessity f`, `simplePossibility f`: the box and diamond of `f.accessible`.
* `necessity f g`, `possibility f g`: the box and diamond of `bestAccessible f g`.
* `humanNecessity f g`, `humanPossibility f g`, `LimitAssumption f g w`.

## Main statements

* `humanNecessity_iff_necessity`: under the Limit Assumption, human necessity is necessity.
* `isRealistic_iff_simpleNecessity_le_id`: a modal base is realistic exactly when simple
  necessity over it is veridical.
* `simpleNecessity_iff_sInf_le`: simple necessity is consequence from the premises at the world.

## Implementation notes

`necessity` quantifies over `bestWorlds` directly, so studies that treat `necessity` and
`possibility` as the Kratzer pair inherit the Limit Assumption; `humanNecessity` is the
limit-free form. Kratzer's comparative possibility, good possibility, weak necessity and slight
possibility are not formalized here.

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
def ConvBackground.accessible (f : ConvBackground W) : SetRel W W :=
  .ofSuccessors f.accessibleWorlds

/-- Under a modal base and an ordering source, `w'` is best-accessible from `w` when it is among
the best worlds accessible from `w`. -/
def bestAccessible (f g : ConvBackground W) : SetRel W W :=
  .ofSuccessors (bestWorlds f g)

@[simp] theorem ConvBackground.mem_accessible {f : ConvBackground W} {w w' : W} :
    w ~[f.accessible] w' ↔ w' ∈ f.accessibleWorlds w := .rfl

@[simp] theorem mem_bestAccessible {f g : ConvBackground W} {w w' : W} :
    w ~[bestAccessible f g] w' ↔ w' ∈ bestWorlds f g w := .rfl

/-- With the empty ordering source, best-world accessibility is base accessibility. -/
@[simp] theorem bestAccessible_bot (f : ConvBackground W) : bestAccessible f ⊥ = f.accessible :=
  congrArg ofSuccessors (funext (bestWorlds_bot f))

/-! ### Operators -/

/-- Simple necessity holds when `p` holds at every accessible world,
`⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')`, Definition 5 of [kratzer-1977]. -/
def simpleNecessity (f : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  □[f.accessible] p w

/-- Simple possibility holds when `p` holds at some accessible world,
`⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')`, Definition 6 of [kratzer-1977]. -/
def simplePossibility (f : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  ◇[f.accessible] p w

/-- Necessity with an ordering source holds when `p` holds at every best world,
`⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')`, the Limit Assumption form of
`humanNecessity`. -/
def necessity (f g : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  □[bestAccessible f g] p w

/-- Possibility with an ordering source holds when `p` holds at some best world,
`⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')`. -/
def possibility (f g : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  ◇[bestAccessible f g] p w

/-- Necessity is monotone in the prejacent: Kratzer's *must* is closed under entailment,
`box_mono` over the best accessible worlds. -/
theorem necessity_mono {f g : ConvBackground W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : necessity f g p w) : necessity f g q w :=
  box_mono (bestAccessible f g) hpq w h

/-- Possibility is monotone in the prejacent. -/
theorem possibility_mono {f g : ConvBackground W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : possibility f g p w) : possibility f g q w :=
  diamond_mono (bestAccessible f g) hpq w h

/-- Necessity of a conjunction is the conjunction of necessities, `box_inf` over the best
accessible worlds. -/
theorem necessity_and {f g : ConvBackground W} {p q : W → Prop} {w : W} :
    necessity f g (fun v ↦ p v ∧ q v) w ↔ necessity f g p w ∧ necessity f g q w :=
  iff_of_eq (congrFun (box_inf (bestAccessible f g)) w)

/-- Kratzer's *must* eliminates conjunction. -/
theorem necessity_and_left {f g : ConvBackground W} {p q : W → Prop} {w : W}
    (h : necessity f g (fun v ↦ p v ∧ q v) w) : necessity f g p w :=
  (necessity_and.mp h).1

/-! ### Human necessity

[kratzer-1981]'s official definition needs no Limit Assumption, asking each accessible world to
see, at least as good, a witness below which only `p`-worlds occur. `necessity`, universal
quantification over `bestWorlds`, is its Limit Assumption collapse. -/

/-- Human necessity holds when every accessible world has an accessible world at least as good,
below which `p` holds throughout ([kratzer-1981], restated as necessity in [kratzer-2012]). It is
neutral with respect to the Limit Assumption, after Lewis's counterfactual semantics. -/
def humanNecessity (f g : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ f.accessibleWorlds w,
    atLeastAsGoodAs (g w) v u ∧ ∀ z ∈ f.accessibleWorlds w, atLeastAsGoodAs (g w) z v → p z

/-- Human necessity implies best-worlds necessity, unconditionally. -/
theorem necessity_of_humanNecessity {f g : ConvBackground W} {p : W → Prop}
    {w : W} (h : humanNecessity f g p w) : necessity f g p w := by
  rintro w' ⟨hacc, hmin⟩
  obtain ⟨v, hvacc, hvle, hall⟩ := h w' hacc
  exact hall w' hacc (hmin hvacc hvle)

/-- The Limit Assumption holds at `w` when every accessible world sees a best world at least as
good. -/
def LimitAssumption (f g : ConvBackground W) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ bestWorlds f g w, atLeastAsGoodAs (g w) v u

/-- The Limit Assumption holds on a finite frame, where every accessible world lies above a best
one. -/
theorem LimitAssumption.of_finite [Finite W] (f g : ConvBackground W) (w : W) :
    LimitAssumption f g w := fun _ hu ↦
  Preorder.exists_le_mem_minimals (letI := premisePreorder (g w); wellFounded_lt) hu

/-- Under the Limit Assumption, best-worlds necessity implies human necessity. -/
theorem humanNecessity_of_necessity {f g : ConvBackground W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) (h : necessity f g p w) :
    humanNecessity f g p w := by
  intro u hu
  obtain ⟨v, hvbest, hvle⟩ := hlim u hu
  refine ⟨v, hvbest.1, hvle, fun z hz hzv ↦ h z ⟨hz, fun z' hz' hz'z ↦ ?_⟩⟩
  exact atLeastAsGoodAs_trans hzv (hvbest.2 hz' (atLeastAsGoodAs_trans hz'z hzv))

/-- Under the Limit Assumption, [kratzer-1981]'s human necessity is exactly universal
quantification over the best worlds. -/
theorem humanNecessity_iff_necessity {f g : ConvBackground W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) :
    humanNecessity f g p w ↔ necessity f g p w :=
  ⟨necessity_of_humanNecessity, humanNecessity_of_necessity hlim⟩

/-- Human possibility is the dual of `humanNecessity`, holding when the negation is not a human
necessity ([kratzer-2012]). -/
def humanPossibility (f g : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  ¬ humanNecessity f g (fun v ↦ ¬ p v) w

/-- Under the Limit Assumption, human possibility is existential quantification over the best
worlds. -/
theorem humanPossibility_iff_possibility {f g : ConvBackground W}
    {p : W → Prop} {w : W} (hlim : LimitAssumption f g w) :
    humanPossibility f g p w ↔ possibility f g p w := by
  rw [humanPossibility, humanNecessity_iff_necessity hlim, necessity, possibility, not_box]
  simp [Diamond]

/-- With the empty ordering source, human necessity is simple necessity, [kratzer-1981]'s
equivalence for arbitrary `f` and empty `g`. -/
theorem humanNecessity_bot_iff (f : ConvBackground W) (p : W → Prop) (w : W) :
    humanNecessity f ⊥ p w ↔ simpleNecessity f p w := by
  constructor
  · intro h u hu
    obtain ⟨v, _, _, hall⟩ := h u hu
    exact hall u hu (atLeastAsGoodAs_empty u v)
  · intro h u hu
    exact ⟨u, hu, atLeastAsGoodAs_empty u u, fun z hz _ ↦ h z hz⟩

/-! ### Characterization lemmas -/

@[simp]
theorem simpleNecessity_iff (f : ConvBackground W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem simplePossibility_iff (f : ConvBackground W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem necessity_iff (f g : ConvBackground W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

@[simp]
theorem possibility_iff (f g : ConvBackground W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Simple necessity is consequence from the premises at the world, `⋂f(w) ⊆ p`, Definition 5 of
[kratzer-1977]. -/
theorem simpleNecessity_iff_sInf_le (f : ConvBackground W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ sInf (f w) ≤ p := Iff.rfl

/-- Simple possibility is compatibility with the premises at the world, `⋂f(w) ∩ p ≠ ∅`,
Definition 6 of [kratzer-1977]. -/
theorem simplePossibility_iff_not_disjoint (f : ConvBackground W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ¬ Disjoint (sInf (f w)) p := by
  simp [simplePossibility_iff, Pi.disjoint_iff, Prop.disjoint_iff, not_forall]

/-- Necessity with the empty ordering source is simple necessity. -/
@[simp] theorem necessity_bot_iff (f : ConvBackground W) (p : W → Prop) (w : W) :
    necessity f ⊥ p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff, simpleNecessity_iff, bestWorlds_bot]

/-! ### Monotonicity in the modal base -/

/-- Premise growth preserves simple necessity, since more evidence leaves fewer accessible
worlds and so at least as many necessities. This is [kratzer-2012]'s point about epistemic
change over time, the approaching-man dialogue, where one conversational background represents
evidence that grows as time goes by, and what *must* hold on the earlier evidence still must on
the later. -/
theorem simpleNecessity_mono {f f' : ConvBackground W} {p : W → Prop} {w : W} (h : f w ⊆ f' w)
    (hNec : simpleNecessity f p w) : simpleNecessity f' p w :=
  fun w' hw' ↦ hNec w' (ConvBackground.accessibleWorlds_anti h hw')

/-- Adding `p` to an ordering source that holds a proposition incompatible with `p` makes nothing
necessary that a best world verifying the latter fails. -/
theorem not_necessity_insert {f g : ConvBackground W} {p q r : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u)
    (hur : ¬ r u) : ¬ necessity f (fun v ↦ insert p (g v)) r w :=
  fun h ↦ hur (h u (mem_bestWorlds_insert hq hpq hu huq))

/-! ### Frame conditions on `ConvBackground.accessible` -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem ConvBackground.IsRealistic.refl {f : ConvBackground W} (h : f.IsRealistic) :
    f.accessible.IsRefl :=
  ⟨fun w ↦ h w⟩

/-- A realistic base gives serial accessibility. -/
theorem ConvBackground.IsRealistic.isSerial {f : ConvBackground W} (h : f.IsRealistic) :
    IsSerial f.accessible :=
  ⟨fun w ↦ ⟨w, h.refl.refl w⟩⟩

/-- A modal base is realistic exactly when its accessibility relation is reflexive. -/
theorem isRealistic_iff_refl {f : ConvBackground W} : f.IsRealistic ↔ f.accessible.IsRefl :=
  ⟨ConvBackground.IsRealistic.refl, fun h w ↦ h.refl w⟩

/-- A modal base is realistic exactly when simple necessity over it is veridical, what must be
the case being the case, so **T** defines realism. -/
theorem isRealistic_iff_simpleNecessity_le_id {f : ConvBackground W} :
    f.IsRealistic ↔ simpleNecessity f ≤ id :=
  isRealistic_iff_refl.trans box_T_iff.symm

/-- A modal base is realistic exactly when what is actual is possible over it: read
epistemically, an asserted fact can be a *might*; read deontically, everything actual is
permitted. -/
theorem isRealistic_iff_id_le_simplePossibility {f : ConvBackground W} :
    f.IsRealistic ↔ id ≤ simplePossibility f :=
  isRealistic_iff_refl.trans diamond_T_iff.symm

/-- Under the empty modal base, every world is accessible. -/
theorem accessible_bot (w w' : W) : w ~[(⊥ : ConvBackground W).accessible] w' := by simp

/-! ### Modal axioms -/

/-- Modal duality, `□p ↔ ¬◇¬p`, is the box-diamond duality (`ModalLogic.not_diamond`), since
`necessity` is `□[bestAccessible f g]`. -/
theorem duality (f g : ConvBackground W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' ↦ ¬ p w') w := by
  rw [necessity, possibility, not_diamond]
  simp [Box]

/-- Necessity distributes over implication, the K axiom `□(p → q) → □p → □q`. -/
theorem necessity_K (f g : ConvBackground W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' ↦ p w' → q w') w) (hP : necessity f g p w) :
    necessity f g q w :=
  box_K hImpl hP

/-- Over a totally realistic base, necessity is veridical whatever the ordering source, the T
axiom for full necessity. -/
theorem ConvBackground.IsTotallyRealistic.necessity_le_id {f : ConvBackground W}
    (hTotal : f.IsTotallyRealistic) (g : ConvBackground W) : necessity f g ≤ id := by
  intro p w hNec
  have hacc : f.accessibleWorlds w = {w} := hTotal w
  refine hNec w ⟨by rw [hacc]; exact Set.mem_singleton w, fun v hv _ ↦ ?_⟩
  rw [hacc, Set.mem_singleton_iff] at hv
  subst hv
  exact atLeastAsGoodAs_refl _ _

end Modality
