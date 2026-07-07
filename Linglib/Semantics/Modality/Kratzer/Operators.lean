/-
[kratzer-1981] Modal Operators — IL Foundation

Kratzer-style necessity and possibility, defined as `box`/`diamond` from
`Intensional` over conversational-background-derived accessibility
relations. Frame conditions on the accessibility relation are derived from
conversational-background properties; modal-axiom derivations then follow from
the polymorphic correspondence theorems in `RestrictedModality`.

## Main declarations

* `kratzerR`, `kratzerBestR`: accessibility relations from a modal base alone
  and from a modal base together with an ordering source.
* `simpleNecessity`, `simplePossibility`: `□`/`◇` over `kratzerR`.
* `necessity`, `possibility`: `□`/`◇` over `kratzerBestR`.
* `duality`: `□p ↔ ¬◇¬p`, delegating to `box_neg_diamond`.
* `K_axiom`, `totally_realistic_gives_T`: instances of generic axioms applied
  to Kratzer-specific accessibility.
* `restrictedBase`: conditional-as-restrictor on the modal base.

## Implementation notes

`necessity` follows the Limit-Assumption-collapsed form: it quantifies over
`bestWorlds f g w` directly, not over the Lewis-style "good-enough below every
accessible world" structure (Kratzer 2012, p. 40). Downstream studies treating
`necessity`/`possibility` as the Kratzer pair inherit the LA. A Limit-Assumption-
free variant is left for future work.

`atLeastAsGoodPossibility` and the rest of the comparative-possibility scale
from Kratzer 2012 §2.4 (good possibility, weak necessity, slight possibility)
are not yet formalized.

Sources:
- Kratzer, A. (1981). The Notional Category of Modality. In H. J. Eikmeyer &
  H. Rieser (eds.), *Words, Worlds, and Contexts*, 38–74. Berlin: de Gruyter.
- Kratzer, A. (2012). *Modals and Conditionals*. OUP.
-/

import Linglib.Semantics.Modality.Kratzer.Ordering
import Linglib.Core.Logic.Modal.Basic
import Linglib.Semantics.Dynamic.UpdateSemantics.Necessity

namespace Semantics.Modality.Kratzer

open Core.Logic.Modal

variable {W : Type*}

/-! ### Accessibility relations -/

/-- Accessibility relation derived from a modal base.

    `kratzerR f w w'` iff `w'` satisfies all propositions in `f(w)`,
    i.e., `w' ∈ ⋂f(w)` in Kratzer's notation. -/
def kratzerR (f : ModalBase W) : AccessRel W :=
  fun w w' => ∀ p ∈ f w, p w'

/-- Accessibility restricted to best worlds (modal base + ordering source).

    `kratzerBestR f g w w'` iff `w'` is among the best accessible worlds
    from `w` — accessible via `f` and maximal under the `g(w)`-ordering. -/
def kratzerBestR (f : ModalBase W) (g : OrderingSource W) : AccessRel W :=
  fun w w' => w' ∈ bestWorlds f g w

/-- With the empty ordering source, best-world accessibility reduces to base
    accessibility. -/
theorem kratzerBestR_empty (f : ModalBase W) (w w' : W) :
    kratzerBestR f (emptyBackground (W := W)) w w' ↔ kratzerR f w w' := by
  rw [kratzerBestR, kratzerR, empty_ordering_emptyBackground]
  rfl

/-! ### Operators -/

/-- **Simple f-necessity**: `p` holds at every accessible world.
    `⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')`. -/
def simpleNecessity (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  box (kratzerR f) p w

/-- **Simple f-possibility**: `p` holds at some accessible world.
    `⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')`. -/
def simplePossibility (f : ModalBase W) (p : W → Prop) (w : W) : Prop :=
  diamond (kratzerR f) p w

/-- **Necessity with ordering**: `p` holds at every best world.
    `⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')`.

    Adopts the Limit-Assumption-collapsed form. -/
def necessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  box (kratzerBestR f g) p w

/-- **Possibility with ordering**: `p` holds at some best world.
    `⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')`. -/
def possibility (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) : Prop :=
  diamond (kratzerBestR f g) p w

/-! ### The Portner identification

[portner-2018]'s gloss on his (3): reading the mood state's components
as a modal base and ordering source, `□_cs` expresses simple necessity
and `□_≤` human necessity ([kratzer-1981]). Stated over `stateAt`. -/

open Semantics.Dynamic.Default in
/-- Simple necessity is informational necessity over the induced state
(the ordering source is irrelevant). -/
theorem simpleNecessity_iff_boxCs (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ (stateAt f g w).boxCs p :=
  Iff.rfl

open Semantics.Dynamic.Default in
/-- Preferential necessity over the induced state implies Kratzer
necessity: `bestWorlds` is contained in the state's optimal set. -/
theorem necessity_of_boxLe (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : (stateAt f g w).boxLe p) : necessity f g p w :=
  fun w' hw' => h w' (bestWorlds_subset_optimal f g w hw')

open Semantics.Dynamic.Default in
/-- On connected ordering sources, Kratzer necessity is preferential
necessity over the induced state — human necessity as `□_≤`. -/
theorem necessity_iff_boxLe_of_connected (f : ModalBase W)
    (g : OrderingSource W) (p : W → Prop) (w : W)
    (hconn : Core.Order.Normality.connected (kratzerNormality (g w))) :
    necessity f g p w ↔ (stateAt f g w).boxLe p := by
  rw [show necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' from Iff.rfl,
    bestWorlds_eq_optimal_of_connected f g w hconn]
  exact Iff.rfl

open Semantics.Dynamic.Default ExpState in
/-- Veltman acceptance at a Kratzer state: the induced state supports
asserting `p` iff `p` is a simple necessity. -/
theorem le_assert_iff_simpleNecessity (f : ModalBase W)
    (g : OrderingSource W) (p : W → Prop) (w : W) :
    stateAt f g w ≤ (stateAt f g w).assert p ↔ simpleNecessity f p w :=
  ((stateAt f g w).le_assert_iff p).trans
    (simpleNecessity_iff_boxCs f g p w).symm

/-! ### Characterization lemmas -/

@[simp]
theorem simpleNecessity_iff_all (f : ModalBase W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

@[simp]
theorem simplePossibility_iff_any (f : ModalBase W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ accessibleWorlds f w, p w' := Iff.rfl

@[simp]
theorem necessity_iff_all (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

@[simp]
theorem possibility_iff_any (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Necessity with an empty ordering source collapses to simple necessity. -/
theorem necessity_empty_iff_simple (f : ModalBase W) (p : W → Prop) (w : W) :
    necessity f (emptyBackground (W := W)) p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff_all, simpleNecessity_iff_all]
  rw [empty_ordering_emptyBackground]

/-! ### Frame conditions on `kratzerR` -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem realistic_refl (f : ModalBase W) (hReal : isRealistic f) :
    Std.Refl (kratzerR f) :=
  ⟨fun w p hp => hReal w p hp⟩

/-- Realistic base: the evaluation world is itself accessible. -/
theorem realistic_gives_reflexive_access (f : ModalBase W)
    (hReal : isRealistic f) (w : W) :
    w ∈ accessibleWorlds f w :=
  (realistic_refl f hReal).refl w

/-- Realistic ⟹ serial. -/
theorem realistic_is_serial (f : ModalBase W) (hReal : isRealistic f) :
    IsSerial (kratzerR f) :=
  ⟨fun w => ⟨w, (realistic_refl f hReal).refl w⟩⟩

/-- Empty modal base gives universal accessibility. -/
theorem empty_base_universal_access (w : W) :
    accessibleWorlds (emptyBackground (W := W)) w = Set.univ := by
  ext w'
  simp only [accessibleWorlds, emptyBackground, propIntersection,
             List.not_mem_nil, false_implies, forall_const, Set.mem_setOf_eq,
             Set.mem_univ]

/-! ### Modal axioms (from `RestrictedModality`) -/

/-- **Modal duality**: `□p ↔ ¬◇¬p`. Since `necessity = box (kratzerBestR f g)`,
    this is the box–diamond duality of the modal square of opposition
    (`Core.Logic.Modal.modalSquare_relations`). -/
theorem duality (f : ModalBase W) (g : OrderingSource W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' => ¬ p w') w := by
  rw [necessity, possibility, box_neg_diamond]

/-- **K (Distribution)**: `□(p → q) → □p → □q`. -/
theorem K_axiom (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' => p w' → q w') w)
    (hP : necessity f g p w) :
    necessity f g q w :=
  box_K (kratzerBestR f g) p q w hImpl hP

/-- Totally realistic base: simple T holds for full necessity. -/
theorem totally_realistic_gives_T (f : ModalBase W) (g : OrderingSource W)
    (hTotal : isTotallyRealistic f)
    (p : W → Prop) (w : W)
    (hNec : necessity f g p w) : p w := by
  have hSelf : kratzerBestR f g w w := by
    refine ⟨?_, fun w'' hw'' => ?_⟩
    · show w ∈ propIntersection (f w)
      rw [hTotal w]; rfl
    · have : w'' ∈ propIntersection (f w) := hw''
      rw [hTotal w] at this
      cases this
      exact ordering_reflexive (g w) w
  exact hNec w hSelf

/-! ### Conditionals as modal-base restriction -/

/-- "If α, must β" is `must_{f + α} β`: prepend the antecedent to the modal base. -/
def restrictedBase (f : ModalBase W) (antecedent : W → Prop) : ModalBase W :=
  fun w => antecedent :: f w

end Semantics.Modality.Kratzer
