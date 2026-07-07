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

/-! ### Human necessity

[kratzer-1981]'s official definition needs no Limit Assumption: it
asks each accessible world to see, at least as good, a witness below
which only `p`-worlds occur. `necessity` (universal quantification
over `bestWorlds`) is its Limit-Assumption collapse. -/

/-- Human necessity ([kratzer-1981]; restated verbatim as "Necessity"
in [kratzer-2012]): every accessible world has an accessible world at
least as good, below which `p` holds throughout. Neutral with respect
to the Limit Assumption, after Lewis's counterfactual semantics. -/
def humanNecessity (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  ∀ u ∈ accessibleWorlds f w, ∃ v ∈ accessibleWorlds f w,
    atLeastAsGoodAs (g w) v u ∧
    ∀ z ∈ accessibleWorlds f w, atLeastAsGoodAs (g w) z v → p z

/-- Human necessity implies best-worlds necessity, unconditionally. -/
theorem necessity_of_humanNecessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W}
    (h : humanNecessity f g p w) : necessity f g p w := by
  rintro w' ⟨hacc, hmin⟩
  obtain ⟨v, hvacc, hvle, hall⟩ := h w' hacc
  exact hall w' hacc (hmin hvacc hvle)

/-- The Limit Assumption at `w`: every accessible world sees a best
world at least as good. -/
def LimitAssumption (f : ModalBase W) (g : OrderingSource W) (w : W) : Prop :=
  ∀ u ∈ accessibleWorlds f w, ∃ v ∈ bestWorlds f g w,
    atLeastAsGoodAs (g w) v u

/-- Under the Limit Assumption, best-worlds necessity implies human
necessity. -/
theorem humanNecessity_of_necessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W}
    (hlim : LimitAssumption f g w) (h : necessity f g p w) :
    humanNecessity f g p w := by
  intro u hu
  obtain ⟨v, hvbest, hvle⟩ := hlim u hu
  refine ⟨v, hvbest.1, hvle, fun z hz hzv => h z ⟨hz, fun z' hz' hz'z => ?_⟩⟩
  exact ordering_transitive (g w) z v z' hzv
    (hvbest.2 hz' (ordering_transitive (g w) z' z v hz'z hzv))

/-- Under the Limit Assumption, [kratzer-1981]'s human necessity is
exactly universal quantification over the best worlds. -/
theorem humanNecessity_iff_necessity {f : ModalBase W} {g : OrderingSource W}
    {p : W → Prop} {w : W} (hlim : LimitAssumption f g w) :
    humanNecessity f g p w ↔ necessity f g p w :=
  ⟨necessity_of_humanNecessity, humanNecessity_of_necessity hlim⟩

/-- Human possibility ([kratzer-2012]: "a possibility ... iff its
negation ... is not a necessity"): the dual of `humanNecessity`. -/
def humanPossibility (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  ¬ humanNecessity f g (fun v => ¬ p v) w

/-- With the empty ordering source, human necessity is simple necessity
([kratzer-1981], her equivalence for arbitrary `f` and empty `g`). -/
theorem humanNecessity_emptyBackground_iff (f : ModalBase W)
    (p : W → Prop) (w : W) :
    humanNecessity f emptyBackground p w ↔ simpleNecessity f p w := by
  constructor
  · intro h u hu
    obtain ⟨v, _, _, hall⟩ := h u hu
    exact hall u hu ((empty_ordering_all_equivalent u v).1)
  · intro h u hu
    exact ⟨u, hu, (empty_ordering_all_equivalent u u).1,
      fun z hz _ => h z hz⟩

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
    refine ⟨?_, fun w'' hw'' _ => ?_⟩
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
