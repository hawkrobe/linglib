module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Piecewise

/-!
# The DRT box

In discourse representation theory, a box contains two pieces of information:
a universe of discourse referents, and a set of conditions recording what has
been established about them. Boxes can be nested, and different theories
instantiate conditions in different ways
([venhuizen-bos-hendriks-brouwer-2018]; [liu-2021]). This file develops basic
results about boxes, including renaming, extension, and recursions.

## Implementation notes

An embedding of discourse referents into a model is a total function `V → M`; the
textbook's are partial, so a sub-box *extends* its input on its universe, rendered here as
agreement off the universe (`Box.Extends`).
-/

@[expose] public section

namespace DRT

universe w x

variable {V : Type w} {C : Type x} {W D E M : Type*}

/-- A DRT *box*, generic over the condition type `C`; `DRS` instantiates `C`
at `Condition L V`. -/
@[ext] structure Box (V : Type w) (C : Type x) where
  /-- The universe `U`: the discourse referents the box introduces. -/
  referents : Finset V
  /-- The box's conditions. -/
  conditions : List C

namespace Box

/-- A condition of a box is smaller than the box — the recursion measure for
definitions descending through the nested condition list. -/
theorem sizeOf_lt_of_mem_conditions [SizeOf C] {K : Box V C} {c : C}
    (h : c ∈ K.conditions) : sizeOf c < sizeOf K := by
  obtain ⟨U, conds⟩ := K
  have : sizeOf c < sizeOf conds := List.sizeOf_lt_of_mem h
  simp only [Box.mk.sizeOf_spec]
  omega

-- Registers the `Box`-through-`List` nesting step with the default termination
-- tactic: recursions descending into a box's conditions need no `decreasing_by`.
macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| have := DRT.Box.sizeOf_lt_of_mem_conditions (by assumption); omega)

/-! ### Functorial action -/

variable [DecidableEq W] {f : V → W} {g : C → D} {K : Box V C}

/-- `K.map f g` applies `f` to the universe and `g` to each condition. -/
def map (f : V → W) (g : C → D) (K : Box V C) : Box W D :=
  ⟨K.referents.image f, K.conditions.map g⟩

/-- Well-founded recursions may traverse sub-boxes with `Box.map`: preprocessing
re-marks the condition list, exposing `· ∈ K.conditions` to termination proofs. -/
@[wf_preprocess] theorem map_wfParam :
    map f g (wfParam K) = ⟨K.referents.image f, (wfParam K.conditions).map g⟩ := by
  simp [wfParam, map]

@[simp] theorem referents_map : (K.map f g).referents = K.referents.image f := rfl

@[simp] theorem conditions_map : (K.map f g).conditions = K.conditions.map g := rfl

@[simp] theorem map_id [DecidableEq V] : K.map id id = K := by
  simp [map]

@[congr] theorem map_congr {f' : V → W} {g' : C → D} {K' : Box V C} (hf : f = f')
    (hg : ∀ c ∈ K.conditions, g c = g' c) (hK : K = K') : K.map f g = K'.map f' g' := by
  subst hK; subst hf
  simp [map, List.map_congr_left hg]

theorem map_map {X : Type*} [DecidableEq X] {f' : W → X} {g' : D → E} :
    (K.map f g).map f' g' = K.map (f' ∘ f) (g' ∘ g) := by
  simp [map, Finset.image_image, List.map_map]

theorem map_eq_self [DecidableEq V] {g : C → C} {K : Box V C}
    (h : ∀ c ∈ K.conditions, g c = c) : K.map id g = K :=
  (map_congr (g' := id) rfl h rfl).trans map_id

theorem map_map_of_forall {X : Type*} [DecidableEq X] (f : V → W) (f' : W → X) {g' : D → E}
    {g'' : C → E} (h : ∀ c ∈ K.conditions, g' (g c) = g'' c) :
    (K.map f g).map f' g' = K.map (f' ∘ f) g'' :=
  map_map.trans (map_congr rfl h rfl)

/-! ### The extension relation -/

/-- `K.Extends f g` (written `f [K] g`) if the output embedding `g` differs
from the input `f` at most on `K`'s universe — the total-assignment rendering
of "`f ⊆ g` and `Dom g = Dom f ∪ U_K`". -/
def Extends (K : Box V C) (f g : V → M) : Prop := ∀ x ∉ K.referents, g x = f x

section Extends

variable {K : Box V C} {f f₁ f₂ g : V → M}

theorem Extends.refl (K : Box V C) (f : V → M) : K.Extends f f := fun _ _ => rfl

variable [DecidableEq V]

/-- `f` extends to the embedding taking `g`'s values on the universe. -/
theorem extends_piecewise (K : Box V C) (f g : V → M) :
    K.Extends f (K.referents.piecewise g f) :=
  fun _ hx => Finset.piecewise_eq_of_notMem _ _ _ hx

theorem eqOn_piecewise_of_extends (h₁ : K.Extends f₁ g) {S : Set V}
    (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) : Set.EqOn g (K.referents.piecewise g f₂) S :=
  fun x _ => by grind [Extends, Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-- Some `K`-extension of the input satisfies `P` whenever one of another input does, if the
inputs agree off the universe wherever `P` looks. -/
theorem exists_extends_imp (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∃ g, K.Extends f₁ g ∧ P g) → ∃ g, K.Extends f₂ g ∧ P g := fun ⟨g, hg, hPg⟩ =>
  ⟨_, extends_piecewise K f₂ g, hP _ _ (eqOn_piecewise_of_extends hg h) hPg⟩

theorem exists_extends_congr (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∃ g, K.Extends f₁ g ∧ P g) ↔ ∃ g, K.Extends f₂ g ∧ P g :=
  ⟨exists_extends_imp K hP h, exists_extends_imp K hP h.symm⟩

/-- Every `K`-extension of the input satisfies `P` whenever every one of another input does, if
the inputs agree off the universe wherever `P` looks. -/
theorem forall_extends_imp (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∀ g, K.Extends f₁ g → P g) → ∀ g, K.Extends f₂ g → P g := fun H g hg =>
  hP _ g (eqOn_piecewise_of_extends hg h.symm).symm (H _ (extends_piecewise K f₁ g))

theorem forall_extends_congr (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∀ g, K.Extends f₁ g → P g) ↔ ∀ g, K.Extends f₂ g → P g :=
  ⟨forall_extends_imp K hP h, forall_extends_imp K hP h.symm⟩

end Extends

end Box

end DRT
