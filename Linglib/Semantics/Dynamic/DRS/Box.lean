import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# The DRT box

In discourse representation theory, a box contains two pieces of information:
a universe of discourse referents, and a set of conditions recording what has
been established about them. Boxes can be nested, and different theories
instantiate conditions in different ways
([venhuizen-bos-hendriks-brouwer-2018]; [liu-2021]). This file develops basic
results about boxes, including renaming, extension, and recursions.
-/

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

/-- An *embedding function* is a function that maps discourse referents to
individuals in a model — here total (deviation note in `DRS/Verification.lean`).
Only the model's domain `M` appears; its interpretation of the relation
symbols enters with verification (`f.Verifies K`, `DRS/Verification.lean`). -/
abbrev Embedding (V : Type w) (M : Type*) := V → M

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

@[simp] theorem map_id' [DecidableEq V] : K.map id (fun c => c) = K := map_id

@[congr] theorem map_congr {f' : V → W} {g' : C → D} {K' : Box V C} (hf : f = f')
    (hg : ∀ c ∈ K.conditions, g c = g' c) (hK : K = K') : K.map f g = K'.map f' g' := by
  subst hK; subst hf
  simp [map, List.map_congr_left hg]

theorem map_map {X : Type*} [DecidableEq X] {f' : W → X} {g' : D → E} :
    (K.map f g).map f' g' = K.map (f' ∘ f) (g' ∘ g) := by
  simp [map, Finset.image_image, List.map_map]

theorem map_eq_self [DecidableEq V] {g : C → C} {K : Box V C}
    (h : ∀ c ∈ K.conditions, g c = c) : K.map id g = K :=
  (map_congr rfl h rfl).trans map_id'

theorem map_map_of_forall {X : Type*} [DecidableEq X] (f : V → W) (f' : W → X) {g' : D → E}
    {g'' : C → E} (h : ∀ c ∈ K.conditions, g' (g c) = g'' c) :
    (K.map f g).map f' g' = K.map (f' ∘ f) g'' :=
  map_map.trans (map_congr rfl h rfl)

/-! ### The extension relation -/

/-- `K.Extends f g` (written `f [K] g`) if the output embedding `g` differs
from the input `f` at most on `K`'s universe — the total-assignment rendering
of "`f ⊆ g` and `Dom g = Dom f ∪ U_K`". -/
def Extends (K : Box V C) (f g : Embedding V M) : Prop := ∀ x ∉ K.referents, g x = f x

end Box

end DRT
