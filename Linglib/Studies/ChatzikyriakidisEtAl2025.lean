module

public import Linglib.Studies.Cooper2023
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Order.Concept

/-!
# Chatzikyriakidis, Cooper, Gregoromichelaki and Sutton (2025): Types and the Structure of Meaning

Ranta models an agent's beliefs as a context, a sequence of hypotheses about variables, and Cooper
recasts the context as a record type whose labels play the role of the variables. An agent believes
a type when its belief type is a subtype of some relabelling of it, so the labels of a complement
make no difference to the truth of a belief report. They make a difference to anaphora. In Geach's
*Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed
Cob's sow*, the two belief contexts overlap in the label of the witch, so that Nob's question is
about Hob's witch although no witch need exist. The datum is
`Data/Examples/ChatzikyriakidisEtAl2025.json`.

## Main statements

* `Kim.believes`: a belief type with the fields of (32) believes (34) under every labelling of
  (34), in every modal system.
* `HobNob.believes_witch`, `HobNob.extension_witch_actual`: Hob believes that there is a witch,
  and there is none.
* `HobNob.same_witch`, `HobNob.other_witch`: Hob's belief and Nob's question, aligned on the
  witch's label, cannot both be true when different witches did the deeds, while Hob's belief and
  a relabelling of Nob's question can.

## Implementation notes

* A record type is the set of its fields `ℓ : P(ℓ₁, …, ℓₙ)`, each a predicate applied to the
  labels it depends on, and its witnesses are the upper polar of its fields under satisfaction.
  Labels are flat, so a path such as `idᵢ.x` is one label.
* A relabelling is a permutation of the labels, extending a one-one relabelling of a record type's
  finitely many labels, so the relabellings of a record type are its orbit.
* The ptypes come from a modal system whose types are predicates and whose objects are pairs of
  arguments and a witness.

## TODO

* Manifest fields (31), and the point of view by which a Roman reports Alexander's belief about
  Zeus with the name *Jupiter*.
* Section 3 of the Element, on polysemy, copredication and counting.

## References

* [chatzikyriakidis-etal-2025]
* [ranta-1994]
* [cooper-2023]
* [geach-1967]
-/

@[expose] public section

namespace ChatzikyriakidisEtAl2025

open Cooper2023 MulAction Pointwise

/-! ### Record types over a modal system -/

section RecType

variable {M Pred L E : Type}

/-- A field `ℓ : P(ℓ₁, …, ℓₙ)` of a record type (30b) has a label, a predicate, and the labels the
predicate is applied to. -/
structure RecField (Pred L : Type) where
  label : L
  pred : Pred
  args : List L

/-- A record type is the set of its fields. -/
abbrev RecType (Pred L : Type) := Set (RecField Pred L)

/-- A permutation of the labels relabels a field. -/
instance : MulAction (Equiv.Perm L) (RecField Pred L) where
  smul σ f := ⟨σ f.label, f.pred, f.args.map σ⟩
  one_smul f := by cases f; simp [HSMul.hSMul]
  mul_smul _ _ _ := by simp only [HSMul.hSMul, Equiv.Perm.coe_mul, Function.comp_apply,
    List.map_map]

namespace RecField

variable (σ : Equiv.Perm L) (f : RecField Pred L)

@[simp] theorem smul_label : (σ • f).label = σ f.label := rfl
@[simp] theorem smul_pred : (σ • f).pred = f.pred := rfl
@[simp] theorem smul_args : (σ • f).args = f.args.map σ := rfl

@[simp] theorem smul_mk (ℓ : L) (P : Pred) (a : List L) :
    σ • (⟨ℓ, P, a⟩ : RecField Pred L) = ⟨σ ℓ, P, a.map σ⟩ :=
  rfl

end RecField

/-- The modal system of record types over a modal system of ptypes. A record type occurs where its
predicates occur, and a record witnesses it when its value at each field's label witnesses the
field's predicate at its values at the field's arguments. -/
def recTypes (ms : ModalSystem M Pred (List E × E)) : ModalSystem M (RecType Pred L) (L → E) :=
  fun p ↦
  { occurs T := ∀ f ∈ T, (ms p).occurs f.pred
    witnesses T r := r ∈ upperPolar (fun f r ↦ (ms p).witnesses f.pred (f.args.map r, r f.label)) T
    occurs_of_witnesses _ _ h _ hf := (ms p).occurs_of_witnesses (h hf) }

variable {ms : ModalSystem M Pred (List E × E)} {T T₁ T₂ B : RecType Pred L} {p : M} {r : L → E}

theorem mem_extension_recTypes : r ∈ (recTypes ms).extension T p ↔
    ∀ f ∈ T, (ms p).witnesses f.pred (f.args.map r, r f.label) :=
  .rfl

/-- Merging record types intersects their witnesses. -/
theorem extension_recTypes_union : (recTypes ms).extension (T₁ ∪ T₂) p =
    (recTypes ms).extension T₁ p ∩ (recTypes ms).extension T₂ p :=
  upperPolar_union ..

theorem mem_extension_recTypes_smul (σ : Equiv.Perm L) :
    r ∈ (recTypes ms).extension (σ • T) p ↔ r ∘ σ ∈ (recTypes ms).extension T p := by
  simp [mem_extension_recTypes, Set.mem_smul_set, List.map_map]

/-- A record type with more fields is a subtype, since its witnesses have the fields of the other.
-/
theorem subtypeR_recTypes_of_subset (h : T₂ ⊆ T₁) : (recTypes ms).SubtypeR T₁ T₂ :=
  fun _ ↦ upperPolar_anti _ h

/-- A belief type that contains the fields of a relabelling of a type believes it. -/
theorem subtypeRelabel_of_smul_subset (σ : Equiv.Perm L) (h : σ • T ⊆ B) :
    (recTypes ms).SubtypeRelabel (orbitRel (Equiv.Perm L) _) B T :=
  ⟨σ • T, ⟨σ⁻¹, inv_smul_smul σ T⟩, (subtypeR_recTypes_of_subset h).subtypeI⟩

/-- Belief is blind to the labels of the believed type. -/
theorem subtypeRelabel_smul (σ : Equiv.Perm L) :
    (recTypes ms).SubtypeRelabel (orbitRel (Equiv.Perm L) _) B (σ • T) ↔
      (recTypes ms).SubtypeRelabel (orbitRel (Equiv.Perm L) _) B T :=
  ModalSystem.subtypeRelabel_congr ⟨σ, rfl⟩

end RecType

/-! ### *Kim believes that some woman is a conductor*, (32)–(35) -/

namespace Kim

inductive Pred | ind | woman | conductor

/-- The labels of (32) and (34). The path `idᵢ.x` of (32) is the label `«idᵢ.x»`. -/
inductive Label | x | c | e | «idᵢ.x» | «idᵢ.e» | «idⱼ.e»
  deriving DecidableEq

/-- The fields of Kim's belief type (32). -/
def belief : RecType Pred Label :=
  {⟨.«idᵢ.x», .ind, []⟩, ⟨.«idᵢ.e», .woman, [.«idᵢ.x»]⟩, ⟨.«idⱼ.e», .conductor, [.«idᵢ.x»]⟩}

/-- The complement (34) of the report. -/
def complement : RecType Pred Label :=
  {⟨.x, .ind, []⟩, ⟨.c, .woman, [.x]⟩, ⟨.e, .conductor, [.x]⟩}

/-- The relabelling (35a). -/
def relabelling : Equiv.Perm Label :=
  Equiv.swap .x .«idᵢ.x» * Equiv.swap .c .«idᵢ.e» * Equiv.swap .e .«idⱼ.e»

/-- Relabelling (34) by (35a) gives the fields of (32), the type (35b). -/
theorem relabelling_smul_complement : relabelling • complement = belief := by
  simp [relabelling, complement, belief, Set.smul_set_insert, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def]

/-- Whatever its labelling, (34) is believed by any belief type with the fields of (32), in every
modal system. -/
theorem believes {M E : Type} (ms : ModalSystem M Pred (List E × E)) {B : RecType Pred Label}
    (hB : belief ⊆ B) (τ : Equiv.Perm Label) :
    (recTypes ms).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) B (τ • complement) :=
  (subtypeRelabel_smul τ).2 <|
    subtypeRelabel_of_smul_subset relabelling (relabelling_smul_complement ▸ hB)

end Kim

/-! ### Intentional identity

Hob believes that a witch blighted Bob's mare, and Nob, who believes only that there is a witch,
wonders whether she killed Cob's sow. In the actual possibility there are no witches; in the other,
one witch blighted the mare and another killed the sow. -/

namespace HobNob

inductive Pred | ind | witch | blightedBobsMare | killedCobsSow

/-- The witch `x`, her being one `c`, the blighting `b` and the killing `k`, and another label
`y`. -/
inductive Label | x | y | c | b | k
  deriving DecidableEq

/-- The context Hob and Nob share, that there is a witch. -/
def witch : RecType Pred Label := {⟨.x, .ind, []⟩, ⟨.c, .witch, [.x]⟩}

/-- Hob's belief that a witch blighted Bob's mare. -/
def hob : RecType Pred Label := insert ⟨.b, .blightedBobsMare, [.x]⟩ witch

/-- The content of Nob's question, that she killed Cob's sow, with *she* the witch of the shared
context. -/
def nob : RecType Pred Label := insert ⟨.k, .killedCobsSow, [.x]⟩ witch

inductive Possib | actual | twoWitches
  deriving DecidableEq

/-- Two women and a situation. -/
inductive Obj | w₁ | w₂ | s
  deriving DecidableEq

/-- Both women are individuals in both possibilities. In `twoWitches` both are witches, `w₁`
blighted Bob's mare and `w₂` killed Cob's sow, in the situation `s`. -/
def system : ModalSystem Possib Pred (List Obj × Obj) := fun p ↦
  { occurs _ := True
    witnesses
      | .ind, (args, a) => args = [] ∧ a ≠ .s
      | .witch, (args, a) => p = .twoWitches ∧ (args = [.w₁] ∨ args = [.w₂]) ∧ a = .s
      | .blightedBobsMare, (args, a) => p = .twoWitches ∧ args = [.w₁] ∧ a = .s
      | .killedCobsSow, (args, a) => p = .twoWitches ∧ args = [.w₂] ∧ a = .s
    occurs_of_witnesses _ _ _ := trivial }

/-- No witch exists. -/
theorem extension_witch_actual : (recTypes system).extension witch .actual = ∅ := by
  ext r
  simp [mem_extension_recTypes, witch, system]

/-- Hob believes that there is a witch. -/
theorem believes_witch :
    (recTypes system).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) hob witch :=
  subtypeRelabel_of_smul_subset 1 (by simp [hob])

/-- Nob, whose belief type is that there is a witch, does not believe that she blighted Bob's
mare. -/
theorem not_believes_blighted :
    ¬ (recTypes system).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) witch hob := by
  rintro ⟨T, ⟨σ, hσ : σ • T = hob⟩, h⟩
  let r : Label → Obj := fun ℓ ↦ if ℓ = .c then .s else .w₂
  have hr : r ∈ (recTypes system).extension T .twoWitches :=
    h .twoWitches (fun _ _ ↦ trivial) (fun _ _ ↦ trivial) <| by
      simp [mem_extension_recTypes, witch, system, r]
  rw [← inv_smul_smul σ T, hσ, mem_extension_recTypes_smul, mem_extension_recTypes] at hr
  have := hr _ (Set.mem_insert _ _)
  simp [system, r] at this
  grind

/-- *She (the same witch)*. Aligned on the witch's label, Hob's belief and the content of Nob's
question are not both true where different witches blighted the mare and killed the sow. -/
theorem same_witch : (recTypes system).extension (hob ∪ nob) .twoWitches = ∅ := by
  ext r
  simp [mem_extension_recTypes, hob, nob, witch, system]
  grind

/-- Moving Nob's witch to another label, which leaves Nob's beliefs as they are, makes Hob's belief
and the content of Nob's question true together. -/
theorem other_witch :
    ((recTypes system).extension (hob ∪ Equiv.swap Label.x .y • nob) .twoWitches).Nonempty := by
  refine ⟨fun | .x => .w₁ | .y => .w₂ | _ => .s, ?_⟩
  rw [extension_recTypes_union, Set.mem_inter_iff, mem_extension_recTypes_smul]
  simp [mem_extension_recTypes, hob, nob, witch, system, Equiv.swap_apply_def]

end HobNob

end ChatzikyriakidisEtAl2025
