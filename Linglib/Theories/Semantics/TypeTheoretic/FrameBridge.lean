import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Typed Frames as TTR Record Types @cite{chatzikyriakidis-etal-2025}

Chatzikyriakidis et al. (2025) §2–3 argue that typed attribute-value
frames (Petersen 2007, Löbner 2014, Osswald & Kallmeyer 2018) and
TTR record types (Cooper 2023) are "notational variants" for
representing structured propositions.

The central observation: a Lean `structure` *is* a typed frame.
Each field name is an attribute; each field type is the attribute's
value type. No separate "frame" infrastructure is needed — the
equivalence is definitional.

This module makes the equivalence explicit with `Frame2`, a minimal
frame with named attributes and typed values, and proves it embeds
into `SimpleRecordType2` (a TTR record type) with preserved truth.

linglib's existing `Probabilistic/Scenarios/` models a *different*
tradition — probabilistic scenario semantics (Erk & Herbelot 2024).
The typed-frame tradition here is structural, not distributional.

## References

- Chatzikyriakidis et al. (2025). Types and the Structure of Meaning. §2–3.
- Petersen, W. (2007). Representation of Concepts as Frames.
- Löbner, S. (2014). Evidence for Frames from Human Language.
- Osswald, R. & Kallmeyer, L. (2018). Towards a Formalization of
  Role-Semantic Resources Using Frame Logic. Nat. Lang. & Ling. Theory.
- Cooper, R. (2023). From Perception to Communication. OUP.
-/

namespace Semantics.TypeTheoretic

/-! ## Frames as named record types

A frame is a record with named, typed attributes. In Lean, every
`structure` is already a frame: field names are attributes, field
types are value types. We define `Frame2` to make the frame/record
correspondence explicit for proofs. -/

/-- A two-attribute frame: the common case for linguistic examples.
Frame attributes carry names (unlike raw `SimpleRecordType2`),
making the frame/record correspondence concrete. -/
structure Frame2 (A₁ A₂ : Type) where
  /-- Name of the first attribute -/
  attr₁Name : String
  /-- Value of the first attribute -/
  val₁ : A₁
  /-- Name of the second attribute -/
  attr₂Name : String
  /-- Value of the second attribute -/
  val₂ : A₂

/-! ## Frame ↔ Record Type equivalence

A `Frame2 A₁ A₂` is isomorphic to `SimpleRecordType2 A₁ A₂`
(modulo the attribute names, which are metadata). The attribute
names are the TTR labels; the value types are the field types.
This is the formal content of "frames and record types are
notational variants." -/

/-- Every frame can be viewed as a simple record type. -/
def Frame2.toRecord {A₁ A₂ : Type} (f : Frame2 A₁ A₂) :
    SimpleRecordType2 A₁ A₂ :=
  ⟨f.val₁, f.val₂⟩

/-- Every simple record type can be viewed as a frame. -/
def Frame2.fromRecord {A₁ A₂ : Type}
    (name₁ name₂ : String) (r : SimpleRecordType2 A₁ A₂) :
    Frame2 A₁ A₂ :=
  ⟨name₁, r.fst, name₂, r.snd⟩

/-- The roundtrip preserves values. -/
theorem frame2_record_roundtrip_values {A₁ A₂ : Type} (f : Frame2 A₁ A₂) :
    let r := f.toRecord
    let f' := Frame2.fromRecord f.attr₁Name f.attr₂Name r
    f'.val₁ = f.val₁ ∧ f'.val₂ = f.val₂ :=
  ⟨rfl, rfl⟩

/-! ## Frame-based propositions

A frame is "true" when it has a witness — an instance with values
for all attributes. This is exactly TTR's `IsTrue T = Nonempty T`. -/

/-- A frame *type* (unfilled frame): specifies attribute types
without providing values. True iff fillable. -/
structure FrameType2 (A₁ A₂ : Type) where
  attr₁Name : String
  attr₂Name : String

/-- A frame type is "true" (fillable) iff the corresponding
record type is inhabited. -/
def FrameType2.isTrue {A₁ A₂ : Type} (_ft : FrameType2 A₁ A₂) : Prop :=
  IsTrue (SimpleRecordType2 A₁ A₂)

/-- Frame truth = TTR record type truth. -/
theorem frame_truth_eq_record_truth (A₁ A₂ : Type)
    (ft : FrameType2 A₁ A₂) :
    ft.isTrue ↔ IsTrue (SimpleRecordType2 A₁ A₂) :=
  Iff.rfl

/-- Frame truth = conjunction of attribute inhabitation. -/
theorem frame_truth_iff_attrs {A₁ A₂ : Type}
    (ft : FrameType2 A₁ A₂) :
    ft.isTrue ↔ Nonempty A₁ ∧ Nonempty A₂ :=
  ⟨λ ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩,
   λ ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩⟩

/-! ## Frames as structured propositions

The key argument from Chatzikyriakidis et al. (2025) §2: frames
(= record types) provide *structured* propositions with finer
identity than sets of worlds. Two frames with the same truth
conditions but different attributes are distinct. -/

/-- Two frame types with different attributes but the same value
types: structurally distinct despite identical truth conditions.
This parallels `ext_equiv_not_implies_int_eq` for ITypes. -/
theorem frame_structure_matters :
    let ft₁ : FrameType2 Bool Bool := ⟨"agent", "theme"⟩
    let ft₂ : FrameType2 Bool Bool := ⟨"cause", "effect"⟩
    -- Same truth conditions (both require Bool × Bool to be inhabited)
    (ft₁.isTrue ↔ ft₂.isTrue) ∧
    -- But different structure (different attribute names)
    ft₁.attr₁Name ≠ ft₂.attr₁Name :=
  ⟨Iff.rfl, by simp⟩

end Semantics.TypeTheoretic
