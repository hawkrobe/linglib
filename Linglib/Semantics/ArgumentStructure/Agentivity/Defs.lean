import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# The Agentivity Lattice [grimm-2011]: carriers and order structure

[grimm-2011] reformulates [dowty-1991]'s proto-role entailments as
**privative features** organized into a lattice via subset inclusion. The key
innovations over Dowty:

1. **Privative opposition** (Table 2, §2.1): Proto-Patient is not a separate
   cluster but the *underspecified* (∅) pole of each agentivity feature.
   "Patient" = lacking agentive properties.

2. **Instigation replaces causation**: Dowty's "causing an event in another
   participant" is decomposed into "instigation" — independent action whose
   effects can be attributed to the argument. This removes the relational
   aspect (causation implies a second participant; instigation does not).

3. **Persistence replaces P-Patient features** (§2.2, Fig. 2): Dowty's 5
   P-Patient entailments (CoS, IT, CA, stationary, DE) are replaced by 4
   persistence dimensions tracking whether the entity persists existentially
   and qualitatively at the beginning and end of the event.

4. **Lattice structure** (§2.2): the possible feature combinations, ordered
   by inclusion and constrained by logical dependencies (volition →
   sentience), form a lattice. Cases are **connected regions** of this
   lattice (see `Agentivity/CaseRegions.lean`).

## Carriers vs. Grimm's lattices

The carrier types here are implementation **supersets** of Grimm's lattices;
the validity predicates carve out the paper's objects:

- `Agentivity` is the Boolean cube on `Agentivity.Feature` (16 elements),
  with the pointwise `BooleanAlgebra`. Grimm's Fig. 1 lattice is its
  12-element `Agentivity.Valid` subset (volition → sentience).
- `PersistenceLevel` is exactly Grimm's five valid persistence levels
  (Fig. 2) — here the carrier *is* the paper's object.
- `ParticipantType` (Grimm's "participant type": agentivity × persistence)
  is the full product carrier (80 elements). Grimm's Fig. 3 lattice is its
  38-element `ParticipantType.Valid` subset (`AgentivityValid` ∧
  `CrossValid`).

## Mathlib integration

All ordering infrastructure uses Mathlib typeclasses:
- `Agentivity`: `BooleanAlgebra` (pointwise, from `Pi`), `Fintype`
- `PersistenceLevel`: `Lattice`, `BoundedOrder`, `Fintype`
- `ParticipantType`: `Lattice`, `BoundedOrder`, `Fintype`

The bridges to [dowty-1991]'s `EntailmentProfile` live in
`EntailmentProfile.lean`; the case-region geometry lives in
`Agentivity/CaseRegions.lean`.
-/

namespace ArgumentStructure

/-! ### Agentivity (Table 2, §2.1) -/

/-- The four agentivity primitives (Table 2 (agentive properties), p.520).

    Each has an agentive (+) and non-agentive (∅) pole; the non-agentive
    pole is simply the absence of the property — the **privative
    opposition** that replaces Dowty's two independent clusters. -/
inductive Agentivity.Feature where
  /-- +volition: the participant intends to bring about the event. -/
  | volition
  /-- +sentience: conscious involvement in the action or state. -/
  | sentience
  /-- +instigation: prior independent action whose effects can be
      attributed to this argument. Replaces Dowty's "causation" (p.521). -/
  | instigation
  /-- +motion: the argument is in motion during the event. -/
  | motion
  deriving DecidableEq, Repr, Fintype

/-- An argument's agentivity: which of the four primitives it bears, as a
    point of the Boolean cube on `Agentivity.Feature`. Order, lattice, and
    Boolean-algebra structure are pointwise, so `a ≤ b` is feature-set
    inclusion; Grimm's Fig. 1 lattice is the 12-element `Valid` subset of
    the 16-element cube. -/
def Agentivity := Agentivity.Feature → Bool

namespace Agentivity

instance : DecidableEq Agentivity :=
  inferInstanceAs (DecidableEq (Feature → Bool))

instance : Fintype Agentivity := inferInstanceAs (Fintype (Feature → Bool))

instance : BooleanAlgebra Agentivity :=
  inferInstanceAs (BooleanAlgebra (Feature → Bool))

instance : DecidableRel (α := Agentivity) (· ≤ ·) := fun a b =>
  decidable_of_iff (∀ f, a f ≤ b f) Iff.rfl

instance : DecidableRel (α := Agentivity) (· < ·) := fun _ _ =>
  decidable_of_iff' _ lt_iff_le_not_ge

/-- Build an agentivity value from the four indicators, in Table 2 order. -/
def mk (volition sentience instigation motion : Bool) : Agentivity
  | .volition => volition
  | .sentience => sentience
  | .instigation => instigation
  | .motion => motion

instance : Repr Agentivity :=
  ⟨fun a _ => repr (a .volition, a .sentience, a .instigation, a .motion)⟩

@[simp] theorem mk_inj {v s i m v' s' i' m' : Bool} :
    mk v s i m = mk v' s' i' m' ↔ v = v' ∧ s = s' ∧ i = i' ∧ m = m' := by
  constructor
  · intro h
    exact ⟨congrFun h .volition, congrFun h .sentience,
      congrFun h .instigation, congrFun h .motion⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- Volition indicator. -/
def volition (a : Agentivity) : Bool := a .volition

/-- Sentience indicator. -/
def sentience (a : Agentivity) : Bool := a .sentience

/-- Instigation indicator. -/
def instigation (a : Agentivity) : Bool := a .instigation

/-- Motion indicator. -/
def motion (a : Agentivity) : Bool := a .motion

/-- Validity: volition presupposes sentience (p.521, following
    [dowty-1991] p.607). Carves Grimm's 12-element Fig. 1 lattice out of
    the 16-element cube. -/
def Valid (a : Agentivity) : Prop := a.volition = true → a.sentience = true

instance (a : Agentivity) : Decidable a.Valid := by
  unfold Valid; infer_instance

/-- Number of positive features (= height in the cube). -/
def featureCount (a : Agentivity) : Nat :=
  a.volition.toNat + a.sentience.toNat + a.instigation.toNat + a.motion.toNat

/-- The inclusion order, componentwise. -/
theorem le_iff (a b : Agentivity) :
    a ≤ b ↔
      (a.volition = true → b.volition = true) ∧
      (a.sentience = true → b.sentience = true) ∧
      (a.instigation = true → b.instigation = true) ∧
      (a.motion = true → b.motion = true) := by
  revert a b; decide

end Agentivity

/-! ### Persistence levels (§2.2, Fig. 2) -/

/-- The five valid persistence levels (p.524–525, Fig. 2).

    Each level is a valid combination of four persistence dimensions:
    - ExPB: existential persistence (beginning) — entity exists before event
    - ExPE: existential persistence (end) — entity exists after event
    - QuPB: qualitative persistence (beginning) — qualities unchanged before
    - QuPE: qualitative persistence (end) — qualities unchanged after

    Constraints (ExPB→QuPB, QuPE→ExPE, etc.) reduce the 16 possible
    combinations to exactly 5. -/
inductive PersistenceLevel where
  /-- ∅ExPB, ∅ExPE, ∅QuPB, ∅QuPE — entity has no entailed existence.
      Arguments of *seek*, *want*; negated copulas. -/
  | totalNonPersistence
  /-- ∅ExPB, +ExPE, ∅QuPB, +QuPE — entity comes into existence.
      Objects of *build*, *invent*; subjects of *appear*. -/
  | exPersEnd
  /-- +ExPB, ∅ExPE, +QuPB, ∅QuPE — entity exists before, ceases to exist.
      Subjects of *die*, *evaporate*; objects of *destroy*, *ruin*. -/
  | exPersBeginning
  /-- +ExPB, +ExPE, +QuPB, ∅QuPE — entity persists but is qualitatively
      changed. Objects of transitive *move*, *dim*, *frighten*;
      intransitive subjects of *fall*. -/
  | quPersBeginning
  /-- +ExPB, +ExPE, +QuPB, +QuPE — entity persists unchanged throughout.
      Prototypical transitive subjects; unaffected objects of *see*, *cut at*. -/
  | totalPersistence
  deriving DecidableEq, Repr

/-- Existential persistence at beginning (positive feature).
    Also serves as "entity exists at the beginning of the event." -/
def PersistenceLevel.exPersB : PersistenceLevel → Bool
  | .exPersBeginning | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Existential persistence at end (positive feature). -/
def PersistenceLevel.exPersE : PersistenceLevel → Bool
  | .exPersEnd | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Qualitative persistence at beginning (positive feature). -/
def PersistenceLevel.quPersB : PersistenceLevel → Bool
  | .exPersBeginning | .quPersBeginning | .totalPersistence => true
  | _ => false

/-- Qualitative persistence at end (positive feature). -/
def PersistenceLevel.quPersE : PersistenceLevel → Bool
  | .exPersEnd | .totalPersistence => true
  | _ => false

instance : Fintype PersistenceLevel where
  elems := {.totalNonPersistence, .exPersEnd, .exPersBeginning,
            .quPersBeginning, .totalPersistence}
  complete x := by cases x <;> simp

/-- Subset inclusion ordering on persistence features. -/
private def PersistenceLevel.leBool (a b : PersistenceLevel) : Bool :=
  (!a.exPersB || b.exPersB) && (!a.exPersE || b.exPersE) &&
  (!a.quPersB || b.quPersB) && (!a.quPersE || b.quPersE)

instance : PartialOrder PersistenceLevel where
  le a b := a.leBool b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := PersistenceLevel) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.leBool b = true))

instance : OrderBot PersistenceLevel where
  bot := .totalNonPersistence
  bot_le := by decide

instance : OrderTop PersistenceLevel where
  top := .totalPersistence
  le_top := by decide

/-- Join on persistence levels. The 5 valid levels do not form a sublattice
    of the powerset on {ExPB, ExPE, QuPB, QuPE} — the join is the smallest
    valid level containing the union of features. -/
def PersistenceLevel.sup' (a b : PersistenceLevel) : PersistenceLevel :=
  match a, b with
  | .totalNonPersistence, x | x, .totalNonPersistence => x
  | .totalPersistence, _ | _, .totalPersistence => .totalPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning
  | .quPersBeginning, .exPersBeginning => .quPersBeginning
  | .exPersBeginning, .exPersEnd
  | .exPersEnd, .exPersBeginning => .totalPersistence
  | .exPersEnd, .quPersBeginning
  | .quPersBeginning, .exPersEnd => .totalPersistence

/-- Meet on persistence levels. The largest valid level contained in the
    intersection of features. -/
def PersistenceLevel.inf' (a b : PersistenceLevel) : PersistenceLevel :=
  match a, b with
  | .totalPersistence, x | x, .totalPersistence => x
  | .totalNonPersistence, _ | _, .totalNonPersistence => .totalNonPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning
  | .quPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersBeginning, .exPersEnd
  | .exPersEnd, .exPersBeginning => .totalNonPersistence
  | .exPersEnd, .quPersBeginning
  | .quPersBeginning, .exPersEnd => .totalNonPersistence

instance : Lattice PersistenceLevel where
  sup := PersistenceLevel.sup'
  inf := PersistenceLevel.inf'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

/-! ### Combined agentivity-lattice node (§2.2, Fig. 3) -/

/-- A node of the product carrier: agentivity features × persistence level
    (80 elements). Grimm's Fig. 3 agentivity lattice is the 38-node `Valid`
    subset, carved by:

    1. volition → sentience (`AgentivityValid`)
    2. If the argument does not exist at the beginning (totalNonPersistence
       or exPersEnd), it cannot have any agentivity properties
       (`CrossValid`, p.526–527). -/
structure ParticipantType where
  agentivity  : Agentivity
  persistence : PersistenceLevel
  deriving DecidableEq, Repr

/-- The agentivity constraint: volition → sentience. -/
def ParticipantType.AgentivityValid (n : ParticipantType) : Prop :=
  n.agentivity.Valid

instance (n : ParticipantType) : Decidable n.AgentivityValid := by
  unfold ParticipantType.AgentivityValid; infer_instance

/-- The cross-lattice constraint: if the argument does not exist at the
    beginning of the event, it cannot have any agentivity properties. -/
def ParticipantType.CrossValid (n : ParticipantType) : Prop :=
  n.persistence.exPersB = true ∨ n.agentivity = ⊥

instance (n : ParticipantType) : Decidable n.CrossValid := by
  unfold ParticipantType.CrossValid; infer_instance

/-- Full validity: both constraints satisfied. Carves Grimm's 38-node
    Fig. 3 lattice out of the 80-element carrier. -/
def ParticipantType.Valid (n : ParticipantType) : Prop :=
  n.AgentivityValid ∧ n.CrossValid

instance (n : ParticipantType) : Decidable n.Valid := by
  unfold ParticipantType.Valid; infer_instance

def ParticipantType.equiv : ParticipantType ≃ (Agentivity × PersistenceLevel) where
  toFun n := (n.agentivity, n.persistence)
  invFun p := ⟨p.1, p.2⟩
  left_inv n := by cases n; rfl
  right_inv p := by cases p; rfl

instance : Fintype ParticipantType := Fintype.ofEquiv _ ParticipantType.equiv.symm

/-- Product order: componentwise `≤` on agentivity and persistence. -/
instance : LE ParticipantType where
  le a b := a.agentivity ≤ b.agentivity ∧ a.persistence ≤ b.persistence

instance : LT ParticipantType where
  lt a b := a ≤ b ∧ ¬ b ≤ a

instance : PartialOrder ParticipantType where
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h g := ⟨le_trans h.1 g.1, le_trans h.2 g.2⟩
  le_antisymm a b h g := by
    have := le_antisymm h.1 g.1
    have := le_antisymm h.2 g.2
    cases a; cases b; simp_all

instance : DecidableRel (α := ParticipantType) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.agentivity ≤ b.agentivity ∧ a.persistence ≤ b.persistence))

instance : OrderBot ParticipantType where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := ⟨bot_le, bot_le⟩

instance : OrderTop ParticipantType where
  top := ⟨⊤, ⊤⟩
  le_top _ := ⟨le_top, le_top⟩

/-- Componentwise lattice: meet/join on each axis independently. -/
instance : Lattice ParticipantType where
  sup a b := ⟨a.agentivity ⊔ b.agentivity, a.persistence ⊔ b.persistence⟩
  inf a b := ⟨a.agentivity ⊓ b.agentivity, a.persistence ⊓ b.persistence⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ h1 h2 := ⟨sup_le h1.1 h2.1, sup_le h1.2 h2.2⟩
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h1 h2 := ⟨le_inf h1.1 h2.1, le_inf h1.2 h2.2⟩

/-! ### Named participant types -/

/-- Maximal Agent (Fig. 4): all agentivity features at total persistence —
    the top of the participant lattice. The prototypical transitive
    subject. -/
def maximalAgent : ParticipantType := ⊤

/-- Maximal Patient (Fig. 4): no agentivity features,
    existential persistence (beginning). The prototypical affected object
    that ceases to exist (break, destroy). -/
def maximalPatient : ParticipantType :=
  ⟨⊥, .exPersBeginning⟩

/-- The "effector" participant type: instigation + motion, total
    persistence. The canonical agent of effective action verbs (kill, break).
    §3, labeled Ia/IIa in Fig. 5. -/
def effectorAgent : ParticipantType :=
  ⟨.mk false false true true, .totalPersistence⟩

/-- Sentience without instigation, at qualitative persistence (beginning):
    the single position where Grimm's §5.1 dative uses converge —
    recipients, dative experiencers, and second arguments of two-place
    communication/service verbs (Fig. 7). -/
def sentientNonInstigator : ParticipantType :=
  ⟨.mk false true false false, .quPersBeginning⟩

/-! ### Transitivity region (§3, Fig. 4) -/

/-- A node is in the **transitivity region** iff its persistence level
    is in {exPersBeginning, quPersBeginning, totalPersistence}.

    The transitivity region excludes totalNonPersistence and exPersEnd
    because the prototypical transitive event requires both participants
    to exist at the beginning (p.529–530). -/
def ParticipantType.InTransitiveRegion (n : ParticipantType) : Prop :=
  n.persistence.exPersB = true

instance (n : ParticipantType) : Decidable n.InTransitiveRegion := by
  unfold ParticipantType.InTransitiveRegion; infer_instance

/-- Tsunoda's transitivity hierarchy (§3, example 8).

    | Class | Example verbs | Transitivity |
    |-------|--------------|-------------|
    | I     | kill, break  | Highest     |
    | II    | shoot, hit   | Middle      |
    | III   | search, seek | Lowest      |

    Named `TransitivityRank` (rank on Tsunoda's hierarchy) to avoid
    collision with `ArgumentStructure.AuxiliarySelection.TransitivityClass`
    (the Burzio unaccusative/unergative/transitive classification). -/
inductive TransitivityRank where
  /-- Resultative Effective Action: kill, break. Object is destroyed
      (exPersBeginning). Maximal opposition between agent and patient. -/
  | resultativeEffective
  /-- Contact: shoot, hit. Object is affected but persists
      (quPersBeginning). Less opposition than Class I. -/
  | contact
  /-- Pursuit: search, seek. Object may not even exist
      (totalNonPersistence). Outside the transitivity region. -/
  | pursuit
  deriving DecidableEq, Repr

/-- The canonical patient position for each transitivity class
    (Fig. 5). The agent position for all three classes is `effectorAgent`
    (Fig. 5, Ia/IIa share the same agent node; Grimm doesn't separately
    label IIIa). -/
def TransitivityRank.patientType : TransitivityRank → ParticipantType
  | .resultativeEffective => ⟨⊥, .exPersBeginning⟩     -- Ip
  | .contact              => ⟨⊥, .quPersBeginning⟩     -- IIp
  | .pursuit              => ⟨⊥, .totalNonPersistence⟩ -- IIIp

end ArgumentStructure
