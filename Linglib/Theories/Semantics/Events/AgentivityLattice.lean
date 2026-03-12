import Linglib.Theories.Semantics.Events.EntailmentProfile
import Linglib.Theories.Semantics.Events.Affectedness
import Linglib.Theories.Semantics.Events.LevinClassProfiles
import Linglib.Core.Case.Basic
import Linglib.Core.Prominence
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Prod

/-!
# The Agentivity Lattice @cite{grimm-2011}

@cite{grimm-2011} reformulates @cite{dowty-1991}'s proto-role entailments as
**privative features** organized into a lattice via subset inclusion. The key
innovations over Dowty:

1. **Privative opposition**: Proto-Patient is not a separate cluster but the
   *underspecified* (∅) pole of each agentivity feature. "Patient" = lacking
   agentive properties.

2. **Instigation replaces causation**: Dowty's "causing an event in another
   participant" is decomposed into "instigation" — independent action whose
   effects can be attributed to the argument. This removes the relational
   aspect (causation implies a second participant; instigation does not).

3. **Persistence replaces P-Patient features**: Dowty's 5 P-Patient entailments
   (CoS, IT, CA, stationary, DE) are replaced by 4 persistence dimensions
   tracking whether the entity persists existentially and qualitatively at the
   beginning and end of the event.

4. **Lattice structure**: The powerset of features, ordered by inclusion and
   constrained by logical dependencies (volition → sentience), forms a lattice.
   Cases are **connected regions** of this lattice.

## Mathlib integration

All ordering infrastructure uses Mathlib typeclasses:
- `AgentivityNode`: `Lattice`, `BoundedOrder`, `Fintype` (16 elements)
- `PersistenceLevel`: `Lattice`, `BoundedOrder`, `Fintype` (5 elements)
- `GrimmNode`: `PartialOrder`, `BoundedOrder`, `Fintype` (80 elements)

## Bridges

- `AgentivityNode.fromEntailmentProfile` → `EntailmentProfile` (proto-roles)
- `PersistenceLevel.fromEntailmentProfile` → `EntailmentProfile` (proto-roles)
- `GrimmNode.toCaseRegion` → `Core.Case` (case assignment)
- Transitivity hierarchy → `Tsunoda` verb classification
-/

namespace Semantics.Events.AgentivityLattice

open Semantics.Events.ProtoRoles
open Core

-- ════════════════════════════════════════════════════
-- § 1. Agentivity Primitives (@cite{grimm-2011} Table 2, §2.1)
-- ════════════════════════════════════════════════════

/-- The four agentivity primitives (@cite{grimm-2011} Table 2 (agentive properties), p.520).

    Each has an agentive (+) and non-agentive (∅) pole. The non-agentive
    pole is not a separate feature — it is simply the absence of the
    agentive property. This is the **privative opposition** that replaces
    Dowty's two independent clusters. -/
structure AgentivityNode where
  /-- +volition: the participant intends to bring about the event. -/
  volition    : Bool
  /-- +sentience: conscious involvement in the action or state. -/
  sentience   : Bool
  /-- +instigation: prior independent action whose effects can be
      attributed to this argument. Replaces Dowty's "causation"
      (@cite{grimm-2011} p.521). -/
  instigation : Bool
  /-- +motion: the argument is in motion during the event. -/
  motion      : Bool
  deriving DecidableEq, Repr, BEq

/-- Validity constraint: volition presupposes sentience
    (@cite{grimm-2011} p.521, following @cite{dowty-1991} p.607). -/
def AgentivityNode.valid (a : AgentivityNode) : Bool :=
  !a.volition || a.sentience

/-- Number of positive agentivity features (= height in the lattice). -/
def AgentivityNode.featureCount (a : AgentivityNode) : Nat :=
  a.volition.toNat + a.sentience.toNat +
  a.instigation.toNat + a.motion.toNat

/-- Equivalence with `Bool⁴` for `Fintype` derivation. -/
def AgentivityNode.equiv : AgentivityNode ≃ (Bool × Bool × Bool × Bool) where
  toFun a := (a.volition, a.sentience, a.instigation, a.motion)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv a := by cases a; rfl
  right_inv p := by obtain ⟨_, _, _, _⟩ := p; rfl

instance : Fintype AgentivityNode := Fintype.ofEquiv _ AgentivityNode.equiv.symm

/-- Subset inclusion ordering on agentivity features. `a ≤ b` iff every
    feature of `a` is also a feature of `b`. Defined componentwise as
    `Bool` implication; the `PartialOrder` axioms are verified by `decide`
    over the 16-element `Fintype`. -/
private def AgentivityNode.leBool (a b : AgentivityNode) : Bool :=
  (!a.volition || b.volition) && (!a.sentience || b.sentience) &&
  (!a.instigation || b.instigation) && (!a.motion || b.motion)

instance : PartialOrder AgentivityNode where
  le a b := a.leBool b = true
  le_refl a := by simp [AgentivityNode.leBool]
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := AgentivityNode) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.leBool b = true))

/-- Lattice: componentwise `∨` for join, `∧` for meet. -/
instance : Lattice AgentivityNode where
  sup a b := ⟨a.volition || b.volition, a.sentience || b.sentience,
              a.instigation || b.instigation, a.motion || b.motion⟩
  inf a b := ⟨a.volition && b.volition, a.sentience && b.sentience,
              a.instigation && b.instigation, a.motion && b.motion⟩
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : OrderBot AgentivityNode where
  bot := ⟨false, false, false, false⟩
  bot_le := by decide

instance : OrderTop AgentivityNode where
  top := ⟨true, true, true, true⟩
  le_top := by decide

-- ════════════════════════════════════════════════════
-- § 2. Persistence Levels (@cite{grimm-2011} §2.2, Fig. 2)
-- ════════════════════════════════════════════════════

/-- The five valid persistence levels (@cite{grimm-2011} p.524–525, Fig. 2).

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
  deriving DecidableEq, Repr, BEq

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

/-- Number of positive persistence features. -/
def PersistenceLevel.featureCount : PersistenceLevel → Nat
  | .totalNonPersistence => 0
  | .exPersEnd => 2           -- {ExPE, QuPE}
  | .exPersBeginning => 2     -- {ExPB, QuPB}
  | .quPersBeginning => 3     -- {ExPB, ExPE, QuPB}
  | .totalPersistence => 4    -- {ExPB, ExPE, QuPB, QuPE}

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
  bot_le := by native_decide

instance : OrderTop PersistenceLevel where
  top := .totalPersistence
  le_top := by native_decide

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
  le_sup_left := by native_decide
  le_sup_right := by native_decide
  sup_le := by native_decide
  inf_le_left := by native_decide
  inf_le_right := by native_decide
  le_inf := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Combined Agentivity Lattice Node (@cite{grimm-2011} Fig. 3)
-- ════════════════════════════════════════════════════

/-- A node in the full agentivity lattice = agentivity features ×
    persistence level, subject to:

    1. volition → sentience (agentivity constraint)
    2. If the argument does not exist at the beginning (totalNonPersistence
       or exPersEnd), it cannot have any agentivity properties
       (@cite{grimm-2011} p.526–527). -/
structure GrimmNode where
  agentivity  : AgentivityNode
  persistence : PersistenceLevel
  deriving DecidableEq, Repr, BEq

/-- The agentivity constraint: volition → sentience. -/
def GrimmNode.agentivityValid (n : GrimmNode) : Bool :=
  n.agentivity.valid

/-- The cross-lattice constraint: if the argument does not exist at the
    beginning of the event, it cannot have any agentivity properties. -/
def GrimmNode.crossValid (n : GrimmNode) : Bool :=
  n.persistence.exPersB || n.agentivity == ⊥

/-- Full validity: both constraints satisfied. -/
def GrimmNode.valid (n : GrimmNode) : Bool :=
  n.agentivityValid && n.crossValid

/-- Total feature count (agentivity + persistence). -/
def GrimmNode.featureCount (n : GrimmNode) : Nat :=
  n.agentivity.featureCount + n.persistence.featureCount

def GrimmNode.equiv : GrimmNode ≃ (AgentivityNode × PersistenceLevel) where
  toFun n := (n.agentivity, n.persistence)
  invFun p := ⟨p.1, p.2⟩
  left_inv n := by cases n; rfl
  right_inv p := by cases p; rfl

instance : Fintype GrimmNode := Fintype.ofEquiv _ GrimmNode.equiv.symm

/-- Product order: componentwise `≤` on agentivity and persistence. -/
instance : LE GrimmNode where
  le a b := a.agentivity ≤ b.agentivity ∧ a.persistence ≤ b.persistence

instance : LT GrimmNode where
  lt a b := a ≤ b ∧ ¬ b ≤ a

instance : PartialOrder GrimmNode where
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h g := ⟨le_trans h.1 g.1, le_trans h.2 g.2⟩
  le_antisymm a b h g := by
    have := le_antisymm h.1 g.1
    have := le_antisymm h.2 g.2
    cases a; cases b; simp_all

instance : DecidableRel (α := GrimmNode) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.agentivity ≤ b.agentivity ∧ a.persistence ≤ b.persistence))

instance : OrderBot GrimmNode where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := ⟨bot_le, bot_le⟩

instance : OrderTop GrimmNode where
  top := ⟨⊤, ⊤⟩
  le_top _ := ⟨le_top, le_top⟩

-- ════════════════════════════════════════════════════
-- § 4. Named Participant Types
-- ════════════════════════════════════════════════════

/-- Maximal Agent (@cite{grimm-2011} Fig. 4): all agentivity features,
    total persistence. The prototypical transitive subject. -/
def maximalAgent : GrimmNode :=
  ⟨⟨true, true, true, true⟩, .totalPersistence⟩

/-- Maximal Patient (@cite{grimm-2011} Fig. 4): no agentivity features,
    existential persistence (beginning). The prototypical affected object
    that ceases to exist (break, destroy). -/
def maximalPatient : GrimmNode :=
  ⟨⟨false, false, false, false⟩, .exPersBeginning⟩

/-- The "effector" participant type: instigation + motion, total
    persistence. The canonical agent of effective action verbs (kill, break).
    @cite{grimm-2011} §3, labeled Ia/IIa in Fig. 5. -/
def effectorAgent : GrimmNode :=
  ⟨⟨false, false, true, true⟩, .totalPersistence⟩

/-- Experiencer: sentience only, qualitative persistence (beginning).
    The dative experiencer of psych verbs (@cite{grimm-2011} §5.1.1). -/
def experiencerNode : GrimmNode :=
  ⟨⟨false, true, false, false⟩, .quPersBeginning⟩

/-- Recipient: sentience, qualitative persistence (beginning).
    The canonical dative recipient (@cite{grimm-2011} Fig. 7). -/
def recipientNode : GrimmNode :=
  ⟨⟨false, true, false, false⟩, .quPersBeginning⟩

-- ════════════════════════════════════════════════════
-- § 5. Transitivity Region (@cite{grimm-2011} §3, Fig. 4)
-- ════════════════════════════════════════════════════

/-- A node is in the **transitivity region** iff its persistence level
    is in {exPersBeginning, quPersBeginning, totalPersistence}.

    The transitivity region excludes totalNonPersistence and exPersEnd
    because the prototypical transitive event requires both participants
    to exist at the beginning (@cite{grimm-2011} p.529–530). -/
def GrimmNode.inTransitiveRegion (n : GrimmNode) : Bool :=
  n.persistence.exPersB

/-- Tsunoda's transitivity hierarchy (@cite{grimm-2011} §3, example 8).

    | Class | Example verbs | Transitivity |
    |-------|--------------|-------------|
    | I     | kill, break  | Highest     |
    | II    | shoot, hit   | Middle      |
    | III   | search, seek | Lowest      | -/
inductive TransitivityClass where
  /-- Resultative Effective Action: kill, break. Object is destroyed
      (exPersBeginning). Maximal opposition between agent and patient. -/
  | resultativeEffective
  /-- Contact: shoot, hit. Object is affected but persists
      (quPersBeginning). Less opposition than Class I. -/
  | contact
  /-- Pursuit: search, seek. Object may not even exist
      (totalNonPersistence). Outside the transitivity region. -/
  | pursuit
  deriving DecidableEq, Repr, BEq

/-- The canonical agent position for each transitivity class.
    All classes share the same agent type: instigation + motion,
    total persistence (@cite{grimm-2011} Fig. 5, labeled Ia/IIa). -/
def TransitivityClass.agentNode : TransitivityClass → GrimmNode
  | _ => effectorAgent

/-- The canonical patient position for each transitivity class
    (@cite{grimm-2011} Fig. 5). -/
def TransitivityClass.patientNode : TransitivityClass → GrimmNode
  | .resultativeEffective => ⟨⊥, .exPersBeginning⟩     -- Ip
  | .contact              => ⟨⊥, .quPersBeginning⟩     -- IIp
  | .pursuit              => ⟨⊥, .totalNonPersistence⟩ -- IIIp

-- ════════════════════════════════════════════════════
-- § 6. Case Regions (@cite{grimm-2011} §4, Figs. 6–7)
-- ════════════════════════════════════════════════════

/-- Case regions on the agentivity lattice. A case marker corresponds
    to a **connected region** of the lattice (@cite{grimm-2011} §4). -/
inductive CaseRegion where
  /-- Nominative (accusative systems) / Ergative (ergative systems):
      the region spreading from maximal agent. Marks subjects. -/
  | nomErg
  /-- Accusative (accusative systems) / Absolutive (ergative systems):
      the region spreading from maximal patient and existential
      persistence (beginning). Marks objects. -/
  | accAbs
  /-- Dative: the region around sentience + qualitative persistence
      (beginning). Marks recipients, experiencers, benefactives
      (@cite{grimm-2011} §5.1, Fig. 7). -/
  | dative
  /-- Oblique: the middle region between core cases. -/
  | oblique
  deriving DecidableEq, Repr, BEq

/-- Predicts the case region for a node based on its lattice position.

    - nomErg: has instigation + total persistence — the prototypical
      transitive subject region.
    - accAbs: no agentivity + persistence with existsBeginning — the
      prototypical affected object region.
    - dative: sentience (without instigation) + qualitative persistence
      (beginning) — recipients, experiencers, benefactives.
    - oblique: everything else. -/
def GrimmNode.toCaseRegion (n : GrimmNode) : CaseRegion :=
  if n.agentivity.instigation && n.persistence == .totalPersistence then
    .nomErg
  else if n.agentivity == ⊥ &&
          (n.persistence == .exPersBeginning || n.persistence == .quPersBeginning) then
    .accAbs
  else if n.agentivity.sentience && !n.agentivity.instigation &&
          n.persistence == .quPersBeginning then
    .dative
  else
    .oblique

/-- Maps a case region to its canonical morphological case in an
    accusative alignment system. -/
def CaseRegion.toAccusativeCase : CaseRegion → Case
  | .nomErg  => .nom
  | .accAbs  => .acc
  | .dative  => .dat
  | .oblique => .inst  -- oblique marked by instrumental or PP

/-- Maps a case region to its canonical morphological case in an
    ergative alignment system. -/
def CaseRegion.toErgativeCase : CaseRegion → Case
  | .nomErg  => .erg
  | .accAbs  => .abs
  | .dative  => .dat
  | .oblique => .inst

-- ════════════════════════════════════════════════════
-- § 7. Bridge to EntailmentProfile (@cite{dowty-1991})
-- ════════════════════════════════════════════════════

/-- Map Dowty's P-Agent entailments to Grimm's agentivity features.

    The correspondence is direct for 3 of 4 features:
    - volition = volition
    - sentience = sentience
    - causation → instigation (@cite{grimm-2011} p.521)
    - movement = motion

    Independent existence is handled by the persistence dimension. -/
def AgentivityNode.fromEntailmentProfile (p : EntailmentProfile) : AgentivityNode :=
  ⟨p.volition, p.sentience, p.causation, p.movement⟩

/-- Map Dowty's P-Patient entailments to Grimm's persistence level.

    This is an approximate mapping — Grimm's system is genuinely different
    from Dowty's. The diagnostic features:

    - DE + IT → exPersEnd: entity created incrementally (build, invent)
    - DE + ¬IT → exPersBeginning: entity ceases to exist (die, evaporate)
    - IT + ¬DE → exPersBeginning: entity consumed incrementally (eat)
    - CoS + ¬IT + ¬DE → quPersBeginning: changed but persists (kick, move)
    - ¬CoS + ¬DE → totalPersistence or totalNonPersistence

    Dowty's DE ("does not exist independently of the event") maps to
    Grimm's creation/destruction axis. IT (incremental theme) disambiguates:
    DE+IT = creation (exPersEnd), DE+¬IT = destruction (exPersBeginning). -/
def PersistenceLevel.fromPatientProfile (p : EntailmentProfile) : PersistenceLevel :=
  if p.dependentExistence && p.incrementalTheme then
    .exPersEnd                                  -- build, invent (created)
  else if p.dependentExistence then
    .exPersBeginning                            -- die, destroy (ceases to exist)
  else if p.incrementalTheme then
    .exPersBeginning                            -- eat (consumed incrementally)
  else if p.changeOfState then
    .quPersBeginning                            -- kick, move (changed but persists)
  else if p.causallyAffected || p.stationary then
    .totalPersistence                           -- see object, sit (unaffected)
  else
    .totalNonPersistence                        -- seek, want

/-- Map a full EntailmentProfile to a GrimmNode.

    The agentivity features come from the P-Agent entailments;
    the persistence level comes from the P-Patient entailments. -/
def GrimmNode.fromSubjectProfile (p : EntailmentProfile) : GrimmNode :=
  ⟨.fromEntailmentProfile p, .totalPersistence⟩

def GrimmNode.fromObjectProfile (p : EntailmentProfile) : GrimmNode :=
  ⟨.fromEntailmentProfile p, .fromPatientProfile p⟩

-- ════════════════════════════════════════════════════
-- § 8. Lattice Properties (from Mathlib instances)
-- ════════════════════════════════════════════════════

-- Reflexivity, transitivity, antisymmetry are provided by PartialOrder.
-- ⊥ ≤ a, a ≤ ⊤ are provided by OrderBot/OrderTop.
-- Join/meet associativity, commutativity, absorption from Lattice.

/-- Persistence incomparability: exPersEnd and exPersBeginning are
    incomparable — neither is a subset of the other's features. -/
theorem exPersEnd_incomparable_exPersBeginning :
    ¬ (PersistenceLevel.exPersEnd ≤ PersistenceLevel.exPersBeginning) ∧
    ¬ (PersistenceLevel.exPersBeginning ≤ PersistenceLevel.exPersEnd) := by
  decide

/-- Their join is ⊤ (totalPersistence). -/
theorem exPersEnd_sup_exPersBeginning :
    PersistenceLevel.exPersEnd ⊔ PersistenceLevel.exPersBeginning = ⊤ := by
  native_decide

/-- Their meet is ⊥ (totalNonPersistence). -/
theorem exPersEnd_inf_exPersBeginning :
    PersistenceLevel.exPersEnd ⊓ PersistenceLevel.exPersBeginning = ⊥ := by
  native_decide

/-- Maximal agent is ⊤ on the combined lattice. -/
theorem maximalAgent_eq_top : maximalAgent = ⊤ := by native_decide

-- ════════════════════════════════════════════════════
-- § 9. Named Participant Verification
-- ════════════════════════════════════════════════════

-- Validity

theorem maximalAgent_valid : maximalAgent.valid = true := by native_decide
theorem maximalPatient_valid : maximalPatient.valid = true := by native_decide
theorem effectorAgent_valid : effectorAgent.valid = true := by native_decide
theorem experiencerNode_valid : experiencerNode.valid = true := by native_decide

-- Maximal agent is at the top, maximal patient is lower

theorem maximalAgent_featureCount :
    maximalAgent.featureCount = 8 := by native_decide

theorem maximalPatient_featureCount :
    maximalPatient.featureCount = 2 := by native_decide

theorem maximalPatient_le_maximalAgent :
    maximalPatient ≤ maximalAgent := by decide

theorem maximalAgent_not_le_maximalPatient :
    ¬ maximalAgent ≤ maximalPatient := by decide

-- Maximal agent and patient are in the transitivity region

theorem maximalAgent_in_transitiveRegion :
    maximalAgent.inTransitiveRegion = true := by native_decide

theorem maximalPatient_in_transitiveRegion :
    maximalPatient.inTransitiveRegion = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 10. Transitivity Hierarchy Verification (@cite{grimm-2011} §3)
-- ════════════════════════════════════════════════════

/-- Class I patients (break) are in the transitivity region. -/
theorem classI_patient_in_region :
    (TransitivityClass.resultativeEffective.patientNode).inTransitiveRegion
    = true := by native_decide

/-- Class II patients (shoot) are in the transitivity region. -/
theorem classII_patient_in_region :
    (TransitivityClass.contact.patientNode).inTransitiveRegion
    = true := by native_decide

/-- Class III patients (search) are OUTSIDE the transitivity region.
    This captures Tsunoda's observation that pursuit verbs deviate most
    strongly from the prototypical transitive paradigm. -/
theorem classIII_patient_outside_region :
    (TransitivityClass.pursuit.patientNode).inTransitiveRegion
    = false := by native_decide

/-- Class I patient (break: exPersBeginning) has lower persistence than
    Class II patient (shoot: quPersBeginning). The Class I object is
    more affected — it ceases to exist. -/
theorem classI_patient_lower_persistence :
    (TransitivityClass.resultativeEffective.patientNode).persistence.featureCount <
    (TransitivityClass.contact.patientNode).persistence.featureCount := by
  native_decide

/-- Class I patient ≤ Class II patient on the lattice
    (exPersBeginning ≤ quPersBeginning). -/
theorem classI_patient_le_classII :
    TransitivityClass.resultativeEffective.patientNode ≤
    TransitivityClass.contact.patientNode := by decide

/-- Class III patient ≤ Class I patient
    (totalNonPersistence ≤ exPersBeginning). -/
theorem classIII_patient_le_classI :
    TransitivityClass.pursuit.patientNode ≤
    TransitivityClass.resultativeEffective.patientNode := by decide

-- ════════════════════════════════════════════════════
-- § 11. Case Region Verification (@cite{grimm-2011} §4)
-- ════════════════════════════════════════════════════

/-- Maximal agent maps to NOM/ERG region. -/
theorem maximalAgent_nomErg :
    maximalAgent.toCaseRegion = .nomErg := by native_decide

/-- Maximal patient maps to ACC/ABS region. -/
theorem maximalPatient_accAbs :
    maximalPatient.toCaseRegion = .accAbs := by native_decide

/-- The effector agent (instigation + motion, total persistence) maps to
    NOM/ERG. This is the agent of break/kill (@cite{grimm-2011} Fig. 5, Ia). -/
theorem effectorAgent_nomErg :
    effectorAgent.toCaseRegion = .nomErg := by native_decide

/-- The experiencer/recipient maps to the dative region
    (@cite{grimm-2011} §5.1, Fig. 7). -/
theorem experiencer_dative :
    experiencerNode.toCaseRegion = .dative := by native_decide

/-- The recipient maps to the dative region. -/
theorem recipient_dative :
    recipientNode.toCaseRegion = .dative := by native_decide

/-- Class I patient (break object: destroyed) maps to ACC/ABS. -/
theorem classI_patient_accAbs :
    (TransitivityClass.resultativeEffective.patientNode).toCaseRegion
    = .accAbs := by native_decide

/-- Class II patient (shoot object: affected but persists) maps to ACC/ABS. -/
theorem classII_patient_accAbs :
    (TransitivityClass.contact.patientNode).toCaseRegion
    = .accAbs := by native_decide

/-- Accusative alignment: maximal agent → NOM, maximal patient → ACC. -/
theorem accusative_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
    maximalPatient.toCaseRegion.toAccusativeCase = .acc := ⟨rfl, rfl⟩

/-- Ergative alignment: maximal agent → ERG, maximal patient → ABS. -/
theorem ergative_alignment :
    maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
    maximalPatient.toCaseRegion.toErgativeCase = .abs := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Bridge Verification: EntailmentProfile → GrimmNode
-- ════════════════════════════════════════════════════

/-- kick subject → agentivity {V,S,I,M} (full agent). -/
theorem kick_subject_agentivity :
    AgentivityNode.fromEntailmentProfile kickSubjectProfile
    = ⟨true, true, true, true⟩ := rfl

/-- kick object → persistence quPersBeginning (affected but persists).
    CoS=true, IT=false, DE=false → qualitatively changed. -/
theorem kick_object_persistence :
    PersistenceLevel.fromPatientProfile kickObjectProfile
    = .quPersBeginning := by native_decide

/-- build object → persistence exPersEnd (entity created). -/
theorem build_object_persistence :
    PersistenceLevel.fromPatientProfile buildObjectProfile
    = .exPersEnd := by native_decide

/-- die subject → persistence exPersBeginning (entity ceases to exist).
    DE=true, IT=false → entity is destroyed. -/
theorem die_subject_persistence :
    PersistenceLevel.fromPatientProfile dieSubjectProfile
    = .exPersBeginning := by native_decide

/-- run subject → agentivity {V,S,M} (no instigation). -/
theorem run_subject_agentivity :
    AgentivityNode.fromEntailmentProfile runSubjectProfile
    = ⟨true, true, false, true⟩ := rfl

/-- arrive subject → agentivity {M} (motion only). -/
theorem arrive_subject_agentivity :
    AgentivityNode.fromEntailmentProfile arriveSubjectProfile
    = ⟨false, false, false, true⟩ := rfl

/-- see subject → agentivity {S} (sentience only). -/
theorem see_subject_agentivity :
    AgentivityNode.fromEntailmentProfile seeSubjectProfile
    = ⟨false, true, false, false⟩ := rfl

/-- sweep basic subject → agentivity {M} (motion only, variable agentivity). -/
theorem sweep_basic_agentivity :
    AgentivityNode.fromEntailmentProfile sweepBasicSubjectProfile
    = ⟨false, false, false, true⟩ := rfl

/-- sweep broom subject → agentivity {V,S,I,M} (instrument lexicalization
    adds full agentivity, @cite{rappaport-hovav-levin-2024}). -/
theorem sweep_broom_agentivity :
    AgentivityNode.fromEntailmentProfile sweepBroomSubjectProfile
    = ⟨true, true, true, true⟩ := rfl

/-- Instrument lexicalization strictly increases agentivity on the lattice:
    sweep basic {M} < sweep broom {V,S,I,M}. -/
theorem sweep_lexicalization_increases :
    AgentivityNode.fromEntailmentProfile sweepBasicSubjectProfile <
    AgentivityNode.fromEntailmentProfile sweepBroomSubjectProfile := by
  constructor <;> decide

-- ════════════════════════════════════════════════════
-- § 13. Grimm ↔ Dowty ASP Consistency
-- ════════════════════════════════════════════════════

/-- Grimm's agentivity lattice ordering is consistent with Dowty's
    pAgentDominates: if Grimm a ≤ Grimm b on agentivity, then
    Dowty a dominates Dowty b on P-Agent features.

    This holds because the feature-to-feature mapping is a bijection
    on the first 4 P-Agent features (volition, sentience, causation=instigation,
    movement=motion). -/
theorem grimm_agentivity_consistent_with_dowty
    (p q : EntailmentProfile)
    (h : AgentivityNode.fromEntailmentProfile p ≤
         AgentivityNode.fromEntailmentProfile q) :
    (!p.volition || q.volition) = true ∧
    (!p.sentience || q.sentience) = true ∧
    (!p.causation || q.causation) = true ∧
    (!p.movement || q.movement) = true := by
  simp only [LE.le, AgentivityNode.leBool, AgentivityNode.fromEntailmentProfile,
             Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

private theorem bImpl (a b : Bool) (h : a = true → b = true) :
    (!a || b) = true := by cases a <;> simp_all

/-- The Dowty→Grimm bridge is monotone: if one EntailmentProfile
    dominates another on P-Agent features, the corresponding
    AgentivityNodes are ordered. -/
theorem fromEntailmentProfile_monotone
    (p q : EntailmentProfile)
    (hv : p.volition = true → q.volition = true)
    (hs : p.sentience = true → q.sentience = true)
    (hc : p.causation = true → q.causation = true)
    (hm : p.movement = true → q.movement = true) :
    AgentivityNode.fromEntailmentProfile p ≤
    AgentivityNode.fromEntailmentProfile q := by
  show AgentivityNode.leBool _ _ = true
  simp only [AgentivityNode.leBool, AgentivityNode.fromEntailmentProfile, Bool.and_eq_true]
  exact ⟨⟨⟨bImpl _ _ hv, bImpl _ _ hs⟩, bImpl _ _ hc⟩, bImpl _ _ hm⟩

-- ════════════════════════════════════════════════════
-- § 14. Dative Polysemy (@cite{grimm-2011} §5.1)
-- ════════════════════════════════════════════════════

/-- The dative region unifies recipients, experiencers, and second
    arguments of communication/service verbs — they all share the
    semantic properties of **sentience** and **qualitative persistence
    (beginning)** (@cite{grimm-2011} Fig. 7, p.536).

    This explains dative "polysemy": the diverse uses of the dative
    share a connected region on the lattice, not a single function. -/
theorem dative_unifies_recipient_experiencer :
    recipientNode.toCaseRegion = .dative ∧
    experiencerNode.toCaseRegion = .dative := ⟨rfl, rfl⟩

/-- The dative experiencer subject (@cite{grimm-2011} §5.1.1) has the
    same lattice position as the dative recipient — sentience +
    qualitative persistence. This explains why languages cross-linguistically
    use the same case (dative) for both. -/
theorem dative_experiencer_eq_recipient :
    experiencerNode = recipientNode := rfl

-- ════════════════════════════════════════════════════
-- § 15. Russian Genitive/Accusative Alternation (@cite{grimm-2011} §5.2)
-- ════════════════════════════════════════════════════

/-- The Russian genitive/accusative alternation arises when the object
    of an intensional verb (want, seek, await) falls in a region covered
    by two cases. The accusative covers existential persistence (beginning);
    the genitive covers total non-persistence (@cite{grimm-2011} Fig. 8).

    - Accusative (specific reading): the object is referential → exists
      → existential persistence (beginning) → ACC region.
    - Genitive (non-specific reading): the object need not exist →
      total non-persistence → GEN region.

    The alternation is limited to verbs whose objects have no persistence
    entailments — only intensional verbs like *want*, *seek*, *await*
    license the genitive (@cite{grimm-2011} p.541). -/
structure GenAccAlternation where
  /-- The object node under the specific/referential reading. -/
  specificReading : GrimmNode
  /-- The object node under the non-specific reading. -/
  nonSpecificReading : GrimmNode
  /-- The specific reading has more persistence features. -/
  specific_more_persistent :
    nonSpecificReading.persistence ≤ specificReading.persistence

/-- The canonical Russian gen/acc alternation for intensional verbs:
    ACC (specific) ↔ GEN (non-specific). -/
def russianGenAcc : GenAccAlternation :=
  { specificReading := ⟨⊥, .exPersBeginning⟩
    nonSpecificReading := ⟨⊥, .totalNonPersistence⟩
    specific_more_persistent := bot_le }

/-- The specific reading maps to the ACC/ABS region. -/
theorem genAcc_specific_is_acc :
    russianGenAcc.specificReading.toCaseRegion = .accAbs := by native_decide

-- ════════════════════════════════════════════════════
-- § 16. Upward/Downward Closure (@cite{grimm-2011} §2.3, p.528)
-- ════════════════════════════════════════════════════

/-- Agents are **upwards closed** in the agentivity dimension
    (@cite{grimm-2011} p.528): if `a` qualifies as agent for a predicate
    (i.e., `a` has at least the entailments required by the verb), then
    any `b ≥ a` also qualifies. An entity with *more* agentive properties
    can always fill an agent role requiring fewer.

    Formally: the set of acceptable agents for a verb with minimum
    requirement `minReq` is `{a | minReq ≤ a}`, which is an upper set. -/
theorem agent_upward_closed (minReq a b : AgentivityNode)
    (ha : minReq ≤ a) (hab : a ≤ b) :
    minReq ≤ b :=
  le_trans ha hab

/-- Patients are **downwards closed** in the persistence dimension
    (@cite{grimm-2011} p.528): if `p` qualifies as patient (i.e., `p`
    has at most the persistence features of the verb's patient slot),
    then any `q ≤ p` also qualifies. A *more* affected entity (less
    persistence) can always fill a patient role.

    Formally: the set of acceptable patients for a verb with maximum
    persistence `maxPers` is `{p | p ≤ maxPers}`, which is a lower set. -/
theorem patient_downward_closed (maxPers p q : PersistenceLevel)
    (hp : p ≤ maxPers) (hqp : q ≤ p) :
    q ≤ maxPers :=
  le_trans hqp hp

-- ════════════════════════════════════════════════════
-- § 17. Semantic Opposition (@cite{grimm-2011} §3, p.530)
-- ════════════════════════════════════════════════════

/-- Semantic opposition between two GrimmNodes. Transitivity increases
    with the distance between agent and patient on the lattice. We measure
    this as the difference in total feature counts — higher opposition
    means more prototypically transitive. -/
def semanticOpposition (agent patient : GrimmNode) : Int :=
  (agent.featureCount : Int) - (patient.featureCount : Int)

/-- Maximal agent vs maximal patient has the highest opposition (8 - 2 = 6). -/
theorem maximal_opposition :
    semanticOpposition maximalAgent maximalPatient = 6 := by native_decide

/-- Class I (break) has more opposition than Class II (shoot):
    the patient is more affected (fewer persistence features). -/
theorem classI_more_opposition_than_classII :
    semanticOpposition effectorAgent
      (TransitivityClass.resultativeEffective.patientNode) >
    semanticOpposition effectorAgent
      (TransitivityClass.contact.patientNode) := by native_decide

-- ════════════════════════════════════════════════════
-- § 18. End-to-End: EntailmentProfile → Case
-- ════════════════════════════════════════════════════

/-- Full pipeline: kick subject → GrimmNode → NOM/ERG → NOM (accusative). -/
theorem kick_subject_to_nom :
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase
    = .nom := by native_decide

/-- Full pipeline: kick object → GrimmNode → ACC/ABS → ACC (accusative). -/
theorem kick_object_to_acc :
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toAccusativeCase
    = .acc := by native_decide

/-- Build subject → NOM (full agent, total persistence). -/
theorem build_subject_to_nom :
    (GrimmNode.fromSubjectProfile buildSubjectProfile).toCaseRegion.toAccusativeCase
    = .nom := by native_decide

/-- Build object → OBLIQUE (not ACC). The object of *build* maps to
    exPersEnd (entity comes into existence), which falls OUTSIDE the
    transitivity region (@cite{grimm-2011} p.529–530). Creation verbs
    are non-prototypically transitive — the object does not exist at
    the beginning of the event to "undergo its effects."
    This is a correct prediction: creation verb objects cross-linguistically
    show atypical case marking (e.g., pseudo-cleft asymmetry). -/
theorem build_object_outside_acc :
    (GrimmNode.fromObjectProfile buildObjectProfile).toCaseRegion ≠ .accAbs := by
  native_decide

/-- Full pipeline: see subject → OBLIQUE (not NOM/ERG).
    The see-subject has sentience but no instigation, so it falls
    outside the NOM/ERG region. Grimm's system predicts non-canonical
    case for perception verb subjects cross-linguistically. -/
theorem see_subject_not_nomErg :
    (GrimmNode.fromSubjectProfile seeSubjectProfile).toCaseRegion ≠ .nomErg := by
  native_decide

/-- Full pipeline: die subject (unaccusative) → ACC/ABS.
    The sole argument of *die* maps to the patient region (no agentivity,
    exPersBeginning). In an ergative system this → ABS (= intransitive
    subject). -/
theorem die_subject_to_abs :
    (GrimmNode.fromObjectProfile dieSubjectProfile).toCaseRegion.toErgativeCase
    = .abs := by native_decide

-- ════════════════════════════════════════════════════
-- § 19. Canonical Verb-Agentivity Chain (@cite{grimm-2011} §2.2, p.523–524)
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011} illustrates the agentivity lattice with a chain of
    canonical verbs, each adding one feature. This demonstrates that the
    lattice directly formalizes "degree of agentivity" — higher on the
    lattice means more agentive. -/

/-- sit/stand subject: ⊥ (no agentivity). @cite{grimm-2011} p.523. -/
def sitAgentivity : AgentivityNode := ⊥

/-- know/see subject: sentience only. @cite{grimm-2011} p.524. -/
def knowAgentivity : AgentivityNode := ⟨false, true, false, false⟩

/-- discover subject: sentience + instigation. @cite{grimm-2011} p.524. -/
def discoverAgentivity : AgentivityNode := ⟨false, true, true, false⟩

/-- look at subject: sentience + instigation + motion. @cite{grimm-2011} p.524. -/
def lookAtAgentivity : AgentivityNode := ⟨false, true, true, true⟩

/-- assassinate subject: all four features. @cite{grimm-2011} p.524. -/
def assassinateAgentivity : AgentivityNode := ⊤

/-- The canonical verb chain is totally ordered and forms a maximal
    chain from ⊥ to ⊤ in the agentivity lattice. -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧
    knowAgentivity < discoverAgentivity ∧
    discoverAgentivity < lookAtAgentivity ∧
    lookAtAgentivity < assassinateAgentivity := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-- All canonical verb positions satisfy volition → sentience. -/
theorem canonical_verbs_valid :
    sitAgentivity.valid = true ∧ knowAgentivity.valid = true ∧
    discoverAgentivity.valid = true ∧ lookAtAgentivity.valid = true ∧
    assassinateAgentivity.valid = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 20. Persistence Covering Relations (@cite{grimm-2011} Fig. 2)
-- ════════════════════════════════════════════════════

/-- exPersEnd and quPersBeginning are incomparable (neither ≤ the other).
    Their feature sets are {ExPE, QuPE} and {ExPB, ExPE, QuPB} —
    QuPE ∉ {ExPB, ExPE, QuPB} and ExPB ∉ {ExPE, QuPE}.
    This means the persistence lattice has TWO independent paths from ⊥ to ⊤:
    (1) ⊥ → exPersEnd → ⊤
    (2) ⊥ → exPersBeginning → quPersBeginning → ⊤ -/
theorem exPersEnd_incomparable_quPersBeginning :
    ¬ (PersistenceLevel.exPersEnd ≤ PersistenceLevel.quPersBeginning) ∧
    ¬ (PersistenceLevel.quPersBeginning ≤ PersistenceLevel.exPersEnd) := by
  decide

/-- The persistence lattice inclusion chain (2) from Fig. 2:
    exPersBeginning ≤ quPersBeginning ≤ totalPersistence. -/
theorem persistence_chain :
    PersistenceLevel.exPersBeginning ≤ PersistenceLevel.quPersBeginning ∧
    PersistenceLevel.quPersBeginning ≤ PersistenceLevel.totalPersistence := by
  decide

-- ════════════════════════════════════════════════════
-- § 21. DOM and the Agentivity Lattice (@cite{grimm-2011} §4)
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011} (p.534): "it is a combination of verbal and nominal
    properties which trigger DOM." The lattice provides a formal account:

    1. The case regions defined in §6 (`toCaseRegion`) map lattice positions
       to cases — ACC/ABS for ⊥-agentivity objects with existential
       persistence, DATIVE for sentient non-instigators with qualitative
       persistence (Fig. 7).

    2. When we map nominal animacy to baseline agentive capacity and
       combine it with the verb's persistence profile, animate/human
       objects shift from ACC/ABS into the DATIVE region.

    3. This is NOT a DOM-specific definition — it reuses `toCaseRegion`
       (§6) and `inTransitiveRegion` (§5), both defined for general
       case theory. The DOM prediction is a CONSEQUENCE of case theory.

    The verb class effect (@cite{von-heusinger-2008}) also falls out:
    verbs whose subjects map to NOM/ERG provide maximal contrast with
    the object — DOM can regularize. Verbs whose subjects fall outside
    NOM/ERG provide less contrast — DOM remains sensitive to nominal
    properties. -/

open Core.Prominence

-- ── §21.1 Animacy → agentivity mapping ──

/-- Map nominal animacy to baseline agentive capacity on the lattice.

    Only *inherent* referent properties are mapped — not event-specific
    ones like instigation or motion:

    - Human: volition + sentience (capacity for intentional action)
    - Animate: sentience (conscious but non-volitional)
    - Inanimate: ⊥ (no inherent agentive capacity)

    The exclusion of instigation and motion is principled: these are
    event properties (did the participant instigate THIS event? move
    during THIS event?), not referent properties. Volition and sentience
    are inherent capacities of the referent type. -/
def animacyToAgentivity : AnimacyLevel → AgentivityNode
  | .human     => ⟨true, true, false, false⟩   -- {V, S}
  | .animate   => ⟨false, true, false, false⟩  -- {S}
  | .inanimate => ⊥

/-- All animacy-derived nodes satisfy volition → sentience. -/
theorem animacy_all_valid (a : AnimacyLevel) :
    (animacyToAgentivity a).valid = true := by
  cases a <;> native_decide

/-- The mapping is monotone: higher animacy → higher agentivity.
    This is a structural property of the feature-subset ordering,
    not a stipulation. -/
theorem animacy_agentivity_monotone :
    animacyToAgentivity .inanimate ≤ animacyToAgentivity .animate ∧
    animacyToAgentivity .animate ≤ animacyToAgentivity .human := by
  constructor <;> decide

-- ── §21.2 The core derivation: case regions predict DOM ──

/-- Combine a referent's nominal agentivity (from animacy) with the
    verb's persistence profile for the object. -/
def objectNodeWithAnimacy (animacy : AnimacyLevel)
    (verbPersistence : PersistenceLevel) : GrimmNode :=
  ⟨animacyToAgentivity animacy, verbPersistence⟩

/-- **The key non-circular derivation.** For canonical transitive objects
    (quPersBeginning = contact verbs like kick, hit, push):

    - Inanimate: `⟨⊥, qPB⟩` → `toCaseRegion` = **accAbs**
      (prototypical patient, no DOM needed)
    - Animate: `⟨{S}, qPB⟩` → `toCaseRegion` = **dative**
      (sentience shifts it into the dative region, Fig. 7)
    - Human: `⟨{V,S}, qPB⟩` → `toCaseRegion` = **dative**
      (volition + sentience, also in dative region)

    `toCaseRegion` was defined in §6 for general case theory, not for
    DOM. That it automatically separates inanimate objects (accAbs) from
    animate/human objects (dative) is the lattice's genuine prediction. -/
theorem inanimate_object_in_accAbs :
    (objectNodeWithAnimacy .inanimate .quPersBeginning).toCaseRegion
    = .accAbs := by native_decide

theorem animate_object_in_dative :
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion
    = .dative := by native_decide

theorem human_object_in_dative :
    (objectNodeWithAnimacy .human .quPersBeginning).toCaseRegion
    = .dative := by native_decide

-- ── §21.3 DOM predicted when object leaves ACC/ABS ──

/-- DOM is predicted when the object is in the transitivity region
    but its nominal agentivity pushes it outside the ACC/ABS case
    region. Both conditions use infrastructure defined for general
    case theory (§5, §6), not for DOM. -/
def domPredictedByLattice (animacy : AnimacyLevel)
    (verbPersistence : PersistenceLevel) : Bool :=
  let node := objectNodeWithAnimacy animacy verbPersistence
  node.inTransitiveRegion && node.toCaseRegion != .accAbs

/-- Inanimate objects of canonical transitives: in ACC/ABS, no DOM. -/
theorem inanimate_canonical_no_dom :
    domPredictedByLattice .inanimate .quPersBeginning = false := by
  native_decide

/-- Animate objects of canonical transitives: outside ACC/ABS, DOM
    predicted. The lattice reason: sentience pushes the object into
    the dative region (@cite{grimm-2011} Fig. 7). -/
theorem animate_canonical_dom :
    domPredictedByLattice .animate .quPersBeginning = true := by
  native_decide

/-- Human objects: also outside ACC/ABS, DOM predicted. -/
theorem human_canonical_dom :
    domPredictedByLattice .human .quPersBeginning = true := by
  native_decide

-- ── §21.4 Resultative transitives (exPersBeginning) ──

/-- The same pattern holds for resultative verbs (break, destroy):
    inanimate objects stay in ACC/ABS, animate/human objects do not. -/
theorem inanimate_resultative_no_dom :
    domPredictedByLattice .inanimate .exPersBeginning = false := by
  native_decide

theorem animate_resultative_dom :
    domPredictedByLattice .animate .exPersBeginning = true ∧
    domPredictedByLattice .human .exPersBeginning = true :=
  ⟨by native_decide, by native_decide⟩

-- ── §21.5 Creation verbs: outside transitivity entirely ──

/-- Creation verb objects (build, invent — exPersEnd) are outside the
    transitivity region at ALL animacy levels. The object does not
    exist at event start, so it cannot "intrude" on the agent's role.
    DOM is inapplicable, not merely unnecessary. -/
theorem creation_outside_transitivity (a : AnimacyLevel) :
    (objectNodeWithAnimacy a .exPersEnd).inTransitiveRegion = false := by
  cases a <;> native_decide

-- ── §21.6 Verb class effect: subject case region ──

/-- Whether the subject maps to the NOM/ERG case region. When true,
    the verbal semantics alone provides maximal contrast between
    subject (NOM/ERG) and object (ACC/ABS or below), and DOM can
    regularize — it is redundant for disambiguation.

    @cite{von-heusinger-2008}: *matar* 'kill' (Class 1, subject →
    NOM/ERG) regularized DOM centuries before *ver* 'see' (Class 2,
    subject → oblique). -/
def subjectInAgentRegion (subjProfile : EntailmentProfile) : Bool :=
  (GrimmNode.fromSubjectProfile subjProfile).toCaseRegion == .nomErg

/-- Kick subject → NOM/ERG: maximal verbal contrast.
    Corresponds to *matar* 'kill' — DOM regularized early. -/
theorem kick_subject_in_agent_region :
    subjectInAgentRegion kickSubjectProfile = true := by native_decide

/-- See subject → NOT NOM/ERG: insufficient verbal contrast.
    Corresponds to *ver* 'see' — DOM remained variable. -/
theorem see_subject_not_in_agent_region :
    subjectInAgentRegion seeSubjectProfile = false := by native_decide

/-- Build subject → NOM/ERG: high verbal contrast, but moot because
    the object is outside the transitivity region (§21.5). -/
theorem build_subject_in_agent_region :
    subjectInAgentRegion buildSubjectProfile = true := by native_decide

-- ── §21.7 Monotonicity: Aissen's staircase from lattice structure ──

/-- The lattice reproduces @cite{aissen-2003}'s monotonicity prediction:
    if DOM is predicted for a lower animacy level, it is also predicted
    for all higher levels. Universally quantified over persistence.

    This is NOT stipulated — it follows from:
    1. `animacyToAgentivity` is monotone (higher animacy → more features)
    2. `toCaseRegion` maps ⊥ agentivity to accAbs, non-⊥ to dative/oblique
    3. Once agentivity is non-⊥, adding features keeps it non-⊥ -/
theorem dom_monotone_inanimate_animate (p : PersistenceLevel) :
    domPredictedByLattice .inanimate p = true →
    domPredictedByLattice .animate p = true := by
  cases p <;> decide

theorem dom_monotone_animate_human (p : PersistenceLevel) :
    domPredictedByLattice .animate p = true →
    domPredictedByLattice .human p = true := by
  cases p <;> decide

-- ── §21.8 Limitation: totalPersistence ──

/-! For totalPersistence objects (perception verbs: see, hear, know),
    `toCaseRegion` maps `⟨⊥, totalPersistence⟩` to oblique, not accAbs,
    because totalPersistence is not in {exPersBeginning, quPersBeginning}.
    This means `domPredictedByLattice` returns true for ALL animacy levels,
    including inanimate — overpredicting DOM for perception verb objects.

    This reflects a genuine theoretical point: Grimm's system treats
    perception verb objects as non-prototypical patients (they are not
    affected or changed). But it means `domPredictedByLattice` is most
    informative for verbs in the transitivity region's core: contact
    (quPersBeginning) and resultative effective (exPersBeginning) verbs. -/
theorem totalPersistence_all_outside_accAbs (a : AnimacyLevel) :
    (objectNodeWithAnimacy a .totalPersistence).toCaseRegion ≠ .accAbs := by
  cases a <;> native_decide

-- ════════════════════════════════════════════════════
-- § 22. Projection Kernel Theorems
-- ════════════════════════════════════════════════════

/-- **AgentivityNode kernel**: two profiles map to the same agentivity node
    iff they agree on {V, S, C, M}. The 5th P-Agent feature (IE) and all
    5 P-Patient features are irrelevant — they are dropped by the projection.

    This formally characterizes the information loss: `fromEntailmentProfile`
    is a surjection whose fibers are the equivalence classes of profiles
    agreeing on {V, S, C, M}. -/
theorem fromEntailmentProfile_eq_iff (p q : EntailmentProfile) :
    AgentivityNode.fromEntailmentProfile p =
    AgentivityNode.fromEntailmentProfile q ↔
    p.volition = q.volition ∧ p.sentience = q.sentience ∧
    p.causation = q.causation ∧ p.movement = q.movement := by
  simp [AgentivityNode.fromEntailmentProfile, AgentivityNode.mk.injEq]

/-- Independent existence is lost by the agentivity projection.
    Two profiles differing only in IE map to the same node.
    Concrete witness: full agent (IE=true) and agent-without-IE. -/
theorem fromEntailmentProfile_drops_IE :
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, false, false, false, false, false⟩ =
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, false, false, false, false, false, false⟩ := rfl

/-- All P-Patient features are lost by the agentivity projection.
    A profile with 5 P-Patient features maps to the same node as one with 0. -/
theorem fromEntailmentProfile_drops_patient :
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, true, true, true, true, true⟩ =
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, false, false, false, false, false⟩ := rfl

-- ════════════════════════════════════════════════════
-- § 23. wellFormedPair Non-Preservation
-- ════════════════════════════════════════════════════

/-- **wellFormedPair is not preserved by the Grimm projection.**

    @cite{dowty-1991}'s `wellFormedPair` constrains inter-argument entailment
    pairings: causation→CoS, movement→stationary, IE→DE. These are
    *relational* constraints between two profiles.

    @cite{grimm-2011}'s system replaces them with a single persistence
    dimension on the patient side. The IE feature is dropped entirely
    from the agentivity projection, so the IE→DE constraint becomes
    invisible.

    Witness: s₁ = {C} and s₂ = {C, IE} map to the same AgentivityNode
    (both have instigation only). With o = {CoS}, wellFormedPair holds
    for s₁ (IE=false, so IE→DE vacuously satisfied) but fails for s₂
    (IE=true but DE=false). The Grimm system cannot detect this. -/
theorem wellFormedPair_not_preserved_by_grimm :
    ∃ s₁ o₁ s₂ o₂ : EntailmentProfile,
    wellFormedPair s₁ o₁ = true ∧ wellFormedPair s₂ o₂ = false ∧
    GrimmNode.fromSubjectProfile s₁ = GrimmNode.fromSubjectProfile s₂ ∧
    GrimmNode.fromObjectProfile o₁ = GrimmNode.fromObjectProfile o₂ :=
  ⟨⟨false, false, true, false, false, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   ⟨false, false, true, false, true, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 24. ArgTemplate → GrimmNode Bridge
-- ════════════════════════════════════════════════════

open Semantics.Events.LevinClassProfiles
open Semantics.Events.Affectedness

/-- Project an ArgTemplate's subject profile to a GrimmNode. -/
def _root_.Semantics.Events.LevinClassProfiles.ArgTemplate.subjectGrimm
    (t : ArgTemplate) : GrimmNode :=
  GrimmNode.fromSubjectProfile t.subjectProfile

/-- Project an ArgTemplate's object profile (if any) to a GrimmNode. -/
def _root_.Semantics.Events.LevinClassProfiles.ArgTemplate.objectGrimm
    (t : ArgTemplate) : Option GrimmNode :=
  t.objectProfile.map GrimmNode.fromObjectProfile

/-- Project an ArgTemplate's object to its affectedness degree. -/
def _root_.Semantics.Events.LevinClassProfiles.ArgTemplate.objectAffectedness
    (t : ArgTemplate) : Option AffectednessDegree :=
  t.objectProfile.map profileToDegree

-- ── Per-template GrimmNode verification ──

/-- Manner-contact subject → full agent on the Grimm lattice. -/
theorem mannerContact_subject_grimm :
    mannerContact.subjectGrimm.agentivity = ⊤ := by native_decide

/-- Manner-contact object → potential affectedness (no CoS entailed). -/
theorem mannerContact_object_affectedness :
    mannerContact.objectAffectedness = some AffectednessDegree.potential := rfl

/-- Result-change object → nonquantized affectedness (CoS, no IT). -/
theorem resultChange_object_affectedness :
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized := rfl

/-- Creation object → quantized affectedness (CoS + IT). -/
theorem creation_object_affectedness :
    creation.objectAffectedness = some AffectednessDegree.quantized := rfl

/-- Consumption object → quantized affectedness (CoS + IT). -/
theorem consumption_object_affectedness :
    consumption.objectAffectedness = some AffectednessDegree.quantized := rfl

/-- Self-motion (intransitive) → no object affectedness. -/
theorem selfMotion_no_object :
    selfMotion.objectAffectedness = none := rfl

/-- **Affectedness ordering across templates**: the named templates
    are ordered by truth-conditional strength on the object side,
    reproducing @cite{beavers-2010}'s hierarchy:
    creation/consumption (quantized) > resultChange (nonquantized)
    > mannerContact (potential) > perception (unspecified). -/
theorem template_affectedness_hierarchy :
    AffectednessDegree.ge .quantized .nonquantized = true ∧
    AffectednessDegree.ge .nonquantized .potential = true ∧
    creation.objectAffectedness = some AffectednessDegree.quantized ∧
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized ∧
    mannerContact.objectAffectedness = some AffectednessDegree.potential ∧
    perception.objectAffectedness = some AffectednessDegree.unspecified :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ── Cross-projection consistency: affectedness vs. persistence ──

/-- The affectedness and persistence projections are consistent for
    manner-contact objects: potential affectedness ↔ totalPersistence
    (the object may change but the verb doesn't entail it). -/
theorem mannerContact_cross_projection :
    mannerContact.objectAffectedness = some AffectednessDegree.potential ∧
    mannerContact.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .totalPersistence := ⟨rfl, by native_decide⟩

/-- Result-change: nonquantized ↔ quPersBeginning (changed but persists). -/
theorem resultChange_cross_projection :
    resultChange.objectAffectedness = some AffectednessDegree.nonquantized ∧
    resultChange.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .quPersBeginning := ⟨rfl, by native_decide⟩

/-- Creation: quantized ↔ exPersEnd (entity comes into existence). -/
theorem creation_cross_projection :
    creation.objectAffectedness = some AffectednessDegree.quantized ∧
    creation.objectProfile.map PersistenceLevel.fromPatientProfile =
      some .exPersEnd := ⟨rfl, by native_decide⟩

end Semantics.Events.AgentivityLattice
