import Linglib.Semantics.ArgumentStructure.Agentivity
import Linglib.Semantics.ArgumentStructure.PersistenceLevel
import Mathlib.Data.Fintype.Prod

/-!
# Participant types ([grimm-2011] §2.2, Fig. 3)

A participant type pairs an agentivity value with a persistence level —
Grimm's term for a node of the full lattice ("each node of the lattice
determines one type of participant"). The product carrier has 80 elements;
Grimm's Fig. 3 lattice is the 38-element `Valid` subset (volition →
sentience, and no agentivity without existence at the event's beginning,
p.526–527).

Named participant types anchor the case regions (`CaseRegion.lean`):
`maximalAgent = ⊤`, `maximalPatient`, `effectorAgent`, and the dative
convergence point `sentientNonInstigator`. Tsunoda's transitivity hierarchy
(§3, example 8) is `TransitivityRank`, with the canonical patient
placement of each class (Fig. 5).
-/

namespace ArgumentStructure

/-- A participant type: agentivity × persistence (80 elements). Grimm's
    Fig. 3 lattice is the 38-element `Valid` subset. -/
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

/-- Full validity: both constraints satisfied. Carves Grimm's 38-element
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
