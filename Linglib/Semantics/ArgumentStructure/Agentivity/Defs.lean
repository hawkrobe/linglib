import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
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

- `AgentivityNode` is the full Boolean cube on the four agentivity
  primitives (16 elements). Grimm's Fig. 1 lattice is its 12-node
  `AgentivityNode.Valid` subset (volition → sentience).
- `PersistenceLevel` is exactly Grimm's five valid persistence levels
  (Fig. 2) — here the carrier *is* the paper's object.
- `GrimmNode` is the full product carrier (80 elements). Grimm's Fig. 3
  agentivity lattice is its 38-node `GrimmNode.Valid` subset
  (`AgentivityValid` ∧ `CrossValid`).

## Mathlib integration

All ordering infrastructure uses Mathlib typeclasses:
- `AgentivityNode`: `Lattice`, `BoundedOrder`, `Fintype`
- `PersistenceLevel`: `Lattice`, `BoundedOrder`, `Fintype`
- `GrimmNode`: `Lattice`, `BoundedOrder`, `Fintype`

The bridges to [dowty-1991]'s `EntailmentProfile` live in
`EntailmentProfile.lean`; the case-region geometry lives in
`Agentivity/CaseRegions.lean`.
-/

namespace ArgumentStructure.AgentivityLattice

/-! ### Agentivity primitives (Table 2, §2.1) -/

/-- The four agentivity primitives (Table 2 (agentive properties), p.520).

    Each has an agentive (+) and non-agentive (∅) pole. The non-agentive
    pole is not a separate feature — it is simply the absence of the
    agentive property. This is the **privative opposition** that replaces
    Dowty's two independent clusters.

    The carrier is the full 16-element Boolean cube; Grimm's Fig. 1
    lattice is the 12-node `Valid` subset. -/
structure AgentivityNode where
  /-- +volition: the participant intends to bring about the event. -/
  volition    : Bool
  /-- +sentience: conscious involvement in the action or state. -/
  sentience   : Bool
  /-- +instigation: prior independent action whose effects can be
      attributed to this argument. Replaces Dowty's "causation"
      (p.521). -/
  instigation : Bool
  /-- +motion: the argument is in motion during the event. -/
  motion      : Bool
  deriving DecidableEq, Repr

/-- Validity constraint: volition presupposes sentience
    (p.521, following [dowty-1991] p.607). Carves Grimm's 12-node
    Fig. 1 lattice out of the 16-element carrier. -/
def AgentivityNode.Valid (a : AgentivityNode) : Prop :=
  a.volition = true → a.sentience = true

instance (a : AgentivityNode) : Decidable a.Valid := by
  unfold AgentivityNode.Valid; infer_instance

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

instance : DecidableRel (α := AgentivityNode) (· < ·) := fun _ _ =>
  decidable_of_iff' _ lt_iff_le_not_ge

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

/-- Characterisation of the inclusion order by componentwise implication.
    Public interface to the private `leBool`; verified by `decide` over the
    16 × 16 pairs. -/
theorem AgentivityNode.le_iff (a b : AgentivityNode) :
    a ≤ b ↔
      (a.volition = true → b.volition = true) ∧
      (a.sentience = true → b.sentience = true) ∧
      (a.instigation = true → b.instigation = true) ∧
      (a.motion = true → b.motion = true) := by
  revert a b; decide

-- Componentwise Bool monotonicity (extracted from leBool)

theorem AgentivityNode.le_instigation_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : a.instigation = true) : b.instigation = true := by
  have hbool : a.leBool b = true := hab
  cases hi : b.instigation
  · simp [AgentivityNode.leBool, h, hi] at hbool
  · rfl

theorem AgentivityNode.le_sentience_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : a.sentience = true) : b.sentience = true := by
  have hbool : a.leBool b = true := hab
  cases hi : b.sentience
  · simp [AgentivityNode.leBool, h, hi] at hbool
  · rfl

theorem AgentivityNode.ge_instigation_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : b.instigation = false) : a.instigation = false := by
  have hbool : a.leBool b = true := hab
  cases hi : a.instigation
  · rfl
  · simp [AgentivityNode.leBool, hi, h] at hbool

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
structure GrimmNode where
  agentivity  : AgentivityNode
  persistence : PersistenceLevel
  deriving DecidableEq, Repr

/-- The agentivity constraint: volition → sentience. -/
def GrimmNode.AgentivityValid (n : GrimmNode) : Prop :=
  n.agentivity.Valid

instance (n : GrimmNode) : Decidable n.AgentivityValid := by
  unfold GrimmNode.AgentivityValid; infer_instance

/-- The cross-lattice constraint: if the argument does not exist at the
    beginning of the event, it cannot have any agentivity properties. -/
def GrimmNode.CrossValid (n : GrimmNode) : Prop :=
  n.persistence.exPersB = true ∨ n.agentivity = ⊥

instance (n : GrimmNode) : Decidable n.CrossValid := by
  unfold GrimmNode.CrossValid; infer_instance

/-- Full validity: both constraints satisfied. Carves Grimm's 38-node
    Fig. 3 lattice out of the 80-element carrier. -/
def GrimmNode.Valid (n : GrimmNode) : Prop :=
  n.AgentivityValid ∧ n.CrossValid

instance (n : GrimmNode) : Decidable n.Valid := by
  unfold GrimmNode.Valid; infer_instance

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

/-- Componentwise lattice: meet/join on each axis independently. -/
instance : Lattice GrimmNode where
  sup a b := ⟨a.agentivity ⊔ b.agentivity, a.persistence ⊔ b.persistence⟩
  inf a b := ⟨a.agentivity ⊓ b.agentivity, a.persistence ⊓ b.persistence⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ h1 h2 := ⟨sup_le h1.1 h2.1, sup_le h1.2 h2.2⟩
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h1 h2 := ⟨le_inf h1.1 h2.1, le_inf h1.2 h2.2⟩

/-! ### Named participant types -/

/-- Maximal Agent (Fig. 4): all agentivity features,
    total persistence. The prototypical transitive subject. -/
def maximalAgent : GrimmNode :=
  ⟨⟨true, true, true, true⟩, .totalPersistence⟩

/-- Maximal Patient (Fig. 4): no agentivity features,
    existential persistence (beginning). The prototypical affected object
    that ceases to exist (break, destroy). -/
def maximalPatient : GrimmNode :=
  ⟨⟨false, false, false, false⟩, .exPersBeginning⟩

/-- The "effector" participant type: instigation + motion, total
    persistence. The canonical agent of effective action verbs (kill, break).
    §3, labeled Ia/IIa in Fig. 5. -/
def effectorAgent : GrimmNode :=
  ⟨⟨false, false, true, true⟩, .totalPersistence⟩

/-- The lattice position {sentience} × qualitative persistence (beginning).
    Per Grimm 2011 §5.1, diverse uses of the dative converge on this single
    region — recipients, experiencers, and benefactives are aliases below. -/
def sentientNonInstigatorNode : GrimmNode :=
  ⟨⟨false, true, false, false⟩, .quPersBeginning⟩

/-- Dative experiencer of psych verbs (§5.1.1). Alias of
    `sentientNonInstigatorNode` — the convergence with `recipientNode` is by
    construction, not a theorem. -/
abbrev experiencerNode : GrimmNode := sentientNonInstigatorNode

/-- Canonical dative recipient (Fig. 7). Alias of `sentientNonInstigatorNode`
    — see the docstring there for the unified treatment. -/
abbrev recipientNode : GrimmNode := sentientNonInstigatorNode

/-! ### Transitivity region (§3, Fig. 4) -/

/-- A node is in the **transitivity region** iff its persistence level
    is in {exPersBeginning, quPersBeginning, totalPersistence}.

    The transitivity region excludes totalNonPersistence and exPersEnd
    because the prototypical transitive event requires both participants
    to exist at the beginning (p.529–530). -/
def GrimmNode.InTransitiveRegion (n : GrimmNode) : Prop :=
  n.persistence.exPersB = true

instance (n : GrimmNode) : Decidable n.InTransitiveRegion := by
  unfold GrimmNode.InTransitiveRegion; infer_instance

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
def TransitivityRank.patientNode : TransitivityRank → GrimmNode
  | .resultativeEffective => ⟨⊥, .exPersBeginning⟩     -- Ip
  | .contact              => ⟨⊥, .quPersBeginning⟩     -- IIp
  | .pursuit              => ⟨⊥, .totalNonPersistence⟩ -- IIIp

/-! ### Lattice properties (from Mathlib instances)

Reflexivity, transitivity, antisymmetry are provided by `PartialOrder`;
`⊥ ≤ a`, `a ≤ ⊤` by `OrderBot`/`OrderTop`; join/meet associativity,
commutativity, absorption by `Lattice`. -/

/-- Persistence incomparability: exPersEnd and exPersBeginning are
    incomparable — neither is a subset of the other's features. -/
theorem exPersEnd_incomparable_exPersBeginning :
    ¬ (PersistenceLevel.exPersEnd ≤ PersistenceLevel.exPersBeginning) ∧
    ¬ (PersistenceLevel.exPersBeginning ≤ PersistenceLevel.exPersEnd) := by
  decide

/-- Their join is ⊤ (totalPersistence). -/
theorem exPersEnd_sup_exPersBeginning :
    PersistenceLevel.exPersEnd ⊔ PersistenceLevel.exPersBeginning = ⊤ := by
  decide

/-- Their meet is ⊥ (totalNonPersistence). -/
theorem exPersEnd_inf_exPersBeginning :
    PersistenceLevel.exPersEnd ⊓ PersistenceLevel.exPersBeginning = ⊥ := by
  decide

/-- Maximal agent is ⊤ on the combined lattice. -/
@[simp]
theorem maximalAgent_eq_top : maximalAgent = ⊤ := by decide

/-! ### Named participant verification -/

-- Validity

theorem maximalAgent_valid : maximalAgent.Valid := by decide
theorem maximalPatient_valid : maximalPatient.Valid := by decide
theorem effectorAgent_valid : effectorAgent.Valid := by decide
theorem experiencerNode_valid : experiencerNode.Valid := by decide

-- Maximal agent is at the top, maximal patient is lower

theorem maximalAgent_featureCount :
    maximalAgent.featureCount = 8 := by decide

theorem maximalPatient_featureCount :
    maximalPatient.featureCount = 2 := by decide

theorem maximalPatient_le_maximalAgent :
    maximalPatient ≤ maximalAgent := by decide

theorem maximalAgent_not_le_maximalPatient :
    ¬ maximalAgent ≤ maximalPatient := by decide

-- Maximal agent and patient are in the transitivity region

theorem maximalAgent_in_transitiveRegion :
    maximalAgent.InTransitiveRegion := by decide

theorem maximalPatient_in_transitiveRegion :
    maximalPatient.InTransitiveRegion := by decide

/-! ### Upward/downward closure (§2.3, p.528) -/

/-- Agents are **upwards closed** in the agentivity dimension
    (p.528): if `a` qualifies as agent for a predicate
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
    (p.528): if `p` qualifies as patient (i.e., `p`
    has at most the persistence features of the verb's patient slot),
    then any `q ≤ p` also qualifies. A *more* affected entity (less
    persistence) can always fill a patient role.

    Formally: the set of acceptable patients for a verb with maximum
    persistence `maxPers` is `{p | p ≤ maxPers}`, which is a lower set. -/
theorem patient_downward_closed (maxPers p q : PersistenceLevel)
    (hp : p ≤ maxPers) (hqp : q ≤ p) :
    q ≤ maxPers :=
  le_trans hqp hp

/-! ### Persistence covering relations (Fig. 2) -/

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

end ArgumentStructure.AgentivityLattice
