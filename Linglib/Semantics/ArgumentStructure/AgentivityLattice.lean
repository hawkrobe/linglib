import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Affectedness.Profile
import Linglib.Semantics.Lexical.LevinClassProfiles
import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Prod

/-!
# The Agentivity Lattice [grimm-2011]

[grimm-2011] reformulates [dowty-1991]'s proto-role entailments as
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
- `GrimmNode.toCaseRegion` → `Case` (case assignment)
- Transitivity hierarchy → `Tsunoda` verb classification
-/

namespace Semantics.ArgumentStructure.AgentivityLattice

open _root_.ArgumentStructure (EntailmentProfile)
open _root_.ArgumentStructure.EntailmentProfile
open Core

-- ════════════════════════════════════════════════════
-- § 1. Agentivity Primitives (Table 2, §2.1)
-- ════════════════════════════════════════════════════

/-- The four agentivity primitives (Table 2 (agentive properties), p.520).

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
      (p.521). -/
  instigation : Bool
  /-- +motion: the argument is in motion during the event. -/
  motion      : Bool
  deriving DecidableEq, Repr

/-- Validity constraint: volition presupposes sentience
    (p.521, following [dowty-1991] p.607). -/
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
-- § 2. Persistence Levels (§2.2, Fig. 2)
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 3. Combined Agentivity Lattice Node (Fig. 3)
-- ════════════════════════════════════════════════════

/-- A node in the full agentivity lattice = agentivity features ×
    persistence level, subject to:

    1. volition → sentience (agentivity constraint)
    2. If the argument does not exist at the beginning (totalNonPersistence
       or exPersEnd), it cannot have any agentivity properties
       (p.526–527). -/
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

/-- Full validity: both constraints satisfied. -/
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

-- ════════════════════════════════════════════════════
-- § 4. Named Participant Types
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 5. Transitivity Region (§3, Fig. 4)
-- ════════════════════════════════════════════════════

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
  deriving DecidableEq, Repr

/-- The canonical patient position for each transitivity class
    (Fig. 5). The agent position for all three classes is `effectorAgent`
    (Fig. 5, Ia/IIa share the same agent node; Grimm doesn't separately
    label IIIa). -/
def TransitivityClass.patientNode : TransitivityClass → GrimmNode
  | .resultativeEffective => ⟨⊥, .exPersBeginning⟩     -- Ip
  | .contact              => ⟨⊥, .quPersBeginning⟩     -- IIp
  | .pursuit              => ⟨⊥, .totalNonPersistence⟩ -- IIIp

-- ════════════════════════════════════════════════════
-- § 6. Case Regions (§4, Figs. 6–7)
-- ════════════════════════════════════════════════════

/-- Case regions on the agentivity lattice. Per Grimm 2011 (abstract,
    §2.3, §4), a core case marker corresponds to a **connected region** of
    the lattice; the three core regions (`nomErg`, `accAbs`, `dative`) are
    proved order-convex (`IsOrderConvex`) below. `oblique` is the residual
    "middle region" (Grimm p.533) — not claimed to be connected. -/
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
      (§5.1, Fig. 7). -/
  | dative
  /-- Oblique: the middle region between core cases. -/
  | oblique
  deriving DecidableEq, Repr

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

-- ── Connectedness of core case regions (Grimm 2011 abstract + §4) ──

/-- A predicate on a partial order is **order-convex** if it is closed
    under intervals: whenever `P a` and `P b` and `a ≤ x ≤ b`, also `P x`.
    This is the standard order-theoretic capture of "connected region" in
    a finite lattice. -/
def IsOrderConvex {α : Type*} [LE α] (P : α → Prop) : Prop :=
  ∀ ⦃a b x : α⦄, P a → P b → a ≤ x → x ≤ b → P x

-- Characterisation lemmas (single `decide` over 80 GrimmNode elements each)

private theorem GrimmNode.toCaseRegion_eq_nomErg_iff (n : GrimmNode) :
    n.toCaseRegion = .nomErg ↔
    n.agentivity.instigation = true ∧ n.persistence = .totalPersistence := by
  rcases n with ⟨⟨v, s, i, m⟩, p⟩
  cases v <;> cases s <;> cases i <;> cases m <;> cases p <;> decide

private theorem GrimmNode.toCaseRegion_eq_accAbs_iff (n : GrimmNode) :
    n.toCaseRegion = .accAbs ↔
    n.agentivity = ⊥ ∧
    (n.persistence = .exPersBeginning ∨ n.persistence = .quPersBeginning) := by
  rcases n with ⟨⟨v, s, i, m⟩, p⟩
  cases v <;> cases s <;> cases i <;> cases m <;> cases p <;> decide

private theorem GrimmNode.toCaseRegion_eq_dative_iff (n : GrimmNode) :
    n.toCaseRegion = .dative ↔
    n.agentivity.sentience = true ∧ n.agentivity.instigation = false ∧
    n.persistence = .quPersBeginning := by
  rcases n with ⟨⟨v, s, i, m⟩, p⟩
  cases v <;> cases s <;> cases i <;> cases m <;> cases p <;> decide

-- Componentwise Bool monotonicity for AgentivityNode (extracted from leBool)

private theorem AgentivityNode.le_instigation_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : a.instigation = true) : b.instigation = true := by
  have hbool : a.leBool b = true := hab
  cases hi : b.instigation
  · simp [AgentivityNode.leBool, h, hi] at hbool
  · rfl

private theorem AgentivityNode.le_sentience_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : a.sentience = true) : b.sentience = true := by
  have hbool : a.leBool b = true := hab
  cases hi : b.sentience
  · simp [AgentivityNode.leBool, h, hi] at hbool
  · rfl

private theorem AgentivityNode.ge_instigation_mono {a b : AgentivityNode}
    (hab : a ≤ b) (h : b.instigation = false) : a.instigation = false := by
  have hbool : a.leBool b = true := hab
  cases hi : a.instigation
  · rfl
  · simp [AgentivityNode.leBool, hi, h] at hbool

private theorem AgentivityNode.le_bot {a : AgentivityNode} (h : a ≤ ⊥) : a = ⊥ := by
  have hbool : a.leBool ⊥ = true := h
  rcases a with ⟨v, s, i, m⟩
  cases v <;> cases s <;> cases i <;> cases m <;>
    first | rfl | (simp [AgentivityNode.leBool] at hbool)

/-- The `nomErg` region is order-convex: any node between two nomErg nodes
    is itself nomErg. The region equals `{n | n.agentivity.instigation = true
    ∧ n.persistence = .totalPersistence}`, the intersection of an upper set
    (instigation = true) with the singleton at top persistence. -/
theorem nomErg_orderConvex :
    IsOrderConvex (fun n : GrimmNode => n.toCaseRegion = .nomErg) := by
  intro a b x ha hb hax hxb
  rw [GrimmNode.toCaseRegion_eq_nomErg_iff] at *
  refine ⟨AgentivityNode.le_instigation_mono hax.1 ha.1, ?_⟩
  have hpers : (.totalPersistence : PersistenceLevel) ≤ x.persistence := ha.2 ▸ hax.2
  exact le_antisymm le_top hpers

/-- The `accAbs` region is order-convex. It equals
    `{n | n.agentivity = ⊥ ∧ n.persistence ∈ {.exPersBeginning, .quPersBeginning}}`
    — the singleton at bottom agentivity intersected with the persistence
    interval `[.exPersBeginning, .quPersBeginning]`. -/
theorem accAbs_orderConvex :
    IsOrderConvex (fun n : GrimmNode => n.toCaseRegion = .accAbs) := by
  intro a b x ha hb hax hxb
  rw [GrimmNode.toCaseRegion_eq_accAbs_iff] at *
  refine ⟨AgentivityNode.le_bot (hb.1 ▸ hxb.1), ?_⟩
  -- x.persistence is in [a.persistence, b.persistence]; both endpoints in {exPB, qPB}.
  -- Case-split on x.persistence (5 cases) using the bounds to rule out the other 3.
  have hax_p : a.persistence ≤ x.persistence := hax.2
  have hxb_p : x.persistence ≤ b.persistence := hxb.2
  rcases ha.2 with hap | hap <;> rcases hb.2 with hbp | hbp <;>
    rw [hap] at hax_p <;> rw [hbp] at hxb_p <;>
    (try exact absurd (hax_p.trans hxb_p) (by decide)) <;>
    (cases hxp : x.persistence <;> rw [hxp] at hax_p hxb_p <;>
      first | (left; rfl) | (right; rfl) | exact absurd hax_p (by decide) |
              exact absurd hxb_p (by decide))

/-- The `dative` region is order-convex. It equals
    `{n | n.agentivity.sentience = true ∧ n.agentivity.instigation = false
    ∧ n.persistence = .quPersBeginning}` — sentience upper set ∩ instigation
    lower set ∩ persistence singleton. -/
theorem dative_orderConvex :
    IsOrderConvex (fun n : GrimmNode => n.toCaseRegion = .dative) := by
  intro a b x ha hb hax hxb
  rw [GrimmNode.toCaseRegion_eq_dative_iff] at *
  refine ⟨AgentivityNode.le_sentience_mono hax.1 ha.1,
          AgentivityNode.ge_instigation_mono hxb.1 hb.2.1, ?_⟩
  have h1 : x.persistence ≤ b.persistence := hxb.2
  have h2 : a.persistence ≤ x.persistence := hax.2
  rw [hb.2.2] at h1
  rw [ha.2.2] at h2
  exact le_antisymm h1 h2

/-- Counterexample showing `oblique` is NOT order-convex. With
    `a = ⟨{motion}, .quPersBeginning⟩` and `b = ⟨{motion, sentience, instigation},
    .quPersBeginning⟩`, both oblique, the in-between node
    `⟨{motion, sentience}, .quPersBeginning⟩` is dative. This is consistent with
    Grimm (p.533): oblique is the residual region between maximal agent and
    maximal patient, not a positively-characterised connected case. -/
theorem oblique_not_orderConvex :
    ¬ IsOrderConvex (fun n : GrimmNode => n.toCaseRegion = .oblique) := by
  intro h
  have habs := h (a := ⟨⟨false, false, false, true⟩, .quPersBeginning⟩)
                 (b := ⟨⟨false, true, true, true⟩, .quPersBeginning⟩)
                 (x := ⟨⟨false, true, false, true⟩, .quPersBeginning⟩)
                 (by decide) (by decide) (by decide) (by decide)
  exact absurd habs (by decide)

-- ════════════════════════════════════════════════════
-- § 7. Bridge to EntailmentProfile ([dowty-1991])
-- ════════════════════════════════════════════════════

/-- Map Dowty's P-Agent entailments to Grimm's agentivity features.

    The correspondence is direct for 3 of 4 features:
    - volition = volition
    - sentience = sentience
    - causation → instigation (p.521)
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
  decide

/-- Their meet is ⊥ (totalNonPersistence). -/
theorem exPersEnd_inf_exPersBeginning :
    PersistenceLevel.exPersEnd ⊓ PersistenceLevel.exPersBeginning = ⊥ := by
  decide

/-- Maximal agent is ⊤ on the combined lattice. -/
@[simp]
theorem maximalAgent_eq_top : maximalAgent = ⊤ := by decide

-- ════════════════════════════════════════════════════
-- § 9. Named Participant Verification
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 10. Grimm ↔ Dowty ASP Consistency
-- ════════════════════════════════════════════════════

/-- Grimm's agentivity lattice ordering is consistent with Dowty's
    PAgentDominates: if Grimm a ≤ Grimm b on agentivity, then
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
-- § 11. Dative Polysemy (§5.1)
-- ════════════════════════════════════════════════════

/-- The dative region unifies recipients, experiencers, and second
    arguments of communication/service verbs — they all share the
    semantic properties of **sentience** and **qualitative persistence
    (beginning)** (Fig. 7, p.536).

    Because `recipientNode` and `experiencerNode` are abbrevs of
    `sentientNonInstigatorNode`, the convergence is by construction; the
    theorem below asserts only that this single lattice position falls in
    the dative case region. -/
theorem sentientNonInstigator_in_dative :
    sentientNonInstigatorNode.toCaseRegion = .dative := rfl

-- ════════════════════════════════════════════════════
-- § 12. Upward/Downward Closure (§2.3, p.528)
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 13. Persistence Covering Relations (Fig. 2)
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

end Semantics.ArgumentStructure.AgentivityLattice
