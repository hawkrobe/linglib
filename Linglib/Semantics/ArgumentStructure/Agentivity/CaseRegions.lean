import Linglib.Semantics.ArgumentStructure.Agentivity.Defs
import Linglib.Features.Case.Basic

/-!
# Case as a connected region of the agentivity lattice [grimm-2011]

[grimm-2011] §4's central claim: a core case marker corresponds to a
**connected region** of the agentivity lattice, spreading outwards from the
maximal agent and maximal patient nodes (Figs. 6–7). This file assigns each
`ParticipantType` its case region (`ParticipantType.toCaseRegion`), maps regions to
morphological cases under accusative and ergative alignment, and sharpens
the connectedness claim: each core region is an order **interval** anchored
at its pole (`toCaseRegion_eq_nomErg_iff` etc.), with order-convexity a
corollary. The dative region unifies recipients, experiencers, and second
arguments of two-place communication/service verbs (§5.1, Fig. 7).
-/

namespace ArgumentStructure

/-! ### Case regions (§4, Figs. 6–7) -/

/-- Case regions on the agentivity lattice. Per Grimm 2011 (abstract,
    §2.3, §4), a core case marker corresponds to a **connected region** of
    the lattice; the three core regions (`nomErg`, `accAbs`, `dative`) are
    order intervals anchored at the poles (`toCaseRegion_eq_nomErg_iff`
    etc.). `oblique` is the residual "middle region" (Grimm p.532–533) —
    not connected (`oblique_not_orderConvex`). -/
inductive CaseRegion where
  /-- Nominative (accusative systems) / Ergative (ergative systems):
      the region spreading from maximal agent. Marks subjects. -/
  | nomErg
  /-- Accusative (accusative systems) / Absolutive (ergative systems):
      the region spreading from maximal patient and existential
      persistence (beginning). Marks objects. -/
  | accAbs
  /-- Dative: the region around sentience + qualitative persistence
      (beginning). Marks recipients, experiencers, and second arguments
      of two-place communication/service verbs (§5.1, Fig. 7). -/
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
def ParticipantType.toCaseRegion (n : ParticipantType) : CaseRegion :=
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

/-! ### Core case regions are order intervals (Grimm 2011 abstract + §4)

The abstract's central claim — a core case marker is a connected region
"spreading outwards from the maximal agent and maximal patient nodes" — in
sharpened form: each core region is an order **interval** anchored at its
pole. NOM/ERG is the up-set of `minimalInstigator` (its top is
`maximalAgent = ⊤`); ACC/ABS runs from `maximalPatient` up to the
contact-verb patient; the dative sits above `sentientNonInstigator`.
Order-convexity ("connectedness") follows by transitivity. -/

/-- The bottom of the NOM/ERG interval: instigation alone, at total
    persistence — the minimal acceptable agent of *kill* (§2.3: natural
    forces such as electricity or the explosion). -/
def minimalInstigator : ParticipantType := ⟨.mk false false true false, ⊤⟩

/-- **NOM/ERG is the up-set of the minimal instigator** — the interval from
    `minimalInstigator` to `maximalAgent = ⊤`. -/
theorem ParticipantType.toCaseRegion_eq_nomErg_iff (n : ParticipantType) :
    n.toCaseRegion = .nomErg ↔ minimalInstigator ≤ n := by
  revert n; decide

/-- **ACC/ABS is the interval from the maximal patient to the contact-verb
    patient**: ⊥ agentivity, persistence between `exPersBeginning` and
    `quPersBeginning`. -/
theorem ParticipantType.toCaseRegion_eq_accAbs_iff (n : ParticipantType) :
    n.toCaseRegion = .accAbs ↔
      maximalPatient ≤ n ∧ n ≤ TransitivityRank.contact.patientType := by
  revert n; decide

/-- **The dative is the interval above `sentientNonInstigator`**:
    sentience without instigation, pinned at `quPersBeginning`. -/
theorem ParticipantType.toCaseRegion_eq_dative_iff (n : ParticipantType) :
    n.toCaseRegion = .dative ↔
      sentientNonInstigator ≤ n ∧
      n ≤ ⟨.mk true true false true, .quPersBeginning⟩ := by
  revert n; decide

/-- A predicate on a partial order is **order-convex** if it is closed
    under intervals: whenever `P a` and `P b` and `a ≤ x ≤ b`, also `P x`.
    This is the standard order-theoretic capture of "connected region" in
    a finite lattice. -/
def IsOrderConvex {α : Type*} [LE α] (P : α → Prop) : Prop :=
  ∀ ⦃a b x : α⦄, P a → P b → a ≤ x → x ≤ b → P x

/-- Connectedness of NOM/ERG, from the interval form. -/
theorem nomErg_orderConvex :
    IsOrderConvex (fun n : ParticipantType => n.toCaseRegion = .nomErg) := by
  intro a b x ha hb hax hxb
  rw [ParticipantType.toCaseRegion_eq_nomErg_iff] at ha ⊢
  exact ha.trans hax

/-- Connectedness of ACC/ABS, from the interval form. -/
theorem accAbs_orderConvex :
    IsOrderConvex (fun n : ParticipantType => n.toCaseRegion = .accAbs) := by
  intro a b x ha hb hax hxb
  rw [ParticipantType.toCaseRegion_eq_accAbs_iff] at ha hb ⊢
  exact ⟨ha.1.trans hax, hxb.trans hb.2⟩

/-- Connectedness of the dative, from the interval form. -/
theorem dative_orderConvex :
    IsOrderConvex (fun n : ParticipantType => n.toCaseRegion = .dative) := by
  intro a b x ha hb hax hxb
  rw [ParticipantType.toCaseRegion_eq_dative_iff] at ha hb ⊢
  exact ⟨ha.1.trans hax, hxb.trans hb.2⟩

/-- Counterexample showing `oblique` is NOT order-convex. With
    `a = ⟨{motion}, .quPersBeginning⟩` and `b = ⟨{motion, sentience, instigation},
    .quPersBeginning⟩`, both oblique, the in-between node
    `⟨{motion, sentience}, .quPersBeginning⟩` is dative. This is consistent with
    Grimm (p.533): oblique is the residual region between maximal agent and
    maximal patient, not a positively-characterised connected case. -/
theorem oblique_not_orderConvex :
    ¬ IsOrderConvex (fun n : ParticipantType => n.toCaseRegion = .oblique) := by
  intro h
  have habs := h (a := ⟨.mk false false false true, .quPersBeginning⟩)
                 (b := ⟨.mk false true true true, .quPersBeginning⟩)
                 (x := ⟨.mk false true false true, .quPersBeginning⟩)
                 (by decide) (by decide) (by decide) (by decide)
  exact absurd habs (by decide)

end ArgumentStructure
