import Linglib.Semantics.ArgumentStructure.Agentivity.Defs
import Linglib.Features.Case.Basic

/-!
# Case as a connected region of the agentivity lattice [grimm-2011]

[grimm-2011] §4's central claim: a core case marker corresponds to a
**connected region** of the agentivity lattice, spreading outwards from the
maximal agent and maximal patient nodes (Figs. 6–7). This file assigns each
`GrimmNode` its case region (`GrimmNode.toCaseRegion`), maps regions to
morphological cases under accusative and ergative alignment, and proves the
connectedness claim for the three core regions as order-convexity
(`IsOrderConvex`). The dative region unifies recipients, experiencers, and
benefactives (§5.1, Fig. 7).
-/

namespace ArgumentStructure.AgentivityLattice

/-! ### Case regions (§4, Figs. 6–7) -/

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

/-! ### Connectedness of core case regions (Grimm 2011 abstract + §4) -/

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
  refine ⟨le_bot_iff.mp (hb.1 ▸ hxb.1), ?_⟩
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

/-! ### Dative polysemy (§5.1) -/

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

end ArgumentStructure.AgentivityLattice
