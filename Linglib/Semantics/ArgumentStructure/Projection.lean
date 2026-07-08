import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.ParticipantType

/-!
# The Dowty→Grimm projection ([grimm-2011] §2.1)

The morphisms from [dowty-1991]'s `EntailmentProfile` to [grimm-2011]'s
lattice objects: `Agentivity.fromEntailmentProfile` (the four P-Agent
features minus independent existence), `PersistenceLevel.fromPatientProfile`
(the P-Patient entailments read as persistence), and their pairing
`ParticipantType.fromSubjectProfile` / `fromObjectProfile`.

The consistency theorems make the projection exact: its kernel
(`fromEntailmentProfile_eq_iff`), its monotonicity, the decomposition of
Dowty's flat count through it (`pAgentScore_decomposition`), dominance as
lattice order plus independent existence (`pAgentDominates_iff`), and the
Argument Selection Principle as lattice dominance
(`outranks_of_lattice_dominance`).
-/

namespace ArgumentStructure

/-- Map Dowty's P-Agent entailments to Grimm's agentivity features.

    The correspondence is direct for 3 of 4 features:
    - volition = volition
    - sentience = sentience
    - causation → instigation (p.521)
    - movement = motion

    Independent existence is handled by the persistence dimension. -/
def Agentivity.fromEntailmentProfile (p : EntailmentProfile) : Agentivity :=
  .mk p.volition p.sentience p.causation p.movement

/-- Two profiles project to the same agentivity node iff they agree on the four
lattice features: the projection drops independent existence and all five
Proto-Patient entailments ([grimm-2011] §2.1 recasts them on the persistence
axis). -/
theorem Agentivity.fromEntailmentProfile_eq_iff (p q : EntailmentProfile) :
    Agentivity.fromEntailmentProfile p = Agentivity.fromEntailmentProfile q ↔
      p.volition = q.volition ∧ p.sentience = q.sentience ∧
      p.causation = q.causation ∧ p.movement = q.movement := by
  simp [Agentivity.fromEntailmentProfile, Agentivity.mk_inj]

/-- Map Dowty's P-Patient entailments to Grimm's persistence level.

    This is an approximate mapping — Grimm's system is genuinely different
    from Dowty's. The diagnostic features:

    - DE + IT → exPersEnd: entity created incrementally (build, invent)
    - DE + ¬IT → exPersBeginning: entity ceases to exist (die, evaporate)
    - IT + ¬DE → exPersBeginning: entity consumed incrementally (eat)
    - CoS + ¬IT + ¬DE → quPersBeginning: changed but persists (move, dim)
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
    .quPersBeginning                            -- move, dim (changed but persists)
  else if p.causallyAffected || p.stationary then
    .totalPersistence                           -- see, kick objects (no entailed change)
  else
    .totalNonPersistence                        -- seek, want

/-- Map a full EntailmentProfile to a ParticipantType.

    The agentivity features come from the P-Agent entailments;
    the persistence level comes from the P-Patient entailments. -/
def ParticipantType.fromSubjectProfile (p : EntailmentProfile) : ParticipantType :=
  ⟨.fromEntailmentProfile p, .totalPersistence⟩

def ParticipantType.fromObjectProfile (p : EntailmentProfile) : ParticipantType :=
  ⟨.fromEntailmentProfile p, .fromPatientProfile p⟩

/-! ### Grimm ↔ Dowty ASP consistency -/

private theorem bImpl (a b : Bool) (h : a = true → b = true) :
    (!a || b) = true := by cases a <;> simp_all

/-- Grimm's agentivity lattice ordering is consistent with Dowty's
    PAgentDominates: if Grimm a ≤ Grimm b on agentivity, then
    Dowty a dominates Dowty b on P-Agent features.

    This holds because the feature-to-feature mapping is a bijection
    on the first 4 P-Agent features (volition, sentience, causation=instigation,
    movement=motion). -/
theorem grimm_agentivity_consistent_with_dowty
    (p q : EntailmentProfile)
    (h : Agentivity.fromEntailmentProfile p ≤
         Agentivity.fromEntailmentProfile q) :
    (!p.volition || q.volition) = true ∧
    (!p.sentience || q.sentience) = true ∧
    (!p.causation || q.causation) = true ∧
    (!p.movement || q.movement) = true := by
  obtain ⟨h1, h2, h3, h4⟩ := (Agentivity.le_iff _ _).mp h
  exact ⟨bImpl _ _ h1, bImpl _ _ h2, bImpl _ _ h3, bImpl _ _ h4⟩

/-- The Dowty→Grimm projection is monotone: if one EntailmentProfile
    dominates another on P-Agent features, the projected agentivity values
    are ordered. -/
theorem fromEntailmentProfile_monotone
    (p q : EntailmentProfile)
    (hv : p.volition = true → q.volition = true)
    (hs : p.sentience = true → q.sentience = true)
    (hc : p.causation = true → q.causation = true)
    (hm : p.movement = true → q.movement = true) :
    Agentivity.fromEntailmentProfile p ≤
    Agentivity.fromEntailmentProfile q :=
  (Agentivity.le_iff _ _).mpr ⟨hv, hs, hc, hm⟩

/-! ### Dominance is lattice order plus independent existence

[dowty-1991]'s five P-Agent entailments (Table 1 of [grimm-2011]) split into
[grimm-2011]'s four agentivity primitives (Table 2) plus independent
existence, which Grimm recasts on the persistence axis (§2.1). The three
theorems below make the split exact: the flat count decomposes through the
projection, the lattice's feature count is monotone in the inclusion order
(§2.3: higher in the lattice = higher degree of agentivity), and Dowty's
`PAgentDominates` is precisely lattice order plus an independent-existence
implication (§2.2). -/

/-- Feature count is monotone in the inclusion order ([grimm-2011] §2.3):
    ascending the Fig. 1 lattice never loses agentivity features. -/
theorem Agentivity.featureCount_monotone : Monotone Agentivity.featureCount :=
  fun _ _ h =>
    (by decide : ∀ a b : Agentivity, a ≤ b → a.featureCount ≤ b.featureCount) _ _ h

/-- Dowty's flat P-Agent count decomposes through the projection: the four
    lattice features ([grimm-2011] Table 2) plus independent existence,
    the one Table 1 entailment Grimm moves to the persistence axis (§2.1). -/
theorem pAgentScore_decomposition (p : EntailmentProfile) :
    p.pAgentScore =
      (Agentivity.fromEntailmentProfile p).featureCount +
        p.independentExistence.toNat :=
  rfl

/-- Dowty's subset dominance is exactly Grimm's lattice order plus an
    independent-existence implication ([grimm-2011] §2.2, Fig. 1): the
    projection loses no dominance information. Derived from
    `fromEntailmentProfile_monotone` and
    `grimm_agentivity_consistent_with_dowty`. -/
theorem pAgentDominates_iff (p q : EntailmentProfile) :
    PAgentDominates p q ↔
      Agentivity.fromEntailmentProfile q ≤
        Agentivity.fromEntailmentProfile p ∧
      (q.independentExistence = true → p.independentExistence = true) := by
  constructor
  · rintro ⟨hv, hs, hc, hm, hie⟩
    exact ⟨fromEntailmentProfile_monotone q p hv hs hc hm, hie⟩
  · rintro ⟨hle, hie⟩
    obtain ⟨h1, h2, h3, h4⟩ := grimm_agentivity_consistent_with_dowty q p hle
    exact ⟨fun hq => by simpa [hq] using h1, fun hq => by simpa [hq] using h2,
           fun hq => by simpa [hq] using h3, fun hq => by simpa [hq] using h4, hie⟩

/-- [grimm-2011]'s Argument Selection Principle as lattice dominance: if
    `subj`'s agentivity node strictly dominates `obj`'s and independent
    existence is preserved, `subj` is selected — for every profile pair,
    via `pAgentDominates_iff`, not per-verb checking. -/
theorem outranks_of_lattice_dominance (subj obj : EntailmentProfile)
    (hlt : Agentivity.fromEntailmentProfile obj <
      Agentivity.fromEntailmentProfile subj)
    (hIE : obj.independentExistence = true → subj.independentExistence = true) :
    OutranksForSubject subj obj :=
  .inl ⟨(pAgentDominates_iff subj obj).mpr ⟨hlt.le, hIE⟩,
    fun hqp =>
      absurd ((pAgentDominates_iff obj subj).mp hqp).1
        (lt_iff_le_not_ge.mp hlt).2⟩

end ArgumentStructure
