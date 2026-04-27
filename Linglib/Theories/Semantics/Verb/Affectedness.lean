import Linglib.Theories.Semantics.Verb.EntailmentProfile
import Linglib.Theories.Semantics.Events.AffectednessHierarchy
import Linglib.Theories.Semantics.Events.ScalarResult

/-!
# Affectedness Hierarchy: EntailmentProfile Projection

@cite{beavers-2010} @cite{dowty-1991} @cite{beavers-2011}
@cite{beavers-koontz-garboden-2020}

The **affectedness hierarchy** is a projection of @cite{dowty-1991}'s P-Patient
entailments onto a four-level total order measuring the strength of truth
conditions about change in the affected argument.

The `AffectednessDegree` enum and the typeclass `extends` chain
(`IsUnspecifiedAffected → IsPotentialAffected → IsNonQuantizedAffected →
IsQuantizedAffected`) live in
`Theories/Semantics/Events/AffectednessHierarchy.lean` (substrate-level,
referenceable by K98 verb-class typeclasses). This file's role: project
Dowty's `EntailmentProfile` to `AffectednessDegree` and verify the
projection on canonical verb profiles. **The enum, `strength`, and `LE`
instance are re-exported here for backward compatibility with existing
consumers.**

## As a projection of EntailmentProfile

`profileToDegree` projects the 10-Boolean `EntailmentProfile` onto
`AffectednessDegree`, retaining only the P-Patient features relevant to
truth-conditional strength. The projection depends on exactly 4 of the
10 features: `changeOfState`, `incrementalTheme`, `causallyAffected`,
and `stationary`. All 5 P-Agent features and `dependentExistence` are
irrelevant (`profileToDegree_depends_only_on_patient`).

This is one of three canonical projections of EntailmentProfile:

- `AgentivityNode.fromEntailmentProfile` → agentivity lattice (@cite{grimm-2011})
- `profileToDegree` → affectedness hierarchy (@cite{beavers-2010})  ← this file
- `PersistenceLevel.fromPatientProfile` → persistence lattice (@cite{grimm-2011})

Each projection preserves different information and serves different
grammatical predictions:

| Projection            | Preserves              | Used for                    |
|-----------------------|------------------------|-----------------------------|
| AgentivityNode        | 4 P-Agent features     | Subject selection, case     |
| AffectednessDegree    | P-Patient strength     | MAP, direct/oblique         |
| PersistenceLevel      | Persistence pattern    | Case regions, DOM           |

## Grammatical consequence

The affectedness hierarchy predicts the **Morphosyntactic Alignment
Principle (MAP)**: when an argument alternates between direct and oblique
realization, the direct variant has truth conditions at least as strong
as the oblique. See `Phenomena/ArgumentStructure/Studies/Beavers2010.lean`
for the empirical verification.

## Interface to root semantics

`AffectednessDegree` relates to **three** levels of change-of-state
representation in the codebase:

- `EntailmentProfile.changeOfState` — the proto-patient entailment (this file's input)
- `MeaningComponents.changeOfState` — the surface diagnostic (in `Core/RootDimensions`)
- `RootEntailments.result` — whether the root itself entails change (in `Core/RootDimensions`)

These are NOT the same concept. @cite{beavers-koontz-garboden-2020} show
that surface CoS can come from either the root or the template. The
projection here operates on the proto-role level, which is the final
composed meaning — not the root-level or surface-diagnostic level.
-/

namespace Semantics.Verb.Affectedness

open Semantics.Verb.EntailmentProfile

-- ════════════════════════════════════════════════════
-- § 1. Re-exports from Events/AffectednessHierarchy
-- ════════════════════════════════════════════════════

/-! The 4-level Beavers affectedness enum, declared in
    `Theories/Semantics/Events/AffectednessHierarchy.lean` and
    re-exported here for backward compatibility with consumers
    (`Beavers2010`, `BeaversUdayana2022`, `StapsRooryck2024`,
    `AgentivityLattice`). -/
export Semantics.Events.AffectednessHierarchy (AffectednessDegree)

namespace AffectednessDegree
export Semantics.Events.AffectednessHierarchy.AffectednessDegree
  (unspecified potential nonquantized quantized strength)
end AffectednessDegree

-- ════════════════════════════════════════════════════
-- § 2. Projection: EntailmentProfile → AffectednessDegree
-- ════════════════════════════════════════════════════

/-- Project an EntailmentProfile onto the affectedness hierarchy.

    This is the canonical P-Patient projection: it retains truth-conditional
    strength while discarding the specific identity of the entailments.

    The projection depends on exactly 4 of the 10 features:
    - `changeOfState` and `incrementalTheme` (distinguish quantized/nonquantized)
    - `causallyAffected` and `stationary` (distinguish potential/unspecified)

    All 5 P-Agent features and `dependentExistence` are irrelevant
    (`profileToDegree_depends_only_on_patient`).

    @cite{beavers-2010} Table 5:
    | Dowty P-Patient         | Beavers entailment    |
    |-------------------------|-----------------------|
    | (a) changeOfState       | nonquantized change   |
    | (b) incrementalTheme    | totally traversed     |
    | (c) causallyAffected    | potential change       |
    | (d) stationary          | potential change       |
    | (e) dependentExistence  | (irrelevant here)     | -/
def profileToDegree (p : EntailmentProfile) : AffectednessDegree :=
  if p.incrementalTheme && p.changeOfState then .quantized
  else if p.changeOfState then .nonquantized
  else if p.causallyAffected || p.stationary then .potential
  else .unspecified

-- ════════════════════════════════════════════════════
-- § 3. Kernel Characterization
-- ════════════════════════════════════════════════════

/-- The projection depends only on {CoS, IT, CA, St}.
    Profiles agreeing on these four features always map to the same degree.
    The remaining 6 features (V, S, C, M, IE, DE) are irrelevant.

    This is the **forward kernel** characterization: sufficient conditions
    for two profiles to have the same image under `profileToDegree`. -/
theorem profileToDegree_depends_only_on_patient (p q : EntailmentProfile)
    (hcos : p.changeOfState = q.changeOfState)
    (hit : p.incrementalTheme = q.incrementalTheme)
    (hca : p.causallyAffected = q.causallyAffected)
    (hst : p.stationary = q.stationary) :
    profileToDegree p = profileToDegree q := by
  simp only [profileToDegree, hcos, hit, hca, hst]

/-- What `quantized` guarantees: both CoS and IT hold. -/
theorem quantized_implies (p : EntailmentProfile)
    (h : profileToDegree p = .quantized) :
    p.changeOfState = true ∧ p.incrementalTheme = true := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `nonquantized` guarantees: CoS without IT. -/
theorem nonquantized_implies (p : EntailmentProfile)
    (h : profileToDegree p = .nonquantized) :
    p.changeOfState = true ∧ p.incrementalTheme = false := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `potential` guarantees: no CoS, but CA or St. -/
theorem potential_implies (p : EntailmentProfile)
    (h : profileToDegree p = .potential) :
    p.changeOfState = false ∧
    (p.causallyAffected = true ∨ p.stationary = true) := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `unspecified` guarantees: no CoS, no CA, no St. -/
theorem unspecified_implies (p : EntailmentProfile)
    (h : profileToDegree p = .unspecified) :
    p.changeOfState = false ∧ p.causallyAffected = false ∧
    p.stationary = false := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

-- ════════════════════════════════════════════════════
-- § 4. Verification on Canonical Profiles
-- ════════════════════════════════════════════════════

/-- Build object: incremental theme + CoS → quantized. -/
theorem build_object_quantized :
    profileToDegree buildObjectProfile = .quantized := rfl

/-- Eat object: incremental theme + CoS → quantized. -/
theorem eat_object_quantized :
    profileToDegree eatObjectProfile = .quantized := rfl

/-- Kick object: CoS but no IT → nonquantized. -/
theorem kick_object_nonquantized :
    profileToDegree kickObjectProfile = .nonquantized := rfl

/-- See subject has no P-Patient features → unspecified. -/
theorem see_unspecified :
    profileToDegree seeSubjectProfile = .unspecified := rfl

/-- Die subject: CoS but no IT → nonquantized (the dying entity
    undergoes change but not incrementally). -/
theorem die_nonquantized :
    profileToDegree dieSubjectProfile = .nonquantized := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge: EntailmentProfile ↔ Typeclass Hierarchy
-- ════════════════════════════════════════════════════

/-! The Bool-side `profileToDegree p = .quantized` and the typeclass-side
    `IsQuantizedAffected θ` say the same thing about Beavers level —
    *modulo* the missing primitive that connects a verb's Dowty profile
    to its substrate-level θ relation.

    **Substrate gap (acknowledged):** linglib has no `HasObjectTheme V α β`
    typeclass providing the canonical θ for a fragment verb. EntailmentProfile
    is per-(verb, argument) Bool data; θ is the abstract semantic relation. A
    structural bridge between them requires per-verb instances binding the
    two — fragment-level work that is not yet built.

    **Available now:** an explicit-witness smart constructor for the
    `(profile, θ, scalar witnesses)` triple. The user provides BOTH the Bool
    declaration (the profile projects to .quantized) AND the scalar witness
    (`Quantized θ g_φ`); the smart constructor packages them into a
    typeclass instance, ensuring the two declarations are jointly consistent.

    Mathlib pattern: when a structural bridge requires content the substrate
    doesn't carry, expose an explicit-witness smart constructor (cf. mathlib's
    `MetricSpace.ofDistTopology` and similar). -/

open Semantics.Events.AffectednessHierarchy
open Semantics.Events.ScalarResult

/-- Joint consistency smart constructor: given a profile that projects to
    `.quantized` AND a scalar witness for some θ on a dimension δ,
    produce an `IsQuantizedAffected θ` instance.

    The two arguments encode parallel commitments — the Bool side
    (`p.profileToDegree = .quantized`) and the scalar side
    (`Quantized θ g_φ`). The smart constructor makes joint consistency
    structural: a consumer cannot construct an instance with a profile
    that projects to `.nonquantized` while declaring `Quantized` on the
    scalar side. -/
@[reducible]
def IsQuantizedAffected.ofProfileAndWitness {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) (p : EntailmentProfile)
    (_h_profile : profileToDegree p = .quantized)
    (forget : ∀ (x : α) (e : β),
              (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (g_φ : δ) (h_quantized : Quantized θ g_φ) :
    IsQuantizedAffected (δ := δ) θ :=
  IsQuantizedAffected.mk' forget g_φ h_quantized

end Semantics.Verb.Affectedness
