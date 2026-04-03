import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile

/-!
# Affectedness Hierarchy

@cite{beavers-2010} @cite{dowty-1991}

The **affectedness hierarchy** is a projection of @cite{dowty-1991}'s P-Patient
entailments onto a four-level total order measuring the strength of truth
conditions about change in the affected argument.

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

namespace Semantics.Lexical.Verb.Affectedness

open Semantics.Lexical.Verb.EntailmentProfile

-- ════════════════════════════════════════════════════
-- § 1. AffectednessDegree (@cite{beavers-2010} §3.1)
-- ════════════════════════════════════════════════════

/-- Four degrees of affectedness, defined by increasingly weaker truth
    conditions about what change — if any — occurs in the event.

    Each degree is an existential generalization over the `result'` relation:
    - `quantized`:    φ → [result'(x, s, g_φ, e)]     (specific result state)
    - `nonquantized`: φ → ∃g[result'(x, s, g, e)]     (some change occurred)
    - `potential`:    φ → ◇∃g[result'(x, s, g, e)]    (change is possible)
    - `unspecified`:  φ → ∃θ[θ(x, e)]                 (x merely participates)

    The hierarchy forms a total order by truth-conditional entailment:
    quantized ≥ nonquantized ≥ potential ≥ unspecified. -/
inductive AffectednessDegree where
  | quantized     -- Specific result state entailed (telic, holistic effect)
  | nonquantized  -- Some change entailed, but not to a specific degree
  | potential     -- Change is possible but not entailed
  | unspecified   -- No change entailment at all (e.g. perception verbs)
  deriving DecidableEq, Repr

namespace AffectednessDegree

/-- Numeric strength: higher = stronger truth conditions. -/
def strength : AffectednessDegree → Nat
  | .quantized    => 3
  | .nonquantized => 2
  | .potential    => 1
  | .unspecified  => 0

/-- The hierarchy ordering: stronger degrees entail weaker ones. -/
def ge (a b : AffectednessDegree) : Bool :=
  a.strength ≥ b.strength

instance : LE AffectednessDegree where
  le a b := b.strength ≥ a.strength

instance (a b : AffectednessDegree) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (b.strength ≥ a.strength))

/-- Each degree entails all weaker degrees (implicational hierarchy). -/
theorem quantized_entails_nonquantized :
    ge .quantized .nonquantized = true := rfl

theorem nonquantized_entails_potential :
    ge .nonquantized .potential = true := rfl

theorem potential_entails_unspecified :
    ge .potential .unspecified = true := rfl

/-- Transitivity: quantized entails potential. -/
theorem quantized_entails_potential :
    ge .quantized .potential = true := rfl

/-- Transitivity: quantized entails unspecified. -/
theorem quantized_entails_unspecified :
    ge .quantized .unspecified = true := rfl

/-- Reflexivity. -/
theorem ge_refl (a : AffectednessDegree) : ge a a = true := by
  cases a <;> rfl

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

end Semantics.Lexical.Verb.Affectedness
