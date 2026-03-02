import Linglib.Theories.Semantics.TypeTheoretic.Underspecification
import Linglib.Phenomena.Anaphora.DonkeyAnaphora
import Linglib.Phenomena.Anaphora.Coreference

/-!
# Bridge: TTR Underspecification -> Anaphora Data
@cite{chomsky-1981} @cite{cooper-2023} @cite{kanazawa-1994}

Connects TTR's localization (donkey anaphora) and binding theory
(reflexivization, anaphoric resolution) from
`Theories.Semantics.TypeTheoretic.Underspecification` to the empirical
data in `Phenomena.Anaphora.DonkeyAnaphora` and
`Phenomena.Anaphora.Coreference`.

Per-datum verification: each theorem verifies one data point from the
Phenomena files against TTR predictions.

-/

namespace Phenomena.Anaphora.Bridge.TypeTheoreticAnaphora

open Semantics.TypeTheoretic
open Phenomena.Anaphora.DonkeyAnaphora
open Phenomena.Anaphora.Coreference

-- ============================================================================
-- Bridge: TTR donkey predictions -> Phenomena/Anaphora/DonkeyAnaphora
-- ============================================================================

/-! ### Per-datum verification: TTR predictions match empirical data

Connect the TTR localization analysis to the theory-neutral donkey
anaphora data in `Phenomena.Anaphora.DonkeyAnaphora`. Each theorem
verifies one data point: the empirical datum records a reading as
available, and TTR produces a witness for that reading.

Changing a Ppty (e.g., making `beats` asymmetric) will break exactly
the theorems whose empirical predictions depend on it. -/

/-- Geach donkey: weak reading available -- TTR predicts checkmark.
    `geachDonkey.weakReading = true` and TTR produces a weak (localize) witness
    for both farmers in the scenario. -/
theorem geach_weak_available :
    geachDonkey.weakReading = true ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer2) :=
  ⟨rfl, ⟨farmer1_weak_donkey⟩, ⟨farmer2_weak_donkey⟩⟩

/-- Geach donkey: strong reading available -- TTR predicts checkmark.
    `geachDonkey.strongReading = true` and TTR produces a conditional
    strong witness for both farmers. -/
theorem geach_strong_available :
    geachDonkey.strongReading = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (strongDonkeyConditional .farmer2) :=
  ⟨rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer2_strong_conditional⟩⟩

/-- Geach donkey: bound reading -- TTR confirms the pronoun depends on
    the indefinite via parametric background (the donkey is the Bg). -/
theorem geach_bound_reading :
    geachDonkey.boundReading = true ∧
    farmerOwnsBeatsDonkey.Bg = DonkeyBg :=
  ⟨rfl, rfl⟩

/-- Strong dominant: both readings TTR-available (consistent with
    `strongDominant` recording both as available with strong preferred). -/
theorem strongDominant_readings_available :
    strongDominant.strongAvailable = true ∧
    strongDominant.weakAvailable = true ∧
    Nonempty (strongDonkeyConditional .farmer1) ∧
    Nonempty (𝔏 farmerOwnsBeatsDonkey .farmer1) :=
  ⟨rfl, rfl, ⟨farmer1_strong_conditional⟩, ⟨farmer1_weak_donkey⟩⟩

-- ============================================================================
-- Bridge: TTR binding -> Phenomena/Anaphora/Coreference (bridge theorem 3)
-- ============================================================================

/-! ### Per-datum verification: binding predictions match coreference data

Connect TTR's reflexivization and anaphoric resolution to the theory-neutral binding
data in `Phenomena.Anaphora.Coreference`.

@cite{cooper-2023} Ch8 section 8.3 gives a type-theoretic account of @cite{chomsky-1981}'s binding conditions:
- **Condition A** (reflexives must be locally bound): reflexivization forces argument identity
- **Condition B** (pronouns must be locally free): anaphoric resolution with disjoint reference
- **Complementary distribution**: reflexivization vs anaphoric resolution for the same position

Each theorem verifies one empirical pattern from `Coreference.lean`.
Changing `reflexivize` or `anaphoricResolve` will break these bridges. -/

/-- TTR's reflexivization predicts Binding Condition A:
    reflexives require a local antecedent because reflexivization forces argument
    identity within the local clause.
    Cooper Ch8, eq (84) + (88): reflexivization at VP level binds reflexive to subject.
    Matches `reflexivePattern` from Phenomena. -/
theorem reflexive_predicts_condA :
    reflexivePattern.requiresAntecedent = true ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- TTR predicts Binding Condition B:
    pronouns allow disjoint reference via anaphoric resolution with a
    constant function (the assignment provides the referent from
    non-local context). Cooper Ch8, eq (28).
    Matches `pronounPattern` from Phenomena. -/
theorem pronoun_predicts_condB :
    pronounPattern.requiresAntecedent = false ∧
    pronounPattern.antecedentDomain = some .nonlocal ∧
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Complementary distribution: reflexive and pronoun are predicted
    by different TTR mechanisms (reflexivization vs anaphoric resolution).
    Cooper Ch8, eqs (67)-(73): "Sam likes him" is NOT appropriate for
    "Sam likes himself" -- reflexivization must be used instead.
    Matches `complementaryDistributionData` from Phenomena. -/
theorem complementary_distribution_predicted :
    reflexivePattern.anaphorType = .reflexive ∧
    pronounPattern.anaphorType = .pronoun ∧
    Nonempty (ℜ like₈ .sam) ∧
    Nonempty (anaphoricResolve likeParam (fun _ => BindInd.bill) .sam) :=
  ⟨rfl, rfl, ⟨samLikesHimself⟩, ⟨samLikesBill⟩⟩

/-- The main bridge theorem (bridge theorem 3):
    TTR's reflexivization predicts the binding data.

    1. Reflexivization forces local coreference (Condition A): Cooper eq (84)
    2. Anaphoric resolution allows disjoint reference (Condition B): Cooper eq (28)
    3. The empirical coreference patterns match: @cite{chomsky-1981}
    4. Reflexivization = anaphoricResolve with id: reflexivization is a special case -/
theorem reflexive_predicts_binding :
    -- Reflexivization forces identity (Condition A)
    (∀ (R : BindInd → BindInd → Type) (x : BindInd), ℜ R x = R x x) ∧
    -- Pronoun resolution allows distinct arguments (Condition B)
    (∀ (y x : BindInd),
      anaphoricResolve likeParam (fun _ => y) x = like₈ x y) ∧
    -- Reflexivization is a special case of anaphoric resolution
    (anaphoricResolve likeParam id = ℜ like₈) ∧
    -- Matches empirical coreference patterns
    reflexivePattern.requiresAntecedent = true ∧
    pronounPattern.requiresAntecedent = false ∧
    reflexivePattern.antecedentDomain = some .local_ ∧
    pronounPattern.antecedentDomain = some .nonlocal :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Anaphora.Bridge.TypeTheoreticAnaphora
