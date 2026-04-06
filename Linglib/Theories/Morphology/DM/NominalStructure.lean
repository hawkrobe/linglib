/-!
# Nominal Phrase Structure (Distributed Morphology)

@cite{adamson-2024} @cite{myler-2016} @cite{kramer-2015}

Structural positions within the extended nominal projection, the
**Gender Locality Hypothesis** (GLH), and the possession-type distinction.

These types encode general claims about nominal structure that are
independent of any particular language:

- The nominal spine: √ROOT < n < (Num) < (Poss) < D
- The GLH: gender features on n must be valued within nP
- Inalienable vs alienable possession: nP-internal vs PossP-external

The GLH was proposed by @cite{adamson-2024}; the inalienable/alienable
structural distinction follows @cite{myler-2016} (following @cite{alexiadou-2003},
@cite{barker-1995}).
-/

namespace Theories.Morphology.DM

-- ============================================================================
-- § 1: Structural Positions in the Nominal Domain
-- ============================================================================

/-- Structural positions within and around the nominal phrase.

    @cite{adamson-2024} distinguishes positions by their locality to n,
    the locus of gender features:

    ```
    [DP D [NumP Num [PossP DP_alienable Poss [nP DP_inalienable [n √ROOT n]]]]]
    ```

    Only positions within nP are local enough to condition gender. -/
inductive NominalPosition where
  | root         -- √ROOT: the acategorial root itself
  | nHead        -- n: the categorizing head bearing gender features
  | specN        -- Spec,nP: inalienable possessor position
  | poss         -- Poss head: alienable possession head
  | specPoss     -- Spec,PossP: alienable possessor position
  | num          -- Num head: number (high/inflectional)
  | d            -- D head: definiteness
  deriving DecidableEq, Repr

/-- Is this position within nP?

    nP-internal positions: root, n head, Spec,nP (inalienable possessor).
    Everything else (Poss, Spec,PossP, Num, D) is outside nP. -/
def NominalPosition.isWithinNP : NominalPosition → Bool
  | .root     => true
  | .nHead    => true
  | .specN    => true
  | .poss     => false
  | .specPoss => false
  | .num      => false
  | .d        => false

-- ============================================================================
-- § 2: Gender Locality Hypothesis (@cite{adamson-2024} (15))
-- ============================================================================

/-- **Gender Locality Hypothesis** (GLH):

    "Gender features on n must be valued only within nP."
    (@cite{adamson-2024} (15))

    A position can influence gender assignment iff it is nP-internal.
    Elements introduced at Poss, Num, D, or higher cannot condition
    gender. -/
def genderLocalityHypothesis (pos : NominalPosition) : Bool :=
  pos.isWithinNP

theorem glh_inalienable_possessor :
    genderLocalityHypothesis .specN = true := rfl

theorem glh_alienable_possessor :
    genderLocalityHypothesis .specPoss = false := rfl

theorem glh_high_number_irrelevant :
    genderLocalityHypothesis .num = false := rfl

theorem glh_definiteness_irrelevant :
    genderLocalityHypothesis .d = false := rfl

theorem glh_root_and_n_local :
    genderLocalityHypothesis .root = true ∧
    genderLocalityHypothesis .nHead = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Possession Types (@cite{myler-2016})
-- ============================================================================

/-- Two types of possession, distinguished by structural position
    (@cite{adamson-2024}, following @cite{myler-2016}).

    - **Inalienable** (iPossession): possessor introduced in Spec,nP.
      The n head bears a selectional feature {D} (`CatHead.selectsD`).
      Semantically introduces a body-part-of / part-whole relation.
    - **Alienable** (aPossession): possessor introduced in Spec,PossP,
      mediated by a Poss head. Requires additional morphological marking
      in many languages (e.g., Teop *te*). -/
inductive PossessionType where
  | inalienable  -- iPossession: possessor in Spec,nP (local to n)
  | alienable    -- aPossession: possessor in Spec,PossP (nonlocal to n)
  deriving DecidableEq, Repr

def PossessionType.possessorPosition : PossessionType → NominalPosition
  | .inalienable => .specN
  | .alienable   => .specPoss

/-- Can this possession type affect gender assignment?
    Derived from the GLH and the possessor's structural position. -/
def PossessionType.canAffectGender (pt : PossessionType) : Bool :=
  genderLocalityHypothesis pt.possessorPosition

theorem inalienable_can_affect_gender :
    PossessionType.inalienable.canAffectGender = true := rfl

theorem alienable_cannot_affect_gender :
    PossessionType.alienable.canAffectGender = false := rfl

-- ============================================================================
-- § 4: Number Feature Position (@cite{adamson-2024} §5.1)
-- ============================================================================

/-- Number features can appear in two positions (@cite{adamson-2024} §5.1):

    - **Low number** (on n): derivational, can interact with gender.
      Evidence: Standard Italian *-a* plurals (masc.sg → fem.pl),
      Tunisian Arabic collectives (Dali & Mathieu 2021).
    - **High number** (on Num): inflectional, cannot interact with gender. -/
inductive NumberPosition where
  | onN    -- low/derivational number (within nP)
  | onNum  -- high/inflectional number (on Num, outside nP)
  deriving DecidableEq, Repr

def NumberPosition.toNominalPosition : NumberPosition → NominalPosition
  | .onN   => .nHead
  | .onNum => .num

theorem low_number_can_affect_gender :
    genderLocalityHypothesis (NumberPosition.onN.toNominalPosition) = true := rfl

theorem high_number_cannot_affect_gender :
    genderLocalityHypothesis (NumberPosition.onNum.toNominalPosition) = false := rfl

-- ============================================================================
-- § 5: External Features (@cite{adamson-2024} §5.2)
-- ============================================================================

/-- Functional heads outside nP whose features cannot affect gender
    assignment under the GLH (@cite{adamson-2024} §5.2). -/
inductive ExternalFeature where
  | case          -- on K or D
  | definiteness  -- on D
  | tense         -- on T (clausal, outside DP entirely)
  | aspect        -- on Asp (clausal)
  | voice         -- on Voice (clausal)
  deriving DecidableEq, Repr

/-- Map external features to their nearest NominalPosition (lower bound).
    Clausal features are outside DP entirely; D is the highest nominal
    position, itself already outside nP. -/
def ExternalFeature.toNominalPosition : ExternalFeature → NominalPosition
  | .case         => .d
  | .definiteness => .d
  | .tense        => .d
  | .aspect       => .d
  | .voice        => .d

theorem external_features_irrelevant (f : ExternalFeature) :
    genderLocalityHypothesis f.toNominalPosition = false := by
  cases f <;> rfl

-- ============================================================================
-- § 6: Possession–Gender Mechanisms (@cite{adamson-2024} §§2.3, 3–4)
-- ============================================================================

/-- Two mechanisms by which iPossession can affect gender
    (@cite{adamson-2024} §§2.3, 3–4):

    1. **Possessee gender**: the noun's gender is determined by WHETHER
       it has an iPossessor. The n head that introduces an iPossessor
       bears particular gender features. (Teop, Jarawara)
    2. **Inherited gender**: the noun's gender is determined by the
       GENDER OF the iPossessor. An unvalued gender probe on n is
       valued via Probe-Goal agreement with the iPossessor DP.
       (Yanyuwa, Coastal Marind) -/
inductive PossessionGenderMechanism where
  | possesseeGender   -- gender determined by having an iPossessor
  | inheritedGender   -- gender copied from iPossessor via agreement
  deriving DecidableEq, Repr

/-- Both mechanisms involve an iPossessor in Spec,nP. -/
def PossessionGenderMechanism.possessorPosition :
    PossessionGenderMechanism → NominalPosition
  | .possesseeGender  => .specN  -- gender determined by n head that licenses iPossessor
  | .inheritedGender  => .specN  -- gender copied from iPossessor via Agree

/-- Both mechanisms are consistent with the GLH: in both possessee gender
    (Teop, Jarawara) and inherited gender (Yanyuwa, Coastal Marind), the
    gender-affecting element is nP-internal. -/
theorem both_mechanisms_glh_consistent :
    genderLocalityHypothesis PossessionGenderMechanism.possesseeGender.possessorPosition = true ∧
    genderLocalityHypothesis PossessionGenderMechanism.inheritedGender.possessorPosition = true :=
  ⟨rfl, rfl⟩

end Theories.Morphology.DM
