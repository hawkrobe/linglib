/-!
# Grammaticalization
@cite{anderson-2006} @cite{bybee-perkins-pagliuca-1994} @cite{lehmann-1985}
@cite{heine-kuteva-2002} @cite{hopper-traugott-2003}

Grammaticalization: the diachronic process by which lexical items become
grammatical markers. The canonical cline is:

    full verb → auxiliary → clitic → affix → zero

This process is cross-linguistically unidirectional: movement is always toward
greater morphological boundedness (@cite{lehmann-1985}, @cite{hopper-traugott-2003}).

## Main definitions

- `GramStage`: stages on the grammaticalization cline
- `GramStage.boundedness`: numeric encoding of morphological boundedness
- `AVCSource`: diachronic source constructions for auxiliary verb constructions

## Connections

- `Core.FormFrequency`: form-frequency correspondence is a parallel diachronic
  process (phonological erosion of frequent forms).
- `Core.Lexical.Binominal`: the bleaching cline for binominals (evaluative →
  pseudo-partitive → quantificational) is a specialized grammaticalization path.
- `Core.Subjectivity`: Traugott's subjectification cline is a semantic
  dimension of grammaticalization (see `Diachronic.Subjectification`).
-/

namespace Diachronic.Grammaticalization

-- ============================================================================
-- §1. The Grammaticalization Cline
-- ============================================================================

/-- Stage on the grammaticalization cline for verbal elements.
    @cite{anderson-2006} Ch 7, @cite{hopper-traugott-2003} Ch 6. -/
inductive GramStage where
  /-- Lexical verb with full argument structure. -/
  | fullVerb
  /-- Grammaticalized verb, restricted morphosyntax. -/
  | auxiliary
  /-- Phonologically reduced, syntactically dependent. -/
  | clitic
  /-- Bound morpheme, part of the verbal word. -/
  | affix
  /-- No overt marker (grammaticalization endpoint). -/
  | zero
  deriving DecidableEq, Repr, BEq

/-- Boundedness increases monotonically along the cline. -/
def GramStage.boundedness : GramStage → Nat
  | .fullVerb  => 0
  | .auxiliary => 1
  | .clitic    => 2
  | .affix     => 3
  | .zero      => 4

instance : LE GramStage where
  le a b := a.boundedness ≤ b.boundedness

instance : LT GramStage where
  lt a b := a.boundedness < b.boundedness

instance (a b : GramStage) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.boundedness ≤ b.boundedness))

instance (a b : GramStage) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.boundedness < b.boundedness))

/-- The cline is strictly ordered: each stage is more bound than the previous. -/
theorem cline_strictly_ordered :
    GramStage.fullVerb < GramStage.auxiliary ∧
    GramStage.auxiliary < GramStage.clitic ∧
    GramStage.clitic < GramStage.affix ∧
    GramStage.affix < GramStage.zero :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Unidirectionality: grammaticalization never reverses. Formalized as:
    if a language has a marker at stage s₂ that historically derives from
    stage s₁, then s₁ < s₂. -/
def isUnidirectional (_s₁ _s₂ : GramStage) (_h : _s₁ < _s₂) : Prop :=
  ¬(_s₂ < _s₁) -- follows from strict ordering, but makes the claim explicit

theorem unidirectional_of_lt {s₁ s₂ : GramStage} (h : s₁ < s₂) :
    isUnidirectional s₁ s₂ h :=
  Nat.not_lt.mpr (Nat.le_of_lt h)

-- ============================================================================
-- §2. Source Constructions
-- ============================================================================

/-- Diachronic source construction from which an AVC grammaticalizes.
    @cite{anderson-2006} §7, @cite{heine-kuteva-2002}. -/
inductive AVCSource where
  /-- Serial verb constructions: two verbs in sequence, one
      grammaticalizes into an auxiliary. Common in West African, SE Asian. -/
  | serialVerb
  /-- Complement-taking verb: matrix verb takes clausal complement,
      the matrix verb grammaticalizes. Common source for modals. -/
  | complementTaking
  /-- Motion verb: 'go'/'come' grammaticalize into future/past markers.
      Cross-linguistically one of the most common paths. -/
  | motionVerb
  /-- Postural verb: 'sit'/'stand'/'lie' grammaticalize into
      progressive/habitual aspect markers. -/
  | posturalVerb
  deriving DecidableEq, Repr, BEq

end Diachronic.Grammaticalization
