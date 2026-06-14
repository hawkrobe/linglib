/-!
# Quantification.Binominal — Defs
[saab-2026] [ten-wolde-2023]

Cross-linguistic types for binominal (N₁-of-N₂) constructions: the
3-way `BinominalType` (Saab 2026, Romance-cross-linguistic) and the
6-way `OfBinominalType` (ten-Wolde 2023, English-specific
grammaticalization cline). Plus the structural-property predicates,
the cline ordering, and diachronic-monotonicity theorems.

## Provenance

Moved from `Core/Lexical/Binominal.lean` in the cleanup that dissolved
`Core/Lexical/`. Lives at `Semantics/Quantification/` (sibling of the
existing `Binominal.lean` semantic-composition file, which consumes
`OfBinominalType` for `quantizingToOfBinominal` and other
construction-specific compositions). Naming follows the mathlib
`Defs.lean` idiom: this file holds the data + structural predicates;
the sibling `Binominal.lean` holds the semantic composition rules.

## Framework commitment

The 6-way `OfBinominalType` taxonomy and the grammaticalization cline
(`clinePosition`, `bleaching_monotone`, `plural_loss_monotone`,
`agreement_loosens_monotone`, etc.) follow [ten-wolde-2023]'s
specific framework. This is one carve-up among several active
frameworks for binominal noun phrase structure:

- [ten-wolde-2023]: 6-way grammaticalization cline (formalized here).
- Aarts 1998 *Binominal noun phrases in English*: different headedness
  diagnostics, no commitment to a single linear cline.
  Not currently in `references.bib`.
- den Dikken 2006 *Relators and Linkers*: RP (Relator Phrase) analysis
  where N-of-N is a predication structure with predicate inversion,
  not a cline. Den Dikken's evaluative BNPs work via predicate
  inversion, not via [N₁ of a]-as-modifier reanalysis.
  Not currently in `references.bib`.
- Selkirk 1977 / Akmajian-Lehrer measure-phrase analysis for
  pseudo-partitives.
- Constructional accounts (Bergen-Binsted, Goldberg): store
  [a hell of a N] as a stored construction with no head-switching.

The 3-way `BinominalType` (Saab 2026) is closer to consensus across
Romance binominals (pseudoPartitive / quantificational / qualitative)
but is not without contestation: e.g., Espinal & Mateu on Romance
evaluatives differ from Saab 2026's grouping.

UNVERIFIED: All ten-Wolde Table/§ references (`Table 4.2`, `§4.3.4`,
`§4.3.5`, `§4.4.5`, `Ch. 7`) cited from memory; verify before
treating as authoritative.
-/

namespace Quantification.Binominal

/-! ### : Three-Way Classification (Spanish, cross-linguistic) -/

/-- The three-way binominal classification ([saab-2026]).

This coarser-grained taxonomy covers the structural types attested
across Romance binominals. The finer-grained English subtypes are
captured by `OfBinominalType`. -/
inductive BinominalType where
  | pseudoPartitive   -- *un grupo de estudiantes* / *a glass of water*
  | quantificational  -- *un montón de estudiantes* / *a bunch of flowers*
  | qualitative       -- *una mierda de departamento* / *that idiot of a doctor*
  deriving DecidableEq, Repr

/-- Does this binominal type license NP-ellipsis?
    [saab-2026]: pseudo-partitive and quantificational yes;
    qualitative no. -/
def BinominalType.licensesNPE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Does the Num head in this structure carry [E]?
    [saab-2026]: Num[E] is present iff the complement of Num
    is a standard nP (not an EquP with an indexical empty noun). -/
def BinominalType.hasNumE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Core result: NP-ellipsis is licensed iff Num has [E]. -/
theorem npe_iff_numE (b : BinominalType) :
    b.licensesNPE = b.hasNumE := by
  cases b <;> rfl

/-! ### : Six-Way Classification (English, ten-Wolde 2023) -/

/-- Which noun is the semantic head of the binominal construction. -/
inductive BNPHead where
  | n₁   -- N₁ denotes the referent (N+PP, head-classifier)
  | n₂   -- N₂ denotes the referent (pseudo-partitive, evaluative, EM, BI)
  deriving Repr, DecidableEq

/-- The six types of *of*-binominal construction ([ten-wolde-2023]).

The ordering reflects the grammaticalization cline:
N+PP → Head-Classifier → Pseudo-partitive / Evaluative → EM → BI.

UNVERIFIED: Cline ordering and per-type characterization rests on
ten-Wolde's diachronic reconstruction; competing frameworks (Aarts,
den Dikken, Selkirk) carve the space differently. -/
inductive OfBinominalType where
  /-- N+PP: N₁ denotes a referent, PP ascribes a property.
      *the beast of the field*, *the hell of the damned* -/
  | nPP
  /-- Head-classifier: PP classifies the type or material of N₁.
      *a cake of rye*, *a beast of prey* -/
  | headClassifier
  /-- Pseudo-partitive: N₁ quantizes, N₂ is semantic head.
      *a glass of water*, *a piece of cake*, *a bunch of flowers* -/
  | pseudoPartitive
  /-- Evaluative BNP (EBNP): N₁ ascribes evaluative property to N₂.
      *that idiot of a doctor*, *a whale of a man* -/
  | evaluative
  /-- Evaluative Modifier (EM): [N₁ of a] is a complex modifier.
      *a hell of a time*, *a whale of a job* -/
  | evaluativeModifier
  /-- Binominal Intensifier (BI): [N₁ of a] intensifies Adj/Quant.
      *a hell of a good time*, *a whale of a lot of fun* -/
  | binominalIntensifier
  deriving Repr, DecidableEq

/-- Which noun is the semantic head of each construction type.

    For evaluative BNPs, N₂ is the semantic and discourse head, though
    syntactic evidence for headedness is inconclusive ([ten-wolde-2023]).
    For EM and BI, N₂ is semantic, syntactic, and discourse head. -/
def OfBinominalType.head : OfBinominalType → BNPHead
  | .nPP                  => .n₁
  | .headClassifier        => .n₁
  | .pseudoPartitive       => .n₂
  | .evaluative            => .n₂
  | .evaluativeModifier    => .n₂
  | .binominalIntensifier  => .n₂

/-- Is N₁ evaluative (expresses speaker attitude)? -/
def OfBinominalType.n₁IsEvaluative : OfBinominalType → Bool
  | .evaluative            => true
  | .evaluativeModifier    => true
  | .binominalIntensifier  => true
  | _                      => false

/-- Is N₁ referential (denotes an entity in the world)? -/
def OfBinominalType.n₁IsReferential : OfBinominalType → Bool
  | .nPP            => true
  | .headClassifier  => true
  | _                => false

/-- Does N₁ undergo semantic bleaching (loss of lexical content)?
    Bleaching increases along the grammaticalization cline.

    The *nature* of bleaching differs: pseudo-partitive N₁ (*glass*, *piece*)
    bleaches from referential noun → quantizing measure term; evaluative N₁
    bleaches from gradable predicate (EBNP) → evaluative modifier (EM) →
    degree intensifier (BI). -/
def OfBinominalType.n₁Bleached : OfBinominalType → Bool
  | .nPP                  => false
  | .headClassifier        => false
  | .pseudoPartitive       => true
  | .evaluative            => true
  | .evaluativeModifier    => true
  | .binominalIntensifier  => true

/-- Does *of* function as a linking device (no independent semantics)?
    In earlier constructions, *of* retains prepositional meaning
    (location, possession); in later ones it is a pure linker. -/
def OfBinominalType.ofIsLinker : OfBinominalType → Bool
  | .nPP                  => false  -- *of* = possession/location
  | .headClassifier        => true   -- *of* links classifier to head
  | .pseudoPartitive       => true
  | .evaluative            => true
  | .evaluativeModifier    => true
  | .binominalIntensifier  => true

/-- Can N₁ appear in plural form?
    Along the cline, N₁ loses the ability to inflect. -/
def OfBinominalType.n₁AllowsPlural : OfBinominalType → Bool
  | .nPP                  => true
  | .headClassifier        => true
  | .pseudoPartitive       => true
  | .evaluative            => true   -- N₁ agrees in number with N₂
  | .evaluativeModifier    => false  -- N₁ frozen in singular
  | .binominalIntensifier  => false

/-- Does Det₂ still mark number?
    In the EBNP, the second determiner marks number; in EM and BI
    it no longer does. -/
def OfBinominalType.det₂MarksNumber : OfBinominalType → Bool
  | .nPP                  => true
  | .headClassifier        => true
  | .pseudoPartitive       => true
  | .evaluative            => true   -- Det₂ still marks number
  | .evaluativeModifier    => false  -- Det₂ no longer marks number
  | .binominalIntensifier  => false

/-- Can *of* be replaced by a copular verb?
    In EBNP, *of* can sometimes be paraphrased with *be* (e.g.,
    "the doctor is an idiot"); in EM and BI it cannot. -/
def OfBinominalType.ofReplaceableByCopula : OfBinominalType → Bool
  | .nPP                  => false  -- *of* is a preposition
  | .headClassifier        => false
  | .pseudoPartitive       => false
  | .evaluative            => true   -- "the doctor is an idiot"
  | .evaluativeModifier    => false  -- "#the game is a hell"
  | .binominalIntensifier  => false

/-- Does [N₁ of a] function as a single constituent (modifier phrase)?
    The reanalysis of [N₁ of a] into a modifier unit is the defining
    structural change at the EM stage. -/
def OfBinominalType.n₁OfAIsConstituent : OfBinominalType → Bool
  | .evaluativeModifier    => true
  | .binominalIntensifier  => true
  | _                      => false

/-- Does N₁ allow descriptive premodification?
    EBNP strongly favors premodification of N₁ (*a total idiot of a doctor*);
    EM and BI block it because [N₁ of a] has been reanalyzed as a unit.
    Earlier constructions (N+PP, HC, PP) allow free premodification of N₁. -/
def OfBinominalType.n₁AllowsDescriptivePremod : OfBinominalType → Bool
  | .nPP                  => true
  | .headClassifier        => true
  | .pseudoPartitive       => true
  | .evaluative            => true   -- *a total idiot of a doctor*
  | .evaluativeModifier    => false  -- *#a total hell of a time*
  | .binominalIntensifier  => false

/-- Can N₂ be a mass noun?
    EBNP and EM restrict N₂ to count and collective nouns; BI extends
    to mass nouns (sporadically — not freely productive), reflecting
    the structural change where [N₁ of a] modifies a following
    adjective rather than N₂ directly. Earlier types (N+PP, HC, PP)
    have no such restriction. -/
def OfBinominalType.n₂AllowsMass : OfBinominalType → Bool
  | .evaluative           => false
  | .evaluativeModifier   => false
  | _                     => true

/-- Level of number agreement between N₁ and N₂. -/
inductive AgreementLevel where
  /-- N₁ and N₂ agree in number. -/
  | agree
  /-- N₁ and N₂ usually agree, with some exceptions. -/
  | usuallyAgree
  /-- N₁ and N₂ do not have to agree in number. -/
  | noAgreement
  deriving Repr, DecidableEq

/-- Numeric encoding: agreement loosens over time. -/
def AgreementLevel.toNat : AgreementLevel → Nat
  | .agree        => 0
  | .usuallyAgree => 1
  | .noAgreement  => 2

instance : LE AgreementLevel where
  le a b := a.toNat ≤ b.toNat

instance (a b : AgreementLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- N₁ & N₂ number agreement along the cline.
    Agreement loosens as grammaticalization proceeds:
    full agreement → usually agree → no agreement required. -/
def OfBinominalType.n₁N₂Agreement : OfBinominalType → AgreementLevel
  | .evaluativeModifier    => .usuallyAgree
  | .binominalIntensifier  => .noAgreement
  | _                      => .agree

/-- Is *of* obligatory in the construction?
    Mandatory for all types except BI, where it can be absent in
    reduced forms like *helluva*, *hella*. -/
def OfBinominalType.ofObligatory : OfBinominalType → Bool
  | .binominalIntensifier  => false
  | _                      => true

/-! ### : Grammaticalization Cline -/

/-- Position on the grammaticalization cline (0 = most lexical, 5 = most grammatical).

Supported by diachronic corpus evidence ([ten-wolde-2023]):
constructions appear in English in this order historically, and N₁ nouns
progress through these stages with increasing semantic bleaching. -/
def OfBinominalType.clinePosition : OfBinominalType → Nat
  | .nPP                  => 0
  | .headClassifier        => 1
  | .pseudoPartitive       => 2
  | .evaluative            => 3
  | .evaluativeModifier    => 4
  | .binominalIntensifier  => 5

/-- The cline is a total order: each type has a unique position. -/
theorem cline_injective (t₁ t₂ : OfBinominalType) :
    t₁.clinePosition = t₂.clinePosition → t₁ = t₂ := by
  cases t₁ <;> cases t₂ <;> simp [OfBinominalType.clinePosition]

/-- Bleaching increases along the cline: all types at position ≥ 2 are bleached. -/
theorem bleaching_after_position_2 (t : OfBinominalType) :
    2 ≤ t.clinePosition → t.n₁Bleached = true := by
  cases t <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁Bleached]

/-- Head switches from N₁ to N₂ at position 2. -/
theorem head_switches_at_2 (t : OfBinominalType) :
    (t.head = .n₁) = (t.clinePosition < 2) := by
  cases t <;> simp [OfBinominalType.head, OfBinominalType.clinePosition]

/-- N₁ plural ability is lost at position 4 (EM). -/
theorem plural_lost_at_4 (t : OfBinominalType) :
    4 ≤ t.clinePosition → t.n₁AllowsPlural = false := by
  cases t <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁AllowsPlural]

/-- Det₂ number marking is lost at the same point as N₁ plural (position 4). -/
theorem det₂_number_lost_at_4 (t : OfBinominalType) :
    4 ≤ t.clinePosition → t.det₂MarksNumber = false := by
  cases t <;> simp [OfBinominalType.clinePosition, OfBinominalType.det₂MarksNumber]

/-- [N₁ of a] constituency emerges at position 4 (EM). -/
theorem n₁_of_a_constituent_at_4 (t : OfBinominalType) :
    4 ≤ t.clinePosition → t.n₁OfAIsConstituent = true := by
  cases t <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁OfAIsConstituent]

/-- N₁ descriptive premodification is lost at position 4 (EM),
    together with N₁ plural and [N₁ of a] constituency. -/
theorem premod_lost_at_4 (t : OfBinominalType) :
    4 ≤ t.clinePosition → t.n₁AllowsDescriptivePremod = false := by
  cases t <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁AllowsDescriptivePremod]

/-- Monotonicity: once N₁ premodification is lost, it stays lost. -/
theorem premod_loss_monotone (t₁ t₂ : OfBinominalType) :
    t₁.clinePosition ≤ t₂.clinePosition →
    t₁.n₁AllowsDescriptivePremod = false → t₂.n₁AllowsDescriptivePremod = false := by
  cases t₁ <;> cases t₂ <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁AllowsDescriptivePremod]

/-- Copula replacement is unique to evaluative BNPs. -/
theorem copula_only_evaluative (t : OfBinominalType) :
    t.ofReplaceableByCopula = true → t = .evaluative := by
  cases t <;> simp [OfBinominalType.ofReplaceableByCopula]

/-- Evaluative types are always N₂-headed. -/
theorem evaluative_is_n₂_headed (t : OfBinominalType) :
    t.n₁IsEvaluative = true → t.head = .n₂ := by
  cases t <;> simp [OfBinominalType.n₁IsEvaluative, OfBinominalType.head]

/-- Referential types are always N₁-headed. -/
theorem referential_is_n₁_headed (t : OfBinominalType) :
    t.n₁IsReferential = true → t.head = .n₁ := by
  cases t <;> simp [OfBinominalType.n₁IsReferential, OfBinominalType.head]

/-- Monotonicity: once bleaching starts, it never reverses. -/
theorem bleaching_monotone (t₁ t₂ : OfBinominalType) :
    t₁.clinePosition ≤ t₂.clinePosition →
    t₁.n₁Bleached = true → t₂.n₁Bleached = true := by
  cases t₁ <;> cases t₂ <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁Bleached]

/-- Monotonicity: once N₁ plural is lost, it stays lost. -/
theorem plural_loss_monotone (t₁ t₂ : OfBinominalType) :
    t₁.clinePosition ≤ t₂.clinePosition →
    t₁.n₁AllowsPlural = false → t₂.n₁AllowsPlural = false := by
  cases t₁ <;> cases t₂ <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁AllowsPlural]

/-- Agreement loosens monotonically along the cline. -/
theorem agreement_loosens_monotone (t₁ t₂ : OfBinominalType) :
    t₁.clinePosition ≤ t₂.clinePosition →
    t₁.n₁N₂Agreement.toNat ≤ t₂.n₁N₂Agreement.toNat := by
  cases t₁ <;> cases t₂ <;> simp [OfBinominalType.clinePosition, OfBinominalType.n₁N₂Agreement, AgreementLevel.toNat]

/-- N₂ mass restriction is non-monotone: it narrows at the evaluative
    stage (positions 3–4) and widens again at BI (position 5), reflecting
    the structural change where [N₁ of a] shifts into AdjP. -/
theorem n₂_mass_nonmonotone :
    OfBinominalType.nPP.n₂AllowsMass = true ∧
    OfBinominalType.evaluative.n₂AllowsMass = false ∧
    OfBinominalType.binominalIntensifier.n₂AllowsMass = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- *of* becomes optional only at the most grammaticalized stage (BI). -/
theorem of_optional_only_at_bi (t : OfBinominalType) :
    t.ofObligatory = false → t.clinePosition = 5 := by
  cases t <;> simp [OfBinominalType.ofObligatory, OfBinominalType.clinePosition]

/-! ### : Cross-Linguistic Mapping -/

/-- Map the three-way Spanish type to the six-way English type.

    UNVERIFIED CROSS-LINGUISTIC CLAIM: this mapping presupposes that
    Spanish *qualitative* maps to English *evaluative* (Saab's *qualitative*
    ≡ ten-Wolde's *evaluative*). Espinal & Mateu on Romance evaluatives
    differ from Saab in details; verify whether the grouping survives
    their critique. -/
def BinominalType.toOfBinominalType : BinominalType → OfBinominalType
  | .pseudoPartitive  => .pseudoPartitive
  | .quantificational => .pseudoPartitive
  | .qualitative      => .evaluative

/-- Spanish qualitative maps to an evaluative (N₂-headed) English type. -/
theorem qualitative_is_evaluative :
    BinominalType.qualitative.toOfBinominalType.head = .n₂ := rfl

/-- Spanish pseudo-partitive/quantificational map to N₂-headed types. -/
theorem quantifying_is_n₂_headed (b : BinominalType) :
    b = .pseudoPartitive ∨ b = .quantificational →
    b.toOfBinominalType.head = .n₂ := by
  intro h; cases h with | inl h | inr h => subst h; rfl

end Quantification.Binominal
