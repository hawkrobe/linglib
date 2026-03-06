/-!
# Binominal Noun Phrase Classification

Cross-linguistic types for binominal (N₁-of-N₂) constructions.

Binominal NPs surface across languages with a linking element (English *of*,
Spanish *de*, French *de*) but differ in internal structure, headedness,
and N₁ semantics. This module provides a shared taxonomy drawn from
@cite{saab-2026} (Spanish) and @cite{ten-wolde-2023} (English).

## Taxonomy

The six-way classification follows @cite{ten-wolde-2023}'s hierarchy,
which subsumes @cite{saab-2026}'s three-way Spanish split:

| Type | Example | N₁ function | Head |
|------|---------|-------------|------|
| nPP | *the beast of the field* | referential | N₁ |
| headClassifier | *a cake of rye* | classifies N₂ | N₁ |
| pseudoPartitive | *a glass of water* | quantizes N₂ | N₂ |
| evaluative | *that idiot of a doctor* | evaluates N₂ | N₂ |
| evaluativeModifier | *a hell of a time* | [N₁ of a] modifies N₂ | N₂ |
| binominalIntensifier | *a whale of a good time* | [N₁ of a] intensifies Adj | N₂ |

The first three are **quantifying** BNPs; the last three are **quality** BNPs
(@cite{ten-wolde-2023}).
-/

namespace Core.Lexical.Binominal

-- ═══════════════════════════════════════════════════════════════
-- § 1: Three-Way Classification (Spanish, cross-linguistic)
-- ═══════════════════════════════════════════════════════════════

/-- The three-way binominal classification (@cite{saab-2026}).

This coarser-grained taxonomy covers the structural types attested
across Romance binominals. The finer-grained English subtypes are
captured by `OfBinominalType`. -/
inductive BinominalType where
  | pseudoPartitive   -- *un grupo de estudiantes* / *a glass of water*
  | quantificational  -- *un montón de estudiantes* / *a bunch of flowers*
  | qualitative       -- *una mierda de departamento* / *that idiot of a doctor*
  deriving DecidableEq, BEq, Repr

/-- Does this binominal type license NP-ellipsis?
    @cite{saab-2026}: pseudo-partitive and quantificational yes;
    qualitative no. -/
def BinominalType.licensesNPE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Does the Num head in this structure carry [E]?
    @cite{saab-2026}: Num[E] is present iff the complement of Num
    is a standard nP (not an EquP with an indexical empty noun). -/
def BinominalType.hasNumE : BinominalType → Bool
  | .pseudoPartitive  => true
  | .quantificational => true
  | .qualitative      => false

/-- Core result: NP-ellipsis is licensed iff Num has [E]. -/
theorem npe_iff_numE (b : BinominalType) :
    b.licensesNPE = b.hasNumE := by
  cases b <;> rfl

-- ═══════════════════════════════════════════════════════════════
-- § 2: Six-Way Classification (English)
-- ═══════════════════════════════════════════════════════════════

/-- Which noun is the semantic head of the binominal construction. -/
inductive BNPHead where
  | n₁   -- N₁ denotes the referent (N+PP, head-classifier)
  | n₂   -- N₂ denotes the referent (pseudo-partitive, evaluative, EM, BI)
  deriving Repr, DecidableEq, BEq

/-- The six types of *of*-binominal construction (@cite{ten-wolde-2023}).

The ordering reflects the grammaticalization cline:
N+PP → Head-Classifier → Pseudo-partitive / Evaluative → EM → BI. -/
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
  deriving Repr, DecidableEq, BEq

/-- Which noun is the semantic head of each construction type. -/
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
    Bleaching increases along the grammaticalization cline. -/
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

-- ═══════════════════════════════════════════════════════════════
-- § 3: Grammaticalization Cline
-- ═══════════════════════════════════════════════════════════════

/-- Position on the grammaticalization cline (0 = most lexical, 5 = most grammatical).

Supported by diachronic corpus evidence (@cite{ten-wolde-2023}):
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

/-- Evaluative types are always N₂-headed. -/
theorem evaluative_is_n₂_headed (t : OfBinominalType) :
    t.n₁IsEvaluative = true → t.head = .n₂ := by
  cases t <;> simp [OfBinominalType.n₁IsEvaluative, OfBinominalType.head]

/-- Referential types are always N₁-headed. -/
theorem referential_is_n₁_headed (t : OfBinominalType) :
    t.n₁IsReferential = true → t.head = .n₁ := by
  cases t <;> simp [OfBinominalType.n₁IsReferential, OfBinominalType.head]

-- ═══════════════════════════════════════════════════════════════
-- § 4: Cross-Linguistic Mapping
-- ═══════════════════════════════════════════════════════════════

/-- Map the three-way Spanish type to the six-way English type. -/
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

end Core.Lexical.Binominal
