/-!
# Paradigm Function Morphology (PFM): Core
@cite{stump-2001}

Paradigm Function Morphology (@cite{stump-2001}) is a lexicalist,
parallel, process-based, realizational theory of morphology. Its
core objects are:

- **Lexeme**: a stored unit of lexical meaning and syntactic category
  (e.g., CABIN, EAT). Not a word form — a lexeme is the abstract
  entity that a paradigm is *of*.

- **Morphosyntactic property set (σ)**: a set of contrastive inflectional
  features that uniquely picks out a cell in a paradigm (e.g.,
  {PRESENT, 3, SG} for English verbs).

- **Paradigm function**: maps a (lexeme, σ) pair to a word form. The
  paradigm function is decomposed into ordered **rule blocks**, each
  contributing one "layer" of inflection.

- **Realization rule (RR)**: a morphophonological process within a rule
  block that transforms a phonological stem in the context of a σ.
  The Elsewhere Condition resolects among competing RRs in the same block.

- **Rule of Referral**: a rule that states an identity between paradigm
  cells — the exponent for one cell is the same as for another. Used
  to capture metasyncretisms. @cite{zwicky-1985}

@cite{kalin-bjorkman-etal-2026} §2.2, Table 2, Table 4.
-/

namespace Morphology.PFM

-- ============================================================================
-- §1: Lexeme and Morphosyntactic Property Sets
-- ============================================================================

/-- A morphosyntactic property set: the bundle of contrastive
    inflectional features that identifies a paradigm cell.

    In PFM, σ is a set of feature-value pairs. We represent it as
    a list of features for simplicity. The Elsewhere Condition
    operates over subset relations on these sets. -/
structure MorphPropertySet (Feature : Type) where
  features : List Feature
  deriving DecidableEq, Repr, BEq

/-- A lexeme: an abstract unit of lexical meaning, identified by a
    name and a syntactic category. A lexeme has a **root/stem** (the
    phonological base that realization rules operate on) and a
    **paradigm** (the set of all σs that apply to it). -/
structure Lexeme where
  name : String
  category : String
  stem : String
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Realization Rules
-- ============================================================================

/-- A realization rule: a morphophonological process that transforms
    a stem in the context of a morphosyntactic property set.

    `Feature`: the type of morphosyntactic features.

    A RR specifies:
    1. A **context**: which features in σ license the rule
    2. A **category restriction**: which lexeme categories it applies to
    3. A **realization**: the stem → stem transformation

    The Elsewhere Condition selects the most specific applicable RR
    in each rule block. -/
structure RealizationRule (Feature : Type) where
  /-- Which features must be present in σ for this rule to apply. -/
  context : List Feature
  /-- Which lexeme category this rule applies to (e.g., "verb"). -/
  category : String
  /-- The stem transformation. -/
  realize : String → String
  /-- Specificity: number of features in the context. Used for
      Elsewhere Condition resolution. -/
  specificity : Nat := 0

/-- Does a realization rule match a given property set and lexeme? -/
def RealizationRule.matches {Feature : Type} [BEq Feature]
    (rr : RealizationRule Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : Bool :=
  lex.category == rr.category &&
  rr.context.all (σ.features.contains ·)

-- ============================================================================
-- §3: Rule Blocks
-- ============================================================================

/-- A rule block: an ordered set of competing realization rules.
    Each block contributes one "layer" of morphological realization.
    Within a block, the Elsewhere Condition selects the most specific
    applicable rule. -/
structure RuleBlock (Feature : Type) where
  /-- The block's label (e.g., "Block I", "Block II"). -/
  label : String
  /-- The rules in this block, in no particular order (the Elsewhere
      Condition handles selection). -/
  rules : List (RealizationRule Feature)

/-- Apply a rule block to a stem: find the most specific matching
    rule and apply its transformation. Returns `none` if no rule
    matches (the block is vacuously satisfied). -/
def RuleBlock.apply {Feature : Type} [BEq Feature]
    (block : RuleBlock Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme)
    (stem : String) : Option String :=
  let matching := block.rules.filter (·.matches σ lex)
  let best := matching.foldl (init := none) fun acc rr =>
    match acc with
    | none => some rr
    | some prev =>
      if rr.specificity > prev.specificity then some rr
      else some prev
  best.map (·.realize stem)

-- ============================================================================
-- §4: Paradigm Function
-- ============================================================================

/-- A paradigm function: an ordered sequence of rule blocks that,
    applied in order, maps a (stem, σ) pair to a word form.

    The paradigm function is the central object of PFM. Each block
    applies in sequence, threading the stem through. If a block has
    no matching rule, the stem passes through unchanged. -/
structure ParadigmFunction (Feature : Type) where
  blocks : List (RuleBlock Feature)

/-- Apply a paradigm function: thread the stem through all blocks
    in order. -/
def ParadigmFunction.apply {Feature : Type} [BEq Feature]
    (pf : ParadigmFunction Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : String :=
  pf.blocks.foldl (init := lex.stem) fun stem block =>
    (block.apply σ lex stem).getD stem

-- ============================================================================
-- §5: Rules of Referral
-- ============================================================================

/-- A Rule of Referral (@cite{zwicky-1985}, @cite{stump-2001}):
    states that the realization of one paradigm cell is identical
    to the realization of another.

    Used to capture **metasyncretisms** — syncretisms that hold
    across an entire morphological system (e.g., gender neutralization
    in the plural in Amharic).

    A referral maps property set σ₁ to σ₂, meaning: "the word form
    for σ₁ is whatever the paradigm function yields for σ₂." -/
structure RuleOfReferral (Feature : Type) where
  /-- The property set whose realization is being referred. -/
  source : MorphPropertySet Feature
  /-- The property set it is referred *to*. -/
  target : MorphPropertySet Feature

/-- Apply a Rule of Referral: if the input σ matches the source,
    evaluate the paradigm function at the target σ instead. -/
def RuleOfReferral.apply {Feature : Type} [BEq Feature]
    (ref : RuleOfReferral Feature)
    (pf : ParadigmFunction Feature)
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : Option String :=
  if σ == ref.source then
    some (pf.apply ref.target lex)
  else
    none

-- ============================================================================
-- §6: Full PFM derivation
-- ============================================================================

/-- Derive a word form in PFM: apply referrals first (if any match),
    then fall back to the paradigm function. -/
def derive {Feature : Type} [BEq Feature]
    (pf : ParadigmFunction Feature)
    (referrals : List (RuleOfReferral Feature))
    (σ : MorphPropertySet Feature)
    (lex : Lexeme) : String :=
  match referrals.findSome? (·.apply pf σ lex) with
  | some form => form
  | none => pf.apply σ lex

end Morphology.PFM
