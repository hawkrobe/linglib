import Linglib.Core.InformationTheory
import Linglib.Core.MorphRule

/-!
# The Low Conditional Entropy Conjecture @cite{ackerman-malouf-2013}

Ackerman, F. & Malouf, R. (2013). Morphological Organization: The Low
Conditional Entropy Conjecture. *Language* 89(3), 429–464.

## E-complexity vs. I-complexity

Languages differ dramatically in their **enumerative complexity** (E-complexity):
how many inflection classes, allomorphic variants, and paradigm cells they
have. But this apparent complexity is misleading. The key question is
**integrative complexity** (I-complexity): given that a speaker knows *some*
forms of a lexeme, how hard is it to predict the *rest*?

## The LCEC

The Low Conditional Entropy Conjecture states that the average conditional
entropy of paradigm cells — how uncertain you are about one cell given another —
is uniformly low across typologically diverse languages, regardless of
E-complexity. Formally:

    I-complexity(L) = (1 / n(n-1)) · Σᵢ≠ⱼ H(Cᵢ | Cⱼ)

is low for all natural languages L, where Cᵢ ranges over paradigm cells and
H(Cᵢ | Cⱼ) is the conditional entropy of cell i given cell j.

## Implicative structure

The LCEC holds because morphological systems are organized by **implicative
relations**: knowing one form of a lexeme typically narrows down (or fully
determines) the others. These relations form a network whose density keeps
I-complexity low even when E-complexity is high.

## Main definitions

- `InflectionClass`: a paradigm row (cell index → surface form)
- `ParadigmSystem`: a collection of inflection classes with frequencies
- `cellEntropy`: H(Cᵢ) — entropy of a single paradigm cell
- `conditionalCellEntropy`: H(Cᵢ | Cⱼ) — conditional entropy of cell pair
- `iComplexity`: average conditional entropy across all cell pairs
- `eComplexity`: number of distinct inflection classes
- `LCECHolds`: predicate asserting I-complexity is below a threshold

## References

- Ackerman, F. & Malouf, R. (2013). Morphological Organization: The Low
  Conditional Entropy Conjecture. *Language* 89(3), 429–464.
- Stump, G. & Finkel, R. A. (2013). Morphological Typology: From Word to
  Paradigm. CUP.
- Blevins, J. P. (2006). Word-based morphology. *Journal of Linguistics*
  42(3), 531–573.
-/

namespace Morphology.WP

open Core.InformationTheory

-- ============================================================================
-- §1. Inflection Classes and Paradigm Systems
-- ============================================================================

/-- An inflection class: a function from cell index to surface realization.

    Two lexemes belong to the same inflection class iff they have identical
    paradigm structure (same mapping from cells to exponents, ignoring the
    stem). In practice, classes are identified by their *pattern* of
    allomorphic alternations, not by absolute forms. -/
structure InflectionClass (numCells : Nat) where
  /-- Realization of each cell (indexed 0..numCells-1) -/
  realize : Fin numCells → String

instance {n : Nat} : BEq (InflectionClass n) where
  beq a b := (List.finRange n).all λ i => a.realize i == b.realize i

/-- A paradigm system: the full inventory of inflection classes in a language,
    each paired with its frequency (proportion of lexemes in that class).

    - `numCells`: number of paradigm cells (e.g., 4 for a 4-cell verb system)
    - `entries`: inflection classes paired with their frequencies (should sum to 1) -/
structure ParadigmSystem (numCells : Nat) where
  /-- Inflection classes paired with their lexicon frequencies -/
  entries : List (InflectionClass numCells × ℚ)

-- ============================================================================
-- §2. Distribution Extraction
-- ============================================================================

/-- Group a tagged list by key, summing associated ℚ values.

    This is the core operation for extracting marginal and joint distributions
    from paradigm data: multiple inflection classes may share the same
    realization in a cell, so their frequencies need to be summed. -/
def groupBySum {α : Type} [BEq α] (tagged : List (α × ℚ)) : List (α × ℚ) :=
  tagged.foldl (λ acc (key, f) =>
    match acc.find? (λ (k, _) => k == key) with
    | some _ => acc.map (λ (k, p) => if k == key then (k, p + f) else (k, p))
    | none => acc ++ [(key, f)]
  ) []

/-- Extract the marginal distribution of realizations in a single cell.

    Groups inflection classes by their realization in cell `c` and sums
    their frequencies. Returns a distribution over surface forms. -/
def cellDistribution {n : Nat} (ps : ParadigmSystem n) (c : Fin n) :
    List (String × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => (ic.realize c, f))

/-- Extract the joint distribution of realizations in two cells.

    Returns pairs ((formᵢ, formⱼ), frequency) for all inflection classes,
    with shared patterns summed. -/
def jointCellDistribution {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : List ((String × String) × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => ((ic.realize ci, ic.realize cj), f))

-- ============================================================================
-- §3. Complexity Measures
-- ============================================================================

/-- E-complexity: the number of distinct inflection classes.

    This is the "enumerative" complexity that varies wildly across
    languages (e.g., Kwerba: 2 classes, Chiquihuitlán Mazatec: 109). -/
def eComplexity {n : Nat} (ps : ParadigmSystem n) : Nat :=
  ps.entries.length

/-- H(Cᵢ): Shannon entropy of a single paradigm cell.

    Measures how unpredictable the realization of cell `c` is when you
    know nothing about the lexeme. High entropy = many equiprobable
    realizations; low entropy = one dominant form. -/
def cellEntropy {n : Nat} (ps : ParadigmSystem n) (c : Fin n) : ℚ :=
  entropy (cellDistribution ps c)

/-- H(Cᵢ | Cⱼ): conditional entropy of cell `ci` given cell `cj`.

    Measures how uncertain you are about cell `ci`'s realization *after*
    learning cell `cj`'s realization. This is the core quantity in the LCEC:
    low H(Cᵢ | Cⱼ) means knowing form j strongly constrains form i.

    When H(Cᵢ | Cⱼ) = 0, cell j *fully determines* cell i — an
    implicative relation in the sense of Wurzel (1984). -/
def conditionalCellEntropy {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : ℚ :=
  conditionalEntropy (jointCellDistribution ps ci cj) (cellDistribution ps cj)

/-- I-complexity: average conditional entropy across all directed cell pairs.

    I-complexity = (1 / n(n-1)) · Σᵢ≠ⱼ H(Cᵢ | Cⱼ)

    This is Ackerman & Malouf's (2013) central measure. It quantifies
    how hard it is, on average, to predict one paradigm cell from another.
    The LCEC asserts this is uniformly low across languages. -/
def iComplexity {n : Nat} (ps : ParadigmSystem n) : ℚ :=
  let cells := List.finRange n
  let pairs := cells.flatMap λ ci => (cells.filter (· != ci)).map λ cj => (ci, cj)
  let total := pairs.map λ (ci, cj) => conditionalCellEntropy ps ci cj
  let sum := total.foldl (· + ·) 0
  let numPairs := n * (n - 1)
  if numPairs == 0 then 0 else sum / numPairs

-- ============================================================================
-- §4. The Low Conditional Entropy Conjecture
-- ============================================================================

/-- The LCEC holds for a paradigm system if its I-complexity is below
    a threshold (Ackerman & Malouf use ~1.5 bits as the empirical bound
    across their 10-language sample; the highest observed value is
    Chiquihuitlán Mazatec at 0.709 bits). -/
def LCECHolds {n : Nat} (ps : ParadigmSystem n) (threshold : ℚ) : Prop :=
  iComplexity ps ≤ threshold

-- ============================================================================
-- §5. Implicative Relations
-- ============================================================================

/-- An implicative relation between two cells: knowing cell `cj` fully
    determines cell `ci` (conditional entropy = 0).

    These are the building blocks of paradigm organization. A rich network
    of implicative relations is what keeps I-complexity low. -/
def isImplicative {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : Prop :=
  conditionalCellEntropy ps ci cj = 0

/-- A paradigm system has *transparent* structure if every cell pair is
    implicative — knowing any one cell fully determines all others.

    This is the strongest form of low I-complexity (I-complexity = 0).
    It corresponds to Carstairs-McCarthy's (2010) No Blur Principle /
    synonymy avoidance, which the LCEC subsumes as a special case. -/
def isTransparent {n : Nat} (ps : ParadigmSystem n) : Prop :=
  ∀ (ci cj : Fin n), ci ≠ cj → isImplicative ps ci cj

/-- Transparent paradigm systems have I-complexity = 0. -/
theorem transparent_iComplexity_zero {n : Nat} (ps : ParadigmSystem n)
    (h : isTransparent ps) : iComplexity ps = 0 := by
  sorry -- TODO: follows from all conditionalCellEntropy terms being 0

-- ============================================================================
-- §6. Connections to Core.MorphRule
-- ============================================================================

/-- Extract a `ParadigmSystem` from a list of `Stem`s.

    Each unique paradigm pattern (sequence of inflected forms) becomes an
    inflection class. The number of cells is `paradigm.length + 1` (base
    form + one per inflectional rule). This bridges `Core.MorphRule`'s
    rule-based view to the W&P observed-paradigm view. -/
def fromStems {σ : Type} (stems : List (Core.Morphology.Stem σ))
    (baseMeaning : σ) (numCells : Nat)
    (cellExtractor : List (String × Features × σ) → Fin numCells → String) :
    ParadigmSystem numCells :=
  let allParadigms := stems.map λ s =>
    let forms := s.allForms baseMeaning
    { realize := cellExtractor forms : InflectionClass numCells }
  -- Deduplicate: group by pattern and count frequencies
  let total := stems.length
  let unique := groupBySum (allParadigms.map λ ic => (ic, (1 : ℚ)))
  { entries := unique.map λ (ic, count) => (ic, count / total) }

end Morphology.WP
