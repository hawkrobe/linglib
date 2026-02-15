import Linglib.Theories.TruthConditional.Numeral.Polysemy

/-!
# Snyder (2026): Number Word Polysemy Data

Key example sentences from Snyder (2026, *L&P* 49:57–100) illustrating the
nine semantic functions of number words. These examples motivate Polymorphic
Contextualism: any adequate theory of number words must derive all nine uses
from a single lexical entry.

## The Core Data Pattern

Number words appear in at least nine syntactic/semantic configurations.
The challenge is that no single semantic type (e, ⟨e,t⟩, or ⟨⟨e,t⟩,t⟩)
directly generates all nine. Any theory must explain how the others arise.

## References

- Snyder, E. (2026). Numbers as kinds. *L&P* 49, 57–100.
-/

namespace Phenomena.NumeralSemantics.Snyder2026

open TruthConditional.Numeral.Polysemy (SemanticFunction)

-- ============================================================================
-- Section 1: The Nine Semantic Functions (Snyder (1a-f), (76g-j))
-- ============================================================================

/-- An example sentence exhibiting a semantic function of a number word. -/
structure NumberWordExample where
  /-- Example number from the paper -/
  exNum : String
  /-- The example sentence -/
  sentence : String
  /-- Which semantic function it exhibits -/
  function : SemanticFunction
  /-- Acceptability judgment -/
  acceptable : Bool
  deriving Repr

/-- (1a) Predicative: "Mars's moons are two (in number)." -/
def ex1a : NumberWordExample :=
  { exNum := "1a", sentence := "Mars's moons are two (in number)"
    function := .predicative, acceptable := true }

/-- (1b) Attributive: "Mars has two moons." -/
def ex1b : NumberWordExample :=
  { exNum := "1b", sentence := "Mars has two moons"
    function := .attributive, acceptable := true }

/-- (1c) Quantificational: "Two moons orbit Mars." -/
def ex1c : NumberWordExample :=
  { exNum := "1c", sentence := "Two moons orbit Mars"
    function := .quantificational, acceptable := true }

/-- (1d) Specificational: "The number of Mars's moons is two." -/
def ex1d : NumberWordExample :=
  { exNum := "1d", sentence := "The number of Mars's moons is two"
    function := .specificational, acceptable := true }

/-- (1e) Numeral: "Two is a prime number." -/
def ex1e : NumberWordExample :=
  { exNum := "1e", sentence := "Two is a prime number"
    function := .numeral, acceptable := true }

/-- (1f) Close appositive: "The number two is even." -/
def ex1f : NumberWordExample :=
  { exNum := "1f", sentence := "The number two is even"
    function := .closeAppositive, acceptable := true }

/-- All six core examples from (1). -/
def coreExamples : List NumberWordExample :=
  [ex1a, ex1b, ex1c, ex1d, ex1e, ex1f]

/-- All core examples are acceptable. -/
theorem core_examples_acceptable :
    coreExamples.all (·.acceptable) = true := rfl

-- ============================================================================
-- Section 2: The Identification Problem (§3.1, (20a-b))
-- ============================================================================

/-- A truth-value judgment on a close appositive with a specific number system. -/
structure IdentificationDatum where
  exNum : String
  sentence : String
  truthValue : Bool
  deriving Repr

/-- (20a) "The von Neumann ordinal two is two-membered." — TRUE
    (von Neumann 2 = {∅, {∅}}, which has two members) -/
def ex20a : IdentificationDatum :=
  { exNum := "20a"
    sentence := "The von Neumann ordinal two is two-membered"
    truthValue := true }

/-- (20b) "The Zermelo ordinal two is two-membered." — FALSE
    (Zermelo 2 = {{∅}}, which has one member) -/
def ex20b : IdentificationDatum :=
  { exNum := "20b"
    sentence := "The Zermelo ordinal two is two-membered"
    truthValue := false }

/-- (20a) and (20b) are jointly coherent: speakers accept both without
    sensing contradiction. This is the Identification Problem — any theory
    treating 'two' as a rigid designator wrongly predicts incoherence. -/
theorem identification_jointly_coherent :
    ex20a.truthValue = true ∧ ex20b.truthValue = false := ⟨rfl, rfl⟩

-- ============================================================================
-- Section 3: Taxonomic Interpretations (§3.4, (47))
-- ============================================================================

/-- (47d) "Two comes in several varieties." — acceptable.
    This requires 'two' to denote a kind with subkinds. -/
def ex47d : NumberWordExample :=
  { exNum := "47d", sentence := "Two comes in several varieties"
    function := .taxonomic, acceptable := true }

/-- (47e) "Each kind of two belongs to a different number system." — acceptable. -/
def ex47e : NumberWordExample :=
  { exNum := "47e"
    sentence := "Each kind of two belongs to a different number system"
    function := .taxonomic, acceptable := true }

-- ============================================================================
-- Section 4: Token and Kind Reference (§5.3, (76g-j))
-- ============================================================================

/-- (76g) "Two is next to a five on the board." — acceptable (token reference). -/
def ex76g : NumberWordExample :=
  { exNum := "76g", sentence := "Two is next to a five on the board"
    function := .tokenRef, acceptable := true }

/-- (76i) "Two comes in several varieties." — acceptable (kind reference). -/
def ex76i : NumberWordExample :=
  { exNum := "76i", sentence := "Two comes in several varieties"
    function := .kindRef, acceptable := true }

/-- All nine semantic functions are attested in acceptable sentences. -/
def allExamples : List NumberWordExample :=
  [ex1a, ex1b, ex1c, ex1d, ex1e, ex1f, ex47d, ex76g, ex76i]

theorem all_examples_acceptable :
    allExamples.all (·.acceptable) = true := rfl

theorem nine_functions_attested :
    allExamples.length = 9 := rfl

end Phenomena.NumeralSemantics.Snyder2026
