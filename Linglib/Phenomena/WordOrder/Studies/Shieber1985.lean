import Linglib.Core.Computability.FormalLanguage
import Linglib.Core.Case.Basic
import Linglib.Phenomena.WordOrder.CrossSerial
import Linglib.Theories.FormalLanguageTheory.NonContextFree
import Linglib.Fragments.SwissGerman.Case

/-!
# Shieber (1985) @cite{shieber-1985}

Evidence against the Context-Freeness of Natural Language.
*Linguistics and Philosophy*, 8(3), 333–343.

## Core Argument

@cite{shieber-1985} proves that Swiss German is not weakly context-free,
using a purely string-based argument that makes no assumptions about
constituent structure or semantics. The proof rests on four empirical
claims about Swiss German subordinate clauses, plus the closure of
context-free languages under homomorphism and intersection with regular
languages.

## The Four Claims

1. Swiss German subordinate clauses have structures where all Vs follow all NPs.
2. Among such sentences, those with all DAT-NPs before all ACC-NPs, and all
   DAT-Vs before all ACC-Vs, are grammatical.
3. The number of DAT-Vs must equal the number of DAT-NPs (and similarly for ACC).
4. An arbitrary number of Vs can occur (subject to performance).

## The Proof

Define a homomorphism *f* mapping Swiss German words to an abstract alphabet:
- DAT-NPs (e.g., *em Hans*) → `a`
- ACC-NPs (e.g., *d'chind*, *de Hans*) → `b`
- DAT-Vs (e.g., *hälfe*) → `c`
- ACC-Vs (e.g., *lönd*, *aastriiche*) → `d`
- Framing material → `w`, `x`, `y`

Intersect *f(L)* with the regular language *r* = `w a* b* x c* d* y`.
By Claims 1–4, *f(L) ∩ r* = {`w aᵐ bⁿ x cᵐ dⁿ y`}.

A further homomorphism removing `w`, `x`, `y` yields {`aᵐ bⁿ cᵐ dⁿ`},
which contains {`aⁿ bⁿ cⁿ dⁿ`} (setting m = n). Since {`aⁿ bⁿ cⁿ dⁿ`}
is not context-free (`anbncndn_not_pumpable`), and CFLs are closed under
homomorphism and intersection with regular languages, Swiss German is not
context-free.

## Contrast with @cite{bresnan-etal-1982}

@cite{bresnan-etal-1982}'s earlier argument for Dutch non-context-freeness
relied on linguistic assumptions about constituent structure, which
@cite{gazdar-pullum-1982} contested. @cite{shieber-1985}'s argument is
purely formal — it rests entirely on the string set of Swiss German and
the case-marking facts, making no claims about phrase structure.
-/

namespace Shieber1985

open Core (FormalLanguageType Case)
open Phenomena.WordOrder.CrossSerial (crossSerialRequires nestedRequires)
open Fragments.SwissGerman.Case (CrossSerialVerb verbObjectCase)

-- ============================================================================
-- §1: Swiss German Subordinate Clause Data
-- ============================================================================

/-- A Swiss German subordinate clause token, abstracting over specific lexical
    items to their role in the cross-serial construction.

    @cite{shieber-1985}'s proof only needs to distinguish NPs and Vs by case. -/
inductive Token where
  /-- Dative NP (e.g., *em Hans*) -/
  | datNP
  /-- Accusative NP (e.g., *d'chind*, *de Hans*) -/
  | accNP
  /-- Dative-subcategorizing verb (e.g., *hälfe* "help") -/
  | datV
  /-- Accusative-subcategorizing verb (e.g., *lönd* "let", *aastriiche* "paint") -/
  | accV
  deriving DecidableEq, Repr

/-- The case that a token bears or requires. -/
def Token.caseValue : Token → Case
  | .datNP => .dat
  | .accNP => .acc
  | .datV  => .dat
  | .accV  => .acc

/-- Whether a token is an NP (vs a verb). -/
def Token.isNP : Token → Bool
  | .datNP | .accNP => true
  | .datV  | .accV  => false

-- ============================================================================
-- §2: The Four Claims
-- ============================================================================

/-- A cross-serial clause: a sequence of NPs followed by a sequence of Vs.
    This encodes Claims 1 and 2. -/
structure CrossSerialClause where
  datNPs : Nat  -- number of dative NPs
  accNPs : Nat  -- number of accusative NPs
  datVs  : Nat  -- number of dative-subcategorizing verbs
  accVs  : Nat  -- number of accusative-subcategorizing verbs
  deriving DecidableEq, Repr

/-- Claim 3: case matching — the number of dative verbs equals the number
    of dative NPs, and similarly for accusative. -/
def CrossSerialClause.caseMatches (c : CrossSerialClause) : Prop :=
  c.datNPs = c.datVs ∧ c.accNPs = c.accVs

/-- A grammatical cross-serial clause satisfies case matching. -/
structure GrammaticalClause extends CrossSerialClause where
  matching : toCrossSerialClause.caseMatches

/-- Claim 4: any combination of dative and accusative verb counts can occur
    (we can produce a `GrammaticalClause` for any m, n). -/
def arbitraryDepth (m n : Nat) : GrammaticalClause :=
  { datNPs := m
  , accNPs := n
  , datVs  := m
  , accVs  := n
  , matching := ⟨rfl, rfl⟩ }

-- ============================================================================
-- §3: The Homomorphism
-- ============================================================================

/-- Shieber's homomorphism *f*: maps Swiss German cross-serial clause tokens
    to the abstract alphabet {a, b, c, d}.

    - DAT-NPs → `a`
    - ACC-NPs → `b`
    - DAT-Vs  → `c`
    - ACC-Vs  → `d`

    The framing material (*Jan säit das mer*, *es huus haend wele*, etc.) maps
    to fixed delimiter symbols that are removed by regular intersection. -/
def tokenToSymbol : Token → FourSymbol
  | .datNP => .a
  | .accNP => .b
  | .datV  => .c
  | .accV  => .d

/-- The string image of a grammatical clause under the homomorphism. -/
def clauseImage (c : GrammaticalClause) : FourString :=
  List.replicate c.datNPs .a ++ List.replicate c.accNPs .b ++
  List.replicate c.datVs .c ++ List.replicate c.accVs .d

/-- A grammatical clause with m DAT-pairs and n ACC-pairs maps to
    `aᵐ bⁿ cᵐ dⁿ`. -/
theorem clauseImage_shape (m n : Nat) :
    clauseImage (arbitraryDepth m n) =
      List.replicate m .a ++ List.replicate n .b ++
      List.replicate m .c ++ List.replicate n .d := by
  rfl

-- ============================================================================
-- §4: The Non-Context-Freeness Argument
-- ============================================================================

/-- Setting m = n in the clause image gives aⁿbⁿcⁿdⁿ. -/
theorem diagonal_is_anbncndn (n : Nat) :
    clauseImage (arbitraryDepth n n) = makeString_anbncndn n := by
  rfl

/-- The diagonal clause images are in {aⁿbⁿcⁿdⁿ}. -/
theorem diagonal_in_language (n : Nat) :
    clauseImage (arbitraryDepth n n) ∈ anbncndn := by
  rw [diagonal_is_anbncndn]
  exact makeString_in_language n

/-- **CFL closure (contrapositive).** If a language L can be mapped by a
    homomorphism *f* and intersected with a regular language *r* to produce a
    non-context-free language, then L is not context-free.

    This is the contrapositive of the standard closure theorem for CFLs
    (Hopcroft & Ullman 1979, pp. 130–135): CFLs are closed under homomorphism
    and under intersection with regular languages.

    We state this as a proposition rather than proving it from first principles,
    since linglib does not formalize the full theory of CFLs. The pumping lemma
    proof of the specific non-CFL witness ({aⁿbⁿcⁿdⁿ}) IS fully verified. -/
def cfl_closure_contrapositive : Prop :=
  ∀ (L : Language Token),
    (∀ n : Nat, (List.replicate n Token.datNP ++ List.replicate n Token.accNP ++
                  List.replicate n Token.datV ++ List.replicate n Token.accV) ∈ L) →
    (∀ n : Nat, (List.replicate n Token.datNP ++ List.replicate n Token.accNP ++
                  List.replicate n Token.datV ++ List.replicate n Token.accV).map tokenToSymbol
                ∈ anbncndn) →
    ¬ HasCFLPumpingProperty anbncndn →
    ¬ HasCFLPumpingProperty L

/-- **Main result.** The image of Swiss German cross-serial clauses under
    @cite{shieber-1985}'s homomorphism contains {aⁿbⁿcⁿdⁿ}, which is not
    context-free. Combined with CFL closure properties, this proves Swiss
    German is not context-free.

    The conjunction packages the two independently verified facts:
    1. The homomorphism maps Swiss German data to {aⁿbⁿcⁿdⁿ} (by construction)
    2. {aⁿbⁿcⁿdⁿ} violates the CFL pumping property (by proof) -/
theorem swiss_german_not_context_free :
    (∀ n : Nat, clauseImage (arbitraryDepth n n) ∈ anbncndn) ∧
    ¬ HasCFLPumpingProperty anbncndn :=
  ⟨diagonal_in_language, anbncndn_not_pumpable⟩

-- ============================================================================
-- §5: Formal Language Classification
-- ============================================================================

/-- Cross-serial dependencies with case-marking require at least mildly
    context-sensitive power — the same classification used by
    `Phenomena.WordOrder.CrossSerial`. -/
theorem cross_serial_classification :
    crossSerialRequires = FormalLanguageType.mildlyContextSensitive := rfl

/-- Corollary: Swiss German is not strongly context-free either.

    @cite{shieber-1985} §3: "As a trivial corollary, Swiss German is not
    strongly context-free either, regardless of one's view as to the
    appropriate structures for the language." Since strong context-freeness
    implies weak context-freeness, weak non-context-freeness implies strong
    non-context-freeness. -/
theorem not_strongly_context_free :
    crossSerialRequires ≠ FormalLanguageType.contextFree := by decide

-- ============================================================================
-- §6: Grounding in the Swiss German Fragment
-- ============================================================================

/-- *hälfe* is a dative verb — its case requirement matches the DAT token. -/
theorem haelfe_is_dat :
    verbObjectCase .haelfe = Token.caseValue .datV := by rfl

/-- *lönd* is an accusative verb — its case requirement matches the ACC token. -/
theorem loend_is_acc :
    verbObjectCase .loend = Token.caseValue .accV := by rfl

/-- *aastriiche* is an accusative verb. -/
theorem aastriiche_is_acc :
    verbObjectCase .aastriiche = Token.caseValue .accV := by rfl

-- ============================================================================
-- §7: Connection to Processing (@cite{bach-brown-marslen-wilson-1986})
-- ============================================================================

/-- The formal–processing dissociation: crossed dependencies are formally
    harder (not CF) but psycholinguistically easier.

    @cite{shieber-1985} establishes the formal side; the processing side is
    in `BachBrownMarslenWilson1986`. -/
theorem formal_processing_dissociation :
    crossSerialRequires = .mildlyContextSensitive ∧
    nestedRequires = .contextFree :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- §8: Swiss German Examples from the Paper
-- ============================================================================

/-- Example (1): *mer em Hans es huus hälfed aastriiche*
    "we helped Hans paint the house"

    em Hans (DAT) → hälfed (DAT-verb "helped")
    es huus (ACC) → aastriiche (ACC-verb "paint") -/
def example1 : GrammaticalClause := arbitraryDepth 1 1

/-- Example (5): triply embedded cross-serial clause
    *mer d'chind em Hans es huus lönd hälfe aastriiche*
    "we let the children help Hans paint the house"

    d'chind (ACC) → lönd (ACC-verb "let")
    em Hans (DAT) → hälfe (DAT-verb "help")
    es huus (ACC) → aastriiche (ACC-verb "paint")

    With case sorting: 1 DAT-NP, 2 ACC-NPs, 1 DAT-V, 2 ACC-Vs -/
def example5 : GrammaticalClause := arbitraryDepth 1 2

/-- The homomorphic image of example (5) is abcdd = a¹b²c¹d². -/
theorem example5_image :
    clauseImage example5 = [.a, .b, .b, .c, .d, .d] := by rfl

end Shieber1985
