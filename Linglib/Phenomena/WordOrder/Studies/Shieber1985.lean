import Linglib.Core.Computability.ContextFreeGrammar.Closure
import Linglib.Core.Computability.NonContextFree.AnBnCnDn
import Linglib.Core.Computability.NonContextFree.AmBnCmDn
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Core.Case.Basic
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
context-free languages under string homomorphism and intersection with
regular languages (axiomatized in `Linglib.Core.Computability.ContextFreeGrammar.Closure`,
citing @cite{hopcroft-ullman-1979}).

## The Four Claims

1. Swiss German subordinate clauses have structures where all Vs follow all NPs.
2. Among such sentences, those with all DAT-NPs before all ACC-NPs, and all
   DAT-Vs before all ACC-Vs, exist as a *regular-intersection-filterable*
   subset. This is **not** a grammaticality condition on Swiss German itself
   — SG freely allows interleaved NP orderings — but the case-sorted subset
   is what Shieber's homomorphism + regular intersection isolates.
3. The number of DAT-Vs equals the number of DAT-NPs (and similarly for ACC).
4. An arbitrary number of Vs can occur (subject to performance).

## What Is Formalized Here

Shieber's full theorem — Swiss German is not weakly CF — is
`swiss_german_not_contextFree` below. Proof bottoms out at the two CFL
closure axioms in `Linglib.Core.Computability.ContextFreeGrammar.Closure`
(homomorphism + intersection-with-regular, cited Hopcroft–Ullman 1979) and
`ambncmdn_not_contextFree` (the two-parameter pumping result) in
`Linglib.Core.Computability.NonContextFree`.

A weaker pedagogical waypoint, `swiss_german_diagonal_not_contextFree`, uses
only the simpler one-parameter `anbncndn` substrate; it covers just the
diagonal (`m = n`) subset of SG clauses.

## Contrast with @cite{bresnan-etal-1982}

@cite{bresnan-etal-1982}'s earlier argument for Dutch non-context-freeness
relied on linguistic assumptions about constituent structure, which
@cite{gazdar-pullum-1982} contested. @cite{shieber-1985}'s argument is
purely formal — it rests entirely on the string set of Swiss German and
the case-marking facts, making no claims about phrase structure.

## Subsequent literature

- @cite{huybregts-1976} gave a contemporaneous Swiss German argument.
- Joshi (1985) introduced TAG and the mild-CS hierarchy; Vijay-Shanker–Weir
  (1994) established the equivalence of TAG/CCG/MCFG/MG within mild-CS.
  The MCS classification of cross-serial dependencies is post-Shieber and not
  attributable to him; he proved only *not weakly CF*.
- Manaster-Ramer (1987) raised concerns about the universality of Shieber's
  case-matching premise.
- Stabler (1997) and Kobele (2006) provide MG analyses of the same data.

The processing-side dissociation (cross-serial easier than nested despite
greater formal complexity) is the subject of @cite{bach-brown-marslen-wilson-1986},
formalized in `Phenomena.WordOrder.Studies.BachBrownMarslenWilson1986` —
not duplicated here.
-/

namespace Shieber1985

open Core (Case StringHom)
open Fragments.SwissGerman.Case (CrossSerialVerb verbObjectCase)

-- ============================================================================
-- §1: Swiss German Subordinate Clause Tokens
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
-- §2: Case-Sorted Cross-Serial Clauses
-- ============================================================================

/-- The abstract shape of a *case-sorted* cross-serial clause: counts of
    each (case × NP/V) combination, in the canonical order DAT-NPs, ACC-NPs,
    DAT-Vs, ACC-Vs.

    This is **not** a grammaticality condition on Swiss German — SG freely
    allows interleaved NP orderings — but the case-sorted shape is what
    Shieber's homomorphism + regular intersection isolates from the full
    SG language. -/
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

/-- A case-sorted clause that satisfies case matching. Renamed from the
    misleading `GrammaticalClause` — case matching is part of grammaticality,
    but case-*sorting* is not (per Claim 2 framing above). -/
structure CaseMatchedClause extends CrossSerialClause where
  matching : toCrossSerialClause.caseMatches

/-- Claim 4: any combination of dative and accusative verb counts can occur
    (we can produce a `CaseMatchedClause` for any m, n). -/
def arbitraryDepth (m n : Nat) : CaseMatchedClause :=
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
    - ACC-Vs  → `d` -/
def tokenToSymbol : Token → FourSymbol
  | .datNP => .a
  | .accNP => .b
  | .datV  => .c
  | .accV  => .d

/-- Letter-to-letter lift of `tokenToSymbol` to a `StringHom`: each input
    token maps to a singleton output string. -/
def tokenStringHom : StringHom Token FourSymbol := fun t => [tokenToSymbol t]

/-- The token sequence corresponding to a case-matched clause: NPs first
    (DAT then ACC), then Vs (DAT then ACC). -/
def caseSortedTokens (c : CaseMatchedClause) : List Token :=
  List.replicate c.datNPs .datNP ++ List.replicate c.accNPs .accNP ++
  List.replicate c.datVs .datV ++ List.replicate c.accVs .accV

/-- The string image of a case-matched clause's token sequence under
    `tokenStringHom`: a string in {a,b,c,d}*. -/
def clauseImage (c : CaseMatchedClause) : FourString :=
  List.replicate c.datNPs .a ++ List.replicate c.accNPs .b ++
  List.replicate c.datVs .c ++ List.replicate c.accVs .d

/-- The image of a case-matched clause is the `StringHom.apply` of
    `tokenStringHom` on its case-sorted token sequence. -/
theorem clauseImage_eq_apply (c : CaseMatchedClause) :
    clauseImage c = StringHom.apply tokenStringHom (caseSortedTokens c) := by
  simp [clauseImage, caseSortedTokens, tokenStringHom, tokenToSymbol,
        StringHom.apply, List.flatMap_append, List.flatMap_replicate]

/-- A case-matched clause with m DAT-pairs and n ACC-pairs maps to
    `aᵐ bⁿ cᵐ dⁿ`. -/
theorem clauseImage_shape (m n : Nat) :
    clauseImage (arbitraryDepth m n) =
      List.replicate m .a ++ List.replicate n .b ++
      List.replicate m .c ++ List.replicate n .d := rfl

-- ============================================================================
-- §4: The Diagonal Non-Context-Freeness Result
-- ============================================================================

/-- Setting m = n in the clause image gives `aⁿbⁿcⁿdⁿ`. -/
theorem diagonal_is_anbncndn (n : Nat) :
    clauseImage (arbitraryDepth n n) = makeString_anbncndn n := rfl

/-- The diagonal clause images are in {aⁿbⁿcⁿdⁿ}. -/
theorem diagonal_in_language (n : Nat) :
    clauseImage (arbitraryDepth n n) ∈ anbncndn := by
  rw [diagonal_is_anbncndn]; exact makeString_in_language n

/-- The diagonal subset of Swiss German cross-serial clauses (encoded as
    token sequences): case-matched, case-sorted, with `m = n`. -/
def swissGermanDiagonalLang : Language Token :=
  { ts | ∃ n : Nat, ts = caseSortedTokens (arbitraryDepth n n) }

/-- The homomorphic image of the diagonal SG language under `tokenStringHom`
    is exactly `anbncndn`.

    This is the load-bearing equality for Shieber's argument: it sits at the
    interface between linguistic data (the diagonal SG clauses) and the
    formal-language witness (`anbncndn`) whose non-CF status is established
    in `Linglib.Core.Computability.NonContextFree`. -/
theorem stringMap_diagonal_eq_anbncndn :
    Language.stringMap tokenStringHom swissGermanDiagonalLang = anbncndn := by
  ext w
  constructor
  · rintro ⟨v, ⟨n, hv⟩, hApply⟩
    rw [← hApply, hv, ← clauseImage_eq_apply, diagonal_is_anbncndn]
    exact makeString_in_language n
  · intro hw
    obtain ⟨n, rfl⟩ := (mem_anbncndn_iff w).mp hw
    refine ⟨caseSortedTokens (arbitraryDepth n n), ⟨n, rfl⟩, ?_⟩
    rw [← clauseImage_eq_apply, diagonal_is_anbncndn]

/-- **Diagonal Swiss German is not context-free.** A formal corollary of
    @cite{shieber-1985}'s argument, using only the one-parameter substrate
    `{aⁿbⁿcⁿdⁿ}`. The image of the diagonal SG language under `tokenStringHom`
    equals `anbncndn` (not CF), so by closure under string homomorphism
    (`Linglib.Core.Computability.ContextFreeGrammar.Closure`), the source is not CF. -/
theorem swiss_german_diagonal_not_contextFree :
    ¬ swissGermanDiagonalLang.IsContextFree := by
  apply Language.not_isContextFree_of_stringMap_not tokenStringHom
  rw [stringMap_diagonal_eq_anbncndn]
  exact anbncndn_not_contextFree

/-- The full Swiss German cross-serial language: token sequences corresponding
    to case-matched, case-sorted clauses with arbitrary `m, n` (no diagonal
    restriction). Strict superset of `swissGermanDiagonalLang`. -/
def swissGermanLang : Language Token :=
  { ts | ∃ m n : Nat, ts = caseSortedTokens (arbitraryDepth m n) }

/-- The homomorphic image of the full SG language under `tokenStringHom`
    is exactly `ambncmdn = {aᵐbⁿcᵐdⁿ}`. Both directions of equality use
    `mem_ambncmdn_iff`'s structural decomposition. -/
theorem stringMap_swissGerman_eq_ambncmdn :
    Language.stringMap tokenStringHom swissGermanLang = ambncmdn := by
  ext w
  constructor
  · rintro ⟨v, ⟨m, n, hv⟩, hApply⟩
    rw [← hApply, hv, ← clauseImage_eq_apply, clauseImage_shape]
    exact makeString_ambncmdn_in_language m n
  · intro hw
    obtain ⟨m, n, rfl⟩ := (mem_ambncmdn_iff w).mp hw
    refine ⟨caseSortedTokens (arbitraryDepth m n), ⟨m, n, rfl⟩, ?_⟩
    rw [← clauseImage_eq_apply, clauseImage_shape]
    rfl

/-- **@cite{shieber-1985}'s main theorem.** Swiss German subordinate clauses
    are not weakly context-free.

    The proof: the homomorphic image of the case-matched cross-serial language
    under `tokenToSymbol` equals `ambncmdn = {aᵐbⁿcᵐdⁿ}` (proven non-CF in
    `Linglib.Core.Computability.NonContextFree.ambncmdn_not_contextFree` by
    a two-parameter extension of the pumping argument). By CFL closure under
    string homomorphism (`Linglib.Core.Computability.ContextFreeGrammar.Closure`), the source
    Swiss German language is not context-free. -/
theorem swiss_german_not_contextFree :
    ¬ swissGermanLang.IsContextFree := by
  apply Language.not_isContextFree_of_stringMap_not tokenStringHom
  rw [stringMap_swissGerman_eq_ambncmdn]
  exact ambncmdn_not_contextFree

-- ============================================================================
-- §5: Strong Context-Freeness Corollary
-- ============================================================================

/-- Swiss German is not strongly context-free either. Shieber §3: any
    strongly-CF analysis induces a weakly-CF string set; since the string
    set isn't weakly CF (`swiss_german_not_contextFree` above), no such
    strongly-CF analysis exists. -/
theorem not_strongly_context_free :
    ¬ swissGermanLang.IsContextFree := swiss_german_not_contextFree

-- ============================================================================
-- §6: Grounding in the Swiss German Fragment
-- ============================================================================

/-- Verbs in the Swiss German fragment have case requirements that match
    their Token-level classification (DAT-V or ACC-V). Collapsed from three
    near-identical theorems into one decide-checked conjunction. -/
theorem fragment_case_grounding :
    verbObjectCase .haelfe = Token.caseValue .datV ∧
    verbObjectCase .loend = Token.caseValue .accV ∧
    verbObjectCase .aastriiche = Token.caseValue .accV := by decide

-- ============================================================================
-- §7: Examples from the Paper
-- ============================================================================

/-- Example (1): *mer em Hans es huus hälfed aastriiche*
    "we helped Hans paint the house"

    em Hans (DAT) → hälfed (DAT-verb "helped");
    es huus (ACC) → aastriiche (ACC-verb "paint"). -/
def example1 : CaseMatchedClause := arbitraryDepth 1 1

/-- Example (5): triply embedded cross-serial clause
    *mer d'chind em Hans es huus lönd hälfe aastriiche*
    "we let the children help Hans paint the house"

    d'chind (ACC) → lönd (ACC-verb "let");
    em Hans (DAT) → hälfe (DAT-verb "help");
    es huus (ACC) → aastriiche (ACC-verb "paint").

    With case sorting: 1 DAT-NP, 2 ACC-NPs, 1 DAT-V, 2 ACC-Vs. -/
def example5 : CaseMatchedClause := arbitraryDepth 1 2

/-- The homomorphic image of example (5) is `abbcdd = a¹b²c¹d²`. -/
theorem example5_image :
    clauseImage example5 = [.a, .b, .b, .c, .d, .d] := rfl

end Shieber1985
