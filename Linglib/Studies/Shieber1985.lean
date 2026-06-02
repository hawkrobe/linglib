import Linglib.Core.Computability.ContextFreeGrammar.Closure
import Linglib.Core.Computability.NonContextFree.AnBnCnDn
import Linglib.Core.Computability.NonContextFree.AmBnCmDn
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Features.Case
import Linglib.Fragments.SwissGerman.Case

/-!
# Shieber (1985) [shieber-1985]

Evidence against the Context-Freeness of Natural Language.
*Linguistics and Philosophy*, 8(3), 333–343.

## Core Argument

[shieber-1985] proves that Swiss German is not weakly context-free,
using a purely string-based argument that makes no assumptions about
constituent structure or semantics. The proof rests on four empirical
claims about Swiss German subordinate clauses, plus the closure of
context-free languages under string homomorphism and intersection with
regular languages (proven in `Linglib.Core.Computability.ContextFreeGrammar.{Map, InterRegular}`
following [bar-hillel-perles-shamir-1961] / [hopcroft-motwani-ullman-2000]
Theorems 7.24, 7.27).

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

`swiss_german_not_contextFree` proves: **Swiss German subordinate clauses are
not weakly context-free**. The language `swissGermanLang` allows any token
sequence whose cross-serial core (after stripping `matrix` boundary tokens —
matrix subjects, complementizers, auxiliaries, finite verbs of the embedding
clause) has shape `nps ++ vs` with case counts matched. Matrix tokens may
appear interleaved anywhere; Shieber's homomorphism erases them.

The proof exercises both legs of the Bar-Hillel schema
(`Language.not_isContextFree_via_witness` from `Closure.lean`):

* **Homomorphism leg** (`tokenStringHom`): cross-serial NPs and Vs map to
  singleton {a,b,c,d} letters; matrix tokens map to `[]` (Shieber's ε-erasure).
* **Regular-intersection leg** (`caseSorted = a*b*c*d*`): selects only
  case-sorted images, isolating the canonical cross-serial shape from any
  source-string interleaving of cross-serial tokens.

The witness language `stringMap h L ⊓ R = ambncmdn` — non-CF by
`ambncmdn_not_contextFree` (two-parameter pumping). Per the Bar-Hillel
schema, source SG is non-CF.

Proof bottoms out at the two CFL closure theorems in
`Linglib.Core.Computability.ContextFreeGrammar.{Map, InterRegular}`
(homomorphism + intersection-with-regular, both proven; see those files for
[bar-hillel-perles-shamir-1961] / [hopcroft-motwani-ullman-2000]
construction details) and `ambncmdn_not_contextFree` (the two-parameter
pumping result) in `Linglib.Core.Computability.NonContextFree`.

A weaker pedagogical waypoint, `swiss_german_diagonal_not_contextFree`, uses
only the simpler one-parameter `anbncndn` substrate; it covers just the
diagonal (`m = n`) subset of SG clauses with no matrix material.

## Remaining idealizations

The `matrix` token is a single abstract constructor, not a richer model of
SG matrix material's internal structure (specific lexical items, agreement,
finite-verb fronting). For Shieber's purpose — showing non-CFness of the
string set — this abstraction is faithful: he too treats matrix material as
an erasable substring under the homomorphism. A richer model that ties
matrix-token positions to specific SG fragment data would be a substantive
extension; the current formalization captures Shieber's full argument
without it.

## Contrast with [bresnan-etal-1982]

[bresnan-etal-1982]'s earlier argument for Dutch non-context-freeness
relied on linguistic assumptions about constituent structure, which
[gazdar-pullum-1982] contested. [shieber-1985]'s argument is
purely formal — it rests entirely on the string set of Swiss German and
the case-marking facts, making no claims about phrase structure.

## Subsequent literature

- [huybregts-1976] gave a contemporaneous Swiss German argument.
- Joshi (1985) introduced TAG and the mild-CS hierarchy; Vijay-Shanker–Weir
  (1994) established the equivalence of TAG/CCG/MCFG/MG within mild-CS.
  The MCS classification of cross-serial dependencies is post-Shieber and not
  attributable to him; he proved only *not weakly CF*.
- Manaster-Ramer (1987) raised concerns about the universality of Shieber's
  case-matching premise.
- Stabler (1997) and Kobele (2006) provide MG analyses of the same data.

The processing-side dissociation (cross-serial easier than nested despite
greater formal complexity) is the subject of [bach-brown-marslen-wilson-1986],
formalized in `BachBrownMarslenWilson1986` —
not duplicated here.
-/

namespace Shieber1985

open Features (Case)
open Core (StringHom)
open SwissGerman.Case (CrossSerialVerb verbObjectCase)

-- ============================================================================
-- §1: Swiss German Subordinate Clause Tokens
-- ============================================================================

/-- A Swiss German subordinate clause token, abstracting over specific lexical
    items to their role in the cross-serial construction.

    [shieber-1985]'s argument projects SG sentences to four case-marked
    classes (DAT-NP / ACC-NP / DAT-V / ACC-V) plus boundary material. The
    `matrix` constructor abstracts non-cross-serial tokens — matrix subjects,
    complementizers, auxiliaries, finite verbs of the embedding clause, etc.
    Shieber's homomorphism erases these to ε; our `tokenStringHom` does the
    same by mapping `matrix` to `[]`. This is what makes the proof apply to
    full Swiss German rather than just the NP*V* sub-shape — matrix tokens
    can appear interleaved anywhere in a sentence, and the homomorphism
    strips them, so the regex-filtered image picks up the cross-serial
    core regardless of how it's wrapped in the source string. -/
inductive Token where
  /-- Dative NP (e.g., *em Hans*) -/
  | datNP
  /-- Accusative NP (e.g., *d'chind*, *de Hans*) -/
  | accNP
  /-- Dative-subcategorizing verb (e.g., *hälfe* "help") -/
  | datV
  /-- Accusative-subcategorizing verb (e.g., *lönd* "let", *aastriiche* "paint") -/
  | accV
  /-- Boundary material: matrix subject, complementizer, auxiliary, finite
      verb of the embedding clause, etc. Erased by `tokenStringHom`
      (Shieber's projection). -/
  | matrix
  deriving DecidableEq, Repr

/-- The case that a token bears or requires. Matrix tokens have no case;
    the field is total at `.dat` as a default (never consulted on matrix
    tokens in any consumer — case-matching predicates filter via `isNP` / `isV`
    first). -/
def Token.caseValue : Token → Case
  | .datNP => .dat
  | .accNP => .acc
  | .datV  => .dat
  | .accV  => .acc
  | .matrix => .dat  -- arbitrary; matrix has no real case

/-- Whether a token is a case-marked NP (vs a verb or matrix material). -/
def Token.isNP : Token → Bool
  | .datNP | .accNP => true
  | .datV  | .accV  => false
  | .matrix         => false

/-- Whether a token is a case-subcategorizing verb (vs an NP or matrix material). -/
def Token.isV : Token → Bool
  | .datNP | .accNP => false
  | .datV  | .accV  => true
  | .matrix         => false

/-- Whether a token is matrix (boundary) material (vs a cross-serial NP/V). -/
def Token.isMatrix : Token → Bool
  | .datNP  => false
  | .accNP  => false
  | .datV   => false
  | .accV   => false
  | .matrix => true

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
    to the abstract alphabet {a, b, c, d}. Matrix tokens have no meaningful
    image; the placeholder `.a` is never observed by any consumer (every use
    site filters via `isMatrix` or constructs from non-matrix tokens). The
    real homomorphism `tokenStringHom` ERASES matrix tokens to `[]`. -/
def tokenToSymbol : Token → FourSymbol
  | .datNP  => .a
  | .accNP  => .b
  | .datV   => .c
  | .accV   => .d
  | .matrix => .a  -- placeholder; never consumed

/-- Shieber's homomorphism, lifted to lists. Cross-serial NPs and Vs map to
    singleton {a,b,c,d} letters; matrix tokens are erased. This `[]`-valued
    case is essential for full-SG fidelity: it lets the schema apply to
    sentences with arbitrary boundary material wrapping the cross-serial
    core. The function is no longer a `StringHom.letterMap` for that reason. -/
def tokenStringHom : StringHom Token FourSymbol := fun
  | .matrix => []
  | t       => [tokenToSymbol t]

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
    [shieber-1985]'s argument, using only the one-parameter substrate
    `{aⁿbⁿcⁿdⁿ}`. The image of the diagonal SG language under `tokenStringHom`
    equals `anbncndn` (not CF), so by closure under string homomorphism
    (`Linglib.Core.Computability.ContextFreeGrammar.Closure`), the source is not CF. -/
theorem swiss_german_diagonal_not_contextFree :
    ¬ swissGermanDiagonalLang.IsContextFree := by
  apply Language.not_isContextFree_of_stringMap_not tokenStringHom
  rw [stringMap_diagonal_eq_anbncndn]
  exact anbncndn_not_contextFree

-- ============================================================================
-- §4: The full Swiss German language and Shieber's schema
-- ============================================================================
-- Shieber's actual paper structure projects FULL Swiss German sentences
-- (including matrix material like subjects, complementizers, auxiliaries)
-- to {a,b,c,d} via a homomorphism that erases boundary words to ε. The
-- regex filter then selects sentences whose stripped image is the canonical
-- case-sorted core. We mechanize this by:
--   * allowing `matrix` tokens interleaved anywhere in `swissGermanLang`,
--   * defining `tokenStringHom` to map matrix tokens to `[]`,
--   * proving the intersection of (image-of-SG) with `caseSorted` equals
--     `ambncmdn`, then applying `not_isContextFree_via_witness`.
-- This makes the headline theorem `swiss_german_not_contextFree` a faithful
-- statement about FULL Swiss German, not just its NP*V* sub-shape.

/-- The Swiss German cross-serial language. A token list `ts` is in this
    language iff:

    * stripping matrix tokens leaves a list of form `nps ++ vs` (NPs precede
      Vs in the cross-serial core), and
    * the case counts match (#DAT-NP = #DAT-V, #ACC-NP = #ACC-V).

    Matrix tokens (subjects, complementizers, auxiliaries) may appear anywhere
    interleaved with cross-serial NPs/Vs — Shieber's homomorphism erases them.
    The case-sorted canonical form `caseSortedTokens (arbitraryDepth m n)`
    (no matrix tokens, NPs and Vs each in canonical case order) is properly
    contained. -/
def swissGermanLang : Language Token :=
  { ts | ∃ nps vs : List Token,
      ts.filter (fun t => !t.isMatrix) = nps ++ vs ∧
      (∀ t ∈ nps, t.isNP = true) ∧
      (∀ t ∈ vs, t.isV = true) ∧
      nps.countP (· == .datNP) = vs.countP (· == .datV) ∧
      nps.countP (· == .accNP) = vs.countP (· == .accV) }

/-- Every case-matched, case-sorted clause (no matrix material) is in the
    (more general) free SG language. -/
theorem caseSortedTokens_in_swissGermanLang (m n : Nat) :
    caseSortedTokens (arbitraryDepth m n) ∈ swissGermanLang := by
  refine ⟨List.replicate m .datNP ++ List.replicate n .accNP,
          List.replicate m .datV ++ List.replicate n .accV, ?_, ?_, ?_, ?_, ?_⟩
  · -- caseSortedTokens has no matrix tokens, so filter is identity.
    show List.filter _ (caseSortedTokens (arbitraryDepth m n)) = _
    simp [caseSortedTokens, arbitraryDepth, List.filter_append,
          List.filter_replicate, Token.isMatrix, List.append_assoc]
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · obtain rfl := List.eq_of_mem_replicate h; rfl
    · obtain rfl := List.eq_of_mem_replicate h; rfl
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · obtain rfl := List.eq_of_mem_replicate h; rfl
    · obtain rfl := List.eq_of_mem_replicate h; rfl
  · simp [List.countP_append, List.countP_replicate]
  · simp [List.countP_append, List.countP_replicate]

-- ----------------------------------------------------------------------------
-- The regular filter `caseSorted` on FourSymbol: a*b*c*d*.
-- ----------------------------------------------------------------------------

/-- DFA states for the case-sorted shape `a*b*c*d*`. -/
inductive CaseSortedState | sA | sB | sC | sD | sDead
  deriving DecidableEq, Fintype, Repr

/-- DFA recognizing `a*b*c*d*` over `FourSymbol`. -/
def caseSortedDFA : DFA FourSymbol CaseSortedState where
  start := .sA
  accept := { .sA, .sB, .sC, .sD }
  step
    | .sA, .a => .sA  | .sA, .b => .sB  | .sA, .c => .sC  | .sA, .d => .sD
    | .sB, .a => .sDead | .sB, .b => .sB | .sB, .c => .sC | .sB, .d => .sD
    | .sC, .a => .sDead | .sC, .b => .sDead | .sC, .c => .sC | .sC, .d => .sD
    | .sD, .a => .sDead | .sD, .b => .sDead | .sD, .c => .sDead | .sD, .d => .sD
    | .sDead, _ => .sDead

/-- The case-sorted shape language `a*b*c*d*` on `FourSymbol`. -/
def caseSorted : Language FourSymbol := caseSortedDFA.accepts

theorem caseSorted_isRegular : caseSorted.IsRegular :=
  ⟨CaseSortedState, inferInstance, caseSortedDFA, rfl⟩

-- DFA evaluation step lemmas: each replicate kᵢ block stabilises in the
-- corresponding state once started or already past it.

private lemma evalFrom_replicate_a (k : Nat) :
    caseSortedDFA.evalFrom .sA (List.replicate k .a) = .sA := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, DFA.evalFrom_cons]; exact ih

private lemma evalFrom_replicate_b (k : Nat) (s : CaseSortedState)
    (h : s = .sA ∨ s = .sB) :
    caseSortedDFA.evalFrom s (List.replicate k .b) =
      (if k = 0 then s else .sB) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl
    · -- step sA b = sB
      show caseSortedDFA.evalFrom .sB (List.replicate k .b) = _
      rw [ih .sB (.inr rfl)]; cases k <;> simp
    · -- step sB b = sB
      show caseSortedDFA.evalFrom .sB (List.replicate k .b) = _
      rw [ih .sB (.inr rfl)]; cases k <;> simp

private lemma evalFrom_replicate_c (k : Nat) (s : CaseSortedState)
    (h : s = .sA ∨ s = .sB ∨ s = .sC) :
    caseSortedDFA.evalFrom s (List.replicate k .c) =
      (if k = 0 then s else .sC) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl | rfl
    all_goals (
      show caseSortedDFA.evalFrom .sC (List.replicate k .c) = _
      rw [ih .sC (.inr (.inr rfl))]; cases k <;> simp)

private lemma evalFrom_replicate_d (k : Nat) (s : CaseSortedState)
    (h : s = .sA ∨ s = .sB ∨ s = .sC ∨ s = .sD) :
    caseSortedDFA.evalFrom s (List.replicate k .d) =
      (if k = 0 then s else .sD) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    rcases h with rfl | rfl | rfl | rfl
    all_goals (
      show caseSortedDFA.evalFrom .sD (List.replicate k .d) = _
      rw [ih .sD (.inr (.inr (.inr rfl)))]; cases k <;> simp)

/-- Concrete witness: every `aᵐbⁿcᵐdⁿ` is case-sorted. -/
theorem makeString_ambncmdn_in_caseSorted (m n : Nat) :
    makeString_ambncmdn m n ∈ caseSorted := by
  show caseSortedDFA.eval (makeString_ambncmdn m n) ∈ caseSortedDFA.accept
  show caseSortedDFA.evalFrom .sA _ ∈ _
  simp only [makeString_ambncmdn, DFA.evalFrom_of_append, evalFrom_replicate_a]
  rw [evalFrom_replicate_b n .sA (.inl rfl)]
  set s_after_b := if n = 0 then CaseSortedState.sA else .sB
  have hs_after_b : s_after_b = .sA ∨ s_after_b = .sB := by
    by_cases hn : n = 0 <;> simp [s_after_b, hn]
  rw [evalFrom_replicate_c m s_after_b (hs_after_b.imp_right (.inl ·))]
  set s_after_c := if m = 0 then s_after_b else .sC
  have hs_after_c : s_after_c = .sA ∨ s_after_c = .sB ∨ s_after_c = .sC := by
    by_cases hm : m = 0
    · simp only [s_after_c, hm, if_true]
      exact hs_after_b.imp_right .inl
    · simp only [s_after_c, hm, if_false]
      right; right; trivial
  rw [evalFrom_replicate_d n s_after_c
    (hs_after_c.imp_right (·.imp_right .inl))]
  -- Final state ∈ accept (which is {.sA, .sB, .sC, .sD}).
  rcases hs_after_c with hSA | hSB | hSC <;>
    by_cases hn : n = 0 <;>
    simp_all (config := { decide := true }) [DFA.accepts, caseSortedDFA]
  all_goals
    first
    | (show CaseSortedState.sA ∈ ({.sA, .sB, .sC, .sD} : Set _); simp)
    | (show CaseSortedState.sB ∈ ({.sA, .sB, .sC, .sD} : Set _); simp)
    | (show CaseSortedState.sC ∈ ({.sA, .sB, .sC, .sD} : Set _); simp)
    | (show CaseSortedState.sD ∈ ({.sA, .sB, .sC, .sD} : Set _); simp)

-- ----------------------------------------------------------------------------
-- The intersection equality: stringMap free SG ⊓ caseSorted = ambncmdn.
-- This is the meat of Shieber's argument: the homomorphism collapses cases
-- to letter identity, the regular filter forces letter-sort to be canonical
-- (a*b*c*d*), and case-matching forces equal counts of a/c and b/d.
-- ----------------------------------------------------------------------------

-- Decomposition substrate: an accepted DFA trajectory partitions the input
-- as a sorted block sequence aᵖbᵠcʳdˢ.

private lemma evalFrom_sDead (xs : List FourSymbol) :
    caseSortedDFA.evalFrom .sDead xs = .sDead := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [DFA.evalFrom_cons]
    show caseSortedDFA.evalFrom .sDead xs = .sDead
    exact ih

private lemma sDead_not_accept : .sDead ∉ caseSortedDFA.accept := by
  intro h
  -- caseSortedDFA.accept is {.sA, .sB, .sC, .sD} as a Set.
  rcases h with h | h | h | h <;> exact CaseSortedState.noConfusion h

private lemma not_dead_of_accept {s : CaseSortedState} {xs : List FourSymbol}
    (h : caseSortedDFA.evalFrom s xs ∈ caseSortedDFA.accept) :
    caseSortedDFA.evalFrom s xs ≠ .sDead := by
  intro h_eq; rw [h_eq] at h; exact sDead_not_accept h

private lemma sD_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept) :
    ∃ u, xs = List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | a =>
      have := not_dead_of_accept h
      have heq : caseSortedDFA.evalFrom .sDead xs = .sDead := evalFrom_sDead xs
      exact absurd heq this
    | b =>
      have := not_dead_of_accept h
      have heq : caseSortedDFA.evalFrom .sDead xs = .sDead := evalFrom_sDead xs
      exact absurd heq this
    | c =>
      have := not_dead_of_accept h
      have heq : caseSortedDFA.evalFrom .sDead xs = .sDead := evalFrom_sDead xs
      exact absurd heq this
    | d =>
      have h' : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept := h
      obtain ⟨u, rfl⟩ := ih h'
      exact ⟨u + 1, by rw [List.replicate_succ]⟩

private lemma sC_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sC xs ∈ caseSortedDFA.accept) :
    ∃ r u, xs = List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | a =>
      have := not_dead_of_accept h
      exact absurd (evalFrom_sDead xs) this
    | b =>
      have := not_dead_of_accept h
      exact absurd (evalFrom_sDead xs) this
    | c =>
      have h' : caseSortedDFA.evalFrom .sC xs ∈ caseSortedDFA.accept := h
      obtain ⟨r, u, rfl⟩ := ih h'
      refine ⟨r + 1, u, ?_⟩
      rw [List.replicate_succ]; rfl
    | d =>
      have h' : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept := h
      obtain ⟨u, rfl⟩ := sD_decomp xs h'
      refine ⟨0, u + 1, ?_⟩
      rw [List.replicate_succ]; rfl

private lemma sB_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sB xs ∈ caseSortedDFA.accept) :
    ∃ q r u, xs = List.replicate q .b ++ List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, 0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | a =>
      have := not_dead_of_accept h
      exact absurd (evalFrom_sDead xs) this
    | b =>
      have h' : caseSortedDFA.evalFrom .sB xs ∈ caseSortedDFA.accept := h
      obtain ⟨q, r, u, rfl⟩ := ih h'
      refine ⟨q + 1, r, u, ?_⟩
      rw [List.replicate_succ]; rfl
    | c =>
      have h' : caseSortedDFA.evalFrom .sC xs ∈ caseSortedDFA.accept := h
      obtain ⟨r, u, rfl⟩ := sC_decomp xs h'
      refine ⟨0, r + 1, u, ?_⟩
      simp [List.replicate_succ, List.replicate]
    | d =>
      have h' : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept := h
      obtain ⟨u, rfl⟩ := sD_decomp xs h'
      refine ⟨0, 0, u + 1, ?_⟩
      simp [List.replicate_succ, List.replicate]

private lemma sA_decomp (xs : List FourSymbol)
    (h : caseSortedDFA.evalFrom .sA xs ∈ caseSortedDFA.accept) :
    ∃ p q r u, xs = List.replicate p .a ++ List.replicate q .b ++
                    List.replicate r .c ++ List.replicate u .d := by
  induction xs with
  | nil => exact ⟨0, 0, 0, 0, rfl⟩
  | cons x xs ih =>
    rw [DFA.evalFrom_cons] at h
    cases x with
    | a =>
      have h' : caseSortedDFA.evalFrom .sA xs ∈ caseSortedDFA.accept := h
      obtain ⟨p, q, r, u, rfl⟩ := ih h'
      refine ⟨p + 1, q, r, u, ?_⟩
      rw [List.replicate_succ]; rfl
    | b =>
      have h' : caseSortedDFA.evalFrom .sB xs ∈ caseSortedDFA.accept := h
      obtain ⟨q, r, u, rfl⟩ := sB_decomp xs h'
      refine ⟨0, q + 1, r, u, ?_⟩
      simp [List.replicate_succ, List.replicate]
    | c =>
      have h' : caseSortedDFA.evalFrom .sC xs ∈ caseSortedDFA.accept := h
      obtain ⟨r, u, rfl⟩ := sC_decomp xs h'
      refine ⟨0, 0, r + 1, u, ?_⟩
      simp [List.replicate_succ, List.replicate]
    | d =>
      have h' : caseSortedDFA.evalFrom .sD xs ∈ caseSortedDFA.accept := h
      obtain ⟨u, rfl⟩ := sD_decomp xs h'
      refine ⟨0, 0, 0, u + 1, ?_⟩
      simp [List.replicate_succ, List.replicate]

/-- Any case-sorted FourString decomposes uniquely into block-sorted
    `aᵖ ++ bᵠ ++ cʳ ++ dˢ`. -/
theorem caseSorted_decomp (xs : List FourSymbol) (h : xs ∈ caseSorted) :
    ∃ p q r u, xs = List.replicate p .a ++ List.replicate q .b ++
                    List.replicate r .c ++ List.replicate u .d :=
  sA_decomp xs h

-- Token-image counting lemmas. `tokenStringHom` maps cross-serial NPs/Vs to
-- singleton {a,b,c,d} letters and matrix tokens to `[]`; counting on the
-- flattened image gives back the source token-equality count.

private lemma count_a_image_eq_count_datNP (ts : List Token) :
    (ts.flatMap tokenStringHom).countP (· == .a) = ts.countP (· == .datNP) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;>
      simp [List.flatMap_cons, List.countP_cons, ih, tokenStringHom, tokenToSymbol]

private lemma count_b_image_eq_count_accNP (ts : List Token) :
    (ts.flatMap tokenStringHom).countP (· == .b) = ts.countP (· == .accNP) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;>
      simp [List.flatMap_cons, List.countP_cons, ih, tokenStringHom, tokenToSymbol]

private lemma count_c_image_eq_count_datV (ts : List Token) :
    (ts.flatMap tokenStringHom).countP (· == .c) = ts.countP (· == .datV) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;>
      simp [List.flatMap_cons, List.countP_cons, ih, tokenStringHom, tokenToSymbol]

private lemma count_d_image_eq_count_accV (ts : List Token) :
    (ts.flatMap tokenStringHom).countP (· == .d) = ts.countP (· == .accV) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;>
      simp [List.flatMap_cons, List.countP_cons, ih, tokenStringHom, tokenToSymbol]

-- Filter-by-non-matrix preserves token-equality counts for cross-serial
-- tokens (matrix is the only token that gets filtered out, and matrix is
-- different from each cross-serial token).

private lemma countP_filter_notMatrix_datNP (ts : List Token) :
    (ts.filter (fun t => !t.isMatrix)).countP (· == .datNP) =
      ts.countP (· == .datNP) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    cases t <;> simp_all [Token.isMatrix, List.countP_cons]

private lemma countP_filter_notMatrix_accNP (ts : List Token) :
    (ts.filter (fun t => !t.isMatrix)).countP (· == .accNP) =
      ts.countP (· == .accNP) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    cases t <;> simp_all [Token.isMatrix, List.countP_cons]

private lemma countP_filter_notMatrix_datV (ts : List Token) :
    (ts.filter (fun t => !t.isMatrix)).countP (· == .datV) =
      ts.countP (· == .datV) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    cases t <;> simp_all [Token.isMatrix, List.countP_cons]

private lemma countP_filter_notMatrix_accV (ts : List Token) :
    (ts.filter (fun t => !t.isMatrix)).countP (· == .accV) =
      ts.countP (· == .accV) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    cases t <;> simp_all [Token.isMatrix, List.countP_cons]

-- countP_caseValue_* lemmas removed: the new `swissGermanLang` definition uses
-- direct token-equality counting (`· == .datNP` etc.) instead of going
-- through `caseValue`, so the bridge lemmas are no longer needed.

/-- The Bar-Hillel-style intersection equality: full SG (with arbitrary matrix
    material), projected to {a,b,c,d} and filtered to case-sorted shape,
    equals exactly the non-CF language `aᵐbⁿcᵐdⁿ`. -/
theorem stringMap_swissGerman_inter_caseSorted_eq_ambncmdn :
    Language.stringMap tokenStringHom swissGermanLang ⊓ caseSorted = ambncmdn := by
  ext w
  refine ⟨?_, ?_⟩
  · -- Forward: SG image filtered to case-sorted shape ⊆ ambncmdn.
    rintro ⟨⟨ts, hts_in, hApply⟩, hw_cs⟩
    -- Decompose the case-sorted image into a^p b^q c^r d^s.
    obtain ⟨p, q, r, s, hw_decomp⟩ := caseSorted_decomp w hw_cs
    -- ts has cross-serial core (nps ++ vs after stripping matrix) with case-
    -- matched counts on cross-serial tokens.
    obtain ⟨nps, vs, hts_filter, h_nps, h_vs, h_dat, h_acc⟩ := hts_in
    -- w = StringHom.apply tokenStringHom ts = ts.flatMap tokenStringHom.
    have hw_flatMap : w = ts.flatMap tokenStringHom := hApply.symm
    -- Counts in w: p = #a, q = #b, r = #c, s = #d (from the decomposition).
    have h_p : w.countP (· == .a) = p := by
      rw [hw_decomp]; simp [List.countP_append, List.countP_replicate]
    have h_q : w.countP (· == .b) = q := by
      rw [hw_decomp]; simp [List.countP_append, List.countP_replicate]
    have h_r : w.countP (· == .c) = r := by
      rw [hw_decomp]; simp [List.countP_append, List.countP_replicate]
    have h_s : w.countP (· == .d) = s := by
      rw [hw_decomp]; simp [List.countP_append, List.countP_replicate]
    -- Bridge image-counts to source token-counts (matrix tokens contribute 0).
    have h_p_eq : p = ts.countP (· == .datNP) := by
      rw [hw_flatMap, count_a_image_eq_count_datNP] at h_p; omega
    have h_q_eq : q = ts.countP (· == .accNP) := by
      rw [hw_flatMap, count_b_image_eq_count_accNP] at h_q; omega
    have h_r_eq : r = ts.countP (· == .datV) := by
      rw [hw_flatMap, count_c_image_eq_count_datV] at h_r; omega
    have h_s_eq : s = ts.countP (· == .accV) := by
      rw [hw_flatMap, count_d_image_eq_count_accV] at h_s; omega
    -- Filter-then-decompose gives nps ++ vs structure on the cross-serial core.
    -- Bridge ts-counts (full string) to filter-counts (cross-serial only) via
    -- the no-op-on-NP/V filter, then split via append.
    have h_p_nps : p = nps.countP (· == .datNP) := by
      rw [h_p_eq, ← countP_filter_notMatrix_datNP, hts_filter, List.countP_append]
      have hvs_zero : vs.countP (· == .datNP) = 0 := by
        apply List.countP_eq_zero.mpr
        intro t ht; have := h_vs t ht; cases t <;> simp_all [Token.isV]
      omega
    have h_r_vs : r = vs.countP (· == .datV) := by
      rw [h_r_eq, ← countP_filter_notMatrix_datV, hts_filter, List.countP_append]
      have hnps_zero : nps.countP (· == .datV) = 0 := by
        apply List.countP_eq_zero.mpr
        intro t ht; have := h_nps t ht; cases t <;> simp_all [Token.isNP]
      omega
    have h_q_nps : q = nps.countP (· == .accNP) := by
      rw [h_q_eq, ← countP_filter_notMatrix_accNP, hts_filter, List.countP_append]
      have hvs_zero : vs.countP (· == .accNP) = 0 := by
        apply List.countP_eq_zero.mpr
        intro t ht; have := h_vs t ht; cases t <;> simp_all [Token.isV]
      omega
    have h_s_vs : s = vs.countP (· == .accV) := by
      rw [h_s_eq, ← countP_filter_notMatrix_accV, hts_filter, List.countP_append]
      have hnps_zero : nps.countP (· == .accV) = 0 := by
        apply List.countP_eq_zero.mpr
        intro t ht; have := h_nps t ht; cases t <;> simp_all [Token.isNP]
      omega
    -- Case matching: #DAT-NP in nps = #DAT-V in vs ⇒ p = r; similarly q = s.
    have h_pr : p = r := by rw [h_p_nps, h_r_vs]; exact h_dat
    have h_qs : q = s := by rw [h_q_nps, h_s_vs]; exact h_acc
    -- Now w = a^p b^q c^p d^q = makeString_ambncmdn p q ∈ ambncmdn.
    refine (mem_ambncmdn_iff w).mpr ⟨p, q, ?_⟩
    rw [hw_decomp, h_pr, h_qs]
    rfl
  · -- Backward: every aᵐbⁿcᵐdⁿ is the image of canonical SG and is case-sorted.
    intro hw
    obtain ⟨m, n, rfl⟩ := (mem_ambncmdn_iff w).mp hw
    refine ⟨?_, makeString_ambncmdn_in_caseSorted m n⟩
    refine ⟨caseSortedTokens (arbitraryDepth m n),
            caseSortedTokens_in_swissGermanLang m n, ?_⟩
    -- The canonical preimage has no matrix tokens, so flatMap = map.
    show StringHom.apply tokenStringHom _ = _
    rw [← clauseImage_eq_apply, clauseImage_shape]
    rfl

/-- **[shieber-1985]'s main theorem.** Swiss German subordinate clauses
    are not weakly context-free.

    Proof structure (the actual Shieber schema, both legs exercised):
    apply `Language.not_isContextFree_via_witness` with the `tokenStringHom`
    homomorphism + `caseSorted` regular filter; the witness is that
    `stringMap h L ⊓ R = ambncmdn`, which is non-CF by
    `ambncmdn_not_contextFree` (two-parameter pumping). The R-leg matters:
    `swissGermanLang` allows interleaved NP/V orderings, and the regular
    filter forces the case-sorted canonical shape needed to land in ambncmdn. -/
theorem swiss_german_not_contextFree :
    ¬ swissGermanLang.IsContextFree := by
  apply Language.not_isContextFree_via_witness tokenStringHom caseSorted
    caseSorted_isRegular
  rw [stringMap_swissGerman_inter_caseSorted_eq_ambncmdn]
  exact ambncmdn_not_contextFree

-- (Shieber §3 also notes that strong context-freeness fails as a corollary —
-- any strongly-CF analysis induces a weakly-CF string set. Since the string
-- set isn't weakly CF, no strongly-CF analysis exists. We don't separately
-- formalize this as a theorem because we have no `IsStronglyContextFree`
-- predicate distinct from `IsContextFree`; the meta-theoretic implication
-- would just be a renamed alias of `swiss_german_not_contextFree`.)

-- ============================================================================
-- §5: Grounding in the Swiss German Fragment
-- ============================================================================

/-- Verbs in the Swiss German fragment have case requirements that match
    their Token-level classification (DAT-V or ACC-V). Collapsed from three
    near-identical theorems into one decide-checked conjunction. -/
theorem fragment_case_grounding :
    verbObjectCase .haelfe = Token.caseValue .datV ∧
    verbObjectCase .loend = Token.caseValue .accV ∧
    verbObjectCase .aastriiche = Token.caseValue .accV := by decide

-- ============================================================================
-- §6: Examples from the Paper
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
