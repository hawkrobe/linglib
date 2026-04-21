import Linglib.Phenomena.Polarity.Studies.Hoeksema1983
import Linglib.Phenomena.Comparison.Studies.Heim2001
import Linglib.Phenomena.Comparison.Studies.Bresnan1973
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalism.DegreeMovement
import Linglib.Theories.Semantics.Degree.ThanClause
import Linglib.Core.Lexical.PolarityItem

/-!
# Bhatt & Pancheva 2004: Late Merger of Degree Clauses
@cite{bhatt-pancheva-2004} @cite{heim-2000} @cite{williams-1974}
@cite{lebeaux-1988} @cite{takahashi-hulsey-2009} @cite{hoeksema-1983}
@cite{bresnan-1973}

Rajesh Bhatt and Roumyana Pancheva. Late Merger of Degree Clauses.
*Linguistic Inquiry* 35(1): 1–45.

## What this file is and isn't

This file is a paper-faithful study of B&P 2004. It does **not** define
late merger or the Heim-Kennedy Constraint — those live in the
syntax–semantics interface module
`Theories/Interfaces/SyntaxSemantics/Minimalism/DegreeMovement.lean`,
which itself imports `Theories/Syntax/Minimalism/Core/LateMerger.lean`
(generic late merger, polymorphic in admissibility) and
`Theories/Semantics/Degree/Comparative.lean` (set-of-degrees comparative
operator). What this file *does* is instantiate that infrastructure for
the empirical claims of B&P, and bridge to neighbouring studies.

## B&P's claims, mapped to this file

- **§3** Late merger of degree clauses. The degree clause is a
  comparative-deletion construction that merges countercyclically with
  DegP after movement. We instantiate `lateMergerBleeds` at the
  degree-specific admissibility predicate and witness the Condition C
  bleeding profile via `degree_lm_bleeds_iff_scope_position_above`.
- **§4.1** Heim-Kennedy Constraint. We use `IsHeimKennedy` from the
  interface module and witness B&P's characteristic prohibition.
- **§5.1** Late merger of degree clauses bleeds Condition C. Captured
  by `degree_lm_bleeds_iff_scope_position_above` (§ 1 below).
- **§5.2** Williams 1974 derived from HKC. We bridge to
  @cite{heim-2001}'s intensional-verb data via
  `bp_hkc_matches_heim_intensional_data` (§ 3 below).
- **§3.9 (Hoeksema 1983 link)** Reduction theorem demoted to
  corollary: `thanClause_reduces_to_max` is one line of
  order-theoretic plumbing, not the substance of the paper.
- **§1.1.1 fn. 4** B&P explicitly reject @cite{bresnan-1973}'s view
  that phrasal "than NP" reduces to clausal "than NP is Adj". Captured
  as prose only (see closing note); the analytical machinery to encode
  the disagreement compositionally lives in @cite{bhatt-takahashi-2011}.

## Polarity remarks

A naive worry: if the surface NP-comparative reduces to an underlying
S-source, does Hoeksema's polarity asymmetry collapse? No. The
reduction is at the level of *values*, not *signatures*: NP-comparative
is a Boolean homomorphism over GQs (signature `.mono`), S-comparative
is anti-additive over degree sets (signature `.antiAdd`). The
licensing-context registry tracks this distinction, and
`reduction_preserves_polarity_signatures` witnesses that B&P's
syntactic uniformity claim does not unify Hoeksema's two algebraic
types.

-/

namespace BhattPancheva2004

open Hoeksema1983
open Bresnan1973 (BresnanThanClauseAnalysis bresnanAnalysisOf)
open Heim2001 (IntensionalVerbDatum intensionalVerbData)
open Minimalism (lateMergerBleeds wlmBleedsCondC ChainPosition admissible_above_binder_bleeds)
open Minimalism.Semantics.DegreeMovement
  (DegreeChainPosition degreeClauseLateMergerBleeds scopeOK_above_binder_bleeds
   ScopeBinding IsHeimKennedy not_isHeimKennedy_QP_above_bound_DegP
   isHeimKennedy_no_dependency isHeimKennedy_dependency_requires_high_DegP
   williams_scope_correlation williams_exempt_when_no_binding)
open Semantics.Degree.Comparative (sComparative sComparative_eq_singleton_of_isGreatest)
open Semantics.Degree.ThanClause (thanClauseDenotation thanClauseMax thanClauseMax_isGreatest)
open Core.Lexical.PolarityItem (LicensingContext contextProperties)

variable {Entity : Type*}

-- ════════════════════════════════════════════════════
-- § 1. Late merger of degree clauses (B&P §3, §5.1)
-- ════════════════════════════════════════════════════

/-- Instantiation of the generic WLM bleeding profile at the
    degree-clause admissibility predicate (`scopeOK`): a scope-licit
    chain position strictly above the pronoun binder bleeds
    Condition C for late-merged degree clauses. The substantive §5.1
    content — that degree-clause late merger *exhibits* the same
    Cond-C-bleeding asymmetry as adjuncts and NP restrictors — is the
    *use* of this theorem against minimal pairs, which would require
    encoding the §5.1 stimulus contrasts. We do not formalize those
    contrasts here. -/
theorem degree_lm_bleeds_iff_scope_position_above
    (chain : List DegreeChainPosition) (binderHeight h : Nat)
    (hgt : h > binderHeight) :
    degreeClauseLateMergerBleeds (⟨h, true⟩ :: chain) binderHeight = true :=
  scopeOK_above_binder_bleeds chain binderHeight h hgt

-- ════════════════════════════════════════════════════
-- § 2. Heim-Kennedy Constraint (B&P §4.1)
-- ════════════════════════════════════════════════════

/-- B&P §4.1: HKC's characteristic prohibition. A QP whose trace is
    in the DegP's restrictor cannot scope strictly above the DegP at
    LF. Direct application of the interface lemma. -/
theorem hkc_blocks_QP_above_bound_DegP
    (degH qpH : Nat) (h : degH < qpH) :
    ¬ IsHeimKennedy ⟨degH, qpH, qpH, true⟩ :=
  not_isHeimKennedy_QP_above_bound_DegP degH qpH h

-- ════════════════════════════════════════════════════
-- § 3. Williams 1974 derived (B&P §5.2)
-- ════════════════════════════════════════════════════

/-- B&P's analytic hypothesis about the intensional-verb data: a verb
    is in the high-DegP-blocking class iff its (raised) subject binds
    into the DegP's restrictor. This function packages the hypothesis
    as a `ScopeBinding` per datum, parameterized by the LF heights of
    the DegP and the intensional verb.

    UNVERIFIED: B&P do not state this as a single equation; the claim
    is reconstructed from B&P §5.2's discussion of Williams 1974 plus
    Heim 2001's observation about which verbs admit the DegP-high
    reading. -/
def bpHypothesizedBinding (d : IntensionalVerbDatum)
    (degHeight intHeight : Nat) : ScopeBinding :=
  ⟨degHeight, intHeight, intHeight, !d.highDegPAvailable⟩

/-- Non-vacuous bridge to @cite{heim-2001}: under B&P's hypothesis
    (`bpHypothesizedBinding`) that high-DegP-blocking iff binding-tail,
    the Heim-Kennedy Constraint reproduces Heim's 4-vs-4 pattern
    *exactly* on the DegP-low LF (where the matrix DegP scopes below
    the intensional verb): HKC permits the LF iff the verb allows
    high-DegP.

    This theorem is *not* a constant — both sides depend on the
    datum's `highDegPAvailable` field. The empirical content is that
    B&P's binding hypothesis correctly predicts Heim's per-verb
    blocking pattern. -/
theorem bp_hkc_matches_heim_intensional_data :
    ∀ d ∈ intensionalVerbData,
      IsHeimKennedy (bpHypothesizedBinding d 0 1) ↔ d.highDegPAvailable = true := by
  intro d _
  cases h : d.highDegPAvailable <;>
    simp [bpHypothesizedBinding, IsHeimKennedy, h]

-- ════════════════════════════════════════════════════
-- § 4. Reduction theorem (B&P §3.9 link to Hoeksema 1983)
-- ════════════════════════════════════════════════════

/-- B&P's clausal-source than-clause denotation `{d | d ≤ μ b}`
    collapses to the singleton `{μ b}` when fed to the S-comparative.
    Direct corollary of `sComparative_eq_singleton_of_isGreatest`
    instantiated at the than-clause's greatest element (the standard's
    measure). -/
theorem thanClause_reduces_to_max
    {D : Type*} [Preorder D] (μ : Entity → D) (b : Entity) :
    sComparative μ (thanClauseDenotation μ b) =
      sComparative μ ({μ b} : Set D) :=
  sComparative_eq_singleton_of_isGreatest μ (thanClauseMax_isGreatest μ b)

/-- Combining @cite{hoeksema-1983} §3.9 (the principal-ultrafilter /
    singleton-degree-set equivalence) with the B&P reduction:
    Hoeksema's NP-comparative GQ on `Q_b` equals the S-comparative on
    the *full* clausal-source than-clause denotation. This is the
    algebraic content of B&P's claim that "than NP" and "than [NP is
    Adj]" deliver coextensive predicates. -/
theorem npGQ_principal_eq_sComp_thanClause
    {D : Type*} [Preorder D] (μ : Entity → D) (b : Entity) :
    npComparativeGQ μ (principalUltrafilter b) =
      sComparative μ (thanClauseDenotation μ b) := by
  rw [npComparativeGQ_principal_eq_sComparative_singleton,
      ← thanClause_reduces_to_max]

-- ════════════════════════════════════════════════════
-- § 5. Polarity asymmetry preserved
-- ════════════════════════════════════════════════════

/-- The B&P reduction is a coincidence of *values*, not of *signatures*.
    The licensing-context registry continues to classify the
    NP-comparative slot as `.mono` (Boolean hom over GQs) and the
    S-comparative slot as `.antiAdd` (over degree sets). The reduction
    cannot be used to argue that NP-comparatives are NPI environments,
    because the reduction's range is the S-comparative's degree-set
    domain, not the NP-comparative's GQ domain. The proof packages
    Hoeksema's two registry theorems so that any future change to
    either signature surfaces here as a recompile failure. -/
theorem reduction_preserves_polarity_signatures :
    (contextProperties .comparativeNP).signature = .mono ∧
    (contextProperties .comparativeS).signature = .antiAdd :=
  ⟨comparativeNP_signature_monotone, comparativeS_signature_anti_additive⟩

/- ## Note on the Bresnan 1973 contrast (B&P §1.1.1 fn. 4)

B&P explicitly reject @cite{bresnan-1973}'s view that surface phrasal
"than NP" reduces to clausal "than NP is Adj" via AP-deletion + copula
stranding (Bresnan's `.maximalDeletion`). On B&P's analysis the phrasal
form is genuinely phrasal — no clausal source.

The disagreement is at the level of *underlying syntactic structure*,
and the diagnostic apparatus needed to derive distinguishing predictions
(binding minimal pairs in the style of Lechner 2004; idiom-chunk tests,
scope diagnostics, ECM cases) is not encoded here. The disagreement is
*formalized* in @cite{bhatt-takahashi-2011} (see
`Phenomena/Comparison/Studies/BhattTakahashi2011.lean`), which supplies
the binding battery (`englishBindingPairs` + `realizesReduction`) and
reaches the conclusion that English in fact patterns with B&T's
Reduction Analysis, vindicating Bresnan's clausal-source view against
B&P's direct view. The cross-tradition bridge is
`bt2011_agrees_with_bresnan_against_bp2004` in that file.

The extensional content of the two analyses agrees for proper-name
standards: `npGQ_principal_eq_sComp_thanClause` (above) shows that the
NP-comparative GQ on `Q_b` and the S-comparative on the than-clause
denotation deliver the same predicate. Their *intensional* difference
— what underlying structure each posits — is what the BT2011 binding
diagnostic resolves empirically. -/

end BhattPancheva2004
