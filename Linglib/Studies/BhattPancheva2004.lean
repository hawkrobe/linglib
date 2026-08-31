import Linglib.Studies.Hoeksema1983
import Linglib.Semantics.Polarity.Licensing
import Linglib.Studies.Heim2001
import Linglib.Studies.Bresnan1973
import Linglib.Syntax.Minimalist.Movement.DegreeMovement
import Mathlib.Order.Interval.Set.LinearOrder
import Linglib.Semantics.Polarity.Item

/-!
# Bhatt & Pancheva 2004: Late Merger of Degree Clauses
[bhatt-pancheva-2004] [heim-2000] [williams-1974]
[lebeaux-1988] [takahashi-hulsey-2009] [hoeksema-1983]
[bresnan-1973]

Rajesh Bhatt and Roumyana Pancheva. Late Merger of Degree Clauses.
*Linguistic Inquiry* 35(1): 1–45.

## What this file is and isn't

This file is a paper-faithful study of B&P 2004. It does **not** define
late merger or the Heim-Kennedy Constraint — those live in the
syntax–semantics interface module
`Syntax/Minimalist/DegreeMovement.lean`,
which itself imports `Syntax/Minimalism/LateMerger.lean`
(generic late merger, polymorphic in admissibility) and
`Semantics/Degree/Comparative.lean` (set-of-degrees comparative
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
- **§4.2, §5.2** The intensional-verb scope data and the Extraposition-Scope
  Generalization ((39): "at least as high" from countercyclic merger, "exactly as high"
  from §7). We bridge to [heim-2001]'s intensional-verb table via
  `bp_hkc_matches_heim_intensional_data` (§ 3 below).
- **§7** Nonconservativity ((84), (86)) makes early merger contradictory, deriving (90):
  degree clauses merge only at their ultimate scope position —
  `erSem_inter_contradictory`, `erSem_not_conservative`.
- **Hoeksema link** (this file's bridge — B&P do not cite [hoeksema-1983]; §3.9 is
  Hoeksema's section): `thanClause_reduces_to_max` connects B&P's clausal-source
  denotation to the `Studies/Hoeksema1983.lean` registry in one line of order plumbing.
- **§1.1, fn. 4** B&P adopt the essence of [bresnan-1973]'s -er-decomposition
  (more = -er + many); fn. 4 declines only much-insertion in synthetic forms, and
  §1.1.1 leaves the ellipsis analysis of phrasal "than NP" open (see the closing
  note).

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
open Minimalist (lateMergerBleeds wlmBleedsCondC ChainPosition admissible_above_binder_bleeds)
open Minimalist.DegreeMovement
  (degreeClauseLateMergerBleeds scopeOK_above_binder_bleeds
   ScopeBinding IsHeimKennedy not_isHeimKennedy_QP_above_bound_DegP
   isHeimKennedy_no_dependency isHeimKennedy_dependency_requires_high_DegP
   williams_scope_correlation williams_exempt_when_no_binding)
open Core.Order (Comparison)
open Degree (gtOverSet_eq_singleton_of_isGreatest)
open Polarity (LicensingContext)
open Polarity (LicensingContext)

variable {Entity : Type*}

/-! ### Late merger of degree clauses (B&P §3, §5.1) -/

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
    (chain : List ChainPosition) (binderHeight h : Nat)
    (hgt : h > binderHeight) :
    degreeClauseLateMergerBleeds (⟨h, true⟩ :: chain) binderHeight = true :=
  scopeOK_above_binder_bleeds chain binderHeight h hgt

/-! ### Heim-Kennedy Constraint (B&P §4.1) -/

/-- B&P §4.1: HKC's characteristic prohibition. A QP whose trace is
    in the DegP's restrictor cannot scope strictly above the DegP at
    LF. Direct application of the interface lemma. -/
theorem hkc_blocks_QP_above_bound_DegP
    (degH qpH : Nat) (h : degH < qpH) :
    ¬ IsHeimKennedy ⟨degH, qpH, qpH, true⟩ :=
  not_isHeimKennedy_QP_above_bound_DegP degH qpH h

/-! ### Williams 1974 derived (B&P §5.2) -/

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

/-- Non-vacuous bridge to [heim-2001]: under B&P's hypothesis
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

/-! ### Reduction to the Hoeksema registry ([hoeksema-1983] §3.9)

This bridge is the file's, not the paper's: B&P do not cite Hoeksema. -/

/-- B&P's clausal-source than-clause denotation `{d | d ≤ μ b}` (the
    standard's positive extent `Set.Iic (μ b)`) collapses to the singleton
    `{μ b}` when fed to the S-comparative. Direct corollary of
    `gtOverSet_eq_singleton_of_isGreatest` instantiated at the
    than-clause's greatest element (`isGreatest_Iic`). -/
theorem thanClause_reduces_to_max
    {D : Type*} [Preorder D] (μ : Entity → D) (b : Entity) :
    Comparison.gt.overSet μ (Set.Iic (μ b)) =
      Comparison.gt.overSet μ ({μ b} : Set D) :=
  gtOverSet_eq_singleton_of_isGreatest μ isGreatest_Iic

/-- Combining [hoeksema-1983] §3.9 (the principal-ultrafilter /
    singleton-degree-set equivalence) with the B&P reduction:
    Hoeksema's NP-comparative GQ on `Q_b` equals the S-comparative on
    the *full* clausal-source than-clause denotation — the coextensiveness of
    "than NP" and "than [NP is Adj]" for proper-name standards, which §1.1.1's
    comparative-ellipsis remark presupposes. -/
theorem npGQ_principal_eq_sComp_thanClause
    {D : Type*} [Preorder D] (μ : Entity → D) (b : Entity) :
    npComparativeGQ μ (principalUltrafilter b) =
      Comparison.gt.overSet μ (Set.Iic (μ b)) := by
  rw [npComparativeGQ_principal_eq_gtOverSet_singleton,
      ← thanClause_reduces_to_max]

/-! ### Polarity asymmetry preserved -/

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
    LicensingContext.phrasalComparative.properties.strawsonSignature = .mono ∧
    LicensingContext.clausalComparative.properties.strawsonSignature = .antiAdd :=
  ⟨comparativeNP_signature_monotone, comparativeS_signature_anti_additive⟩

/-! ### Nonconservativity forces late merger (B&P §7)

Trace Conversion turns the lower copy of a moved [-er + degree clause] into a definite
over the standard set, so early merger feeds `-er` its own first argument intersected
into the second ((87)). For a conservative quantifier this is harmless ((82)); for `-er`
— standard ⊊ target ((84)) — it is a contradiction ((86)), and further covert movement
of [-er + degree clause] recreates it. Hence (90): degree clauses are merged only in
their ultimate scope position — the "exactly as high" half of the Extraposition-Scope
Generalization ((39)). -/

/-- The comparative degree quantifier over degree sets ((84)): the standard is a proper
    subset of the target. -/
def erSem {D : Type*} (A B : Set D) : Prop := A ⊂ B

/-- Early merger is contradictory ((86), (87)): after Trace Conversion the second
    argument is intersected with the first, and `A ⊂ A ∩ B` is unsatisfiable. -/
theorem erSem_inter_contradictory {D : Type*} (A B : Set D) : ¬ erSem A (A ∩ B) :=
  fun h => h.not_subset Set.inter_subset_left

/-- `-er` is not conservative ((82) vs (86)): on a nonempty degree domain no equivalence
    `Q A B ↔ Q A (A ∩ B)` can hold for it. -/
theorem erSem_not_conservative {D : Type*} [Nonempty D] :
    ¬ ∀ A B : Set D, erSem A B ↔ erSem A (A ∩ B) :=
  fun h => erSem_inter_contradictory (∅ : Set D) Set.univ
    ((h ∅ Set.univ).mp (Set.empty_ssubset.mpr Set.univ_nonempty))

/- ## Note on the Bresnan 1973 relationship (B&P §1.1, fn. 4)

B&P adopt "the essence of Bresnan's analysis" of comparative determiners (more = -er +
many/much, less = -er + little, fewer = -er + few; §1.1); fn. 4's departure concerns
only much-insertion in synthetic adjectival forms such as happier. On phrasal "than NP"
the 2004 text takes no stand: §1.1.1 notes that the phrasal (12) can be assimilated to
the clausal (11) via comparative ellipsis, leaving the clausal-source question open.

`Studies/BhattTakahashi2011.lean` casts B&P 2004 as proponents of a direct (non-clausal)
analysis of English phrasal comparatives (`englishAnalysisPerBhattPancheva2004`,
`bt2011_agrees_with_bresnan_against_bp2004`). That attribution is not supported by the
2004 text; whether it is [bhatt-takahashi-2011]'s own framing awaits that paper. The
extensional agreement for proper-name standards is `npGQ_principal_eq_sComp_thanClause`
above. -/

end BhattPancheva2004
