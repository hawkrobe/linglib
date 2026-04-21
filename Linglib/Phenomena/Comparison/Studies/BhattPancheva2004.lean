import Linglib.Phenomena.Polarity.Studies.Hoeksema1983
import Linglib.Theories.Semantics.Degree.ThanClause
import Linglib.Core.Lexical.PolarityItem

/-!
# Bhatt & Pancheva 2004: Late Merger of Degree Clauses
@cite{bhatt-pancheva-2004} @cite{hoeksema-1983}

Rajesh Bhatt and Roumyana Pancheva. Late Merger of Degree Clauses.
*Linguistic Inquiry* 35(1): 1–45.

## Core Claim

Surface "than NP" comparatives have an underlying clausal source: the
than-clause merges late at LF, after `-er` has raised. The than-clause
denotes a *set of degrees* (the downward-closed predicate
`{d | d ≤ μ b}` for a proper-name standard `b`); the comparative
operator compares the maxima of the matrix predicate and the
than-clause predicate.

## Structural connection to Hoeksema 1983

@cite{hoeksema-1983} §3.9 (Eq. 44) already proved an algebraic version
of this reduction for proper-name standards: the *NP-comparative GQ*
(a `CompleteLatticeHom`) applied to the principal ultrafilter `Q_b`
coincides with the *S-comparative* applied to the singleton degree
set `{μ b}`. We extend this here to the *full* clausal-source than-
clause denotation `{d | d ≤ μ b}`:

```
sComparative μ {μ b}                     (Hoeksema §3.9 endpoint)
  = sComparative μ (thanClauseDenotation μ b)   (B&P clausal-source endpoint)
  = npComparativeGQ μ (principalUltrafilter b)  (Hoeksema §3.9 + Bhatt-Pancheva)
```

The collapse is mathematical, not syntactic: the S-comparative is
anti-additive (Hoeksema Fact 4), so passing it `{μ b}` versus the
whole downward-closed set `{d | d ≤ μ b}` yields the same predicate.

## Polarity asymmetry survives the reduction

A naive worry: if the surface NP-comparative reduces to an underlying
S-source, does Hoeksema's polarity asymmetry collapse? No. The
reduction is at the level of *values*: the NP-comparative GQ applied
to `Q_b` and the S-comparative applied to `{d | d ≤ μ b}` deliver the
same set of entities. The *signatures* on which Zwarts's NPI theory
operates remain distinct: NP-comparative is a Boolean hom (signature
`.mono` over GQs); S-comparative is anti-additive (signature
`.antiAdd` over degree sets). The licensing-context registry tracks
this distinction, and the theorem
`reduction_preserves_polarity_signatures` witnesses that B&P's
syntactic reduction does not unify Hoeksema's two algebraic types.

This is the 2026 picture: B&P's late merger is a syntactic uniformity
claim; Hoeksema's polarity asymmetry is an algebraic-signature claim;
they coexist on different layers.

-/

namespace BhattPancheva2004

open Hoeksema1983
open Semantics.Degree.Comparative (sComparative sComparative_eq_singleton_of_isGreatest)
open Semantics.Degree.ThanClause (thanClauseDenotation thanClauseMax thanClauseMax_isGreatest)
open Core.Lexical.PolarityItem (LicensingContext contextProperties)

variable {Entity : Type*}

/-! ## §3: Reduction theorem -/

/-- B&P's clausal-source than-clause denotation `{d | d ≤ μ b}`
    collapses to the singleton `{μ b}` when fed to the S-comparative.
    Direct corollary of `sComparative_eq_singleton_of_isGreatest`
    instantiated at the than-clause's greatest element (the standard's
    measure). The proof requires no linearity, only `[Preorder D]` and
    `IsGreatest` of `Iic`. -/
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
    Adj]" deliver coextensive predicates — but note that B&P's actual
    syntactic claim (which this theorem does *not* witness) is that
    the two surface forms are nevertheless syntactically distinct
    (B&P §1.1.1 fn. 4, contra @cite{bresnan-1973}). -/
theorem npGQ_principal_eq_sComp_thanClause
    {D : Type*} [Preorder D] (μ : Entity → D) (b : Entity) :
    npComparativeGQ μ (principalUltrafilter b) =
      sComparative μ (thanClauseDenotation μ b) := by
  rw [npComparativeGQ_principal_eq_sComparative_singleton,
      ← thanClause_reduces_to_max]

/-! ## §4: Polarity asymmetry preserved -/

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

end BhattPancheva2004
