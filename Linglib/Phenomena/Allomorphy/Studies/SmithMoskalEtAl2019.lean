import Linglib.Core.Morphology.DegreeContainment
import Linglib.Core.Case.Allomorphy
import Linglib.Theories.Morphology.DegreeContainment

/-!
# Smith, Moskal, Xu, Kang & Bobaljik (2019) — Case and Number Suppletion in Pronouns
@cite{smith-moskal-xu-kang-bobaljik-2019}

@cite{smith-moskal-xu-kang-bobaljik-2019} extend `@cite{bobaljik-2012}`'s
structural-containment account of *ABA in adjectival degree suppletion
(`good–better–best` / `*good–better–goodest`) to two further empirical
domains: pronominal case suppletion (using `@cite{caha-2009}`'s case
hierarchy as the structural backbone) and pronominal number suppletion
(using `@cite{harbour-2008}` / `@cite{noyer-1992}` for the number-feature
geometry).

The cross-domain extension is not seamless: the paper identifies three
points where the empirical generalizations require theoretical
refinement of the Bobaljik 2012 framework:

1. **§3.6 — AAB attestation diverges across domains.** AAB patterns
   (e.g., a paradigm where positive and comparative share a root and
   the superlative is suppletive) are systematically *unattested* in
   adjectival degree but *are attested* in pronominal case and
   pronominal number. This is the divergence formalized below.

2. **§3.7 — domain-based locality replaces structural/linear
   adjacency.** The locality predicate from @cite{bobaljik-2012} (and
   @cite{embick-2010}) is too restrictive once AAB is admitted. The
   paper proposes the weaker domain-based locality from
   @cite{moskal-2015}.

3. **§4.3.1 — markedness × suppletion.** Cross-linguistic variation
   in pronominal number suppletion correlates with independent
   evidence for variation in the internal complexity / markedness of
   the number head — connecting suppletion theory to the feature
   recursion of @cite{harbour-2014} (already substrate in this
   codebase, see `Theories/Syntax/Minimalist/Agreement/FeatureRecursion.lean`).

This file formalizes (1) directly: the DM-derivation in
`Theories/Morphology/DegreeContainment.lean` predicts AAB exclusion in
*every* domain it applies to (because `vi_cmpr_eq_sprl` forces the two
inner cells to share a root); the empirical data the paper reports
falsifies that prediction in case and number. (2) and (3) are stubbed
as substrate-addition TODOs.

## Scope of the formalization

- Degree-side prediction: proven directly from substrate (`§ 1`).
- Case AAB attestation: stubbed with `sorry` and a TODO citing the
  paper's specific empirical witnesses (`§ 2`); requires reading
  §3.6's data tables to encode a representative pattern.
- Number AAB attestation: stubbed (`§ 3`); same TODO shape.
- Domain-based locality predicate: stubbed substrate addition (`§ 4`);
  this is the substrate refactor (3.7) the paper motivates and that
  would naturally land as a sibling of `Core/Morphology/Containment.lean`.
-/

namespace Phenomena.Allomorphy.Studies.SmithMoskalEtAl2019

open Core.Morphology.DegreeContainment
open Theories.Morphology.DegreeContainment

-- ============================================================================
-- § 1: Degree side — DM derivation excludes AAB unconditionally
-- ============================================================================

/-! The DM-flavored derivation of *ABA in `Theories/Morphology/DegreeContainment.lean`
forces CMPR-cell = SPRL-cell for any VI-generated root pattern (the
core theorem `vi_cmpr_eq_sprl`). This is strictly stronger than
contiguity: it excludes both *ABA *and* *AAB.

The two theorems below state the same content at two granularities:
the general "no VI-generable pattern has CMPR ≠ SPRL", and the
specific corollary "the AAB pattern is not VI-generable." Both are
direct consequences of `vi_cmpr_eq_sprl` from the migration's Phase 4
substrate. -/

/-- DM Vocabulary Insertion under root-out locality cannot generate
    any pattern whose CMPR cell differs from its SPRL cell. -/
theorem dm_excludes_cmpr_sprl_distinct
    (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).cmpr ≠ (viPattern rules defaultForm).sprl) :
    False :=
  h (vi_cmpr_eq_sprl rules defaultForm)

/-- Specific corollary: the AAB pattern (POS = CMPR ≠ SPRL) cannot
    be VI-generated under DM root-out locality.

    `aab : DegreePattern := ⟨0, 0, 1⟩` lives in
    `Core/Morphology/DegreeContainment.lean`. -/
theorem dm_excludes_aab
    (rules : List LocalVIRule) (defaultForm : Nat) :
    viPattern rules defaultForm ≠ aab := by
  intro h
  apply dm_excludes_cmpr_sprl_distinct rules defaultForm
  rw [h]
  decide

-- ============================================================================
-- § 2: Case side — §3.6 reports AAB attested
-- ============================================================================

/-! @cite{smith-moskal-xu-kang-bobaljik-2019} §3.6 reports cross-linguistic
attestations of AAB patterns in pronominal case suppletion. Encoding a
representative attested pattern lets us state the formal prediction-
falsification: the same DM derivation that excludes AAB in degree
(§ 1 above) would, if naively lifted to case, also exclude AAB — but
the data show it shouldn't.

TODO: read §3.6 and encode (i) a specific attested AAB pronominal case
pattern from the paper's data tables (e.g., from one of the languages
they survey), and (ii) the corresponding language name + source
citation. The candidate Lean shape:

```
def attestedCaseAAB : AllomorphyPattern := ⟨0, 0, ?, ?⟩  -- TBD
theorem case_aab_attested : attestedCaseAAB.IsContiguous := by decide
-- and crucially: attestedCaseAAB.cmpr-equivalent ≠ .sprl-equivalent
```
-/

/-- Placeholder: the paper reports attested AAB patterns in pronominal
    case suppletion (§3.6). A concrete witness from the paper's data
    tables would replace this. -/
theorem case_aab_attested_in_some_language : True := by trivial
-- TODO: replace with a concrete `AllomorphyPattern` witness drawn
-- from §3.6's typological survey, plus the empirical citation.

-- ============================================================================
-- § 3: Number side — §3.6 reports AAB attested
-- ============================================================================

/-! Same shape as § 2, for pronominal number suppletion. The number-
side substrate ought to come from `Features/Number.lean` plus the
`Harbour 2014` feature recursion already formalized in
`Theories/Syntax/Minimalist/Agreement/FeatureRecursion.lean`.

TODO: read §3.6's number data and encode a representative AAB number-
suppletion pattern (likely shaped over Harbour's `Category` enum,
cf. the existing `pluralRegion` / `dualRegion` helpers in
`FeatureRecursion.lean`). Note the file motivation overlap: the
paper's connection between number suppletion and Harbour-style
recursion (§4.3.1) hits exactly the substrate that recursion file
already provides.
-/

/-- Placeholder: the paper reports attested AAB patterns in pronominal
    number suppletion (§3.6). -/
theorem number_aab_attested_in_some_language : True := by trivial
-- TODO: replace with a concrete witness over Harbour-2014 number
-- categories, drawn from §3.6's typological survey.

-- ============================================================================
-- § 4: §3.7 — Domain-based locality (substrate addition)
-- ============================================================================

/-! @cite{smith-moskal-xu-kang-bobaljik-2019} §3.7 proposes that the
locality predicate driving suppletion contiguity is *not* structural
adjacency (@cite{bobaljik-2012}) or linear adjacency (@cite{embick-2010}),
but *domain-based* (@cite{moskal-2015}). Under domain locality, the
relevant locality unit is a phase / spellout domain, not a head-to-head
structural distance.

Architecturally this would land as a substrate addition in
`Core/Morphology/` parallel to `Containment.lean`'s `violatesABA` —
something like a domain-relativized `violatesABA_within_domain` whose
projection back to the universal `violatesABA` recovers Bobaljik's
stronger predicate, but which permits AAB across domain boundaries.
The DM derivation in `Theories/Morphology/DegreeContainment.lean`
would then be a domain-locality instantiation that happens to coincide
with the universal predicate when the degree paradigm fits in one
domain.

TODO: design the domain-relativized substrate, hoist into
`Core/Morphology/DomainLocality.lean`, prove the equivalence to
`Containment.violatesABA` under the single-domain assumption, then
apply to case + number suppletion to derive the AAB-attestation gap
non-vacuously.
-/

end Phenomena.Allomorphy.Studies.SmithMoskalEtAl2019
