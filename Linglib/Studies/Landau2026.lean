import Linglib.Syntax.Anaphora.Diagnostic
import Linglib.Data.Examples.Landau2026

/-!
# Landau (2026): Silent Resumption: A New Test for Ellipsis

This file formalizes the ellipsis-internal resumption test of [landau-2026]: by the ban on
vacuous quantification ([chomsky-1982]) an Ā-operator binds into a null site only if the site
has structure at LF to host a resumptive variable, so binding into a null site diagnoses a
surface anaphor, an ellipsis, in the sense of [hankamer-sag-1976]. The three diagnostics are
`Diagnostic`s over anaphoric depth: the new test decides depth (`eir_decides`), since a
resumptive dependency is fixed at LF and can be neither bled by derivational timing nor blocked
by an island, whereas the extraction and agreement tests of [merchant-2001] leave a failure
ambiguous (`extraction_not_decides`, `agreement_not_decides`) and are refined by the new test
(`eir_refines_extraction`, `eir_refines_agreement`). The paper's Hebrew nominal ellipses, where
extraction is unavailable, and its cross-linguistic mixed anaphors are rows of
`Data/Examples/Landau2026.json`, and every row's acceptability matches the prediction read off
its depth (`all_eir_consistent`).

## Implementation notes

The paper was not available for this pass, and the row annotations and example numbers carried
over from the earlier version of this file are marked as unverified. A row's depth, domain, and
the availability of extraction are read from its paper features, and passing the test is the
acceptability of the resumptive-binding sentence.

## References

* [landau-2026]
* [hankamer-sag-1976], [chomsky-1982], [merchant-2001]
-/

namespace Landau2026

-- UNVERIFIED: the example numbers and row annotations are those of the earlier version of
-- this file.

open Anaphor (Depth DepthCause)
open Data.Examples (LinguisticExample)

/-! ### Types

Anaphoric depth (deep/surface, [hankamer-sag-1976]) is the framework-neutral
substrate primitive `Anaphor.Depth`; EN/NCA/*pro*/*do so*/*dat doen*/*det* are
`.deep`, VP-ellipsis/ENP/AE/PPE are `.surface`. -/

/-- Syntactic domain of the null element. -/
inductive NullDomain where
  | nP  -- Noun phrase nucleus (complement of Num)
  | DP  -- Full determiner phrase
  | PP  -- Prepositional phrase
  | VP  -- Verb phrase
  deriving DecidableEq, Repr

/-! ### BVQ and the EIR prediction -/

/-- **EIR prediction.** A null site passes the Ellipsis-Internal Resumption test
    iff it has LF-visible internal structure (`Anaphor.Depth.HasInternalStructure`)
    — iff it is a surface anaphor. The paper's argument: by the BVQ
    ([chomsky-1982]) an Ā-operator must bind a variable at LF; a resumptive
    pronoun is that variable, and it can only be hosted inside a site with
    internal structure; so binding into a null site is licensed iff the site is a
    surface anaphor. The prediction is therefore *literally* the substrate
    structural property, not a separate stipulation. -/
abbrev PassesEIR (d : Depth) : Prop := d.HasInternalStructure

/-! ### EIR vs the classic tests (extraction, agreement)

All three are `Diagnostic`s over `Anaphor.Depth`: a pass means the site had
structure to host the variable/trace (surface). They differ only in what a
*failure* admits — and that single field is the paper's whole point. Extraction and
agreement are the two *reliable* classic diagnostics ([landau-2026], after
[merchant-2001]); EIR is the new third one. -/

/-- The **EIR test** as a depth diagnostic. A pass is `hostsVariable` (surface
    structure hosts the resumptive); a failure can *only* be a `deepAnaphor`,
    because resumptive dependencies are established at LF and cannot be bled by
    derivational timing, nor blocked by islands. -/
def eir : Diagnostic Bool Depth :=
  .ofCauses (λ pass => if pass then {.hostsVariable} else {.deepAnaphor}) DepthCause.entails

/-- The **extraction test** as a depth diagnostic. A pass is `hostsVariable`
    (surface); a failure is ambiguous — a `deepAnaphor`, or a *surface* site whose
    Ā-movement was `derivationalBleeding` (bled by ellipsis timing) or
    `islandBlocking`. That extra ambiguity is exactly the gap EIR closes. -/
def extraction : Diagnostic Bool Depth :=
  .ofCauses
    (λ pass => if pass then {.hostsVariable}
                 else {.deepAnaphor, .derivationalBleeding, .islandBlocking})
    DepthCause.entails

@[simp] theorem eir_consistent_true : eir.consistent true = {Depth.surface} := by
  simp [eir, DepthCause.entails]

@[simp] theorem eir_consistent_false : eir.consistent false = {Depth.deep} := by
  simp [eir, DepthCause.entails]

@[simp] theorem extraction_consistent_true : extraction.consistent true = {Depth.surface} := by
  simp [extraction, DepthCause.entails]

@[simp] theorem extraction_consistent_false :
    extraction.consistent false = {Depth.deep, Depth.surface} := by
  simp [extraction, DepthCause.entails, Set.image_insert_eq]

/-- **Headline — Landau's contribution.** EIR *decides* anaphoric depth: on every
    site the verdict recovers the depth exactly — a pass means surface (ellipsis),
    a failure means deep. This is what "a new test for ellipsis" amounts to,
    made precise as `Diagnostic.Decides`. -/
theorem eir_decides : eir.Decides Depth.testOutcome :=
  λ d => by cases d <;> simp [Depth.testOutcome]

/-- Extraction does **not** decide depth: on a deep site its verdict still admits
    `surface` (the failure could be a bled or island-blocked extraction), so it is
    inconclusive exactly where EIR is decisive. -/
theorem extraction_not_decides : ¬ extraction.Decides Depth.testOutcome := by
  intro h
  have hmem : Depth.surface ∈ extraction.consistent (Depth.testOutcome .deep) :=
    ⟨.derivationalBleeding, by simp [Depth.testOutcome], rfl⟩
  rw [h .deep] at hmem
  simp at hmem

/-- EIR strictly refines extraction: identical on a pass, but EIR resolves the
    failure extraction leaves open (its failure-causes are a subset). -/
theorem eir_refines_extraction : eir.Refines extraction := by
  intro o c hc
  cases o <;> simp_all [eir, extraction, DepthCause.entails]

/-- The **agreement test** as a depth diagnostic. The other *reliable* classic
    diagnostic ([landau-2026], after [merchant-2001]). A pass is `hostsVariable`
    (surface); a failure is ambiguous between a `deepAnaphor` and a surface site
    whose agreement was `derivationalBleeding` (bled by ellipsis timing). Agreement
    is not movement, so it has no island confound — but it is still inconclusive on
    failure. (It is also inapplicable in agreement-less languages, the analogue of
    `extractionAvailable = false`.) -/
def agreement : Diagnostic Bool Depth :=
  .ofCauses
    (λ pass => if pass then {.hostsVariable} else {.deepAnaphor, .derivationalBleeding})
    DepthCause.entails

@[simp] theorem agreement_consistent_false :
    agreement.consistent false = {Depth.deep, Depth.surface} := by
  simp [agreement, DepthCause.entails, Set.image_insert_eq]

/-- Agreement, like extraction, does **not** decide depth: its failure also admits
    a bled-but-surface site. EIR escapes this confound too. -/
theorem agreement_not_decides : ¬ agreement.Decides Depth.testOutcome := by
  intro h
  have hmem : Depth.surface ∈ agreement.consistent (Depth.testOutcome .deep) :=
    ⟨.derivationalBleeding, by simp [Depth.testOutcome], rfl⟩
  rw [h .deep] at hmem
  simp at hmem

/-- EIR refines agreement too — so EIR decides depth where *both* reliable classic
    tests are inconclusive, escaping both their derivational-bleeding (and, for
    extraction, island) confounds. This is Landau's actual headline: EIR matches the
    confidence of the classic diagnostics while their failure-confounds it lacks. -/
theorem eir_refines_agreement : eir.Refines agreement := by
  intro o c hc
  cases o <;> simp_all [eir, agreement, DepthCause.entails]

/-! ### Data

The empirical rows live in `Data/Examples/Landau2026.json` (typed
`LinguisticExample`s — the paper's (18a)–(47b) stimuli). The study reads each
row's EIR-relevant classification by projection: `domain`/`depth`/extraction from
`paperFeatures`, and grammaticality straight off the example's `judgment` —
passing EIR *is* the resumptive-binding sentence being acceptable. -/

private def parseDomain : String → NullDomain
  | "DP" => .DP | "PP" => .PP | "VP" => .VP | _ => .nP

private def parseDepth : String → Depth
  | "surface" => .surface | _ => .deep

/-- The null-element domain of an EIR example (from `paperFeatures`). -/
def domainOf (e : LinguisticExample) : NullDomain :=
  parseDomain ((e.paperFeatures.lookup "domain").getD "nP")

/-- The Hankamer–Sag `Anaphor.Depth` of an EIR example (from `paperFeatures`). -/
def depthOf (e : LinguisticExample) : Depth :=
  parseDepth ((e.paperFeatures.lookup "depth").getD "deep")

/-- Whether the example passes EIR — this *is* its grammaticality `judgment`: the
    resumptive-binding sentence is acceptable iff the site hosts the variable. -/
def eirGrammatical (e : LinguisticExample) : Bool :=
  match e.judgment with | .acceptable => true | _ => false

/-- Whether the extraction test is applicable to the example's domain (`false`
    for the Hebrew nominal domains, which are absolute islands). -/
def extractionAvailable (e : LinguisticExample) : Bool :=
  (e.paperFeatures.lookup "extractionAvailable").getD "true" == "true"

/-! ### Data collections

EN/NCA/*pro*/*do so*/*dat doen*/*det* are deep; ENP/AE/PPE/VP-ellipsis surface.
Each example's `comment` in the JSON carries the construction notes. -/

def hebrewData : List LinguisticExample :=
  [Examples.hebrewEN, Examples.hebrewENP, Examples.hebrewNCA_DP,
   Examples.hebrewAE, Examples.hebrewNCA_PP, Examples.hebrewPPE]

def mixedAnaphorData : List LinguisticExample :=
  [Examples.englishDoSo, Examples.dutchDatDoen, Examples.danishDet, Examples.koreanNullObj]

def crossLingData : List LinguisticExample :=
  Examples.englishVPE :: mixedAnaphorData

def allData : List LinguisticExample := Examples.all

/-! ### Summary properties

Every datum's observed grammaticality (`eirGrammatical`, off its `judgment`)
matches the `PassesEIR` prediction read off its depth — the `decide p = true ↔ p`
bridge between a recorded observation and the substrate structural property. -/

/-- All data are consistent: every example's EIR grammaticality matches the
    prediction read off its depth classification. -/
theorem all_eir_consistent :
    ∀ e ∈ allData, (eirGrammatical e = true ↔ PassesEIR (depthOf e)) := by decide

/-- Hebrew has both deep and surface strategies in all three nominal domains
    (nP, DP, PP). -/
theorem hebrew_both_depths_all_domains :
    (∃ e ∈ hebrewData, depthOf e = .deep ∧ domainOf e = .nP) ∧
    (∃ e ∈ hebrewData, depthOf e = .surface ∧ domainOf e = .nP) ∧
    (∃ e ∈ hebrewData, depthOf e = .deep ∧ domainOf e = .DP) ∧
    (∃ e ∈ hebrewData, depthOf e = .surface ∧ domainOf e = .DP) ∧
    (∃ e ∈ hebrewData, depthOf e = .deep ∧ domainOf e = .PP) ∧
    (∃ e ∈ hebrewData, depthOf e = .surface ∧ domainOf e = .PP) := by decide

/-- Extraction is unavailable for all Hebrew domains tested. This is precisely
    why the EIR test is needed: it provides syntactic evidence where the
    extraction test cannot. -/
theorem hebrew_extraction_unavailable :
    ∀ e ∈ hebrewData, extractionAvailable e = false := by decide

/-- All four cross-linguistic mixed anaphors are diagnosed as deep. -/
theorem mixed_anaphors_deep :
    ∀ e ∈ mixedAnaphorData, depthOf e = .deep := by decide

end Landau2026
