import Linglib.Theories.Semantics.Tense.LexicalType
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Before
import Linglib.Theories.Semantics.Tense.SOT.Decomposition
import Linglib.Theories.Semantics.Tense.SOT.Ambiguity

/-!
# @cite{sharvit-2014}: On the universal principles of tense embedding
@cite{sharvit-2014} @cite{ogihara-sharvit-2012} @cite{sharvit-2003}
@cite{beaver-condoravdi-2003} @cite{partee-1973}

@cite{sharvit-2014} ("On the universal principles of tense embedding: The
lesson from *before*", *J. Semantics* 31(2):263-313) makes the
cross-linguistic distinction between **pronominal** and **quantificational**
tense (after @cite{partee-1973} vs Prior 1967) the central engine for
explaining variation in *before*-clauses (English/Polish vs Japanese) and
attitude reports (English vs Polish vs Japanese).

The pronominal/quantificational substrate is in
`Theories/Semantics/Tense/LexicalType.lean`; the
@cite{beaver-condoravdi-2003} `before` semantics + IPF mechanism is in
`Theories/Semantics/Tense/TemporalConnectives/Before.lean`.

## Sharvit's parameter space (numbered example (98), p. 300)

A tensed language is characterized by three Boolean/typed parameters:

- `hasSOT` — whether the language has the SOT rule (delete an embedded
  agreeing tense)
- `shiftablePresent` — whether the present tense's evaluation index can
  be bound (vs. forced free)
- `tenseLexicalType : Option LexicalType` — pronominal or quantificational
  (Sharvit's no-mixing assumption is enforced *structurally* by the
  `Option` type: at most one type per language); `none` indicates a
  tenseless language, falling outside Sharvit's framework

Tenseless languages (Mandarin per Lin 2003-2010; St'át'imcets per
@cite{matthewson-2006}; Medumba per Mucha 2017; Yucatec per Bohnemeyer
2002) are not in Sharvit's scope; they fall under future Studies files
that would extend the substrate. The `tenseLexicalType = none` case is
present as scaffolding.

## Predictions (numbered example (99), p. 301)

Three universal predictions Sharvit derives from this parameter space,
each kernel-checked over the attested-type table:

1. **(99a)**: a language with well-formed PRES-under-PAST in *before*
   exhibits p-shiftability (rather than No-p-shiftability) in
   present-under-past
2. **(99b)**: a language with well-formed PAST-under-PAST in *before*
   AND embedded p-shiftability has "simultaneous" readings of
   past-under-past in attitudes
3. **(99c)**: a language with well-formed PAST-under-PAST in *before*
   AND no "simultaneous" readings exhibits No-p-shiftability of
   past-under-past *before*

## Scope qualifications

- **No-mixing assumption** (§6.1, p. 300): structurally enforced by
  `tenseLexicalType : Option LexicalType` (the `Option` cannot carry both
  values).
- **No-tenseless assumption** (§6.1, p. 299): predictions apply only to
  tensed languages, encoded as the `hasTenses` precondition. Languages
  challenging this assumption (St'át'imcets, Medumba, Mandarin) require a
  separate study file.
- **Modern Greek** (§6.2, parameters in (105a) on p. 304): excluded from
  the typology table pending bib support for the "semantic subjunctive"
  parameter, which Sharvit herself frames as "merely to illustrate this
  point" (p. 305).
- **Spanish A vs B** (§6.2, parameters in (105b/c) on p. 304; fn 17 on
  p. 302): excluded pending independent dialect-typological support —
  Sharvit's footnote 17 acknowledges the Peninsular/River Plate divide is
  unclear.

## Provenance

The earlier `Studies/Sharvit2014.lean` was a 124-LOC orphan whose F5
theorem went through a fictitious `SimultaneousTense` struct in
`Embedded/Simultaneous.lean` (Phase G, 0.230.462, deleted that
substrate). This rewrite (Phase H, 0.230.463) restructures the typology
to use `Option LexicalType` (no-mixing structural), splits
`pShiftability` into bare-vs-embedded after a 2-round audit identified
the predicate as overloaded, drops `modernGreek` pending bib support,
and corrects locator hallucinations ("table 98" → "(98)", "eq 105" →
"(105)" — Sharvit numbers them as examples, not as tables/equations).
-/

namespace Phenomena.TenseAspect.Studies.Sharvit2014

open Semantics.Tense (LexicalType)
open Semantics.Tense.TemporalConnectives.Before

/-! ### §1. The parameter space (Sharvit's numbered example (98)) -/

/-- A language's tense profile per @cite{sharvit-2014} (98), p. 300.
    The no-mixing assumption is enforced structurally by
    `tenseLexicalType : Option LexicalType`; tenselessness is `none`. -/
structure LanguageTenseProfile where
  /-- The SOT rule: deletion of an agreeing embedded tense. -/
  hasSOT          : Bool
  /-- The present's evaluation index can be bound (vs forced free). -/
  shiftablePresent : Bool
  /-- The language's tense lexical type, or `none` for tenseless
      languages (outside Sharvit's framework). -/
  tenseLexicalType : Option LexicalType
  deriving DecidableEq, Repr

namespace LanguageTenseProfile

/-- Sharvit's "tensed language" precondition (§6.1, p. 299). -/
@[simp] def hasTenses (L : LanguageTenseProfile) : Bool :=
  L.tenseLexicalType.isSome

/-- The language's past tense is pronominal (after @cite{partee-1973}). -/
@[simp] def isPronominal (L : LanguageTenseProfile) : Bool :=
  L.tenseLexicalType == some .pronominal

/-- The language's past tense is quantificational (after Prior 1967). -/
@[simp] def isQuantificational (L : LanguageTenseProfile) : Bool :=
  L.tenseLexicalType == some .quantificational

/-! Derived empirical predicates. The substrate facts in
    `TemporalConnectives/Before.lean` (`ipf_quantificationalPast` +
    `pastUnderBefore_wellFormed_iff`) determine these definitions; they
    are not independent stipulations. -/

/-- Sharvit's claim: PAST-under-PAST in *before* is well-formed iff the
    past is pronominal — quantificational past triggers IPF (proved in
    `Before.ipf_quantificationalPast`). -/
@[simp] def wellFormedPastUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  L.isPronominal

/-- Sharvit's claim: PRES-under-PAST in *before* is well-formed iff the
    present is shiftable (the Stump effect, p. 278). -/
@[simp] def wellFormedPresentUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  L.shiftablePresent

/-- Sharvit's claim: a language has "simultaneous" readings of
    past-under-past in attitude reports iff its past is pronominal AND
    the SOT rule is available ((59b), p. 284). -/
@[simp] def simultaneousAttitudeReading (L : LanguageTenseProfile) : Bool :=
  L.isPronominal && L.hasSOT

/-- **Bare** *before*-clause p-shiftability (Sharvit example (51), p.
    281): the embedded past in "John left before Sally arrived" can refer
    to a future Sally-arrival time. Requires quantificational past:
    Japanese has it, English/Polish do not. -/
@[simp] def pShiftabilityBare (L : LanguageTenseProfile) : Bool :=
  L.isQuantificational

/-- **Embedded** *before*-clause p-shiftability (Sharvit examples (66)-
    (68), p. 287): when the bare *before*-clause is itself embedded
    under a matrix attitude verb, even pronominal-past languages acquire
    p-shiftability via SOT-deletion of the matrix past. -/
@[simp] def pShiftabilityEmbedded (L : LanguageTenseProfile) : Bool :=
  L.isQuantificational || (L.isPronominal && L.hasSOT)

/-- @cite{sharvit-2014}'s Embeddability Principle (Sharvit 2003, restated
    p. 299): every language has at least one mechanism for embedding a
    "now"-thought (SOT-deletion, shiftable present, or quantificational
    past). -/
@[simp] def respectsEmbeddability (L : LanguageTenseProfile) : Bool :=
  L.hasSOT || L.shiftablePresent || L.isQuantificational

end LanguageTenseProfile

/-! ### §2. Attested language types (numbered example (98)) -/

/-- English (type 6 in (98), p. 300): SOT, non-shiftable present,
    pronominal past. -/
def english : LanguageTenseProfile where
  hasSOT          := true
  shiftablePresent := false
  tenseLexicalType := some .pronominal

/-- Polish (type 10 in (98), p. 300): no SOT, semi-shiftable present
    (counts as shiftable for the typology), pronominal past. The
    "semi-shiftable" hedge in §4.2 is a Sharvit-internal refinement
    distinguishing Polish from Japanese; Grønn & von Stechow have argued
    against the parameter, attributing the Polish pattern to Aktionsart
    instead. Encoding here follows Sharvit; see linguistics audit
    findings (round-2). -/
def polish : LanguageTenseProfile where
  hasSOT          := false
  shiftablePresent := true
  tenseLexicalType := some .pronominal

/-- Japanese (type 11 in (98), p. 300): no SOT, fully-shiftable present,
    quantificational past. The quantificational classification is in
    line with @cite{ogihara-1996}, the canonical reference; it is the
    dominant view but contested by relative-tense alternatives
    (Kusumoto 1999, Sudo 2012). -/
def japanese : LanguageTenseProfile where
  hasSOT          := false
  shiftablePresent := true
  tenseLexicalType := some .quantificational

/-- The attested language types in Sharvit's table.

    Excluded: Modern Greek (§6.2; pending bib support for the semantic
    subjunctive parameter), Spanish A and B (§6.2; the dialectal split is
    a Sharvit-internal device per fn 17). Tenseless languages
    (St'át'imcets, Medumba, Mandarin) are out of scope per Sharvit's
    no-tenseless assumption and would land in separate Studies files. -/
def attestedTypes : List LanguageTenseProfile :=
  [english, polish, japanese]

/-! ### §3. Structural constraints (§6.1) -/

/-- Every attested language has tenses (Sharvit's no-tenseless
    assumption holds within scope). -/
theorem all_attested_have_tenses :
    ∀ L ∈ attestedTypes, L.hasTenses = true := by decide

/-- Every attested language respects @cite{sharvit-2014}'s Embeddability
    Principle (Sharvit 2003, restated p. 299). -/
theorem all_attested_respect_embeddability :
    ∀ L ∈ attestedTypes, L.respectsEmbeddability = true := by decide

/-! ### §4. Cross-linguistic predictions (Sharvit's numbered example (99)) -/

/-- @cite{sharvit-2014} (99a), p. 301: a well-formed present-under-past
    in *before* implies the language has a shiftable present.
    Definitional under our derivation discipline (the well-formedness
    predicate is *defined* via shiftability per the Stump-effect
    argument, p. 278) — the typology theorem witnesses that the
    derivation goes through on every attested type. -/
theorem eq99a_pres_under_past_before_implies_shiftable :
    ∀ L ∈ attestedTypes, L.hasTenses = true →
      L.wellFormedPresentUnderPastBefore = true → L.shiftablePresent = true := by
  decide

/-- @cite{sharvit-2014} (99b), p. 301: well-formed PAST-under-PAST in
    *before* + embedded p-shiftability ⇒ simultaneous reading of
    past-under-past in attitudes. The substantive content: given (99b's
    antecedent (1)) `isPronominal`, the `isQuantificational` disjunct of
    `pShiftabilityEmbedded` is false; so the antecedent (2) reduces to
    `isPronominal ∧ hasSOT`, which is exactly `simultaneousAttitudeReading`. -/
theorem eq99b_before_and_embedded_pshift_imply_simultaneous :
    ∀ L ∈ attestedTypes, L.hasTenses = true →
      L.wellFormedPastUnderPastBefore = true →
      L.pShiftabilityEmbedded = true →
      L.simultaneousAttitudeReading = true := by
  decide

/-- @cite{sharvit-2014} (99c), p. 301: well-formed PAST-under-PAST in
    *before* + no simultaneous reading in attitudes ⇒ No-p-shiftability
    of bare past-under-past *before*. Contrapositive of the Japanese-
    case generalization: the bare *before*-clause needs quantificational
    past for p-shiftability, but pronominal+no-SOT languages (Polish)
    lack both the simultaneous attitude reading AND the bare *before*
    p-shiftability. -/
theorem eq99c_before_and_no_simultaneous_imply_no_bare_pshift :
    ∀ L ∈ attestedTypes, L.hasTenses = true →
      L.wellFormedPastUnderPastBefore = true →
      L.simultaneousAttitudeReading = false →
      L.pShiftabilityBare = false := by
  decide

/-! ### §5. Per-language verifications -/

example : english.wellFormedPastUnderPastBefore = true := rfl

example : english.simultaneousAttitudeReading = true := rfl

example : english.pShiftabilityBare = false := rfl

example : english.pShiftabilityEmbedded = true := rfl

example : japanese.wellFormedPastUnderPastBefore = false := rfl

example : japanese.pShiftabilityBare = true := rfl

example : polish.wellFormedPastUnderPastBefore = true := rfl

example : polish.simultaneousAttitudeReading = false := rfl

example : polish.pShiftabilityBare = false := rfl

example : polish.pShiftabilityEmbedded = false := rfl

/-! ### §6. Substrate connection: IPF kills quantificational past

The `wellFormedPastUnderPastBefore` predicate is justified by the
@cite{beaver-condoravdi-2003} IPF result formalized in
`TemporalConnectives/Before.lean`. -/

/-- Quantificational-past languages (Japanese) fail
    `wellFormedPastUnderPastBefore`, matching the IPF prediction
    (`Before.ipf_quantificationalPast`). -/
theorem quant_past_languages_fail_before :
    ∀ L ∈ attestedTypes,
      L.isQuantificational = true → L.wellFormedPastUnderPastBefore = false := by
  decide

/-- Pronominal-past languages (English, Polish) satisfy
    `wellFormedPastUnderPastBefore`, in keeping with
    `Before.pastUnderBefore_wellFormed_iff`. -/
theorem pronominal_past_languages_pass_before :
    ∀ L ∈ attestedTypes,
      L.isPronominal = true → L.wellFormedPastUnderPastBefore = true := by
  decide

/-! ### §7. Cross-paper bridge: Sharvit ↔ Klecha on past-under-past

@cite{klecha-2016}'s DOX + NPST modal-base derivation predicts the
simultaneous reading from semantic NPST under doxastic accessibility.
@cite{sharvit-2014}'s SOT + pronominal-past derivation predicts the same
reading from morphological deletion of the embedded past. The agreement
is at the *value layer*; the *mechanism* divergence — Klecha's modal
base vs Sharvit's SOT — is real and discussed in
`Studies/Klecha2016.lean §F1`. -/

/-- @cite{sharvit-2014}'s prediction for English: SOT + pronominal past →
    simultaneous reading of past-under-past in attitudes. -/
theorem english_predicts_simultaneous :
    english.simultaneousAttitudeReading = true := rfl

/-- The bridge to @cite{kratzer-1998}: when SOT applies in English,
    Sharvit's pronominal-past-with-SOT and Kratzer's deletion mechanism
    both produce a tense-stripped embedded clause. -/
theorem english_sot_matches_kratzer :
    english.hasSOT = true ∧
    Semantics.Tense.SOT.Decomposition.sotDeletionApplicable .past .past = true :=
  ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Studies.Sharvit2014
