import Linglib.Semantics.Tense.LexicalType
import Linglib.Semantics.Tense.TemporalConnectives.Before
import Linglib.Semantics.Tense.SOT.Decomposition

/-!
# [sharvit-2014]: On the universal principles of tense embedding
[sharvit-2014] [ogihara-sharvit-2012] [sharvit-2003] [beaver-condoravdi-2003] [partee-1973]

[sharvit-2014] ("On the universal principles of tense embedding: The lesson from *before*",
*J. Semantics* 31(2):263-313) makes the pronominal/quantificational tense distinction (after
[partee-1973] vs Prior 1967) the engine for cross-linguistic variation in *before*-clauses
(English/Polish vs Japanese) and attitude reports. The IPF mechanism it rests on is the
[beaver-condoravdi-2003] `before` semantics (`Semantics/Tense/TemporalConnectives/Before.lean`);
the pronominal/quantificational substrate is `Semantics/Tense/LexicalType.lean`.

## Main definitions

* `Shiftability` — three-valued present shiftability ((71), p. 289): a fully shiftable
  present (Japanese), a semi-shiftable one (Polish), or a non-shiftable one (English).
* `LanguageTenseProfile` — a language's three tense parameters ((98), p. 300): the SOT rule,
  the present's shiftability, and the *past* tense's lexical type (`Option LexicalType`,
  no-mixing structural; `none` = tenseless / out of scope).
* The derived predicates (`wellFormedPastUnderPastBefore`, …) are grounded in the substrate, not
  re-stipulated: well-formedness routes through `Before.triggersIPFInBefore`, SOT-deletion through
  `Decomposition.sotDeletionApplicable`.
* `eq99a`/`eq99b`/`eq99c` — Sharvit's three universal predictions ((99), p. 301).

## Scope

In the typology: English (type 6), Polish (type 10), Japanese (type 11) of (98). Excluded:
Modern Greek and Spanish A/B (§6.2, (105), pp. 303-304), which need a mood parameter and — for
Spanish B — a *mixed* past/present lexical type this profile cannot represent (Sharvit frames them
as illustrative, p. 305); and tenseless languages (`pastLexicalType = none`), outside the
no-tenseless assumption (§6.1, p. 299).
-/

namespace Sharvit2014

open Tense (LexicalType)
open Tense.TemporalConnectives.Before (triggersIPFInBefore)
open Tense.SOT.Decomposition (sotDeletionApplicable)

/-! ### The parameter space ((98)) -/

/-- The present tense's shiftability, three-valued per [sharvit-2014] (71)/(78), pp. 288-291:
    Japanese is fully shiftable, Polish semi-shiftable (bindable, but not by the same binder as
    its referential index), English non-shiftable (forced free). The distinction is load-bearing:
    only a *fully* shiftable present yields a well-formed present-under-past *before*-clause, so
    Polish patterns with English there despite being bindable in attitudes. -/
inductive Shiftability
  /-- Forced free; cannot be bound (English). -/
  | nonShiftable
  /-- Bindable, but not by the binder of its referential index (Polish). -/
  | semiShiftable
  /-- Freely bindable (Japanese). -/
  | fullyShiftable
  deriving DecidableEq, Repr

/-- A language's tense profile per [sharvit-2014] (98), p. 300: the SOT rule, the present's
    shiftability, and the *past* tense's lexical type. The no-mixing assumption (§6.1, p. 300)
    is enforced structurally by `Option LexicalType` (one past type, or `none` for tenseless). -/
structure LanguageTenseProfile where
  /-- The SOT rule: deletion of an agreeing embedded tense. -/
  hasSOT : Bool
  /-- The present tense's shiftability ((71), p. 289). -/
  presentShiftability : Shiftability
  /-- The *past* tense's lexical type, or `none` for tenseless languages (outside
      [sharvit-2014]'s framework). -/
  pastLexicalType : Option LexicalType
  deriving DecidableEq, Repr

namespace LanguageTenseProfile

/-- The language has tenses ([sharvit-2014]'s no-tenseless precondition, §6.1, p. 299). -/
def hasTenses (L : LanguageTenseProfile) : Bool := L.pastLexicalType.isSome

/-- The past tense is pronominal (after [partee-1973]). -/
def isPronominal (L : LanguageTenseProfile) : Bool := L.pastLexicalType == some .pronominal

/-- The past tense is quantificational (after Prior 1967). -/
def isQuantificational (L : LanguageTenseProfile) : Bool :=
  L.pastLexicalType == some .quantificational

/-- The present can be bound at all (semi- or fully shiftable) — enough to host a
    "now"-thought in attitudes. -/
def hasShiftablePresent (L : LanguageTenseProfile) : Bool :=
  L.presentShiftability != .nonShiftable

/-- The present is *fully* shiftable (Japanese), the condition for a well-formed
    present-under-past *before*-clause ((78), p. 291). -/
def hasFullyShiftablePresent (L : LanguageTenseProfile) : Bool :=
  L.presentShiftability == .fullyShiftable

/-! ### Derived empirical predicates

These are not independent stipulations: the *before*-well-formedness predicate routes through the
[beaver-condoravdi-2003] IPF dispatch `Before.triggersIPFInBefore`, and the SOT-derived predicates
through Kratzer's deletion condition `Decomposition.sotDeletionApplicable`. -/

/-- SOT-deletion of an agreeing past-under-past applies when the language has the SOT rule, routed
    through `Decomposition.sotDeletionApplicable` (Kratzer's morphological-identity condition, here
    `.past`/`.past`). -/
def sotAppliesPastUnderPast (L : LanguageTenseProfile) : Bool :=
  L.hasSOT && sotDeletionApplicable Tense.past Tense.past

/-- PAST-under-PAST in *before* is well-formed iff the past does not trigger IPF — the
    technical core `Before.ipf_quantificationalPast`. The body calls the IPF dispatch
    `Before.triggersIPFInBefore`; `wellFormedPastUnderPastBefore_iff_pronominal` records the
    resulting equivalence to `isPronominal` (= `Before.pastUnderBefore_wellFormed_iff`). -/
def wellFormedPastUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  match L.pastLexicalType with
  | some τ => !triggersIPFInBefore τ
  | none   => false

/-- PRES-under-PAST in *before* is well-formed iff the present is *fully* shiftable (the Stump
    effect, p. 278): English (non-shiftable) and Polish (semi-shiftable) are both ruled out; only
    Japanese is well-formed ((78), p. 291). -/
def wellFormedPresentUnderPastBefore (L : LanguageTenseProfile) : Bool :=
  L.hasFullyShiftablePresent

/-- "Simultaneous" past-under-past reading in attitude reports ((59b), p. 284): the past is
    pronominal and SOT-deletion applies. This is the *SOT-derived* reading; Japanese's distinct
    (present-tense) simultaneous reading ((47), p. 280) is a different mechanism, not this. -/
def simultaneousAttitudeReading (L : LanguageTenseProfile) : Bool :=
  L.isPronominal && L.sotAppliesPastUnderPast

/-- **Bare** *before*-clause p-shiftability ((51), p. 281): the embedded past can refer to a
    future time. Requires a quantificational past (Japanese); absent in English/Polish. -/
def pShiftabilityBare (L : LanguageTenseProfile) : Bool := L.isQuantificational

/-- **Embedded** *before*-clause p-shiftability ((66)-(68), p. 287): under a matrix attitude verb,
    even pronominal-past languages acquire p-shiftability via SOT-deletion of the matrix past.
    (Hedged in the paper — "for many speakers".) -/
def pShiftabilityEmbedded (L : LanguageTenseProfile) : Bool :=
  L.isQuantificational || (L.isPronominal && L.sotAppliesPastUnderPast)

/-- [sharvit-2014]'s Embeddability Principle (Sharvit 2003, restated p. 299): every language has
    at least one mechanism for embedding a "now"-thought (SOT, a shiftable present, or a
    quantificational past). -/
def respectsEmbeddability (L : LanguageTenseProfile) : Bool :=
  L.hasSOT || L.hasShiftablePresent || L.isQuantificational

/-- A pronominal past is not quantificational — the `Option LexicalType` no-mixing constraint. -/
theorem isQuantificational_eq_false_of_isPronominal (L : LanguageTenseProfile) :
    L.isPronominal = true → L.isQuantificational = false := by
  intro h
  have : L.pastLexicalType = some .pronominal := by
    simpa [isPronominal] using h
  simp [isQuantificational, this]

/-- Well-formedness of past-under-past in *before* coincides with a pronominal past — imported
    from the IPF result (`Before.pastUnderBefore_wellFormed_iff`), not re-stipulated. -/
theorem wellFormedPastUnderPastBefore_iff_pronominal (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true ↔ L.isPronominal = true := by
  cases hτ : L.pastLexicalType with
  | none => simp [wellFormedPastUnderPastBefore, isPronominal, hτ]
  | some τ => cases τ <;> simp [wellFormedPastUnderPastBefore, isPronominal, triggersIPFInBefore, hτ]

end LanguageTenseProfile

/-! ### Attested language types ((98), p. 300) -/

/-- English (type 6 in (98)): SOT, non-shiftable present, pronominal past. -/
def english : LanguageTenseProfile where
  hasSOT := true
  presentShiftability := .nonShiftable
  pastLexicalType := some .pronominal

/-- Polish (type 10 in (98)): no SOT, semi-shiftable present, pronominal past. The
    "semi-shiftable" hedge (§4.2) distinguishes Polish from Japanese: Polish's present is
    bindable in attitudes but not fully shiftable, so present-under-past in *before* is still
    ill-formed (it patterns with English, not Japanese). Grønn & von Stechow argue against the
    parameter, attributing the Polish pattern to Aktionsart; the encoding here follows Sharvit. -/
def polish : LanguageTenseProfile where
  hasSOT := false
  presentShiftability := .semiShiftable
  pastLexicalType := some .pronominal

/-- Japanese (type 11 in (98)): no SOT, fully-shiftable present, quantificational past. The
    quantificational classification follows [ogihara-1996], the canonical and dominant view;
    it is contested by relative-tense alternatives (Kusumoto 1999, Sudo 2012). -/
def japanese : LanguageTenseProfile where
  hasSOT := false
  presentShiftability := .fullyShiftable
  pastLexicalType := some .quantificational

/-- The attested language types in Sharvit's table ((98)). -/
def attestedTypes : List LanguageTenseProfile := [english, polish, japanese]

/-! ### Structural constraints (§6.1) -/

/-- Every attested language has tenses (the no-tenseless assumption holds within scope). -/
theorem all_attested_have_tenses : ∀ L ∈ attestedTypes, L.hasTenses = true := by decide

/-- Every attested language respects [sharvit-2014]'s Embeddability Principle. -/
theorem all_attested_respect_embeddability :
    ∀ L ∈ attestedTypes, L.respectsEmbeddability = true := by decide

/-! ### Cross-linguistic predictions ((99), p. 301)

Stated and proved over *all* profiles, not the three attested rows: each prediction follows
structurally from the parameter definitions and the substrate grounding. -/

/-- [sharvit-2014] (99a): a well-formed present-under-past in *before* implies a shiftable present.
    Non-trivial under the three-valued `Shiftability`: well-formedness needs *full* shiftability,
    which strictly implies the weaker "shiftable at all" (Polish witnesses the gap). -/
theorem eq99a_pres_under_past_before_implies_shiftable (L : LanguageTenseProfile) :
    L.wellFormedPresentUnderPastBefore = true → L.hasShiftablePresent = true := by
  cases hs : L.presentShiftability <;>
    simp [LanguageTenseProfile.wellFormedPresentUnderPastBefore,
      LanguageTenseProfile.hasFullyShiftablePresent, LanguageTenseProfile.hasShiftablePresent, hs]

/-- [sharvit-2014] (99b): well-formed PAST-under-PAST in *before* + embedded p-shiftability ⇒
    a simultaneous reading of past-under-past in attitudes. Given a pronominal past (from
    well-formedness), the `isQuantificational` disjunct of `pShiftabilityEmbedded` vanishes, so the
    embedded p-shiftability *is* the SOT-deletion that licenses the simultaneous reading. -/
theorem eq99b_before_and_embedded_pshift_imply_simultaneous (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true → L.pShiftabilityEmbedded = true →
      L.simultaneousAttitudeReading = true := by
  intro hwf hemb
  have hpron : L.isPronominal = true :=
    (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mp hwf
  have hquant : L.isQuantificational = false :=
    LanguageTenseProfile.isQuantificational_eq_false_of_isPronominal L hpron
  simp only [LanguageTenseProfile.pShiftabilityEmbedded, hquant, hpron, Bool.false_or,
    Bool.true_and] at hemb
  simp only [LanguageTenseProfile.simultaneousAttitudeReading, hpron, Bool.true_and]
  exact hemb

/-- [sharvit-2014] (99c): well-formed PAST-under-PAST in *before* + no simultaneous reading ⇒
    No-p-shiftability of bare past-under-past *before*. Under this encoding the consequent already
    follows from well-formedness (a pronominal past is not quantificational, so the bare clause
    lacks p-shiftability); the no-simultaneous antecedent (`_hNoSim`) is Sharvit's, kept for
    fidelity to (99c) but not load-bearing here. -/
theorem eq99c_before_and_no_simultaneous_imply_no_bare_pshift (L : LanguageTenseProfile) :
    L.wellFormedPastUnderPastBefore = true → L.simultaneousAttitudeReading = false →
      L.pShiftabilityBare = false := by
  intro hwf _hNoSim
  have hpron : L.isPronominal = true :=
    (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mp hwf
  exact LanguageTenseProfile.isQuantificational_eq_false_of_isPronominal L hpron

/-! ### Substrate connection: IPF and quantificational past

The `wellFormedPastUnderPastBefore` predicate is grounded in the [beaver-condoravdi-2003] IPF
result formalized in `TemporalConnectives/Before.lean`; the two theorems below consume that
grounding via `wellFormedPastUnderPastBefore_iff_pronominal`. -/

/-- Quantificational-past languages (Japanese) fail `wellFormedPastUnderPastBefore`, matching the
    IPF prediction (`Before.ipf_quantificationalPast`). -/
theorem quant_past_languages_fail_before (L : LanguageTenseProfile) :
    L.isQuantificational = true → L.wellFormedPastUnderPastBefore = false := by
  intro h
  have : L.pastLexicalType = some .quantificational := by
    simpa [LanguageTenseProfile.isQuantificational] using h
  simp [LanguageTenseProfile.wellFormedPastUnderPastBefore, this, triggersIPFInBefore]

/-- Pronominal-past languages (English, Polish) satisfy `wellFormedPastUnderPastBefore`, in keeping
    with `Before.pastUnderBefore_wellFormed_iff`. -/
theorem pronominal_past_languages_pass_before (L : LanguageTenseProfile) :
    L.isPronominal = true → L.wellFormedPastUnderPastBefore = true :=
  fun h => (LanguageTenseProfile.wellFormedPastUnderPastBefore_iff_pronominal L).mpr h

/-! ### Per-language payload

The central typological contrast — and a regression guard on the three-valued shiftability: a
binary `shiftablePresent` would wrongly make Polish's present-under-past in *before* well-formed. -/

example : japanese.pShiftabilityBare = true := rfl
example : english.pShiftabilityBare = false := rfl
example : polish.wellFormedPresentUnderPastBefore = false := rfl
example : japanese.wellFormedPresentUnderPastBefore = true := rfl

/-! ### Cross-paper bridge to [kratzer-1998]

The Sharvit ↔ [klecha-2016] comparison (same simultaneous-reading prediction, different
mechanisms) lives in the later paper's study file, `Studies/Klecha2016.lean §F1`. -/

/-- [sharvit-2014]'s prediction for English: SOT + pronominal past yields the simultaneous reading
    of past-under-past in attitudes. -/
theorem english_predicts_simultaneous : english.simultaneousAttitudeReading = true := rfl

/-- Bridge to [kratzer-1998]: English's SOT rule realizes Kratzer's deletion of an agreeing
    past-under-past — `english.hasSOT` and Kratzer's morphological-identity condition
    (`Decomposition.sotDeletionApplicable .past .past`) jointly license the "null" embedded past. -/
theorem english_sot_realizes_kratzer_deletion :
    english.sotAppliesPastUnderPast = true := rfl

end Sharvit2014
