import Linglib.Discourse.SpeechAct.Update
import Linglib.Dialogue.Stalnaker
import Linglib.Dialogue.CommitmentSpace

/-!
# Assertion Theories: Cross-Theory Comparison
[brandom-1994] [cohen-krifka-2014] [farkas-bruce-2010]
[gunlogson-2001] [krifka-2015] [krifka-2020]
[lauer-2013] [stalnaker-1978]

Compares assertion theories along structural dimensions.

## Comparison Matrix

| Theory | Commitment ≠ Belief | Retraction | Source | Entitlements | Probabilistic | Meta-speech-acts |
|--------|---------------------|------------|--------|--------------|---------------|------------------|
| Stalnaker | No | No | No | No | No | No |
| F&B | Yes | No | No | No | No | No |
| Krifka 2015 | Yes | Yes | No | No | No | No |
| Krifka 2020 (JP/ComP) | Yes | Yes | No | No | No | No |
| Cohen-Krifka 2014 | Yes | Yes | No | No | No | Yes |
| Brandom | Yes | Yes | No | Yes | No | No |
| Gunlogson | Yes | Yes | Yes | No | No | No |
| Lauer | Yes | No | No | No | Yes | No |

The "Meta-speech-acts" column flags whether the framework supports
denegation `~A` and derived meta-speech-acts like GRANT (= `~ASSERT(¬·)`).
Cohen-Krifka 2014 introduced the apparatus; Krifka 2015 inherits it but
this file's row for Krifka 2015 records what's *actually formalized* in
its own study file (which scopes to §§1–5, denegation deferred to the
Cohen-Krifka 2014 study).

## Key Embeddings

1. **Stalnaker embeds in Krifka**: when commitment = belief (no lying,
   no hedging), Krifka's model collapses to Stalnaker's.
2. **F&B's dcS/dcL are Krifka commitment states**: dcS = speaker's
   commitment slate, dcL = addressee's commitment slate.
3. **Krifka 2015 and Cohen-Krifka 2014 share the commitment-space
   substrate**; Cohen-Krifka 2014 chronologically precedes and
   introduces denegation, which Krifka 2015 inherits (eq. 5).
4. **Brandom strictly richer than Stalnaker**: entitlements have no
   Stalnaker analog.
5. **Gunlogson models rising declaratives; Stalnaker cannot**.
6. **Lying**: Krifka and Brandom handle it (commitment without belief);
   Stalnaker struggles (assertion = belief update).

-/

namespace Phenomena.Assertion.Compare

-- ════════════════════════════════════════════════════
-- § 1. Comparison Matrix
-- ════════════════════════════════════════════════════

/-- Summary comparison record for one theory. -/
structure AssertionComparison where
  /-- Theory name -/
  name : String
  /-- Separates commitment from belief? -/
  separates : Bool
  /-- Supports retraction? -/
  retraction : Bool
  /-- Models source marking? -/
  source : Bool
  /-- Supports meta-speech-acts (denegation, GRANT)? -/
  metaSpeechActs : Bool := false
  deriving Repr

/-- The full comparison matrix. -/
def comparisonMatrix : List AssertionComparison :=
  [ ⟨"Stalnaker", false, false, false, false⟩
  , ⟨"Farkas & Bruce", true, false, false, false⟩
  , ⟨"Krifka 2015", true, true, false, false⟩
  , ⟨"Krifka 2020 (JP/ComP)", true, true, false, false⟩
  , ⟨"Cohen-Krifka 2014", true, true, false, true⟩
  , ⟨"Brandom", true, true, false, false⟩
  , ⟨"Gunlogson", true, true, true, false⟩
  , ⟨"Lauer", true, false, false, false⟩ ]

/-- The matrix length pin. -/
theorem matrix_correct :
    comparisonMatrix.length = 8 := rfl

/-- Cohen-Krifka 2014 is the only listed theory with substrate-level
    meta-speech-act support (denegation `~A`, GRANT). Krifka 2015 inherits
    the apparatus but its `Studies/Krifka2015.lean` formalization scopes
    to §§1–5; the denegation worked example lives in
    `Studies/CohenKrifka2014.lean`. -/
theorem only_cohen_krifka_has_meta_speech_acts :
    (comparisonMatrix.filter (·.metaSpeechActs)).map (·.name) =
      ["Cohen-Krifka 2014"] := rfl

-- ════════════════════════════════════════════════════
-- § 2. Cross-framework structural agreement via Assertable
-- ════════════════════════════════════════════════════

/-! The matrix in §1 is hand-stipulated. The substrate's
`Discourse.SpeechAct.Assertable` typeclass lets us derive cross-framework
agreement *structurally*: any framework satisfying the
`speakerAssert_subset_prior` and `speakerAssert_narrows` laws must
agree with every other such framework on the projected context set
after assertion.

Two frameworks currently instantiate `Assertable`:
`Dialogue.Stalnaker.StalnakerState` and `Dialogue.Krifka.KrifkaState`.
The theorems below show the value of polymorphism: write the proof
*once* against the typeclass, apply to *both* concrete frameworks.

This is the consumer the audit (CHANGELOG 0.230.677) flagged as
missing — without it, the typeclass's cross-framework theorems
(`speakerAssert_initial_subset`, `speakerAssert_twice_narrows`,
`speakerAssert_twice_subset_prior`) were dead code. -/

open Discourse.SpeechAct (Assertable)
open CommonGround (HasContextSet)

/-- **Polymorphic assertion-narrowing**: any `Assertable` framework
    narrows the context set by the asserted proposition. The
    headline polymorphic theorem from `Assertable.lean`, restated
    here as a Phenomena-level claim about ANY assertion theory in
    the `Assertable` family. -/
theorem any_assertable_narrows_initial
    {S W : Type*} [Assertable S W] (φ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert (Assertable.initial : S) φ) ⊆ {w | φ w} :=
  Assertable.speakerAssert_initial_subset φ

/-- **Stalnaker satisfies the polymorphic theorem**: applying
    `any_assertable_narrows_initial` at the Stalnaker instance. The
    fact that this typechecks is the structural witness that
    Stalnaker's set-intersection assertion semantics genuinely fits
    the Assertable shape. -/
theorem stalnaker_assertion_narrows {W : Type*} (φ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Stalnaker.StalnakerState W) φ) ⊆ {w | φ w} :=
  any_assertable_narrows_initial φ

/-- **Krifka satisfies the polymorphic theorem**: applying
    `any_assertable_narrows_initial` at the Krifka instance.
    Krifka's commitment-space assertion (prepending
    `commit speaker doxastic φ` to the root) gives the same
    structural narrowing despite the radically different state
    representation. -/
theorem krifka_assertion_narrows {W : Type*} (φ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Krifka.KrifkaState W) φ) ⊆ {w | φ w} :=
  any_assertable_narrows_initial φ

/-- **Cross-framework two-step narrowing**: asserting φ then ψ in
    ANY Assertable framework yields a context set ⊆ {φ ∧ ψ}.
    Polymorphic version of `speakerAssert_twice_narrows`. -/
theorem any_assertable_twice_narrows
    {S W : Type*} [Assertable S W] (s : S) (φ ψ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert (Assertable.speakerAssert s φ) ψ) ⊆
        {w | φ w ∧ ψ w} :=
  Assertable.speakerAssert_twice_narrows s φ ψ

/-- **Stalnaker satisfies two-step narrowing**. -/
theorem stalnaker_twice_narrows {W : Type*}
    (s : Dialogue.Stalnaker.StalnakerState W) (φ ψ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert (Assertable.speakerAssert s φ) ψ) ⊆
        {w | φ w ∧ ψ w} :=
  any_assertable_twice_narrows s φ ψ

/-- **Krifka satisfies two-step narrowing**. -/
theorem krifka_twice_narrows {W : Type*}
    (s : Dialogue.Krifka.KrifkaState W) (φ ψ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert (Assertable.speakerAssert s φ) ψ) ⊆
        {w | φ w ∧ ψ w} :=
  any_assertable_twice_narrows s φ ψ

/-- **Cross-framework agreement on initial-state assertion**: starting
    from `initial` in two different Assertable frameworks and
    asserting the same φ yields context sets that BOTH narrow to
    the same φ-witnesses. The polymorphic theorem fires twice with
    the same conclusion shape. The instances may have wildly
    different intermediate representations (Stalnaker = list of
    propositions; Krifka = root + continuations of indexed
    commitments), but their projected context sets agree on the
    φ-narrowing constraint.

    This is the substrate-level "cross-framework agreement"
    structural fact that the §1 matrix's "Stalnaker no separation /
    Krifka separates" rows are silent about. The matrix tracks
    representational differences; this theorem tracks observational
    agreement at the context-set level. -/
theorem stalnaker_krifka_agree_on_initial_assertion {W : Type*} (φ : W → Prop) :
    (HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Stalnaker.StalnakerState W) φ) ⊆ {w | φ w}) ∧
    (HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Krifka.KrifkaState W) φ) ⊆ {w | φ w}) :=
  ⟨any_assertable_narrows_initial φ, any_assertable_narrows_initial φ⟩

end Phenomena.Assertion.Compare
