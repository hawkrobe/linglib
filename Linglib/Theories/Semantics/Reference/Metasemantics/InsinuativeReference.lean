import Linglib.Theories.Semantics.Reference.Metasemantics.Coordination

/-!
# Insinuative reference
@cite{ney-2026}

A speaker uses *insinuative reference* when she utters a directly-
referential expression (typically a demonstrative or "supplementive" in
@cite{king-2013}'s sense — `this`, `those`, `it`) under conditions
where the lexical meaning and salient context license multiple
referents, her actual ("unavowed") intended referent is one of them
while at least one *avowable* alternative could be felicitously claimed
instead, and **she intends to preserve deniability** about the unavowed
intent.

## What this file formalizes vs. what it doesn't

`HasInsinuativeStructure licenses s` captures the *structural* pattern
— multi-licensed referents with a distinguished intended one — but NOT
the speaker-side intent to preserve deniability. The full phenomenon is
the conjunction of the structural pattern and the deniability intent;
the latter is left for a future extension when there is a downstream
consumer that needs to discriminate it (e.g., from pseudo-insinuative
speech, where the structure is present but the intent is absent — see
@cite{ney-2026} §2 (17), the 4chan triple-parentheses case).

## Distinguishing the phenomenon (Ney 2026 §2)

Insinuative reference is distinct from:
- @cite{camp-2018} insinuation: there the speaker intends the unavowed
  content as Gricean *implicature*; here the unavowed referent is the
  expression's *semantic value*.
- @cite{stanley-2015} / @cite{henderson-mccready-2018} /
  @cite{henderson-mccready-2024} / @cite{khoo-2017} dogwhistles:
  those depend on particular conventionalized lexical items;
  insinuative reference is a metasemantic strategy applicable to any
  directly-referential expression.
- @cite{saul-2018} / @cite{saul-2024} intentional overt dogwhistles:
  the closest analogue, but Saul's apparatus depends on a
  partitioned audience; insinuative reference can occur with a
  single hearer.
- @cite{tuters-hagen-2020} pseudo-insinuative speech: structurally
  similar but lacks genuine intent to preserve deniability.

## The shape gap exposed by this file

`HasInsinuativeStructure` requires *multiple* simultaneously-licensed
referents per context. The existing `Demonstratives.lean` types encode
a context's referent functionally (`demonstratum : C → Option E`), so
they cannot host this directly. We work around the gap by taking
`licenses : E → Prop` as an abstract input parameter — the shape of
predicate that a refactored relational `demonstratum` would expose.

The principled fix is to refactor `TrueDemonstrative.demonstratum` to
a relation `Demonstrates : C → E → Prop` (or `C → Set E`), mirroring
the `HasFiberedLookup` move in `Dynamic/Core/`. That refactor is out
of scope for the present file but tracked as a known shape problem.

## What this file proves

- `HasInsinuativeStructure` — the structural pattern as a Prop
- `Scenario` — a fully-spelled-out scenario (intention + licensing +
  both interlocutors' conceptions of reasonableness)
- `Scenario.kingNeyReconstruction_implies_neyRevision` — King's
  reconstruction ≤ Ney's revision
- `exists_ney_succeeds_kingNeyReconstruction_fails` — there is a
  genuine gap: scenarios where Ney's revised account succeeds while
  King's binary reconstruction does not. This is the formal counterpart
  of @cite{ney-2026} §4's resolution.

## What this file does not prove (and why)

The full @cite{ney-2026} §3 `<ONE>`-`<FOUR>` derivation requires
formalizing "available from the common ground" as a relation between
propositions and `CG W` plus a closure principle (something like
"if `P` is true and `P` being available is a CG matter, then `P` is
in CG"). The current `Core/Semantics/CommonGround.lean` provides only
flat `CG W = List (Set W)`. A `commonBelief` operator exists in
`Theories/Semantics/Modality/EpistemicLogic.lean` but is not yet
bridged to `CG W`. The genuine-gap theorem
`exists_ney_succeeds_kingNeyReconstruction_fails` is sufficient to
discriminate the two accounts; the structural derivation is downstream
work.
-/

namespace Semantics.Reference.Metasemantics
namespace InsinuativeReference

open Semantics.Reference.Basic
open Core.CommonGround

universe u v w

variable {C : Type u} {W : Type v} {E : Type w}

/-! ## The structural pattern -/

/-- A speaker intention exhibits the *structural pattern of insinuative
reference* with respect to a licensing predicate iff the unavowed
(intended) referent is licensed *and* at least one avowable
(≠ unavowed) referent is also licensed.

This Prop is the *structure* the phenomenon exhibits, not the full
phenomenon: the speaker's intent to preserve deniability is part of the
phenomenon (@cite{ney-2026} §2) but is not encoded here. See file
docstring. -/
def HasInsinuativeStructure (licenses : E → Prop)
    (s : SpeakerIntention C W E) : Prop :=
  licenses s.intendedRef ∧ ∃ r, r ≠ s.intendedRef ∧ licenses r

/-- The avowable alternative referents are those that are licensed but
distinct from the unavowed intention. -/
def avowableAlternatives (licenses : E → Prop) (s : SpeakerIntention C W E) :
    Set E :=
  {r | r ≠ s.intendedRef ∧ licenses r}

theorem hasInsinuativeStructure_iff (licenses : E → Prop)
    (s : SpeakerIntention C W E) :
    HasInsinuativeStructure licenses s ↔
      licenses s.intendedRef ∧ (avowableAlternatives licenses s).Nonempty := by
  unfold HasInsinuativeStructure avowableAlternatives
  constructor
  · rintro ⟨h₁, r, hne, hr⟩; exact ⟨h₁, ⟨r, hne, hr⟩⟩
  · rintro ⟨h₁, r, hne, hr⟩; exact ⟨h₁, r, hne, hr⟩

/-! ## Fully-spelled-out scenarios -/

/-- A complete insinuative-reference scenario:
- the speaker intention,
- the licensing predicate (which referents the expression + context
  permit as semantic values),
- the speaker's conception of reasonableness `RS`,
- the actual hearer's conception of reasonableness `RH`,
- the witnesses that the unavowed referent is licensed and that an
  avowable alternative exists. -/
structure Scenario (C : Type u) (W : Type v) (E : Type w) where
  intention            : SpeakerIntention C W E
  licenses             : E → Prop
  RS                   : ConceptionOfReasonableness C W E
  RH                   : ConceptionOfReasonableness C W E
  unavowed_licensed    : licenses intention.intendedRef
  has_avowable         : ∃ r, r ≠ intention.intendedRef ∧ licenses r

namespace Scenario

variable {C : Type u} {W : Type v} {E : Type w}

/-- Every `Scenario` exhibits the structural pattern. -/
theorem hasInsinuativeStructure (sc : Scenario C W E) :
    HasInsinuativeStructure sc.licenses sc.intention :=
  ⟨sc.unavowed_licensed, sc.has_avowable⟩

/-- King's binary reconstruction of the coordination account on the
scenario: succeed iff both conceptions cover the intention. -/
def kingNeyReconstructionSucceeds (sc : Scenario C W E) (cg : CG W) : Prop :=
  Account.coordination.kingNeyReconstruction sc.RS sc.RH sc.intention cg

/-- Ney's revised account on the scenario: succeed iff at least one
conception covers the intention. -/
def neyRevisionSucceeds (sc : Scenario C W E) (cg : CG W) : Prop :=
  Account.coordination.neyRevision sc.RS sc.RH sc.intention cg

/-- Scenario-level restatement of
`Account.kingNeyReconstruction_le_neyRevision`. -/
theorem kingNeyReconstruction_implies_neyRevision (sc : Scenario C W E) (cg : CG W) :
    sc.kingNeyReconstructionSucceeds cg → sc.neyRevisionSucceeds cg :=
  Account.kingNeyReconstruction_le_neyRevision sc.RS sc.RH sc.intention cg

end Scenario

/-! ## The genuine gap (Ney 2026 §4)

@cite{ney-2026}'s argument hinges on there being insinuative-reference
scenarios where the *joint* conception covers the intention but the
*shared* conception does not — the speaker's conception covers, the
actual hearer's does not.

In such scenarios:
- Ney's revised account succeeds: the joint covers.
- King's binary reconstruction fails: the shared does not cover.
- The deniability that motivated Ney's revision is preserved: the
  intention need not be available from CG, because the "shared"
  conception (which would close the `<ONE>`-`<FOUR>` argument) does
  not in fact cover.

We exhibit the gap with a small concrete witness over `Bool`. -/

/-- A two-element entity universe witness exhibiting the gap.

`speaker := false`, `intendedRef := true`. The expression is the
constant character returning `intendedRef`. The licensing predicate
admits both `true` and `false` (so the structural pattern holds). The
speaker's conception covers everything (`fun _ => True`); the
hearer's conception covers only intentions whose `intendedRef` is
`false` — so it does *not* cover this intention.

Result: Ney's joint-conception account succeeds (via the speaker's
conception); King's binary reconstruction fails (the hearer's does
not cover). -/
def gapWitness : Scenario Unit Unit Bool where
  intention :=
    { speaker     := false
    , expression  := { character := fun _ _ => true
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := true }
  licenses          := fun _ => True
  RS                := fun _ => True
  RH                := fun s => s.intendedRef = false
  unavowed_licensed := trivial
  has_avowable      := ⟨false, by decide, trivial⟩

theorem gapWitness_hasInsinuativeStructure :
    HasInsinuativeStructure gapWitness.licenses gapWitness.intention :=
  gapWitness.hasInsinuativeStructure

theorem gapWitness_neyRevisionSucceeds (cg : CG Unit) :
    gapWitness.neyRevisionSucceeds cg :=
  Or.inl trivial

theorem gapWitness_not_kingNeyReconstructionSucceeds (cg : CG Unit) :
    ¬ gapWitness.kingNeyReconstructionSucceeds cg := by
  intro h
  exact Bool.true_eq_false_eq_False h.right

/-- @cite{ney-2026} (end of §4): there are insinuative-reference
scenarios where Ney's revised coordination account succeeds while
King's binary reconstruction fails. This is the formal counterpart of
Ney's resolution — the two accounts genuinely diverge on the
phenomenon. -/
theorem exists_ney_succeeds_kingNeyReconstruction_fails :
    ∃ (sc : Scenario Unit Unit Bool) (cg : CG Unit),
      HasInsinuativeStructure sc.licenses sc.intention ∧
      sc.neyRevisionSucceeds cg ∧
      ¬ sc.kingNeyReconstructionSucceeds cg :=
  ⟨gapWitness, CG.empty,
   gapWitness_hasInsinuativeStructure,
   gapWitness_neyRevisionSucceeds _,
   gapWitness_not_kingNeyReconstructionSucceeds _⟩

/-! ## Anaphora discriminator (Ney 2026 §3, "thirdly")

@cite{ney-2026} §3 ("thirdly", pp. 21–22) uses anaphora-availability
as positive evidence that the unavowed referent is a genuine *semantic
value* (not a @cite{camp-2018}-style implicature):

> (4.2) (Yeah,) it must have been thought up by some crazy feminist.

After utterance (4) ("This new workplace policy makes it impossible
to act like a real man"), the pronoun `it` in (4.2) anaphorically
picks out the sexual-harassment policy — the unavowed referent — even
though that policy was never the *direct* propositional content. By
@cite{buring-2005}, anaphora requires a linguistic antecedent, so the
unavowed referent must be a semantic value of `this new workplace
policy` and not merely an implicated content.

Ney contrasts this with example (11) (purely Stanleyan dogwhistling):
"???They founded it and built it" is infelicitous because the
implicated content is not a linguistic antecedent.

We formalize the discriminator as follows: an `Account` *licenses
anaphora* on the speaker's intended referent precisely when the
account succeeds (predicts the referent as the semantic value). A
stub Camp-style implicature-only account never validates the unavowed
as a semantic value, so it never licenses anaphora to the unavowed
referent. The asymmetry recovers @cite{ney-2026}'s contrast
formally.

A bridge to `Phenomena/Anaphora/Studies/Hofmann2025.lean`'s
`AccessDatum` data is left as future work. -/

namespace Account

variable {C W E : Type*}

/-- An `Account` *licenses anaphora* on the speaker's intended referent
in context iff it predicts the referent as a successful semantic
value. Per @cite{buring-2005}, anaphora requires a linguistic-antecedent
semantic value; per @cite{ney-2026} §3 ("thirdly"), this is the test
distinguishing insinuative reference (semantic value, anaphora ok) from
Campian insinuation (implicature, anaphora bad). -/
abbrev LicensesAnaphora (acc : Semantics.Reference.Metasemantics.Account C W E)
    (s : SpeakerIntention C W E) (cg : CG W) : Prop :=
  acc s cg

/-- A stub @cite{camp-2018}-style implicature-only account: the
unavowed content is conveyed by Gricean implicature, not as a semantic
value of any uttered expression. Modeled as the always-false account;
genuine implicature mechanics are out of scope.

The point is the discriminator: a Camp account *predicts no semantic
value* for the unavowed content, so by @cite{buring-2005} no anaphora
is licensed to that content. -/
def implicatureOnly : Semantics.Reference.Metasemantics.Account C W E :=
  fun _ _ => False

@[simp] theorem implicatureOnly_apply (s : SpeakerIntention C W E) (cg : CG W) :
    implicatureOnly s cg ↔ False := Iff.rfl

theorem implicatureOnly_does_not_licenseAnaphora
    (s : SpeakerIntention C W E) (cg : CG W) :
    ¬ LicensesAnaphora implicatureOnly s cg := id

end Account

/-- @cite{ney-2026} §3 ("thirdly") anaphora discriminator: in any
insinuative-reference scenario where Ney's revision succeeds, the
unavowed referent is anaphora-licensing under the revision but not
under a Camp-style implicature-only account.

This is the formal counterpart of @cite{ney-2026}'s contrast between
(4)/(4.2) (insinuative reference; anaphora to unavowed referent
felicitous) and (11) (purely implicated content; anaphora bad), with
anaphora-availability as the discriminator. -/
theorem ney_revision_anaphora_discriminator
    (sc : Scenario C W E) (cg : CG W)
    (h_ney : sc.neyRevisionSucceeds cg) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision sc.RS sc.RH) sc.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly sc.intention cg :=
  ⟨h_ney, id⟩

/-- Corollary of the discriminator: the gap witness exhibits the
contrast — Ney's revision licenses anaphora on the unavowed referent
while a Camp-style account does not. -/
theorem gapWitness_anaphora_discriminator (cg : CG Unit) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision gapWitness.RS gapWitness.RH)
      gapWitness.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly
      gapWitness.intention cg :=
  ney_revision_anaphora_discriminator gapWitness cg
    (gapWitness_neyRevisionSucceeds cg)

end InsinuativeReference
end Semantics.Reference.Metasemantics
