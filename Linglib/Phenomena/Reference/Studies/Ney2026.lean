import Linglib.Theories.Semantics.Reference.Metasemantics.InsinuativeReference
import Linglib.Theories.Semantics.Reference.Metasemantics.CGTransparency

/-!
# Ney (2026) — Insinuative reference and the coordination account
@cite{ney-2026}

Provenance ledger for @cite{ney-2026}. The metasemantic apparatus
(SpeakerIntention, Account, ConceptionOfReasonableness, the parametric
coordination account, King's binary reconstruction, Ney's revision, the
gap theorem, the prima facie challenge, the anaphora discriminator)
lives in `Theories/Semantics/Reference/Metasemantics/`. This file
records the paper's four toy sentences as concrete `Scenario` witnesses
and applies the substantive theorems to each.

## What this file demonstrates per sentence

For each of @cite{ney-2026}'s four canonical examples (§1 example (1)
plus §2 examples (2)–(4)), faithful to the paper's setup where the
hearer in fact recognizes the unavowed intention:

- The example exhibits the structural pattern of insinuative reference
  (multi-licensed referents with unavowed/avowable split).
- @cite{king-2013}'s binary reconstruction succeeds (both conceptions
  cover the unavowed intention — the hearer in fact recognizes).
- @cite{ney-2026}'s revision also succeeds (joint covers a fortiori).
- The §3 prima facie challenge applies: under any CG-transparency of
  the conceptions, King's reconstruction would force the success into
  CG, contradicting the observed deniability ((iia)/(iib)).
- The §3 "thirdly" anaphora discriminator applies: the unavowed
  referent licenses anaphora under both King and Ney, but not under a
  Camp-style implicature-only account.

## What this file additionally proves

`Sentence{1..4}.scenario` together with the *separate* gap-witness
in `InsinuativeReference.lean` jointly demonstrate two distinct facts
in @cite{ney-2026}:

- **Empirical alignment** (these sentences): both binary accounts
  succeed in fact; the divergence is in CG-availability.
- **Existence of a strict gap**
  (`exists_ney_succeeds_kingNeyReconstruction_fails`): there exist
  *other* scenarios where conceptions diverge, on which Ney's
  revision succeeds and King's reconstruction fails outright.

These are complementary: Ney's argument from observed deniability
applies to the first; the gap theorem records that the two accounts
also have differing extensional content.

## Discussion of distinguishing cases (Ney §2)

The paper distinguishes insinuative reference from:
- @cite{camp-2018} insinuation (example (6), the speeding-driver bribe)
  — there the unavowed content is Gricean *implicature*, not a semantic
  value of any uttered expression.
- @cite{henderson-mccready-2018} / @cite{henderson-mccready-2024} /
  @cite{khoo-2017} / @cite{stanley-2015} dogwhistles (example (12),
  "tailspin of culture, in our inner cities") — those depend on
  particular conventionalized lexical items.
- @cite{saul-2018} / @cite{saul-2024} intentional overt dogwhistles
  (example (15), Bush's "wonder-working power") — the closest analogue,
  but Saul's apparatus depends on a partitioned audience.
- pseudo-insinuative speech (example (17), 4chan triple-parentheses
  @cite{tuters-hagen-2020}) — no genuine intent to preserve deniability.

These distinguishing examples are not formalized as `Scenario` here —
they are *contrast cases* and would each require modeling the relevant
mechanism (implicature, conventional implicature, audience partition).
The anaphora discriminator captures the contrast with the
implicature-only case at the formal level.

## Authority

All citations transcribed from the paper's references section
(@cite{ney-2026}, Linguistics & Philosophy, DOI 10.1007/s10988-026-09456-0).
The reasonable-by-the-lights-of-S-or-H reformulation of clause (B) is
stated near the end of @cite{ney-2026} §4; example (1) is from
@cite{ney-2026} §1; examples (2)–(4) and (5)–(6) are from
@cite{ney-2026} §2; the <ONE>-<FOUR> argument structure and the
anaphora discriminator (4.2) are from @cite{ney-2026} §3.
-/

namespace Phenomena.Reference.Studies.Ney2026

open Semantics.Reference.Basic
open Semantics.Reference.Metasemantics
open Semantics.Reference.Metasemantics.InsinuativeReference
open Semantics.Reference.Metasemantics.Account
open Core.CommonGround

/-! ## Sentence (1): "Those people, they are always up to no good."

@cite{ney-2026} §1 example (1). The neighbour points down the street;
the avowable referent is the residents of that part of the
neighbourhood; the unavowed referent is a particular disreputable
family living there. -/

namespace Sentence1
/-- Entities for sentence (1): the unavowed family, the avowable
broader residents, and the speaker. -/
inductive R | family | residents | speaker
  deriving DecidableEq, Repr

/-- The (1) scenario as a `Scenario`. Per @cite{ney-2026} §1, in
successful insinuative reference the hearer in fact recognizes the
unavowed intention — so both `RS` and `RH` cover the family-targeted
intention. The deniability that motivates Ney's revision lives at the
CG-availability level, not the truth level. -/
def scenario : Scenario Unit Unit R where
  intention :=
    { speaker     := .speaker
    , expression  := { character := fun _ _ => .family
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := .family }
  licenses          := fun r => r = .family ∨ r = .residents
  RS                := fun s => s.intendedRef = .family
                             ∨ s.intendedRef = .residents
  RH                := fun s => s.intendedRef = .family
                             ∨ s.intendedRef = .residents
  unavowed_licensed := Or.inl rfl
  has_avowable      := ⟨.residents, by decide, Or.inr rfl⟩

theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure

theorem king_succeeds (cg : CG Unit) :
    scenario.kingNeyReconstructionSucceeds cg :=
  ⟨Or.inl rfl, Or.inl rfl⟩

theorem ney_succeeds (cg : CG Unit) :
    scenario.neyRevisionSucceeds cg :=
  Or.inl (Or.inl rfl)

/-- @cite{ney-2026} §3 prima facie challenge applied: under any
CG-transparency of the conceptions, King's binary reconstruction
forces success into CG. Contradicts the observed deniability of (1). -/
theorem prima_facie_challenge
    (cgOp : Account.CGModalOperator) (cg : CG Unit)
    (transparentRS : Account.CGTransparent cgOp scenario.RS scenario.intention)
    (transparentRH : Account.CGTransparent cgOp scenario.RH scenario.intention) :
    cgOp.inCG (scenario.kingNeyReconstructionSucceeds cg) :=
  Account.prima_facie_challenge_kingNeyReconstruction cgOp
    scenario.RS scenario.RH scenario.intention cg
    transparentRS transparentRH (king_succeeds cg)

/-- @cite{ney-2026} §3 ("thirdly") anaphora discriminator: the
unavowed referent (`.family`) licenses anaphora under Ney's revision
but not under a Camp-style implicature-only account. Captures the
contrast between (4)/(4.2) (anaphora ok) and a Camp-style
continuation. -/
theorem anaphora_discriminator (cg : CG Unit) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision scenario.RS scenario.RH)
      scenario.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly
      scenario.intention cg :=
  ney_revision_anaphora_discriminator scenario cg (ney_succeeds cg)

end Sentence1

/-! ## Sentence (2): "They are crossing the border, bringing drugs,
disease and crime."

@cite{ney-2026} §2 example (2). Avowable: gang members and drug
smugglers. Unavowed: Hispanic immigrants. -/

namespace Sentence2
inductive R | hispanicImmigrants | gangAndSmugglers | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R where
  intention :=
    { speaker     := .speaker
    , expression  := { character := fun _ _ => .hispanicImmigrants
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := .hispanicImmigrants }
  licenses          := fun r => r = .hispanicImmigrants
                             ∨ r = .gangAndSmugglers
  RS                := fun s => s.intendedRef = .hispanicImmigrants
                             ∨ s.intendedRef = .gangAndSmugglers
  RH                := fun s => s.intendedRef = .hispanicImmigrants
                             ∨ s.intendedRef = .gangAndSmugglers
  unavowed_licensed := Or.inl rfl
  has_avowable      := ⟨.gangAndSmugglers, by decide, Or.inr rfl⟩

theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure

theorem king_succeeds (cg : CG Unit) :
    scenario.kingNeyReconstructionSucceeds cg :=
  ⟨Or.inl rfl, Or.inl rfl⟩

theorem ney_succeeds (cg : CG Unit) :
    scenario.neyRevisionSucceeds cg :=
  Or.inl (Or.inl rfl)

theorem prima_facie_challenge
    (cgOp : Account.CGModalOperator) (cg : CG Unit)
    (transparentRS : Account.CGTransparent cgOp scenario.RS scenario.intention)
    (transparentRH : Account.CGTransparent cgOp scenario.RH scenario.intention) :
    cgOp.inCG (scenario.kingNeyReconstructionSucceeds cg) :=
  Account.prima_facie_challenge_kingNeyReconstruction cgOp
    scenario.RS scenario.RH scenario.intention cg
    transparentRS transparentRH (king_succeeds cg)

theorem anaphora_discriminator (cg : CG Unit) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision scenario.RS scenario.RH)
      scenario.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly
      scenario.intention cg :=
  ney_revision_anaphora_discriminator scenario cg (ney_succeeds cg)

end Sentence2

/-! ## Sentence (3): "Those people are using their power in the
international banks to hide the truth from ordinary, Christian
Americans like us."

@cite{ney-2026} §2 example (3). Avowable: white-collar criminals who
aren't true Christians. Unavowed: purported Jewish elites. -/

namespace Sentence3
inductive R | jewishElites | nonChristianWhiteCollar | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R where
  intention :=
    { speaker     := .speaker
    , expression  := { character := fun _ _ => .jewishElites
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := .jewishElites }
  licenses          := fun r => r = .jewishElites
                             ∨ r = .nonChristianWhiteCollar
  RS                := fun s => s.intendedRef = .jewishElites
                             ∨ s.intendedRef = .nonChristianWhiteCollar
  RH                := fun s => s.intendedRef = .jewishElites
                             ∨ s.intendedRef = .nonChristianWhiteCollar
  unavowed_licensed := Or.inl rfl
  has_avowable      := ⟨.nonChristianWhiteCollar, by decide, Or.inr rfl⟩

theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure

theorem king_succeeds (cg : CG Unit) :
    scenario.kingNeyReconstructionSucceeds cg :=
  ⟨Or.inl rfl, Or.inl rfl⟩

theorem ney_succeeds (cg : CG Unit) :
    scenario.neyRevisionSucceeds cg :=
  Or.inl (Or.inl rfl)

theorem prima_facie_challenge
    (cgOp : Account.CGModalOperator) (cg : CG Unit)
    (transparentRS : Account.CGTransparent cgOp scenario.RS scenario.intention)
    (transparentRH : Account.CGTransparent cgOp scenario.RH scenario.intention) :
    cgOp.inCG (scenario.kingNeyReconstructionSucceeds cg) :=
  Account.prima_facie_challenge_kingNeyReconstruction cgOp
    scenario.RS scenario.RH scenario.intention cg
    transparentRS transparentRH (king_succeeds cg)

theorem anaphora_discriminator (cg : CG Unit) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision scenario.RS scenario.RH)
      scenario.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly
      scenario.intention cg :=
  ney_revision_anaphora_discriminator scenario cg (ney_succeeds cg)

end Sentence3

/-! ## Sentence (4): "This new workplace policy makes it impossible to
act like a real man."

@cite{ney-2026} §2 example (4). Avowable: work-scheduling policy.
Unavowed: sexual-harassment policy. This example also drives the
anaphora discriminator argument in @cite{ney-2026} §3 ("thirdly"): the
continuation (4.2) "(Yeah,) it must have been thought up by some crazy
feminist" anaphorically picks out the sexual-harassment policy, which
by @cite{buring-2005} requires a linguistic antecedent — evidence that
the unavowed referent is a genuine semantic value, not an implicature. -/

namespace Sentence4
inductive R | sexualHarassmentPolicy | workSchedulingPolicy | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R where
  intention :=
    { speaker     := .speaker
    , expression  := { character := fun _ _ => .sexualHarassmentPolicy
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := .sexualHarassmentPolicy }
  licenses          := fun r => r = .sexualHarassmentPolicy
                             ∨ r = .workSchedulingPolicy
  RS                := fun s => s.intendedRef = .sexualHarassmentPolicy
                             ∨ s.intendedRef = .workSchedulingPolicy
  RH                := fun s => s.intendedRef = .sexualHarassmentPolicy
                             ∨ s.intendedRef = .workSchedulingPolicy
  unavowed_licensed := Or.inl rfl
  has_avowable      := ⟨.workSchedulingPolicy, by decide, Or.inr rfl⟩

theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure

theorem king_succeeds (cg : CG Unit) :
    scenario.kingNeyReconstructionSucceeds cg :=
  ⟨Or.inl rfl, Or.inl rfl⟩

theorem ney_succeeds (cg : CG Unit) :
    scenario.neyRevisionSucceeds cg :=
  Or.inl (Or.inl rfl)

theorem prima_facie_challenge
    (cgOp : Account.CGModalOperator) (cg : CG Unit)
    (transparentRS : Account.CGTransparent cgOp scenario.RS scenario.intention)
    (transparentRH : Account.CGTransparent cgOp scenario.RH scenario.intention) :
    cgOp.inCG (scenario.kingNeyReconstructionSucceeds cg) :=
  Account.prima_facie_challenge_kingNeyReconstruction cgOp
    scenario.RS scenario.RH scenario.intention cg
    transparentRS transparentRH (king_succeeds cg)

theorem anaphora_discriminator (cg : CG Unit) :
    Account.LicensesAnaphora
      (Account.coordination.neyRevision scenario.RS scenario.RH)
      scenario.intention cg ∧
    ¬ Account.LicensesAnaphora Account.implicatureOnly
      scenario.intention cg :=
  ney_revision_anaphora_discriminator scenario cg (ney_succeeds cg)

end Sentence4

/-! ## Aggregate theorems -/

/-- All four toy sentences exhibit the structural pattern of
insinuative reference: each has a licensed unavowed referent with at
least one licensed avowable alternative. -/
theorem all_four_examples_have_insinuative_structure :
    HasInsinuativeStructure Sentence1.scenario.licenses
                            Sentence1.scenario.intention ∧
    HasInsinuativeStructure Sentence2.scenario.licenses
                            Sentence2.scenario.intention ∧
    HasInsinuativeStructure Sentence3.scenario.licenses
                            Sentence3.scenario.intention ∧
    HasInsinuativeStructure Sentence4.scenario.licenses
                            Sentence4.scenario.intention :=
  ⟨Sentence1.hasInsinuativeStructure,
   Sentence2.hasInsinuativeStructure,
   Sentence3.hasInsinuativeStructure,
   Sentence4.hasInsinuativeStructure⟩

/-- All four toy sentences are King-NeyReconstruction-successful and
Ney-revision-successful (the hearer in fact recognizes the unavowed
intention; both binary conceptions cover). The discriminator between
the accounts is at the CG-availability level — see
`prima_facie_challenge` per sentence. -/
theorem all_four_examples_are_jointly_successful (cg : CG Unit) :
    (Sentence1.scenario.kingNeyReconstructionSucceeds cg ∧
     Sentence1.scenario.neyRevisionSucceeds cg) ∧
    (Sentence2.scenario.kingNeyReconstructionSucceeds cg ∧
     Sentence2.scenario.neyRevisionSucceeds cg) ∧
    (Sentence3.scenario.kingNeyReconstructionSucceeds cg ∧
     Sentence3.scenario.neyRevisionSucceeds cg) ∧
    (Sentence4.scenario.kingNeyReconstructionSucceeds cg ∧
     Sentence4.scenario.neyRevisionSucceeds cg) :=
  ⟨⟨Sentence1.king_succeeds cg, Sentence1.ney_succeeds cg⟩,
   ⟨Sentence2.king_succeeds cg, Sentence2.ney_succeeds cg⟩,
   ⟨Sentence3.king_succeeds cg, Sentence3.ney_succeeds cg⟩,
   ⟨Sentence4.king_succeeds cg, Sentence4.ney_succeeds cg⟩⟩

/-- All four toy sentences exhibit the §3 anaphora discriminator: the
unavowed referent licenses anaphora under Ney's revision but not
under a Camp-style implicature-only account. Formalizes
@cite{ney-2026} §3 ("thirdly") for each canonical example. -/
theorem all_four_examples_exhibit_anaphora_discriminator (cg : CG Unit) :
    (Account.LicensesAnaphora
       (Account.coordination.neyRevision Sentence1.scenario.RS
                                         Sentence1.scenario.RH)
       Sentence1.scenario.intention cg ∧
     ¬ Account.LicensesAnaphora Account.implicatureOnly
         Sentence1.scenario.intention cg) ∧
    (Account.LicensesAnaphora
       (Account.coordination.neyRevision Sentence2.scenario.RS
                                         Sentence2.scenario.RH)
       Sentence2.scenario.intention cg ∧
     ¬ Account.LicensesAnaphora Account.implicatureOnly
         Sentence2.scenario.intention cg) ∧
    (Account.LicensesAnaphora
       (Account.coordination.neyRevision Sentence3.scenario.RS
                                         Sentence3.scenario.RH)
       Sentence3.scenario.intention cg ∧
     ¬ Account.LicensesAnaphora Account.implicatureOnly
         Sentence3.scenario.intention cg) ∧
    (Account.LicensesAnaphora
       (Account.coordination.neyRevision Sentence4.scenario.RS
                                         Sentence4.scenario.RH)
       Sentence4.scenario.intention cg ∧
     ¬ Account.LicensesAnaphora Account.implicatureOnly
         Sentence4.scenario.intention cg) :=
  ⟨Sentence1.anaphora_discriminator cg,
   Sentence2.anaphora_discriminator cg,
   Sentence3.anaphora_discriminator cg,
   Sentence4.anaphora_discriminator cg⟩

end Phenomena.Reference.Studies.Ney2026
