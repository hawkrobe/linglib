import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Core.Semantics.CommonGround

/-!
# Ney 2026 — Insinuative reference and the coordination account
@cite{ney-2026} @cite{king-2013} @cite{king-2014b}

Insinuative reference is a metasemantic strategy: a speaker uses a
directly-referential expression (typically a demonstrative or
"supplementive" in @cite{king-2013}'s sense — `this`, `those`, `it`)
under conditions where the lexical meaning + salient context license
multiple referents, intends one specific ("unavowed") referent while
at least one other ("avowable") referent is also licensed, and intends
to preserve plausible deniability about the unavowed intent.

@cite{ney-2026} introduces the phenomenon, distinguishes it from
related phenomena (@cite{camp-2018} insinuation, dogwhistles per
@cite{stanley-2015} @cite{henderson-mccready-2018}
@cite{henderson-mccready-2024} @cite{khoo-2017} @cite{saul-2018}
@cite{saul-2024}, pseudo-insinuative speech per
@cite{tuters-hagen-2020}), shows it poses a *prima facie* challenge
to @cite{king-2013}'s coordination account (§3, the `<ONE>`-`<FOUR>`
argument), and resolves the challenge by reading the conception of
reasonableness as the *intersection* of the interlocutors' individual
belief-sets — equivalently, the *union* of the hearer-profiles each
agent counts as reasonable (§4 p. 22, revised statement p. 24). The
union is not CG-accessible because membership in it requires private
knowledge of either individual conception.

## Encoding choice (relative to @cite{ney-2026} pp. 22, 24)

`ConceptionOfReasonableness C W E := Set (HearerProfile C W E)` — the
set of hearer-profiles each agent counts as *reasonable*. Then the
verbatim revised statement of @cite{ney-2026} p. 24 — "every competent,
attentive hearer H who is reasonable by the lights of at least one
among the speaker and the actual hearer" — is `∀ h ∈ RS ∪ RH, h
recognizes intention`, i.e., `coordination (RS ⊔ RH)`. The union
*enlarges* the set of required-recognizer hearers, so the success
condition is **harder** under Ney's revision than under the objector's
reconstruction `coordination (RS ⊓ RH)`. `coordination` is therefore
anti-monotone in the conception parameter (`coordination_anti_mono`).

This is the dual of an alternative encoding `Set (SpeakerIntention)`
(intentions deemed recognizable). Under that encoding, Ney's revision
would map to *intersection* of belief-sets (intentions both agents
agree are recognizable) — the same dual content but with monotonicity
reversed, and with the prima-facie argument needing different modal
closures (∧-intro vs universal lift). We pick the hearer-profile
encoding because it matches the verbatim revised statement and makes
Ney's resolution structurally explicit: the *membership* facts for
`RS ⊔ RH` require private knowledge of either RS or RH individually,
hence are not CG-transparent, hence the `<ONE>`-`<FOUR>` chain breaks.

## What this file formalizes vs. what it doesn't

`HasInsinuativeStructure licenses s` captures the *structural pattern*
— multi-licensed referents with a distinguished intended one — but
NOT the speaker-side intent to preserve deniability. The full
phenomenon is the conjunction of the structural pattern and the
deniability intent; the latter is left for a future extension when
there is a downstream consumer that needs to discriminate it (e.g.,
from pseudo-insinuative speech, where the structure is present but
the intent is absent — @cite{ney-2026} §2 (17), the 4chan
triple-parentheses case).

The §3 prima-facie challenge is formalized abstractly:
`prima_facie_challenge` takes `inCG : Prop → Prop` and a CG-transparency
hypothesis on the conception. Substantive Ney soundness — that the
resolution holds under a *realistic* CG operator derived from
`commonBelief` (@cite{stalnaker-2002}) — requires a `CG.toAgentAccess :
CG W → AgentAccessRel W E` bridge in `Core/Semantics/CommonGround.lean`
that does not yet exist. Until that bridge lands, the resolution
theorems are witnessed by toy operators (a degenerate `inCG := · = True`
that distinguishes intersection-CG-transparency from union-CG-transparency
on a small carrier).

## Distinguishing the phenomenon (Ney 2026 §2)

Insinuative reference is distinct from:
- @cite{camp-2018} insinuation: there the unavowed content is conveyed
  by Gricean *implicature*; here it is the expression's *semantic value*.
- @cite{stanley-2015} / @cite{henderson-mccready-2018,2024} /
  @cite{khoo-2017} dogwhistles: those depend on conventionalized lexical
  items. Insinuative reference is a metasemantic strategy applicable
  to any directly-referential expression.
- @cite{saul-2018} / @cite{saul-2024} intentional overt dogwhistles:
  the closest analogue, but Saul's apparatus depends on a partitioned
  audience; insinuative reference can occur with a single hearer.
- pseudo-insinuative speech (@cite{tuters-hagen-2020}): structurally
  similar but lacks genuine intent to preserve deniability.

@cite{ney-2026} §5 proposes reserving "insinuation" for the Camp-style
implicature phenomenon and using "insinuative speech" as the broader
deniability-preserving category encompassing all four. This file's
namespace is `Ney2026`; a future
`Phenomena.InsinuativeSpeech.*` superclass with sibling Camp / Saul
formalizations is the obvious organising principle but is not built
here.

The paper's methodological framing is *non-ideal philosophy of
language* per @cite{beaver-stanley-2023}.

## Substrate primitives this file leans on (with citations)

Imports `Reference.Basic` (@cite{kaplan-1989}'s Character/Content +
@cite{almog-2014}'s ReferentialProfile) and `Core.Semantics.CommonGround`
(@cite{stalnaker-2002}'s context set). `SpeakerIntention.intendedRef`
parallels @cite{donnellan-1966}'s referential-use intended object;
the broader speaker-intent structure connects to @cite{searle-1983}
intentional states (not unified here).

## Shape gaps tracked but not fixed here

1. `TrueDemonstrative.demonstratum : C → Option E` (in
   `Reference/Demonstratives.lean`) is functional — at most one
   referent per context. Insinuative reference needs *multiple*
   simultaneously-licensed referents per context; we work around by
   taking `licenses : E → Prop` as an abstract input parameter. The
   principled fix is to refactor `demonstratum` to a relation
   `C → E → Prop`.
2. `inCG : Prop → Prop` (here taken as hypothesis) should connect to
   `commonBelief` in `Theories/Semantics/Modality/EpistemicLogic.lean`
   once a `CG.toAgentAccess` bridge exists.
3. `SpeakerIntention.intendedRef` parallel-stipulates with
   `Donnellan.DefiniteDescription.intendedRef`; not unified.

## Authority

@cite{ney-2026}, *Linguistics & Philosophy* (2026),
DOI 10.1007/s10988-026-09456-0. Examples (1)–(4) are §1–§2; the
`<ONE>`-`<FOUR>` argument is §3 (pp. 17–19); the conception-of-
reasonableness reading and revised coordination statement are §4
(pp. 22, 24); the anaphora discriminator is §3 ("thirdly", pp. 15–16);
the §5 conclusion proposes the broader "insinuative speech" terminology.
@cite{king-2013} is the primary coordination-account source;
@cite{king-2014b} is its considered restatement.
-/

namespace Ney2026

open Semantics.Reference.Basic Core.CommonGround

/-! ## §1. Metasemantic apparatus -/

/-- A speaker's *referential intention*: a directly-referential
expression used in a context to refer to a particular intended object.

Following @cite{king-2013}'s setup: a speaker `S` uses a demonstrative
expression `δ` in context `c` and intends some object `o` to be its
semantic value. The metasemantic question (formalized by `Account`)
is what conditions must hold for `o` to actually be `δ`'s semantic
value. -/
structure SpeakerIntention (C W E : Type*) where
  /-- The speaker (typically the agent of the context). -/
  speaker      : E
  /-- The referring expression: demonstrative, supplementive, pronoun. -/
  expression   : ReferringExpression C W E
  /-- The Kaplanian context of utterance. -/
  context      : C
  /-- The object the speaker intends to be the semantic value. -/
  intendedRef  : E

/-- A *hearer profile*: a function from speaker intentions to whether
this kind of hearer recognizes the intention as targeting the unavowed
referent.

The "kind of hearer" is characterized purely by which intentions it
would recognize — abstracted away from psychological detail. A
ConceptionOfReasonableness picks out which hearer-profiles count as
reasonable by some agent's lights. -/
abbrev HearerProfile (C W E : Type*) :=
  SpeakerIntention C W E → Prop

/-- An agent's *conception of reasonableness*: the set of hearer-
profiles the agent counts as reasonable.

@cite{ney-2026} §4 (p. 22) introduces this as "an agent's (implicit
and explicit) beliefs about which referential intentions every
reasonable hearer would recognise." Ney explicitly notes (p. 22) that
a language-user counts as reasonable per the *intersection* of
agents' belief-sets iff *either* the speaker or the hearer would
consider them so — i.e., the hearer-profile-set extension of the
intersection-of-beliefs conception is the *union* of individual
hearer-profile-sets. We encode at the hearer-profile level for
correspondence with the verbatim revised statement at p. 24. -/
abbrev ConceptionOfReasonableness (C W E : Type*) :=
  Set (HearerProfile C W E)

/-- A *metasemantics of demonstratives*: a recipe assigning each
speaker intention a success Prop.

`Account` is intentionally CG-free (no `CG W` parameter): in
@cite{ney-2026}'s argument the CG-availability of the success-fact is
the load-bearing modal claim, formalized via the abstract `inCG`
operator on the `prima_facie_challenge` theorem rather than threaded
through every account-application. -/
abbrev Account (C W E : Type*) :=
  SpeakerIntention C W E → Prop

/-- The parametric coordination account, @cite{king-2013} (revised per
@cite{ney-2026} §4 p. 24): success iff every hearer-profile in the
conception of reasonableness `R` recognizes the speaker's intention.

`abbrev` so that membership facts unfold under `decide` and the proofs
of the four canonical sentences reduce to `Or.inl rfl`-style. -/
abbrev coordination {C W E : Type*}
    (R : ConceptionOfReasonableness C W E) : Account C W E :=
  fun s => ∀ h ∈ R, h s

/-- `coordination` is *anti-monotone* in its conception parameter:
enlarging the set of required-recognizer hearers makes the success
condition harder. This is the hearer-profile dual of the formal
property at @cite{ney-2026} p. 22 ("a language-user counts as
reasonable [per the intersection conception] if either the hearer or
the speaker would consider them reasonable"). -/
theorem coordination_anti_mono {C W E : Type*}
    {R₁ R₂ : ConceptionOfReasonableness C W E} (h : R₁ ≤ R₂) :
    coordination R₂ ≤ coordination R₁ :=
  fun _ hs h₀ hh₀ => hs h₀ (h hh₀)

/-! ## §2. King's binary reconstruction vs Ney's revision

@cite{king-2013}'s text (quoted in @cite{ney-2026} §3 p. 17) refers to
"a competent, reasonable, attentive hearer", an unspecified single
conception. @cite{ney-2026} §4 (p. 22) reframes this in interlocutor-
relative terms, then revises (p. 24): "every competent, attentive
hearer H *who is reasonable by the lights of at least one among the
speaker and the actual hearer*".

In our `Set (HearerProfile)` encoding:

- King's "objector" reconstruction (which Ney rejects): `coordination
  (RS ⊓ RH)` — only the hearers *both* agents consider reasonable
  need to recognize. Smaller required-set, easier success.
- Ney's revised account (verbatim p. 24): `coordination (RS ⊔ RH)` —
  every hearer *either* agent considers reasonable must recognize.
  Larger required-set, harder success.

We do not name these as separate definitions; the inline form is
descriptive and avoids author-attributed naming (mathlib idiom: author
attribution lives in docstrings). -/

/-- Ney's revision is pointwise *more restrictive* than the objector's
reconstruction (anti-monotone direction). -/
theorem coordination_union_le_coordination_inter {C W E : Type*}
    (RS RH : ConceptionOfReasonableness C W E) :
    coordination (RS ⊔ RH) ≤ coordination (RS ⊓ RH) :=
  coordination_anti_mono inf_le_sup

/-- Idempotence corollary: when the two conceptions coincide, the two
binary forms collapse to the underlying `coordination R`. -/
theorem coordination_inf_self_eq_sup_self {C W E : Type*}
    (R : ConceptionOfReasonableness C W E) :
    coordination (R ⊓ R) = coordination (R ⊔ R) := by
  rw [inf_idem, sup_idem]

/-! ## §3. Insinuative structural pattern -/

/-- A speaker intention exhibits the *structural pattern of insinuative
reference* with respect to a licensing predicate iff the unavowed
(intended) referent is licensed *and* at least one avowable
(≠ unavowed) referent is also licensed.

This Prop is the *structure* the phenomenon exhibits, not the full
phenomenon: the speaker's intent to preserve deniability is part of
the phenomenon (@cite{ney-2026} §2) but is not encoded here. See file
docstring. -/
def HasInsinuativeStructure {C W E : Type*}
    (licenses : E → Prop) (s : SpeakerIntention C W E) : Prop :=
  licenses s.intendedRef ∧ ∃ r, r ≠ s.intendedRef ∧ licenses r

/-- The avowable alternative referents: licensed but distinct from the
unavowed intention. -/
def avowableAlternatives {C W E : Type*}
    (licenses : E → Prop) (s : SpeakerIntention C W E) : Set E :=
  {r | r ≠ s.intendedRef ∧ licenses r}

theorem hasInsinuativeStructure_iff {C W E : Type*}
    (licenses : E → Prop) (s : SpeakerIntention C W E) :
    HasInsinuativeStructure licenses s ↔
      licenses s.intendedRef ∧ (avowableAlternatives licenses s).Nonempty :=
  Iff.rfl

/-- A complete insinuative-reference scenario: the speaker intention,
the licensing predicate (which referents the expression + context
permit as semantic values), the speaker's and actual hearer's
conceptions of reasonableness (sets of hearer-profiles), and the
witnesses that the unavowed referent is licensed and that an avowable
alternative exists. -/
structure Scenario (C W E : Type*) where
  intention            : SpeakerIntention C W E
  licenses             : E → Prop
  RS                   : ConceptionOfReasonableness C W E
  RH                   : ConceptionOfReasonableness C W E
  unavowed_licensed    : licenses intention.intendedRef
  has_avowable         : ∃ r, r ≠ intention.intendedRef ∧ licenses r

namespace Scenario

variable {C W E : Type*}

/-- Every `Scenario` exhibits the structural pattern. -/
theorem hasInsinuativeStructure (sc : Scenario C W E) :
    HasInsinuativeStructure sc.licenses sc.intention :=
  ⟨sc.unavowed_licensed, sc.has_avowable⟩

end Scenario

/-! ## §4. The §3 prima-facie challenge

@cite{ney-2026} §3's `<ONE>`-`<FOUR>` chain (paper pp. 17–18,
paraphrased):

> ⟨ONE⟩  A reasonable hearer would recognize the speaker's intention
>         to make the unavowed referent the semantic value of the
>         insinuatively-used supplementive (i.e., (B) is satisfied).
> ⟨TWO⟩  It is in CG that the actual hearer is competent, reasonable,
>         and attentive (assumption).
> ⟨THREE⟩ It is in CG that the actual hearer recognizes that intention
>         (from ONE + TWO).
> ⟨FOUR⟩  It is in CG that the unavowed referent is the semantic value
>         (from ONE + THREE).

@cite{ney-2026} §3 (p. 17) shows two independent empirical claims that
the chain's conclusions contradict:

- **(iia)**: post-utterance, it is NOT in CG that the unavowed referent
  IS the semantic value of the insinuatively-used supplementive.
  Witnessed by paper dialogues (2.2)-(2.5) (pp. 16–17): a hearer's
  indication of recognizing the semantic value licenses inferences
  about the hearer that wouldn't be felicitous if the recognition
  were already CG. ⟨FOUR⟩ contradicts (iia).

- **(iib)**: post-utterance, it is NOT in CG that the speaker had the
  unavowed referential intention. Witnessed by paper dialogues
  (2.6)-(2.9): a hearer's indication of recognizing the speaker's
  intention licenses parallel inferences. ⟨THREE⟩ contradicts (iib).

In our encoding, `coordination R s = ∀ h ∈ R, h s` packages "every
reasonable hearer recognizes" (= ⟨THREE⟩ when in CG, contra (iib))
together with "success" (= ⟨FOUR⟩ when in CG, contra (iia)) — King's
biconditional makes them definitionally the same Prop. The empirical
distinction between (iia) and (iib) is therefore documented at this
level rather than encoded as separate Lean propositions.

The chain only goes through if the universal "every reasonable hearer
recognizes" claim — i.e., `coordination R s` for the relevant
conception R — is itself in CG. Under King's "objector" reading
(R = RS ⊓ RH), this is plausible: the intersection of belief-sets is
publicly knowable. Under Ney's revision (R = RS ⊔ RH), it is *not*:
membership in `RS ∪ RH` requires private knowledge of either
individual conception. This is the asymmetry §5 below witnesses. -/

/-- Trivial form: if the universal recognition fact `coordination R s`
is in CG, then it's in CG. The substantive Ney content is in *which
R* makes this premise plausible — see `prima_facie_inter_witness` and
`prima_facie_union_failure_witness` in §5. -/
theorem prima_facie_challenge {C W E : Type*}
    (inCG : Prop → Prop)
    {R : ConceptionOfReasonableness C W E}
    {s : SpeakerIntention C W E}
    (transparent : inCG (coordination R s)) :
    inCG (coordination R s) :=
  transparent

/-! ## §5. Ney's resolution: intersection is CG-transparent, union is not

@cite{ney-2026}'s §4 resolution (pp. 22–24): the conception of
reasonableness as the union of agents' hearer-profile-sets is *not*
CG-accessible — knowing whether a hearer is in `RS ∪ RH` requires
private knowledge of either RS or RH individually. The intersection,
by contrast, is the publicly-shared part of the conceptions and is
CG-accessible.

We exhibit this asymmetry as a single concrete model: a degenerate
`inCG := (· = True)` operator (only logically-true propositions count
as "in CG") that returns `True` for the vacuous intersection-success
and `False` for the non-vacuous union-failure on a hand-built witness.

CAVEAT: This is a toy operator. The substantive Ney claim — that the
asymmetry holds under a *realistic* CG operator derived from
`commonBelief` (@cite{stalnaker-2002}) — requires the `CG.toAgentAccess`
bridge that does not yet exist. -/

/-- A minimal speaker-intention witness over `Bool`: speaker `false`,
intends `true`, with a constant character. -/
private def boolWitness : SpeakerIntention Unit Unit Bool where
  speaker     := false
  expression  := { character := fun _ _ => true
                 , profile := ⟨true, true, false⟩ }
  context     := ()
  intendedRef := true

/-- A hearer-profile that recognizes nothing (always rejects). -/
private def alwaysRejectsProfile : HearerProfile Unit Unit Bool :=
  fun _ => False

/-- The asymmetry @cite{ney-2026} §4 hinges on: there exists a CG
operator and a pair of conceptions where the intersection-success
*is* in CG while the union-success *is not*. Witness: `inCG := id`
(the trivial nonempty operator), `RS = ∅`, `RH = {alwaysRejectsProfile}`.
The intersection is empty (success vacuous); the union contains a
hearer that rejects the intention (success false, not in CG). -/
theorem coordination_inter_in_cg_but_union_not :
    ∃ (inCG : Prop → Prop)
      (RS RH : ConceptionOfReasonableness Unit Unit Bool)
      (s : SpeakerIntention Unit Unit Bool),
      inCG (coordination (RS ⊓ RH) s) ∧
      ¬ inCG (coordination (RS ⊔ RH) s) :=
  ⟨id, ∅, {alwaysRejectsProfile}, boolWitness,
   fun _ hh => hh.1.elim,
   fun hall => hall alwaysRejectsProfile (Or.inr rfl)⟩

/-! ## §6. Extensional gap between intersection and union accounts

Under the right encoding (`Set (HearerProfile)` + anti-monotone
`coordination`), the *intersection* is more permissive than the
*union*. There exist scenarios where King's objector-reconstruction
succeeds (vacuously, on the empty intersection) while Ney's revision
fails (the union contains a non-recognizing hearer).

CAVEAT: This extensional gap is incidental to @cite{ney-2026}'s
substantive argument — Ney does not appeal to it. Ney's actual
argument is at the CG-availability level (§5 above), not the truth
level. The gap witness is included only to demonstrate that the two
account-shapes differ extensionally; it is *not* a model of any
@cite{ney-2026} sentence (in his canonical examples both interlocutors
in fact agree, so under the encoding here both intersection and union
succeed). -/

private def extensionalGapWitness : Scenario Unit Unit Bool where
  intention         := boolWitness
  licenses          := fun _ => True
  RS                := ∅
  RH                := {alwaysRejectsProfile}
  unavowed_licensed := trivial
  has_avowable      := ⟨false, by decide, trivial⟩

theorem exists_inter_succeeds_union_fails :
    ∃ (sc : Scenario Unit Unit Bool),
      HasInsinuativeStructure sc.licenses sc.intention ∧
      coordination (sc.RS ⊓ sc.RH) sc.intention ∧
      ¬ coordination (sc.RS ⊔ sc.RH) sc.intention :=
  ⟨extensionalGapWitness,
   extensionalGapWitness.hasInsinuativeStructure,
   fun _ hh => hh.1.elim,
   fun hall => hall alwaysRejectsProfile (Or.inr rfl)⟩

/-! ## §7. Anaphora discriminator (@cite{ney-2026} §3, "thirdly")

@cite{ney-2026} §3 ("thirdly", pp. 15–16) argues that anaphora-
availability is positive evidence that the unavowed referent is a
genuine semantic value, not @cite{camp-2018}-style implicature.
Sentence (4) "This new workplace policy makes it impossible to act
like a real man." can be felicitously continued by (4.2) "(Yeah,) it
must have been thought up by some crazy feminist", where Ney
specifically identifies the plural anaphor *they* in his subsequent
gloss — anaphorically picking out the sexual-harassment policies (the
unavowed referent). Per @cite{buring-2005} (cited by @cite{ney-2026}
§3 for this point), anaphora requires a linguistic-antecedent semantic
value, so the unavowed referent must be a semantic value of the
demonstrative.

CAVEAT: The contrast formalized below is between Ney's revision and
the trivially-failing `noSemanticValueAccount := ⊥`. A genuine
@cite{camp-2018} formalization with implicature mechanics would also
predict no semantic value, so the discriminator stays formally sound
but is currently unfalsifiable: any always-false account produces the
same negative side. The principled fix is to lift `Account` to range
over `Core.Semantics.ContentLayer.LayeredProp` so that Camp routes the
unavowed content to `.implicature` while coordination routes to
`.atIssue` — a cross-framework integration deferred until a real Camp
study lands. -/

/-- The trivially-failing account: predicts no semantic value for any
intention. Stand-in for an account that places the unavowed content
in implicature space rather than as a semantic value. Defined as the
Pi-type bottom on `Account`. -/
def noSemanticValueAccount {C W E : Type*} : Account C W E := ⊥

@[simp] theorem noSemanticValueAccount_apply {C W E : Type*}
    (s : SpeakerIntention C W E) :
    noSemanticValueAccount s ↔ False :=
  Iff.rfl

theorem anaphora_discriminator_ney_revision {C W E : Type*}
    (sc : Scenario C W E)
    (h : coordination (sc.RS ⊔ sc.RH) sc.intention) :
    coordination (sc.RS ⊔ sc.RH) sc.intention ∧
    ¬ noSemanticValueAccount sc.intention :=
  ⟨h, id⟩

/-! ## §8. The four canonical sentences (@cite{ney-2026} §1, §2)

In @cite{ney-2026}'s canonical examples, the speaker uses a
demonstrative in a context licensing both an avowable referent and
an unavowed referent; both interlocutors in fact recognize the
unavowed intention (the deniability lives at CG-availability, see §5
above). We model this with a permissive hearer-profile that recognizes
the unavowed-or-avowable intention, attributed to both RS and RH. -/

namespace Scenario

variable {E : Type*} [DecidableEq E]

/-- A "perceptive hearer" profile parametrized by the unavowed and
avowable referents: recognizes any intention whose intendedRef is one
of them. -/
def perceptiveHearer (unavowed avowable : E) : HearerProfile Unit Unit E :=
  fun s => s.intendedRef = unavowed ∨ s.intendedRef = avowable

/-- Build a scenario where both interlocutors agree on the conception
{perceptiveHearer unavowed avowable}. Models @cite{ney-2026}'s
canonical case. -/
def mkBinary
    (speaker unavowed avowable : E) (h_ne : avowable ≠ unavowed) :
    Scenario Unit Unit E where
  intention :=
    { speaker     := speaker
    , expression  := { character := fun _ _ => unavowed
                     , profile := ⟨true, true, false⟩ }
    , context     := ()
    , intendedRef := unavowed }
  licenses          := fun r => r = unavowed ∨ r = avowable
  RS                := {perceptiveHearer unavowed avowable}
  RH                := {perceptiveHearer unavowed avowable}
  unavowed_licensed := Or.inl rfl
  has_avowable      := ⟨avowable, h_ne, Or.inr rfl⟩

end Scenario

/-! ### Sentence (1): "Those people, they are always up to no good."
@cite{ney-2026} §1 example (1). Avowable: residents of that part of
the neighbourhood. Unavowed: a particular disreputable family living
there. -/
namespace Sentence1
inductive R | family | residents | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .family .residents (by decide)

theorem inter_succeeds :
    coordination (scenario.RS ⊓ scenario.RH) scenario.intention := by
  rintro _ ⟨rfl, _⟩; exact Or.inl rfl

theorem union_succeeds :
    coordination (scenario.RS ⊔ scenario.RH) scenario.intention := by
  rintro _ (rfl | rfl) <;> exact Or.inl rfl
end Sentence1

/-! ### Sentence (2): "They are crossing the border, bringing drugs,
disease and crime."
@cite{ney-2026} §2 example (2). Avowable: gang members and drug
smugglers. Unavowed: Hispanic immigrants. -/
namespace Sentence2
inductive R | hispanicImmigrants | gangAndSmugglers | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .hispanicImmigrants .gangAndSmugglers (by decide)

theorem inter_succeeds :
    coordination (scenario.RS ⊓ scenario.RH) scenario.intention := by
  rintro _ ⟨rfl, _⟩; exact Or.inl rfl

theorem union_succeeds :
    coordination (scenario.RS ⊔ scenario.RH) scenario.intention := by
  rintro _ (rfl | rfl) <;> exact Or.inl rfl
end Sentence2

/-! ### Sentence (3): "Those people are using their power in the
international banks to hide the truth from ordinary, Christian
Americans like us."
@cite{ney-2026} §2 example (3). Avowable: white-collar criminals who
aren't true Christians. Unavowed: purported Jewish elites. -/
namespace Sentence3
inductive R | jewishElites | nonChristianWhiteCollar | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .jewishElites .nonChristianWhiteCollar (by decide)

theorem inter_succeeds :
    coordination (scenario.RS ⊓ scenario.RH) scenario.intention := by
  rintro _ ⟨rfl, _⟩; exact Or.inl rfl

theorem union_succeeds :
    coordination (scenario.RS ⊔ scenario.RH) scenario.intention := by
  rintro _ (rfl | rfl) <;> exact Or.inl rfl
end Sentence3

/-! ### Sentence (4): "This new workplace policy makes it impossible to
act like a real man."
@cite{ney-2026} §2 example (4). Avowable: work-scheduling policy.
Unavowed: sexual-harassment policy. Continuation (4.2) "(Yeah,) it
must have been thought up by some crazy feminist" drives the §3
anaphora-discriminator argument: in @cite{ney-2026}'s own gloss the
anaphor *they* (in subsequent reference) picks out the sexual-
harassment policies — see §7 above. -/
namespace Sentence4
inductive R | sexualHarassmentPolicy | workSchedulingPolicy | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .sexualHarassmentPolicy .workSchedulingPolicy
    (by decide)

theorem inter_succeeds :
    coordination (scenario.RS ⊓ scenario.RH) scenario.intention := by
  rintro _ ⟨rfl, _⟩; exact Or.inl rfl

theorem union_succeeds :
    coordination (scenario.RS ⊔ scenario.RH) scenario.intention := by
  rintro _ (rfl | rfl) <;> exact Or.inl rfl
end Sentence4

/-! ## §9. Aggregate theorems across the four canonical sentences -/

/-- All four canonical sentences exhibit the structural pattern of
insinuative reference. -/
theorem all_four_examples_have_insinuative_structure :
    HasInsinuativeStructure Sentence1.scenario.licenses
                            Sentence1.scenario.intention ∧
    HasInsinuativeStructure Sentence2.scenario.licenses
                            Sentence2.scenario.intention ∧
    HasInsinuativeStructure Sentence3.scenario.licenses
                            Sentence3.scenario.intention ∧
    HasInsinuativeStructure Sentence4.scenario.licenses
                            Sentence4.scenario.intention :=
  ⟨Sentence1.scenario.hasInsinuativeStructure,
   Sentence2.scenario.hasInsinuativeStructure,
   Sentence3.scenario.hasInsinuativeStructure,
   Sentence4.scenario.hasInsinuativeStructure⟩

/-- All four canonical sentences are jointly successful under both
King's objector reconstruction (intersection) and Ney's revision
(union) — the hearer in fact recognizes the unavowed intention; both
conceptions cover. The discriminator is at the CG-availability level
— see §4–§5 above. -/
theorem all_four_examples_are_jointly_successful :
    (coordination (Sentence1.scenario.RS ⊓ Sentence1.scenario.RH)
                  Sentence1.scenario.intention ∧
     coordination (Sentence1.scenario.RS ⊔ Sentence1.scenario.RH)
                  Sentence1.scenario.intention) ∧
    (coordination (Sentence2.scenario.RS ⊓ Sentence2.scenario.RH)
                  Sentence2.scenario.intention ∧
     coordination (Sentence2.scenario.RS ⊔ Sentence2.scenario.RH)
                  Sentence2.scenario.intention) ∧
    (coordination (Sentence3.scenario.RS ⊓ Sentence3.scenario.RH)
                  Sentence3.scenario.intention ∧
     coordination (Sentence3.scenario.RS ⊔ Sentence3.scenario.RH)
                  Sentence3.scenario.intention) ∧
    (coordination (Sentence4.scenario.RS ⊓ Sentence4.scenario.RH)
                  Sentence4.scenario.intention ∧
     coordination (Sentence4.scenario.RS ⊔ Sentence4.scenario.RH)
                  Sentence4.scenario.intention) :=
  ⟨⟨Sentence1.inter_succeeds, Sentence1.union_succeeds⟩,
   ⟨Sentence2.inter_succeeds, Sentence2.union_succeeds⟩,
   ⟨Sentence3.inter_succeeds, Sentence3.union_succeeds⟩,
   ⟨Sentence4.inter_succeeds, Sentence4.union_succeeds⟩⟩

/-- All four canonical sentences exhibit the §3 anaphora discriminator:
the unavowed referent licenses anaphora under Ney's revision but not
under a no-semantic-value (Camp-style implicature-only) account. -/
theorem all_four_examples_exhibit_anaphora_discriminator :
    (coordination (Sentence1.scenario.RS ⊔ Sentence1.scenario.RH)
                  Sentence1.scenario.intention ∧
     ¬ noSemanticValueAccount Sentence1.scenario.intention) ∧
    (coordination (Sentence2.scenario.RS ⊔ Sentence2.scenario.RH)
                  Sentence2.scenario.intention ∧
     ¬ noSemanticValueAccount Sentence2.scenario.intention) ∧
    (coordination (Sentence3.scenario.RS ⊔ Sentence3.scenario.RH)
                  Sentence3.scenario.intention ∧
     ¬ noSemanticValueAccount Sentence3.scenario.intention) ∧
    (coordination (Sentence4.scenario.RS ⊔ Sentence4.scenario.RH)
                  Sentence4.scenario.intention ∧
     ¬ noSemanticValueAccount Sentence4.scenario.intention) :=
  ⟨anaphora_discriminator_ney_revision _ Sentence1.union_succeeds,
   anaphora_discriminator_ney_revision _ Sentence2.union_succeeds,
   anaphora_discriminator_ney_revision _ Sentence3.union_succeeds,
   anaphora_discriminator_ney_revision _ Sentence4.union_succeeds⟩

/-! ## §10. Sentence (5) — interrogative force

@cite{ney-2026} §2 example (5): "What do you think we should do about
those people—you know, those people who cross the border and bring
disease, drugs and crime?" Same insinuative-reference structure as
Sentence (2) (avowable: gang members and drug smugglers; unavowed:
Hispanic immigrants), but with interrogative rather than assertive
illocutionary force.

@cite{ney-2026} p. 5: "the unavowed content consists of a proposition
and an illocutionary force with which it is presented. In (1)–(4) the
illocutionary force is that of assertion. However, others, such as the
interrogative force, are possible. We can see this in (5)."

The current encoding does not represent illocutionary forces
(`SpeakerIntention` carries no `Force` field). Sentence (5) is included
to demonstrate that the metasemantic apparatus applies identically to
interrogative-force cases. A force-aware refactor would distinguish (5)
from (2) at the type level; not done here. -/

namespace Sentence5
inductive R | hispanicImmigrants | gangAndSmugglers | speaker
  deriving DecidableEq, Repr

def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .hispanicImmigrants .gangAndSmugglers (by decide)

theorem inter_succeeds :
    coordination (scenario.RS ⊓ scenario.RH) scenario.intention := by
  rintro _ ⟨rfl, _⟩; exact Or.inl rfl

theorem union_succeeds :
    coordination (scenario.RS ⊔ scenario.RH) scenario.intention := by
  rintro _ (rfl | rfl) <;> exact Or.inl rfl

theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure
end Sentence5

/-! ## §11. The §4 first-pass response and the Lennon counterexample

@cite{ney-2026} §4 (pp. 19–20) considers a first-pass response to the
prima facie challenge: drop ⟨TWO⟩ from the chain, asserting that "in
cases of insinuative reference, it is not part of the common ground
that the hearer is reasonable." This would break ⟨ONE⟩+⟨TWO⟩ ⟹
⟨THREE⟩ and preserve deniability.

Ney rejects this response because it over-generates (paper p. 19):

> "If I point across a busy street and say 'this is where John Lennon
> was born', I rely on the hearer being reasonable. Otherwise, he may
> fail to recognise that I am referring to the house, not, say, the
> car parked in front of it or another town far behind it. Many other
> linguistic devices similarly depend on the hearer being reasonable."

And p. 20:

> "It should be possible for me felicitously to deny having referred
> to the house rather than to the car. After all, I could insist that
> I did not take the hearer to be reasonable, and that I expected them
> to take me to refer to the car. However, this is not the case."

The Lennon scene has the same structural pattern as Sentence (4)
(multiple licensed referents, hearer-reasonableness load-bearing for
disambiguation) but does NOT admit felicitous deniability. The
first-pass response cannot distinguish them, hence over-generates.
Ney's positive proposal (§5 above) localizes the asymmetry differently:
the *conception* of reasonableness — specifically `RS ⊔ RH` — is not
CG-accessible.

The current encoding cannot fully express the empirical asymmetry
("Lennon has the structure but lacks deniability") because the
deniability intent is not formalized as a `Scenario` field. The Lennon
scene is included as a structural-equivalence witness — the formal
hook for §4's over-generation argument. The empirical asymmetry is
documented but not formally derivable here. -/

namespace LennonScene

/-- Entities for the Lennon scene: the house (intended), a parked car
(visible distractor), the speaker. -/
inductive R | house | car | speaker
  deriving DecidableEq, Repr

/-- Pointing across a busy street saying "this is where John Lennon was
born", the speaker intends the house; the parked car is also a salient
visible referent. -/
def scenario : Scenario Unit Unit R :=
  Scenario.mkBinary .speaker .house .car (by decide)

/-- The Lennon scene exhibits the structural pattern of insinuative
reference (multiple licensed referents with one intended). This is the
formal hook for @cite{ney-2026} §4's over-generation argument: any
account that distinguishes the Lennon scene from genuine insinuative-
reference cases must look beyond `HasInsinuativeStructure`. -/
theorem hasInsinuativeStructure :
    HasInsinuativeStructure scenario.licenses scenario.intention :=
  scenario.hasInsinuativeStructure

end LennonScene

/-- @cite{ney-2026} §4 over-generation result: the Lennon scene and
Sentence (4) both exhibit the structural pattern of insinuative
reference. The §4 first-pass response (drop ⟨TWO⟩) cannot distinguish
them, so it would predict deniability for both — but empirically only
Sentence (4) admits deniability. The structural pattern alone does
not predict deniability; the speaker-side deniability intent (not
encoded here, see file docstring) is the missing distinguisher. -/
theorem first_pass_response_overgenerates :
    HasInsinuativeStructure Sentence4.scenario.licenses
                            Sentence4.scenario.intention ∧
    HasInsinuativeStructure LennonScene.scenario.licenses
                            LennonScene.scenario.intention :=
  ⟨Sentence4.scenario.hasInsinuativeStructure,
   LennonScene.hasInsinuativeStructure⟩

/-! ## §12. §3 firstly: uniqueness vs indirect-speech reduction

@cite{ney-2026} §3 (pp. 14–15) "firstly": insinuative reference cannot
be reduced to indirect speech via the avowable's direct content.
Argument structure (paper pp. 14–15):

(i)  IF insinuative reference were indirect speech, THEN in Sentence (4)
     the direct illocutionary act would assert (22) [= "this new
     workplace policy" with reference = work-scheduling policy], which
     by p. 14 has the same truth conditions as (21) "this new
     work-scheduling policy makes it impossible to act like a real man".
(ii) However, uttering (21) directly does NOT communicate the unavowed
     content (= the sexual-harassment policy makes it impossible).
(iii) Therefore insinuative reference is not indirect-speech-via-
     avowable-direct-content.

@cite{ney-2026} acknowledges (p. 15) that an indirect speech act may
depend on the locutionary word choice rather than direct propositional
content, but argues the only available implicature route would not
involve the avowable referent at all — making the avowable's "direct"
status arbitrary.

A full Lean formalization requires modeling Gricean implicature
derivation, which the current substrate does not provide. The bare
statable hook here is the truth-conditional distinctness of the
avowable and unavowed referents — at minimum the indirect-speech
account has to assign the same content to (4) and (21) under one of
its referent-assignments, and they really are extensionally distinct. -/

/-- Sentence (4)'s avowable and unavowed referents are distinct entities;
hence any account that conflates them under "direct content" makes a
truth-conditionally false prediction. This is the bare hook for
@cite{ney-2026} §3 firstly. The substantive claim — that no Gricean
implicature mechanism reduces insinuative reference to indirect speech
— requires implicature substrate not yet built. -/
theorem sentence4_unavowed_distinct_from_avowable :
    Sentence4.scenario.intention.intendedRef ≠
      Sentence4.R.workSchedulingPolicy := by
  decide

/-! ## §13. §3 secondly: de re vs de dicto recognition

@cite{ney-2026} §3 (p. 16) "secondly": a hearer can recognize the
unavowed content de dicto without being de re aware of any particular
avowable possible referent. Argument structure:

(i)  IF insinuative reference were indirect speech, THEN recognizing
     indirect content requires first grasping direct content (per
     standard accounts of indirect speech).
(ii) However, the hearer of Sentence (4) may be merely de dicto aware
     that there are workplace policies other than the sexual-harassment
     one — they need not have any particular de re grasp of an avowable.
     They can still recognize the unavowed content.
(iii) Therefore insinuative reference is not indirect speech.

The avowable-existence requirement in `HasInsinuativeStructure`
(`∃ r, r ≠ s.intendedRef ∧ licenses r`) is *existential* (de dicto):
no specific avowable is identified. This matches the structural
requirement Ney needs and is the bare hook for the §3 secondly
argument. A full formalization distinguishing de re grasp
(`∃ r, hearer_grasps r ∧ licenses r`) from de dicto grasp
(`hearer_grasps_that (∃ r, licenses r)`) requires belief-state
substrate not yet built; the structural requirement here is sufficient
for what Ney's argument needs at the formal level. -/

end Ney2026
