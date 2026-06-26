import Linglib.Semantics.NaturalLogic
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Polarity.Item
import Linglib.Semantics.Entailment.Polarity
import Linglib.Semantics.Entailment.StrawsonEntailment
import Linglib.Semantics.Exhaustification.FreeChoice
import Linglib.Semantics.Supervaluation.Basic
import Linglib.Studies.Ladusaw1979
import Mathlib.Data.Set.Basic

/-!
# Kadmon & Landman 1993: *Any*

Formalizes [kadmon-landman-1993]'s unified analysis of *any*: *any CN* is the
indefinite *a CN* plus **widening** of the CN denotation along a contextual
dimension, licensed only if widening creates a stronger statement
(**strengthening**), checked at the local proposition (**locality**);
free-choice *any* is the same item with a generic interpretation.
Strengthening subsumes [ladusaw-1979]'s DE condition — widening an existential
strengthens exactly when the context is DE — but K&L stress it is necessary,
not sufficient: *each* and comparative *more often than* are DE yet resist
*any* because widening must also make pragmatic sense (their §3.2).

## Main declarations

- `Strengthening`: the licensing condition — widening `D` to `D'` in context
  `C` creates a stronger statement;
- `de_satisfies_strengthening`: antitone (DE) contexts satisfy strengthening;
- `GuaranteesStrengthening`, `klExplanation`: per-context classification,
  projected from `Semantics.Polarity.Licensing.contextProperties`;
- `ladusaw_de_is_kl_strengthening`: Ladusaw-DE contexts are strengthening
  contexts;
- `sorry_licenses_any`, `glad_does_not_license`: the adversative asymmetry
  (Strawson-DE vs UE, K&L §3.3);
- `widening_satisfies_conditional_strengthening`: widening plus
  restriction-weakening guarantees strengthening in conditional antecedents
  (K&L §3.5.3);
- `VagueRestriction`, `widenAlong`, `dimensionallyUniversal`: the
  domain-vagueness apparatus behind FC *any* and the *almost* test (K&L §4);
- `domain_vague_allows_exceptions`: exception tolerance of generics from
  domain vagueness;
- `VagueRestriction.toSpecSpace`: the finite-case bridge to [fine-1975]'s
  supervaluation — K&L's exception-tolerance zone is Fine's borderline zone.
-/

namespace KadmonLandman1993

open NaturalLogic
open Semantics.Polarity (LicensingContext)
open Semantics.Polarity.Licensing (LicensingMechanism)
open Entailment
open Exhaustification.FreeChoice (Ctx existsInDomain
  widening_strengthens_in_de widening_weakens_in_ue)
open Ladusaw1979 (licensingStrength)
open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff
  superTrue_indet_iff)
open Core.Duality (Truth3)

/-! ### The strengthening condition

K&L's component (C): *any* is licensed only if widening creates a stronger
statement. For a context `C` and domains `D ⊆ D'`, the wide interpretation
must entail the narrow: `C (∃x∈D', Px) ⊆ C (∃x∈D, Px)`. This holds exactly
when `C` is antitone, which is why DE contexts license — and why widening in
UE contexts, where it weakens, leaves *any* unlicensed. -/

/-- K&L's strengthening condition: widening the domain `D` to `D'` in context
`C` creates a stronger statement — the wide interpretation entails the narrow
one. -/
def Strengthening {World Entity : Type*} (C : Ctx World) (D D' : Set Entity)
    (P : Entity → Set World) : Prop :=
  C (existsInDomain D' P) ⊆ C (existsInDomain D P)

/-- In a DE (antitone) context, strengthening is automatic. K&L note that for
many examples this makes the same predictions as [ladusaw-1979], while
explaining *why* DE contexts license: widening must strengthen, and DE
reverses entailment. -/
theorem de_satisfies_strengthening {World Entity : Type*} {C : Ctx World}
    (hDE : Antitone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : Strengthening C D D' P :=
  widening_strengthens_in_de C hDE D D' P hD

/-- In a UE (monotone) context, widening *weakens* — the opposite of
strengthening. This is K&L's explanation for why *any* is out in plain
positive contexts. -/
theorem ue_widening_weakens {World Entity : Type*} {C : Ctx World}
    (hUE : Monotone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : C (existsInDomain D P) ⊆ C (existsInDomain D' P) :=
  widening_weakens_in_ue C hUE D D' P hD

/-! ### Licensing contexts and entailment signatures

Each context's entailment signature and licensing mechanism are projected
from the canonical `Semantics.Polarity.Licensing.contextProperties` table, so
this file's classification cannot drift from the substrate's. -/

/-- A licensing context's entailment signature in [icard-2012]'s lattice —
the Strawson-operative row, matching K&L's own convention of checking the
DE pattern modulo factive presuppositions. -/
abbrev contextEntailmentSig (c : LicensingContext) : EntailmentSig :=
  (Semantics.Polarity.Licensing.contextProperties c).strawsonSignature

/-- A context guarantees K&L strengthening iff its entailment signature is on
the DE side. Contexts with `.mono` or higher signatures are licensed by other
routes: K&L defer questions to [kadmon-landman-1990] and never discuss
superlatives — the Strawson-DE route for the latter is later literature
([von-fintel-1999]). -/
abbrev GuaranteesStrengthening (c : LicensingContext) : Prop :=
  (contextEntailmentSig c).toDEStrength.isSome = true

-- Standard DE contexts guarantee strengthening.
example : ∀ c ∈ [LicensingContext.negation, .nobody, .withoutClause, .few,
    .conditionalAntecedent, .adversative, .beforeClause, .onlyFocus],
    GuaranteesStrengthening c := by decide

-- Non-DE contexts do not guarantee strengthening via DE.
example : ∀ c ∈ [LicensingContext.question, .modalPossibility, .generic],
    ¬ GuaranteesStrengthening c := by decide

/-- A licensing context's K&L mechanism, projected from `contextProperties`:
*why* the context licenses, not merely *that* it does. -/
abbrev klExplanation (c : LicensingContext) : LicensingMechanism :=
  (Semantics.Polarity.Licensing.contextProperties c).mechanism

/-- Drift sentry: every context classified `byStrengthening` has a DE
entailment signature. -/
theorem strengthening_implies_de (ctx : LicensingContext)
    (h : klExplanation ctx = .byStrengthening) :
    GuaranteesStrengthening ctx := by
  revert h; cases ctx <;> decide

/-! ### Compatibility with Ladusaw 1979

K&L's classification refines [ladusaw-1979]'s: every Ladusaw-DE context is a
strengthening context, but K&L additionally explain adversative predicates
(DE on a constant perspective) and conditionals with implicit restrictions. -/

/-- Ladusaw-DE contexts are K&L strengthening contexts — or, where the DE
status is itself only Strawson (superlatives, per the later
[von-fintel-1999]), the Strawson refinement of strengthening. Ladusaw
describes *where* NPIs occur; K&L and the Strawson tradition explain
*why*. -/
theorem ladusaw_de_is_kl_strengthening (ctx : LicensingContext)
    (hDE : licensingStrength ctx = .antiAdditive ∨
           licensingStrength ctx = .downwardEntailing) :
    klExplanation ctx = .byStrengthening ∨
    klExplanation ctx = .byStrawsonDE := by
  revert hDE; cases ctx <;> decide

/-! ### Adversative predicates: *sorry* vs *glad*

K&L §3.3: *sorry that A* entails *want ¬A*, and wanting a set empty entails
wanting all its subsets empty, so for *sorry* the wide interpretation entails
the narrow — strengthening holds. *Glad that A* entails *want A*, and wanting
a set inhabited does not entail wanting each subset inhabited, so
strengthening fails. K&L summarize: adversative predicates are DE on a
constant perspective (and so guarantee strengthening), while predicates like
*glad* are not DE. The constant "perspective" is the `bestOf` parameter; the
factive presupposition means the DE pattern is Strawson, not classical. -/

/-- *Sorry* licenses NPIs: it is Strawson-DE — DE with the perspective
(`bestOf`) held constant. Imported from
`StrawsonEntailment.sorryFull_isStrawsonDE`; consumed by `VonFintel1999`'s
cross-framework bridge. -/
theorem sorry_licenses_any (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (λ p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-- *Sorry* is not classically DE: the doxastic factivity presupposition
blocks it. K&L adopt Ladusaw's convention that the DE pattern need only hold
of the sentence minus its factive presupposition. -/
theorem sorry_not_classically_de :
    ¬IsDownwardEntailing
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World))) :=
  sorryFull_not_de

/-- *Glad* does not freely license NPIs: it is UE, so widening weakens.
K&L: wanting a set to have members does not entail wanting each particular
subset to have members. -/
theorem glad_does_not_license (dox bestOf : World → Set World) :
    Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

/-- A settle-for-less datum (K&L §3.3.2): *any* under *glad* is licensed only
on the interpretation where the speaker's preferred "narrow wish" cannot be
satisfied and they settle for the wide one. With the real wish identified
with the narrow wish, being glad of the wide statement entails that one would
be glad of the narrow one — K&L's (101) entails (102) — so strengthening is
satisfied. -/
structure SettleForLessDatum where
  sentence : String
  grammatical : Bool
  notes : String

/-- K&L (76B). -/
def settleGladTickets : SettleForLessDatum :=
  { sentence := "Be glad we got ANY tickets!"
  , grammatical := true
  , notes := "settle for less: the narrow wish (better tickets) is preferred but unsatisfiable" }

/-- K&L (88). The widening runs from phonologists to linguists, so the narrow
wish (a phonologist likes me) is the preferred, real wish. -/
def settleGladAnybody : SettleForLessDatum :=
  { sentence := "I'm glad ANYBODY likes me!"
  , grammatical := true
  , notes := "settle for less: the narrow wish (a phonologist likes me) is preferred but unsatisfiable" }

/-- K&L (95): *sure* allows no settle-for-less interpretation — their
(96)–(98) lack the characteristic negative implication — so *any* under
*sure* is never rescued. -/
def sureNoSettle : SettleForLessDatum :=
  { sentence := "*I'm sure we got ANY tickets!"
  , grammatical := false
  , notes := "sure has no settle-for-less interpretation" }

/-! ### Conditional antecedents

K&L §3.5 treat conditionals and adversatives as one pattern — DE with a
parameter held constant (the implicit restriction, resp. the perspective);
in mathlib terms, `Antitone (f param)` for fixed `param`. Under the
restrictor analysis of conditionals (cf. [kratzer-1986]), the antecedent of
conditional necessity is classically DE once the modal base is fixed, so
widening the antecedent domain strengthens the conditional. -/

/-- Conditional antecedents satisfy strengthening: conditional necessity is
DE in its antecedent with the modal base held constant. K&L (143): "If John
subscribes to any newspaper, he gets well informed" — widening *newspaper* to
include unimportant newspapers strengthens the conditional. -/
theorem conditional_satisfies_strengthening {W : Type*}
    (domain : W → Set W) (β : Set W) :
    IsDownwardEntailing (λ α => condNecessity domain α β) :=
  conditional_antecedent_antitone domain β

/-- A conditional with an implicit restriction (K&L's (147)): true iff every
relevant case satisfying the restriction and the antecedent satisfies the
consequent. -/
def conditionalWithRestriction {Case : Type*}
    (restriction antecedent consequent : Case → Prop) : Prop :=
  ∀ c, restriction c → antecedent c → consequent c

/-- **Widening always satisfies strengthening in conditional antecedents**
(K&L §3.5.3). Natural-language conditionals are not classically DE — their
(140) does not entail (141) — because the implicit restriction can shift. But
the restriction cannot undo the effect of widening, so the wide restriction
is never stronger than the narrow one, and then the wide conditional entails
the narrow one. K&L: strengthening inferences "do always go through, because
of the relation between the restrictions of the premise and of the
conclusion. The two restrictions are always the same, except that the
restriction of the premise may be somewhat weaker (but never stronger), as
dictated by the widening." -/
theorem widening_satisfies_conditional_strengthening {Case : Type*}
    {R_narrow R_wide A_narrow A_wide consequent : Case → Prop}
    (hRestrWeaker : ∀ c, R_narrow c → R_wide c)
    (hAntWeaker : ∀ c, A_narrow c → A_wide c)
    (hWide : conditionalWithRestriction R_wide A_wide consequent) :
    conditionalWithRestriction R_narrow A_narrow consequent :=
  λ c hR hA => hWide c (hRestrWeaker c hR) (hAntWeaker c hA)

/-! ### Negated because-clauses: metalinguistic licensing

K&L §3.4, contra [linebarger-1987]: `not because [S_]` is not DE (*because
[S_]* is not UE, so negating it yields no DE context), while `not because of
[NP_]` is DE and licenses *any* freely — their (122)/(123) need no negative
implication. In `because [S_]`, *any* is licensed only metalinguistically:
the negation denies *because*'s factive presupposition, and *any* strengthens
that denial. Merely implying the denial is not enough — the rhetorical
conditional (132) can imply it but lacks the metalinguistic denial, and *any*
is out. This is the paper's only genuinely non-DE licensing mechanism. -/

/-- A because-clause licensing datum. The prediction checked below is
`grammatical = npComplement || metalinguisticDenial`; both fields are
annotations transcribed from K&L's §3.4 discussion, so the `#guard` is a
consistency check on the transcription, not a derived prediction. -/
structure BecauseClauseDatum where
  sentence : String
  grammatical : Bool
  /-- *because of [NP_]* (DE under negation, licenses freely) vs *because [S_]* -/
  npComplement : Bool
  /-- Whether the metalinguistic presupposition-denial reading is available.
  Mere implication of the denial does not suffice (K&L on (132)). -/
  metalinguisticDenial : Bool
  notes : String

/-- K&L (105). -/
def becauseEx105 : BecauseClauseDatum :=
  { sentence := "It isn't because Sue said anything bad about me that I'm angry"
  , grammatical := true, npComplement := false, metalinguisticDenial := true
  , notes := "negation denies the factive presupposition of because; any strengthens the denial" }

/-- K&L (106), from [linebarger-1987]; marked #. -/
def becauseEx106 : BecauseClauseDatum :=
  { sentence := "#I didn't help him because I have any sympathy for urban guerillas, although I do sympathize with urban guerillas"
  , grammatical := false, npComplement := false, metalinguisticDenial := false
  , notes := "continuation cancels the negative implication, so no presupposition denial" }

/-- K&L (109): the *any*-bearing sentence of their own constructed Sir
Winfred passage; marked #. The surrounding text cancels the negative
implication, and *any* is bad. -/
def becauseEx109 : BecauseClauseDatum :=
  { sentence := "#Yet, in the present case, it wasn't because he had any such sympathy that he had decided to take on the case"
  , grammatical := false, npComplement := false, metalinguisticDenial := false
  , notes := "textual context cancels the negative implication; because [S_] then rejects any" }

/-- K&L (122). -/
def becauseEx122 : BecauseClauseDatum :=
  { sentence := "It isn't because of anything she said that I'm angry - although she did say all sorts of annoying things - it's because of the faces she was making"
  , grammatical := true, npComplement := true, metalinguisticDenial := false
  , notes := "because of [NP_] is DE under negation: any licensed freely, no negative implication needed" }

/-- K&L (123): the felicitous Sir Winfred variant — the minimal pair with
(109), substituting *because of* + NP. -/
def becauseEx123 : BecauseClauseDatum :=
  { sentence := "Yet, in the present case, it wasn't because of any such sympathy that he had decided to take on the case"
  , grammatical := true, npComplement := true, metalinguisticDenial := false
  , notes := "minimal pair with (109): the NP complement restores plain DE licensing" }

/-- K&L (125). -/
def becauseEx125 : BecauseClauseDatum :=
  { sentence := "It's not because anybody read her paper that she's happy"
  , grammatical := true, npComplement := false, metalinguisticDenial := true
  , notes := "any strengthens the presupposition denial: nobody read it, even on the wide interpretation" }

/-- K&L (132): the rhetorical conditional; marked *. It can imply the denial
of the presupposition, but cannot metalinguistically deny it. -/
def becauseEx132 : BecauseClauseDatum :=
  { sentence := "*If it's because anybody read her paper that she is happy, I'll eat my hat"
  , grammatical := false, npComplement := false, metalinguisticDenial := false
  , notes := "implies the denial but cannot metalinguistically deny the presupposition" }

#guard [becauseEx105, becauseEx106, becauseEx109, becauseEx122, becauseEx123,
        becauseEx125, becauseEx132].all λ d =>
  d.grammatical == (d.npComplement || d.metalinguisticDenial)

/-! ### FC *any* as generic indefinite

K&L's component (FC): PS *any* is a regular indefinite, FC *any* a generic
indefinite; the apparent universal force of FC *any* emerges from genericity
plus widening (§4.3). The episodic/generic split below is projected from the
substrate's mechanism classification. K&L themselves analyze only plain
generics like their (10) and tentatively extend to modals; routing
imperatives and free relatives through the generic mechanism follows the
substrate, not K&L's text (they explicitly defer directives to later work and
never discuss free relatives). -/

/-- Interpretation of the indefinite containing *any*: episodic (PS *any*) or
generic (FC *any*). -/
inductive AnyInterpretation where
  | episodic
  | generic
  deriving DecidableEq, Repr

/-- The interpretation of *any* in a licensing context, projected from the
licensing mechanism: generic exactly when the substrate classifies the
context as licensed by the generic indefinite. -/
def interpretationOf (c : LicensingContext) : AnyInterpretation :=
  match klExplanation c with
  | .byGenericIndefinite => .generic
  | _ => .episodic

theorem interpretationOf_eq_generic_iff (c : LicensingContext) :
    interpretationOf c = .generic ↔ klExplanation c = .byGenericIndefinite := by
  cases h : klExplanation c <;> simp only [interpretationOf, h] <;> decide

/-! ### Vague restrictions and precisifications

K&L §4.1: *every owl* is **domain precise** — context determines a unique
domain — while generic *an owl* is **domain vague**: the normalcy restriction
is inherently underspecified, and different precisifications yield different
domains. This is what lets generics tolerate exceptions ("a poodle gives live
birth" survives male poodles). The `Set`-based notions are stated locally
because the supervaluation substrate (`Semantics/Supervaluation`,
[fine-1975]) is `Finset`-based for computability; the finite-case bridge is
`VagueRestriction.toSpecSpace` below. -/

/-- A vague restriction ⟨v₀, V⟩ (K&L §4.1): a precise part (properties known
to hold) together with its consistent completions, each extending the precise
part, which is itself a minimal precisification. -/
structure VagueRestriction (Property : Type*) where
  /-- The precise part: properties definitely in the restriction. -/
  precise : Set Property
  /-- The consistent ways to complete the restriction. -/
  precisifications : Set (Set Property)
  /-- Every precisification extends the precise part. -/
  extends_precise : ∀ v ∈ precisifications, precise ⊆ v
  /-- The precise part is itself a (minimal) precisification. -/
  precise_mem : precise ∈ precisifications

/-- The domain induced by a property set: the entities satisfying every
property. -/
def domainOf {Property Entity : Type*} (props : Set Property)
    (apply : Property → Set Entity) : Set Entity :=
  {e | ∀ P ∈ props, e ∈ apply P}

/-- Domain precise (K&L (164)): every precisification determines the same
domain as the precise part. -/
def isDomainPrecise {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ∀ v ∈ X.precisifications, domainOf v apply = domainOf X.precise apply

/-- Domain vague: not domain precise — some precisifications yield different
domains. -/
def isDomainVague {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ¬isDomainPrecise X apply

/-- If every precisification equals the precise part, the restriction is
domain precise — the case of *every* and *no*. -/
theorem isDomainPrecise_of_forall_eq {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (h : ∀ v ∈ X.precisifications, v = X.precise) :
    isDomainPrecise X apply :=
  λ v hv => by rw [h v hv]

/-- Widening along a dimension (K&L (174)): remove the properties on the
dimension from the precise part and from every precisification. -/
def widenAlong {Property : Type*} (X : VagueRestriction Property)
    (onDimension : Property → Prop) : VagueRestriction Property where
  precise := {P ∈ X.precise | ¬onDimension P}
  precisifications := (λ v => {P ∈ v | ¬onDimension P}) '' X.precisifications
  extends_precise := by
    rintro v' ⟨v, hv, rfl⟩ P ⟨hPprec, hPnot⟩
    exact ⟨X.extends_precise v hv hPprec, hPnot⟩
  precise_mem := ⟨X.precise, X.precise_mem, rfl⟩

/-- Widening weakens the restriction: the widened precise part is a subset of
the original. -/
theorem widenAlong_weakens_precise {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop) :
    (widenAlong X onDimension).precise ⊆ X.precise :=
  λ _ ⟨h, _⟩ => h

/-- Widening expands the domain: fewer constraints, more entities qualify.
This is the restriction-weakening half of K&L §3.5.3: the restriction cannot
undo the effect of widening. -/
theorem widenAlong_expands_domain {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) :
    domainOf X.precise apply ⊆
    domainOf (widenAlong X onDimension).precise apply :=
  λ _ he P ⟨hPprec, _⟩ => he P hPprec

/-! ### Dimensional universality

K&L (175)–(177): after widening along a dimension {P, ¬P}, no entity is
excluded on the basis of that dimension, so the quantifier is universal with
respect to it. *Any CN* is dimensionally universal; generic *a CN* is not.
Since *almost* requires a domain-precise universal or a dimensionally
universal NP, this derives *almost any owl* vs ungrammatical *almost an owl*
(§4.3). -/

/-- Universality with respect to a dimension (K&L (175)): after widening
along the dimension, every entity in the base denotation is in the domain. -/
def universalWrtDimension {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) (baseDenotation : Set Entity) : Prop :=
  baseDenotation ⊆ domainOf (widenAlong X onDimension).precise apply

/-- A dimension is non-trivial on a base set (K&L (176)): some entity
satisfies a property on the dimension and some entity fails one. -/
def nonTrivialDimension {Property Entity : Type*}
    (onDimension : Property → Prop) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∈ apply P) ∧
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∉ apply P)

/-- Dimensionally universal (K&L (177)): universal with respect to some
non-trivial dimension. -/
def dimensionallyUniversal {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  ∃ onDimension : Property → Prop,
    nonTrivialDimension onDimension apply baseDenotation ∧
    universalWrtDimension X onDimension apply baseDenotation

/-- *Any CN* is dimensionally universal (K&L §4.3): widening along a
non-trivial dimension yields universality with respect to that dimension. -/
theorem any_cn_dimensionally_universal {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) (baseDenotation : Set Entity)
    (hNT : nonTrivialDimension onDimension apply baseDenotation)
    (hBase : baseDenotation ⊆ domainOf {P ∈ X.precise | ¬onDimension P} apply) :
    dimensionallyUniversal (widenAlong X onDimension) apply baseDenotation :=
  ⟨onDimension, hNT, λ _ he P ⟨⟨hPprec, hPnot⟩, _⟩ => hBase he P ⟨hPprec, hPnot⟩⟩

/-- Total widening: if every precise property is on the dimension, widening
empties the precise part — K&L's case where *any CN* becomes not only
universal with respect to the dimension but truly universal. -/
theorem widenAlong_precise_eq_empty {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (hAllOnDim : ∀ P ∈ X.precise, onDimension P) :
    (widenAlong X onDimension).precise = ∅ := by
  ext P
  simp only [widenAlong, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hP, hNot⟩
  exact hNot (hAllOnDim P hP)

/-! ### Generic quantification as vague universality

K&L §4.1.1: a generic is a universal restricted by a vague property set —
"An owl hunts mice" is ∀ ↾ X_owl(Owl)(Hunts mice), their (159). The
traditional GEN operator's hidden normalcy parameter
(`Semantics/Genericity/Generics.lean`) is, on this view, a choice of
precisification; exception tolerance is the freedom to choose another. -/

/-- Truth under one precisification: every entity in the induced domain
satisfies the scope. -/
def genericTrue {Property Entity : Type*} (apply : Property → Set Entity)
    (scope : Entity → Prop) (v : Set Property) : Prop :=
  ∀ e ∈ domainOf v apply, scope e

/-- Supervaluationist truth: true under every precisification. -/
def genericSuperTrue {Property Entity : Type*} (X : VagueRestriction Property)
    (apply : Property → Set Entity) (scope : Entity → Prop) : Prop :=
  ∀ v ∈ X.precisifications, genericTrue apply scope v

/-- Subvaluationist truth: true under some precisification — the
exception-tolerant reading. -/
def genericSubTrue {Property Entity : Type*} (X : VagueRestriction Property)
    (apply : Property → Set Entity) (scope : Entity → Prop) : Prop :=
  ∃ v ∈ X.precisifications, genericTrue apply scope v

/-- Domain vagueness yields two precisifications with different domains —
the room generics need for legitimate exceptions. -/
theorem domain_vague_allows_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (hVague : isDomainVague X apply) :
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply := by
  unfold isDomainVague isDomainPrecise at hVague
  push Not at hVague
  obtain ⟨v, hv, hne⟩ := hVague
  exact ⟨v, hv, X.precise, X.precise_mem, hne⟩

/-- K&L's explanation of exception tolerance: if the restriction is domain
vague and the generic is subvaluationistically true, then there are
precisifications with different domains and the generic holds under one of
them — an apparent counterexample may fall outside the domain under the
operative precisification. -/
theorem domain_vagueness_explains_gen_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) (hVague : isDomainVague X apply)
    (hSub : genericSubTrue X apply scope) :
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply ∧
      genericTrue apply scope v₁ := by
  obtain ⟨v₁, hv₁m, v₂, hv₂m, hne⟩ := domain_vague_allows_exceptions X apply hVague
  obtain ⟨vg, hvgm, hvgt⟩ := hSub
  by_cases h : domainOf vg apply = domainOf v₁ apply
  · exact ⟨vg, hvgm, v₂, hv₂m, by rw [h]; exact hne, hvgt⟩
  · exact ⟨vg, hvgm, v₁, hv₁m, h, hvgt⟩

/-! ### Grounding in Fine 1975 supervaluation

When the precisification set is finite, K&L's truth notions are
[fine-1975]'s: `genericSuperTrue` is super-truth on the induced
specification space, and the exception-tolerance zone — sub-true but not
super-true — is exactly Fine's borderline (`indet`) status. "A poodle gives
live birth" is Fine-indefinite and K&L-assertable. -/

/-- The specification space induced by a vague restriction whose
precisifications are enumerated by a finset. Nonemptiness is K&L's axiom
that the precise part is itself a precisification. -/
def VagueRestriction.toSpecSpace {Property : Type*} (X : VagueRestriction Property)
    (V : Finset (Set Property)) (hV : ↑V = X.precisifications) :
    SpecSpace (Set Property) where
  admissible := V
  nonempty := ⟨X.precise, by rw [← Finset.mem_coe, hV]; exact X.precise_mem⟩

theorem VagueRestriction.mem_toSpecSpace {Property : Type*}
    {X : VagueRestriction Property} {V : Finset (Set Property)}
    {hV : ↑V = X.precisifications} {v : Set Property} :
    v ∈ (X.toSpecSpace V hV).admissible ↔ v ∈ X.precisifications := by
  constructor
  · intro h; rw [← hV]; exact Finset.mem_coe.mpr h
  · intro h
    show v ∈ V
    rw [← Finset.mem_coe, hV]
    exact h

/-- On a finite precisification space, K&L's supervaluationist truth is
[fine-1975]'s super-truth. -/
theorem genericSuperTrue_iff_superTrue {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) [DecidablePred (genericTrue apply scope)]
    (V : Finset (Set Property)) (hV : ↑V = X.precisifications) :
    genericSuperTrue X apply scope ↔
      superTrue (genericTrue apply scope) (X.toSpecSpace V hV) = Truth3.true := by
  rw [superTrue_true_iff]
  exact ⟨λ h v hv => h v (VagueRestriction.mem_toSpecSpace.mp hv),
         λ h v hv => h v (VagueRestriction.mem_toSpecSpace.mpr hv)⟩

/-- **K&L's exception-tolerance zone is Fine's borderline zone.** A generic
that is subvaluationistically but not supervaluationistically true is
exactly one whose supervaluation status is indefinite: assertable for K&L,
borderline for [fine-1975]. -/
theorem genericSubTrue_not_superTrue_iff_indet {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) [DecidablePred (genericTrue apply scope)]
    (V : Finset (Set Property)) (hV : ↑V = X.precisifications) :
    genericSubTrue X apply scope ∧ ¬genericSuperTrue X apply scope ↔
      superTrue (genericTrue apply scope) (X.toSpecSpace V hV) = Truth3.indet := by
  rw [superTrue_indet_iff]
  constructor
  · rintro ⟨⟨v, hv, hvt⟩, hns⟩
    refine ⟨⟨v, VagueRestriction.mem_toSpecSpace.mpr hv, hvt⟩, ?_⟩
    by_contra hno
    exact hns (λ w hw => by
      by_contra hwf
      exact hno ⟨w, VagueRestriction.mem_toSpecSpace.mpr hw, hwf⟩)
  · rintro ⟨⟨v, hv, hvt⟩, ⟨w, hw, hwf⟩⟩
    exact ⟨⟨v, VagueRestriction.mem_toSpecSpace.mp hv, hvt⟩,
           λ hall => hwf (hall w (VagueRestriction.mem_toSpecSpace.mp hw))⟩

/-! ### The *almost* test

K&L: *almost* modifies domain-precise true universal quantifiers (∀ or ¬∃)
and, after §4.3, dimensionally universal NPs. *Some owl* is domain precise
(K&L p. 412 group it with *every owl* and *no owl*) but not universal, so
*almost some owl* is out; generic *an owl* has universal force but a vague
domain; *any owl* is rescued by dimensional universality. -/

/-- Domain precision of an NP's restriction (K&L §4.1.2). -/
inductive DomainPrecision where
  | precise
  | vague
  deriving DecidableEq, Repr

/-- An *almost*-modification datum. -/
structure AlmostDatum where
  np : String
  almostOK : Bool
  precision : DomainPrecision
  /-- Whether the NP is a true universal (∀ or ¬∃). -/
  universalForce : Bool
  dimUniversal : Bool
  deriving DecidableEq, Repr

/-- K&L's condition: a domain-precise universal, or a dimensionally universal
NP. -/
def AlmostDatum.predicted (d : AlmostDatum) : Bool :=
  (d.universalForce && d.precision == .precise) || d.dimUniversal

def almostEvery : AlmostDatum :=
  { np := "every owl", almostOK := true
  , precision := .precise, universalForce := true, dimUniversal := false }

def almostNo : AlmostDatum :=
  { np := "no owl", almostOK := true
  , precision := .precise, universalForce := true, dimUniversal := false }

def almostSome : AlmostDatum :=
  { np := "some owl", almostOK := false
  , precision := .precise, universalForce := false, dimUniversal := false }

def almostGenericA : AlmostDatum :=
  { np := "an owl", almostOK := false
  , precision := .vague, universalForce := true, dimUniversal := false }

def almostAny : AlmostDatum :=
  { np := "any owl", almostOK := true
  , precision := .vague, universalForce := true, dimUniversal := true }

#guard [almostEvery, almostNo, almostSome, almostGenericA, almostAny].all
  λ d => d.predicted == d.almostOK

/-! ### Key examples

`localSig` is the entailment signature at the narrowest operator scoping over
*any* — the one K&L's locality condition (D) checks; `globalSig` the
sentence-level signature. For adversatives the signature idealizes the
factive presupposition away, per K&L's adoption of Ladusaw's convention
(`sorry_not_classically_de` shows classical DE fails). -/

/-- An NPI licensing datum with K&L's explanation. -/
structure KLDatum where
  sentence : String
  grammatical : Bool
  /-- K&L's licensing mechanism for the judgment. -/
  explanation : LicensingMechanism
  /-- Signature at the narrowest operator scoping over *any*. -/
  localSig : EntailmentSig
  /-- Sentence-level signature; defaults to `localSig`. -/
  globalSig : EntailmentSig := localSig
  wideningDimension : Option String := none
  deriving Repr

/-- K&L (1): PS *any* under negation. -/
def ex1 : KLDatum :=
  { sentence := "I don't have any potatoes"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .antiAddMult
  , wideningDimension := some "cooking vs non-cooking potatoes" }

/-- K&L (2): positive context — widening weakens, so strengthening fails. -/
def ex2 : KLDatum :=
  { sentence := "*I have any potatoes"
  , grammatical := false
  , explanation := .strengtheningFails
  , localSig := .mono }

/-- K&L (10): FC *any* in a generic context. -/
def ex10 : KLDatum :=
  { sentence := "Any owl hunts mice"
  , grammatical := true
  , explanation := .byGenericIndefinite
  , localSig := .mono
  , wideningDimension := some "healthy vs sick owls" }

/-- K&L (27b): restrictor of a universal is anti-additive. -/
def ex27b : KLDatum :=
  { sentence := "Every man who has any matches is happy"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .antiAdd
  , wideningDimension := some "dry vs wet matches" }

/-- K&L (55): scope of a universal is UE. -/
def ex55 : KLDatum :=
  { sentence := "*Every boy has any potatoes"
  , grammatical := false
  , explanation := .strengtheningFails
  , localSig := .mult }

/-- K&L (56): locality. The global signature (under negation) composes to DE,
but the local context (scope of *every*) is UE, so *any* is out despite the
DE global context. -/
def ex56 : KLDatum :=
  { sentence := "*It's not the case that every boy has any potatoes"
  , grammatical := false
  , explanation := .strengtheningFails
  , localSig := .mult
  , globalSig := EntailmentSig.compose .antiAddMult .mult }

/-- K&L (72): adversatives license (DE on a constant perspective). -/
def ex72 : KLDatum :=
  { sentence := "I'm surprised that he ever said anything"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti }

/-- K&L (73): non-adversatives do not license. -/
def ex73 : KLDatum :=
  { sentence := "*I'm sure that I ever met him"
  , grammatical := false
  , explanation := .strengtheningFails
  , localSig := .mono }

/-- K&L (82). -/
def ex82 : KLDatum :=
  { sentence := "I'm sorry that anybody hates me"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti
  , wideningDimension := some "phonologists who hate me vs linguists who hate me" }

/-- K&L (143): conditional antecedent. -/
def ex143 : KLDatum :=
  { sentence := "If John subscribes to any newspaper, he gets well informed"
  , grammatical := true
  , explanation := .byStrengthening
  , localSig := .anti
  , wideningDimension := some "important vs unimportant newspapers" }

def allExamples : List KLDatum :=
  [ex1, ex2, ex10, ex27b, ex55, ex56, ex72, ex73, ex82, ex143]

-- Grammatical strengthening examples have DE local signatures.
#guard allExamples.all λ d =>
  !(d.grammatical && d.explanation == .byStrengthening) ||
    d.localSig.toDEStrength.isSome

-- Ungrammatical examples have non-DE local signatures: strengthening fails
-- locally.
#guard allExamples.all λ d => d.grammatical || d.localSig.toDEStrength.isNone

-- Locality (56): the composed global signature is DE, the local one is not.
#guard ex56.globalSig.toDEStrength.isSome
#guard ex56.localSig.toDEStrength.isNone

end KadmonLandman1993
