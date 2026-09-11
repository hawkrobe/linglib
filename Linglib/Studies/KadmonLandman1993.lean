import Linglib.Logic.Natural.Basic
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Polarity.Item
import Linglib.Logic.Natural.Strawson.Basic
import Linglib.Semantics.Supervaluation
import Linglib.Studies.Ladusaw1979
import Linglib.Data.Examples.KadmonLandman1993
import Mathlib.Data.Set.Basic

/-!
# Kadmon and Landman (1993): Any

This file formalizes [kadmon-landman-1993], the unified analysis of *any*: *any CN* is the
indefinite *a CN* with its domain widened along a contextual dimension, licensed only when the
widening makes the statement stronger, the strengthening condition, checked at the narrowest
operator over the indefinite, locality; free-choice *any* is the same item under a generic
interpretation. Widening weakens an existential (`existsInDomain_mono`), so strengthening holds
exactly under an antitone context (`Strengthening`, `de_satisfies_strengthening`), which is why
[ladusaw-1979]'s downward-entailing contexts license and why a positive context does not
(`ue_widening_weakens`); a context's mechanism and signature are read from the substrate's
`LicensingContext.properties` (`klExplanation`, `ladusaw_de_is_kl_strengthening`). Section 3
handles the recalcitrant cases: adversatives are downward entailing with the perspective held
constant, so *sorry* licenses and *glad* does not (`sorry_licenses_any`, `glad_does_not_license`)
except on a settle-for-less reading; a negated *because*-clause licenses only by a
metalinguistic denial of its presupposition; and conditional antecedents strengthen once the
implicit restriction is fixed (`widening_satisfies_conditional_strengthening`). The paper's
judgments follow this classification row by row (`rows_agree`). Section 4 models the generic
restriction as a vague property set (`VagueRestriction`): widening along a dimension makes the
quantifier universal with respect to it (`any_cn_dimensionally_universal`), domain vagueness is
what lets a generic tolerate exceptions (`domain_vague_allows_exceptions`), and *almost* modifies
domain-precise universals and dimensionally universal noun phrases (`almost_rows`). On a finite
precisification space the two truth notions are [fine-1975]'s super-truth and borderline status
(`genericSubTrue_not_superTrue_iff_indet`).

## Implementation notes

* The rows record, at the narrowest operator over *any*, a substrate `LicensingContext` where
  one exists and otherwise the local entailment signature; the settle-for-less and metalinguistic
  readings are the paper's own annotations, so `rows_agree` checks the paper's classification
  against its judgments rather than deriving those two readings.
* The vague-restriction apparatus is `Set`-based; the supervaluation substrate is `Finset`-based
  for computability, and `VagueRestriction.toSpecSpace` is the finite-case bridge.

## References

* [kadmon-landman-1993]
* [ladusaw-1979]
* [linebarger-1987]
* [fine-1975]
-/

namespace KadmonLandman1993

open NaturalLogic Polarity Ladusaw1979 Semantics.Supervaluation Data.Examples

/-! ### The strengthening condition

K&L's component (C): *any* is licensed only if widening creates a stronger
statement. For a context `C` and domains `D ⊆ D'`, the wide interpretation
must entail the narrow: `C (∃x∈D', Px) ⊆ C (∃x∈D, Px)`. This holds exactly
when `C` is antitone, which is why DE contexts license — and why widening in
UE contexts, where it weakens, leaves *any* unlicensed. -/

/-- The existential over a domain: `∃ x ∈ D, P x`. -/
def existsInDomain {World Entity : Type*} (D : Set Entity) (P : Entity → Set World) :
    Set World :=
  λ w => ∃ x ∈ D, P x w

/-- Widening the domain weakens the existential. -/
theorem existsInDomain_mono {World Entity : Type*} {D D' : Set Entity} (P : Entity → Set World)
    (h : D ⊆ D') : existsInDomain D P ⊆ existsInDomain D' P :=
  λ _ ⟨x, hx, hP⟩ => ⟨x, h hx, hP⟩

/-- K&L's strengthening condition: widening the domain `D` to `D'` in context
`C` creates a stronger statement — the wide interpretation entails the narrow
one. -/
def Strengthening {World Entity : Type*} (C : Set World → Set World) (D D' : Set Entity)
    (P : Entity → Set World) : Prop :=
  C (existsInDomain D' P) ⊆ C (existsInDomain D P)

/-- In a DE (antitone) context, strengthening is automatic. K&L note that for
many examples this makes the same predictions as [ladusaw-1979], while
explaining *why* DE contexts license: widening must strengthen, and DE
reverses entailment. -/
theorem de_satisfies_strengthening {World Entity : Type*} {C : Set World → Set World}
    (hDE : Antitone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : Strengthening C D D' P :=
  hDE (existsInDomain_mono P hD)

/-- In a UE (monotone) context, widening *weakens* — the opposite of
strengthening. This is K&L's explanation for why *any* is out in plain
positive contexts. -/
theorem ue_widening_weakens {World Entity : Type*} {C : Set World → Set World}
    (hUE : Monotone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : C (existsInDomain D P) ⊆ C (existsInDomain D' P) :=
  hUE (existsInDomain_mono P hD)

/-! ### Licensing contexts and entailment signatures

Each context's entailment signature and licensing mechanism are projected
from the canonical `Polarity.LicensingContext.properties` table, so
this file's classification cannot drift from the substrate's. -/

/-- A licensing context's entailment signature in [icard-2012]'s lattice —
the Strawson-operative row, matching K&L's own convention of checking the
DE pattern modulo factive presuppositions. -/
abbrev contextSignature (c : LicensingContext) : Signature :=
  c.properties.strawsonSignature

/-- A context guarantees K&L strengthening iff its entailment signature is on
the DE side. Contexts with `.mono` or higher signatures are licensed by other
routes: K&L defer questions to [kadmon-landman-1990] and never discuss
superlatives — the Strawson-DE route for the latter is later literature
([von-fintel-1999]). -/
abbrev GuaranteesStrengthening (c : LicensingContext) : Prop :=
  (contextSignature c).toDEStrength.isSome = true

/-- A licensing context's K&L mechanism, projected from `LicensingContext.properties`:
*why* the context licenses, not merely *that* it does. -/
abbrev klExplanation (c : LicensingContext) : LicensingMechanism :=
  c.properties.mechanism

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
`sorryFull_isStrawsonDE`; consumed by `VonFintel1999`'s
cross-framework bridge. -/
theorem sorry_licenses_any (dox bestOf : Fin 4 → Set (Fin 4)) :
    IsStrawsonDE (sorryFull dox bestOf) (λ p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-- *Sorry* is not classically DE: the doxastic factivity presupposition
blocks it. K&L adopt Ladusaw's convention that the DE pattern need only hold
of the sentence minus its factive presupposition. -/
theorem sorry_not_classically_de :
    ¬Antitone
      (sorryFull (λ (w : Fin 4) => ({w} : Set (Fin 4)))
                 (λ (_ : Fin 4) => ({1} : Set (Fin 4)))) :=
  sorryFull_not_de

/-- *Glad* does not freely license NPIs: it is UE, so widening weakens.
K&L: wanting a set to have members does not entail wanting each particular
subset to have members. -/
theorem glad_does_not_license (dox bestOf : Fin 4 → Set (Fin 4)) :
    Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

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
    Antitone (λ α => condNecessity domain α β) :=
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
[NP_]` is DE and licenses *any* freely — (122)/(123) need no negative
implication. In `because [S_]`, *any* is licensed only metalinguistically:
the negation denies *because*'s factive presupposition, and *any* strengthens
that denial. Merely implying the denial is not enough — the rhetorical
conditional (132) can imply it but lacks the metalinguistic denial, and *any*
is out. This is the paper's only genuinely non-DE licensing mechanism. -/

/-! ### FC *any* as generic indefinite

K&L's component (FC): PS *any* is a regular indefinite, FC *any* a generic
indefinite; the apparent universal force of FC *any* emerges from genericity
plus widening (§4.3). The episodic/generic split below is projected from the
substrate's mechanism classification. K&L themselves analyze only plain
generics like (10) and tentatively extend to modals; routing
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
"An owl hunts mice" is ∀ ↾ X_owl(Owl)(Hunts mice), (159). The
traditional GEN operator's hidden normalcy parameter
(`Semantics/Genericity/Generics.lean`) is, on this view, a choice of
precisification; exception tolerance is the freedom to choose another. -/

/-- Trivalent under one precisification: every entity in the induced domain
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
      superTrue (genericTrue apply scope) (X.toSpecSpace V hV) = Trivalent.true := by
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
      superTrue (genericTrue apply scope) (X.toSpecSpace V hV) = Trivalent.indet := by
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

/-- The domain precision of a noun phrase's restriction, Section 4.1.2. -/
inductive DomainPrecision
  | precise
  | vague
  deriving DecidableEq, Repr

/-- An *almost* row: the noun phrase, its precision, whether it is a true universal and whether
it is dimensionally universal, and the judgment. -/
structure AlmostRow where
  precision : DomainPrecision
  universal : Bool
  dimUniversal : Bool
  ok : Bool
  deriving DecidableEq

/-- An *almost* row from the paper's features. -/
def AlmostRow.ofExample (e : LinguisticExample) : Option AlmostRow := do
  let p ← match e.feature? "precision" with
    | some "precise" => some DomainPrecision.precise
    | some "vague" => some DomainPrecision.vague
    | _ => none
  let u ← e.feature? "universal"
  let d ← e.feature? "dimensionally_universal"
  some ⟨p, u == "yes", d == "yes", e.judgment = .acceptable⟩

/-- The *almost* data of Section 4.3. -/
def almostRows : List AlmostRow := Examples.all.filterMap AlmostRow.ofExample

/-- *Almost* modifies a domain-precise true universal or a dimensionally universal noun phrase:
*every owl*, *no owl* and *any owl*, but not *some owl* nor generic *an owl*. -/
theorem almost_rows :
    ∀ r ∈ almostRows, r.ok = true ↔ (r.universal = true ∧ r.precision = .precise) ∨
      r.dimUniversal = true := by
  decide

/-! ### The licensing data -/

/-- A licensing row: the context at the narrowest operator over *any*, a substrate
`LicensingContext` or a local entailment signature, the settle-for-less and
metalinguistic-denial readings, and the judgment. -/
structure Row where
  context : Option LicensingContext
  localSignature : Signature
  settleForLess : Bool
  metalinguistic : Bool
  grammatical : Bool

/-- The signature at the narrowest operator: the context's Strawson signature where a context
exists, else the local one. -/
def Row.signature (r : Row) : Signature :=
  match r.context with
  | some c => contextSignature c
  | none => r.localSignature

private def contextOf : String → Option LicensingContext
  | "negation" => some .negation
  | "generic" => some .generic
  | "universalRestrictor" => some .universalRestrictor
  | "adversative" => some .adversative
  | "conditionalAntecedent" => some .conditionalAntecedent
  | _ => none

private def signatureOf : String → Option Signature
  | "all" => some .all
  | "mono" => some .mono
  | "anti" => some .anti
  | "mult" => some .mult
  | _ => none

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row :=
  match (e.feature? "context").bind contextOf, (e.feature? "local_signature").bind signatureOf with
  | some c, _ => some ⟨some c, .all, e.feature? "settle_for_less" = some "yes",
      e.feature? "metalinguistic_denial" = some "yes", e.judgment = .acceptable⟩
  | none, some σ => some ⟨none, σ, e.feature? "settle_for_less" = some "yes",
      e.feature? "metalinguistic_denial" = some "yes", e.judgment = .acceptable⟩
  | none, none => none

/-- The licensing data of Sections 1 to 3. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The paper's licensing picture on its own data: *any* is grammatical exactly when the local
context is downward entailing, so widening strengthens, or generic, or read as settling for
less under *glad*, or read as a metalinguistic denial under a negated *because*. -/
theorem rows_agree :
    ∀ r ∈ rows, r.grammatical = true ↔
      r.signature.toDEStrength.isSome = true ∨ r.context = some .generic ∨
        r.settleForLess = true ∨ r.metalinguistic = true := by
  decide

end KadmonLandman1993
