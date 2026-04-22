import Linglib.Theories.Semantics.Causation.CauserSort
import Linglib.Theories.Interfaces.SyntaxSemantics.VoiceSemantics
import Linglib.Core.Case.Basic
import Linglib.Fragments.Sinhala.Verbs

/-!
# @cite{beavers-zubair-2013} Anticausatives in Sinhala

Beavers, John and Cala Zubair. 2013. Anticausatives in Sinhala:
involitivity and causer suppression. *Natural Language and Linguistic
Theory* 31:1–46.

## Empirical core

Colloquial Sinhala has two ways to detransitivize a causative root,
both formally inchoative (no syntactically active causer):

- **Nominative subject**: pure anticausative, no entailed external
  causer. *Nimal giluna* 'Nimal drowned'.
- **Accusative subject**: still inchoative, but entails an external
  causer (passive-like reading). *Nimal-wə giluna* 'Nimal was drowned
  (by someone)'.

The same root that supports both forms (*gilann/gilenn* 'drown')
also has a volitive transitive (*Aruni Nimal-wə giluwa* 'Aruni
drowned Nimal deliberately') and an involitive transitive (*Aruni
atiŋ Nimal-wə giluna* 'Aruni accidentally drowned Nimal'). Roots
that select for an event-sort causer (*minimarann* 'murder',
*kapann* 'cut') have *no* involitive form and do not anticausativize.

## Theoretical contribution

The single mechanism — *causer suppression* — derives all four
patterns. The operator (their ex. (77), p. 37) is:

    ⟦+∅_CS⟧ = λPλyλe[P(y, x, e) ∧ x ∈ U_I]

It (a) deletes the causer syntactically, (b) preserves CAUSE
semantically, and (c) sortally restricts the suppressed causer to
individuals (U_I). The free variable `x` must be bound externally,
yielding two readings (their ex. (78), p. 38):

- **Reflexive coindexation** with the patient `y` → nominative subject
- **Existential closure** of `x` → accusative subject (passive-like)

The U_I restriction is the predictive engine: roots whose causer
sort is `event` or `eventuality` cannot anticausativize because
the suppression operator's required sort is incompatible with the
verb's selectional restriction. This blocks *minimarann* 'murder'
and *kapann* 'cut' from anticausativizing — a structural
type-checking failure rather than a stipulated lexical exception.

The volitive stem (their ex. (71), p. 35) is itself a typed operator:
`⟦+∅_vol⟧ = λP...λv ∈ U_E λe[P(...,v,e)]`. It requires the
penultimate argument to resolve to an event. After causer
suppression, the surviving subject is sortally `individual` — so
the volitive cannot apply. This derives the cross-cutting fact
that anticausativized roots are always involitive.

## Engagement with sibling analyses

B&Z 2013 §6 explicitly rejects @cite{koontz-garboden-2009}'s
reflexivization analysis on the grounds that it predicts the
inchoative is true only when the causer is identified with the
patient — but Sinhala's accusative-subject anticausative entails an
external causer *distinct* from the patient (B&Z §7.3). Causer
suppression admits this reading via existential closure of the
suppressed variable; reflexivization cannot. The empirical content
is captured by the `causerSuppress` operator (in `VoiceSemantics`)
plus the U_I sortal restriction and the binding-mode disjunction in
`Reading` below.

B&Z 2013 also rejects deletion analyses (@cite{krejci-2012},
@cite{bohnemeyer-2004}, Grimshaw 1982) on Monotonicity-Hypothesis
grounds: causer suppression preserves CAUSE in the LSR (the *ibeem*
'by-itself' diagnostic licenses anticausatives, requiring CAUSE),
while deletion does not. The `causerSuppress_eq_suppressArg`
factor-through theorem in `VoiceSemantics` makes the
truth-conditional content of the operator explicit.

The natural next engagement target is @cite{alexiadou-schaefer-2015}'s
featural Voice typology, which B&Z 2013 contrast against (their fn
around (71)).
-/

namespace BeaversZubair2013

open Semantics.Causation
open Fragments.Sinhala.Verbs

-- ════════════════════════════════════════════════════
-- § 1. The Causer Suppression Operator (ex. 77)
-- ════════════════════════════════════════════════════

/-- The two readings of an anticausativized verb (B&Z's ex. (78),
    p. 38). Both have the patient as surface subject; they differ in
    how the suppressed causer variable is bound. -/
inductive Reading where
  /-- (78a): the suppressed causer `x` is coindexed with the patient
      `y` (formally bound by the same λ). Single argument is both
      causer and patient. Nominative subject. -/
  | reflexive
  /-- (78b): the suppressed causer `x` is existentially closed.
      Causer is distinct from patient. Accusative subject (the
      external causer is "marked" via case). -/
  | existential
  deriving DecidableEq, Repr

/-- Case ↔ binding-mode bridge (B&Z 2013 §7.3): accusative case on
    the surface subject of an anticausative *signals* that the
    suppressed causer was bound existentially (not coindexed with
    the patient). Re-uses `Core.Case` (= `UD.Case`) — the canonical
    cross-linguistic case type — rather than introducing a local
    nom/acc enum.

    **Caveat (B&Z fn 27, fn 29)**: accusative case is animacy-conditioned
    and *optional* on animates; it is rare-to-impossible on inanimate
    patients. So existential binding can surface as nominative when
    the patient is inanimate. The bidirectional reading below holds
    only on animate patients with overt accusative; the broader
    empirical picture requires an animacy parameter that we do not
    formalize here. -/
def caseOfReading : Reading → Core.Case
  | .reflexive   => .nom
  | .existential => .acc

/-- One direction (B&Z's strong claim): accusative on the surface
    subject of an anticausative entails existential binding (i.e.,
    a distinct external causer). The converse is animacy-conditioned
    and is therefore not stated here. -/
theorem accusative_implies_existential :
    ∀ r : Reading, caseOfReading r = .acc → r = .existential := by
  intro r; cases r <;> simp [caseOfReading]

/-- The other strong direction: reflexive binding always surfaces
    as nominative (no accusative-marked reflexive anticausatives). -/
theorem reflexive_implies_nominative :
    ∀ r : Reading, r = .reflexive → caseOfReading r = .nom := by
  intro r h; subst h; rfl

-- ════════════════════════════════════════════════════
-- § 2. The Predictive Engine (ex. 77 + ex. 71)
-- ════════════════════════════════════════════════════

/-- A verb anticausativizes iff its causer sort admits individuals.
    This delegates to the canonical `CauserSort.admitsIndividual`
    predicate, which is the type-level encoding of B&Z's
    well-formedness constraint on the suppression operator (ex. 77).

    "Well-formedness" rather than "predicate over verbs" is the right
    framing: the operator is *partial*, defined only when the verb's
    causer sort is compatible with U_I. The blocking of
    anticausativization on *murder*-type roots is therefore a
    type-checking failure, not a stipulated exception. -/
def anticausativizes (v : SinhalaVerb) : Prop :=
  v.causerSort.admitsIndividual

instance (v : SinhalaVerb) : Decidable (anticausativizes v) :=
  inferInstanceAs (Decidable v.causerSort.admitsIndividual)

/-- *kadann* 'break' anticausativizes (causer sort = `any`). -/
theorem break_anticausativizes : anticausativizes kadann := by decide

/-- *gilann* 'drown' anticausativizes (the canonical example). -/
theorem drown_anticausativizes : anticausativizes gilann := by decide

/-- *minimarann* 'murder' does NOT anticausativize. The U_E causer
    sort is incompatible with U_I — a structural type-checking
    failure of the suppression operator, not a stipulated lexical
    exception. -/
theorem murder_no_anticausative : ¬ anticausativizes minimarann := by decide

/-- *kapann* 'cut' does NOT anticausativize, for the same reason. -/
theorem cut_no_anticausative : ¬ anticausativizes kapann := by decide

/-- The volitive operator (B&Z's ex. (71)) admits a verb iff its
    causer sort includes events. The generic predicate
    `CauserSort.admitsVolitive` and the lattice-level theorem
    `not_admitsVolitive_individual` ("anticausatives are always
    involitive", B&Z §8) live in `Theories/Semantics/Causation/CauserSort.lean`;
    here we just verify the predictions for the Sinhala fragment. -/
theorem volitive_admitted_for_murder :
    CauserSort.admitsVolitive minimarann.causerSort := by decide

theorem volitive_admitted_for_break :
    CauserSort.admitsVolitive kadann.causerSort := by decide

-- ════════════════════════════════════════════════════
-- § 3. Operator-Level Type-Checking (the predictive engine)
-- ════════════════════════════════════════════════════

/-! The `anticausativizes` predicate above is the type
    checker's view of B&Z's prediction. The semantic operator that
    actually does the work — `causerSuppress` from
    `Theories/Interfaces/SyntaxSemantics/VoiceSemantics.lean` — takes
    a `CauserSort` and a *proof* that it admits individuals as a
    parameter. The proof obligation IS the predictive engine: a verb
    that does not anticausativize cannot have its operator
    instantiated.

    The theorems below demonstrate this at the operator level: for
    *kadann* 'break' the operator instantiates with a `decide`-discharged
    obligation; for *minimarann* 'murder' no such proof exists. -/

open Interfaces.SyntaxSemantics.VoiceSemantics

/-- The Sinhala suppression operator can be instantiated for *kadann*
    'break' because its causer sort `.any` admits individuals. The
    obligation is discharged by `decide` over the lattice. -/
example {F : Core.IntensionalLogic.Frame} (z : F.Entity)
    (vp : F.Denot (.e ⇒ .t)) :
    F.Denot .t :=
  causerSuppress kadann.causerSort (by decide) z vp

/-- For *minimarann* 'murder' the obligation `causerSort.admitsIndividual`
    *cannot* be discharged — the lattice fact `¬ admitsIndividual .event`
    blocks the operator at the type-checking level, not by a runtime
    exception. This is the formal content of "anticausativization is a
    structural type-checking failure". -/
theorem murder_cannot_instantiate_operator :
    ¬ minimarann.causerSort.admitsIndividual := by decide

end BeaversZubair2013
