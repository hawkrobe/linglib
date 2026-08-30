import Linglib.Semantics.Causation.CauserSort
import Linglib.Semantics.ArgumentStructure.VoiceSemantics
import Linglib.Features.Case.Basic
import Linglib.Fragments.Sinhala.Verbs

/-!
# Anticausatives in Sinhala

Formalization of [beavers-zubair-2013] (NLLT 31). Colloquial Sinhala detransitivizes a
causative root two ways, both formally inchoative: a nominative-subject anticausative
with no external-causer entailment, and an accusative-subject one entailing a distinct
external causer. One operation derives both — causer suppression ((77), p. 37), which
deletes the causer syntactically, preserves CAUSE, and sortally restricts the suppressed
variable to individuals (U_I) — the two subject cases reflecting reflexive vs.
existential resolution of that variable ((78), p. 38). The U_I restriction is the
predictive engine: roots selecting event-sort causers (*minimarann* 'murder', *kapann*
'cut') fail the operator's well-formedness condition, so they do not anticausativize;
and since the volitive ((71), p. 35) demands an event-sort subject while suppression
outputs an individual, anticausatives are obligatorily involitive
(`Causation.CauserSort.not_admitsVolitive_individual`).

The operator is `ArgumentStructure.VoiceSemantics.causerSuppress`; the sort lattice is
`Causation.CauserSort` ((81), p. 40); the verbs are `Fragments/Sinhala/Verbs`. §6
rejects [koontz-garboden-2009]'s reflexivization-only analysis because the accusative
variant's causer is not coidentified with the patient; §4.2 rejects deletion analyses
([grimshaw-1982], [reinhart-2002], [haertl-2003], [bohnemeyer-2007]) on
[koontz-garboden-2009]'s Monotonicity-Hypothesis argument and the *ibeem* 'by itself'
facts. The accusative-as-semantic-case analysis follows [beavers-zubair-2010].

## Main definitions

* `Reading`, `Reading.resolve` — the two resolutions of the suppressed causer, as
  denotations over `causerSuppress`.
* `caseOfReading` — the §7.3 semantic-case convention: accusative signals existential
  resolution.
* `anticausativizes` — the operator's well-formedness condition, read off the verb's
  `CauserSort`.

## Main results

* `causative_entails_existential`, `reflexive_entails_existential` — inchoatives are
  true in agentive contexts ((51)), so the volitive ban is formal, not
  truth-conditional (§5.3).
* `ibeem_incompatible_with_external` — the 'by itself' diagnostic excludes the
  accusative variant ((58)).
* `drown_anticausativizes`, `murder_no_anticausative` — the U_I engine on the
  fragment: the *murder*-class gap is a type-checking failure, not a stipulated
  exception.

## References

* [beavers-zubair-2013] — the paper; [beavers-zubair-2010] — the semantic-case and
  involitive-meaning groundwork.
* [koontz-garboden-2009], [chierchia-2004], [levin-hovav-1995] — the reflexivization
  and existential-binding analyses the paper unifies.
* [grimshaw-1982], [reinhart-2002], [haertl-2003], [bohnemeyer-2007] — deletion
  analyses rejected in §4.2.
* [inman-1993], [henadeerage-2002], [gair-paolillo-1997] — the Sinhala sources.
-/

namespace BeaversZubair2013

open Causation
open Sinhala.Verbs
open ArgumentStructure.VoiceSemantics
open Intensional

/-! ### The two resolutions of the suppressed causer -/

/-- The two readings of an anticausativized verb ((78), p. 38): the suppressed causer
    is coindexed with the patient, or existentially closed. -/
inductive Reading where
  | reflexive
  | existential
  deriving DecidableEq, Repr

/-- A reading's denotation: `causerSuppress` leaves the causer as an open variable;
    reflexive resolution binds it to the patient, existential resolution closes it.
    The verb is causer-first (`vp x y`: causer `x`, patient `y`). -/
def Reading.resolve {E W : Type} {s : CauserSort} (r : Reading)
    (h : s.admitsIndividual) (vp : Denot E W (.e ⇒ .e ⇒ .t)) :
    Denot E W (.e ⇒ .t) :=
  match r with
  | .reflexive   => fun y => causerSuppress s h y vp y
  | .existential => fun y => ∃ x, causerSuppress s h x vp y

/-- Case ↔ resolution (§7.3): Sinhala accusative is a semantic case marking a patient
    caused by a distinct external agent ([beavers-zubair-2010]), so it surfaces only
    under existential resolution; nominative is the elsewhere case. Accusative is
    animacy-conditioned and optional (fn. 27), so the converse is not stated. -/
def caseOfReading : Reading → Case
  | .reflexive   => .nom
  | .existential => .acc

/-- Any causative claim entails the existentially-resolved inchoative: inchoatives are
    true in agentive contexts ((51), §5.3), so the ban on volitive inchoatives must be
    formal rather than truth-conditional. -/
theorem causative_entails_existential {E W : Type} {s : CauserSort}
    (h : s.admitsIndividual) (vp : Denot E W (.e ⇒ .e ⇒ .t)) (x y : E)
    (hxy : vp x y) : Reading.existential.resolve h vp y :=
  ⟨x, hxy⟩

/-- The reflexive resolution entails the existential one: (78a) supplies the patient
    itself as witness for (78b). -/
theorem reflexive_entails_existential {E W : Type} {s : CauserSort}
    (h : s.admitsIndividual) (vp : Denot E W (.e ⇒ .e ⇒ .t)) (y : E)
    (hy : Reading.reflexive.resolve h vp y) : Reading.existential.resolve h vp y :=
  ⟨y, hy⟩

/-- The *ibeem* 'by itself' diagnostic ((58)): no-external-causation contradicts the
    accusative's distinct-external-causer requirement — accusative-subject
    anticausatives reject *ibeem*; nominative ones accept it. -/
theorem ibeem_incompatible_with_external {E : Type} (vp : E → E → Prop) (y : E) :
    ¬ ((∀ x, vp x y → x = y) ∧ ∃ x, x ≠ y ∧ vp x y) :=
  fun ⟨hno, _, hne, hvp⟩ => hne (hno _ hvp)

/-! ### The predictive engine -/

/-- A verb anticausativizes iff its causer sort admits individuals — the
    well-formedness condition of the suppression operator ((77)). The operator is
    partial: `CauserSort.admitsIndividual_iff` confines it to `individual` and `any`. -/
def anticausativizes (v : SinhalaVerb) : Prop :=
  v.causerSort.admitsIndividual

instance (v : SinhalaVerb) : Decidable (anticausativizes v) :=
  inferInstanceAs (Decidable v.causerSort.admitsIndividual)

/-- *kadann* 'break' anticausativizes (causer sort `any`, (76)). -/
theorem break_anticausativizes : anticausativizes kadann := by decide

/-- *gilann* 'drown' anticausativizes (exx. (2)–(3)). -/
theorem drown_anticausativizes : anticausativizes gilann := by decide

/-- *minimarann* 'murder' does not anticausativize: its event-sort causer ((65b)) is
    incompatible with U_I, so `causerSuppress` cannot even be instantiated at this
    verb. -/
theorem murder_no_anticausative : ¬ anticausativizes minimarann := by decide

/-- *kapann* 'cut' patterns with *minimarann*. -/
theorem cut_no_anticausative : ¬ anticausativizes kapann := by decide

/-- The volitive ((71)) admits both *minimarann* and *kadann* — their causer sorts
    include events. After suppression the surviving subject is an individual, which
    `CauserSort.not_admitsVolitive_individual` bars from the volitive: anticausatives
    are always involitive (§8). -/
theorem volitive_admitted :
    CauserSort.admitsVolitive minimarann.causerSort ∧
      CauserSort.admitsVolitive kadann.causerSort := by
  decide

/-- The operator instantiates for *kadann*: the `decide`-discharged obligation is the
    predictive engine at work. -/
example {E W : Type} (z : E) (vp : Denot E W (.e ⇒ .t)) : Denot E W .t :=
  causerSuppress kadann.causerSort (by decide) z vp

end BeaversZubair2013
