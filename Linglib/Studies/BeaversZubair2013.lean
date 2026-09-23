module

public import Linglib.Semantics.Causation.CauserSort
public import Linglib.Syntax.Case.Basic
public import Linglib.Fragments.Sinhala.Verbs

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

The operator is `causerSuppress`; the sort lattice is
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
* `Root.causerSort` — the causer sort the paper assigns each root.
* `anticausativizes` — the operator's well-formedness condition, read off the root's
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

@[expose] public section

namespace BeaversZubair2013

open Causation
open Sinhala.Verbs

/-! ### Causer suppression -/

/-- Causer suppression ((77), p. 37) saturates the causer argument of `vp` with the open
    variable `z`. It is defined only for a root whose causer sort admits individuals. -/
def causerSuppress {E α : Type} (s : CauserSort) (_h : s.admitsIndividual) (z : E)
    (vp : E → α) : α :=
  vp z

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
def Reading.resolve {E : Type} {s : CauserSort} (r : Reading)
    (h : s.admitsIndividual) (vp : E → E → Prop) :
    E → Prop :=
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
theorem causative_entails_existential {E : Type} {s : CauserSort}
    (h : s.admitsIndividual) (vp : E → E → Prop) (x y : E)
    (hxy : vp x y) : Reading.existential.resolve h vp y :=
  ⟨x, hxy⟩

/-- The reflexive resolution entails the existential one: (78a) supplies the patient
    itself as witness for (78b). -/
theorem reflexive_entails_existential {E : Type} {s : CauserSort}
    (h : s.admitsIndividual) (vp : E → E → Prop) (y : E)
    (hy : Reading.reflexive.resolve h vp y) : Reading.existential.resolve h vp y :=
  ⟨y, hy⟩

/-- The *ibeem* 'by itself' diagnostic ((58)): no-external-causation contradicts the
    accusative's distinct-external-causer requirement — accusative-subject
    anticausatives reject *ibeem*; nominative ones accept it. -/
theorem ibeem_incompatible_with_external {E : Type} (vp : E → E → Prop) (y : E) :
    ¬ ((∀ x, vp x y → x = y) ∧ ∃ x, x ≠ y ∧ vp x y) :=
  fun ⟨hno, _, hne, hvp⟩ => hne (hno _ hvp)

/-! ### The roots and their causer sorts -/

/-- The Sinhala roots the paper analyzes. -/
inductive Root where
  | kada | gila | mara | minimara | kapa | vinaashKara
  deriving DecidableEq, Fintype, Repr

/-- The fragment verb of each root. -/
def Root.verb : Root → SinhalaVerb
  | .kada => kadann
  | .gila => gilann
  | .mara => marann
  | .minimara => minimarann
  | .kapa => kapann
  | .vinaashKara => vinaashKarann

/-- The sort each root's causer must satisfy, a point of the lattice (81), p. 40.
    *minimara-* 'murder' selects an event causer, `[[minimara-]] = λyλv∈U_E λe[...]`
    ((65b)), and *kapa-* 'cut' patterns with it; *kada-* 'break' selects none,
    `[[kada-]] = λyλv∈U λe[...]` ((76)), like the other alternating roots. The eventuality
    sort of (80) is motivated by English and German *destroy*, which do not alternate; the
    Sinhala equivalent does (§7.4), so *vinaash-kara-* selects no sort either. -/
def Root.causerSort : Root → CauserSort
  | .minimara | .kapa => .event
  | .kada | .gila | .mara | .vinaashKara => .any

/-! ### The predictive engine -/

/-- A root anticausativizes iff its causer sort admits individuals — the
    well-formedness condition of the suppression operator ((77)). The operator is
    partial: `CauserSort.admitsIndividual_iff` confines it to `individual` and `any`. -/
def anticausativizes (r : Root) : Prop :=
  r.causerSort.admitsIndividual

instance (r : Root) : Decidable (anticausativizes r) :=
  inferInstanceAs (Decidable r.causerSort.admitsIndividual)

/-- *kada-* 'break' anticausativizes (causer sort `any`, (76)). -/
theorem break_anticausativizes : anticausativizes .kada := by decide

/-- *gila-* 'drown' anticausativizes (exx. (2)–(3)). -/
theorem drown_anticausativizes : anticausativizes .gila := by decide

/-- *minimara-* 'murder' does not anticausativize: its event-sort causer ((65b)) is
    incompatible with U_I, so `causerSuppress` cannot even be instantiated at this
    root. -/
theorem murder_no_anticausative : ¬ anticausativizes .minimara := by decide

/-- *kapa-* 'cut' patterns with *minimara-*. -/
theorem cut_no_anticausative : ¬ anticausativizes .kapa := by decide

/-- The volitive ((71)) admits both *minimara-* and *kada-* — their causer sorts
    include events. After suppression the surviving subject is an individual, which
    `CauserSort.not_admitsVolitive_individual` bars from the volitive: anticausatives
    are always involitive (§8). -/
theorem volitive_admitted :
    Root.minimara.causerSort.admitsVolitive ∧ Root.kada.causerSort.admitsVolitive := by
  decide

/-- The operator instantiates for *kada-*: the `decide`-discharged obligation is the
    predictive engine at work. -/
example {E : Type} (z : E) (vp : E → Prop) : Prop :=
  causerSuppress Root.kada.causerSort (by decide) z vp

/-- Among these roots, those with an involitive stem are exactly those that
    anticausativize. This is a correlation in the data, not a prediction: the involitive is
    the elsewhere form (p. 38), and experiencer verbs such as *dænenn* 'feel' and *ridenn*
    'ache' (around (74)) take individual subjects but have no volitive stem. -/
theorem hasInvolitive_iff_anticausativizes (r : Root) :
    hasInvolitive r.verb ↔ anticausativizes r := by
  cases r <;> decide

end BeaversZubair2013
