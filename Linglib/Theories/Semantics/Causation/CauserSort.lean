import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic.DeriveFintype

/-!
# Causer sort lattice

@cite{beavers-zubair-2013} @cite{levin-hovav-1995}

`CauserSort` is the sortal-type lattice for causers from
@cite{beavers-zubair-2013} ex. (81). Atoms are `event`, `state`,
`individual`; named sorts are `event`, `state`, `eventuality` (=
`event` ⊔ `state`), `individual`, and `any` (top). The order is
subset-on-atoms.

The structure is a `SemilatticeSup` (joins exist for every pair) but
not a `Lattice` — `event ⊓ state` would be the empty Finset, which
has no constructor.

The anticausativization operator (B&Z's ex. (77)) requires the
surviving causer position to resolve to `individual`, which
mechanically blocks roots that select for `event` or `eventuality`
(e.g., *murder*, *destroy*). The volitive operator (their ex. (71))
requires `event`. Both predictions follow from `≤`-checks on the
lattice rather than from stipulated lexical exceptions.
-/

namespace Semantics.Causation

/-- The three irreducible sorts (atoms) a causer position may resolve
    to. Used as the underlying Finset of `CauserSort`; not intended
    as a standalone API. -/
inductive CauserSortAtom where
  | event
  | state
  | individual
  deriving DecidableEq, Repr, Fintype

/-- Sortal type a verb may select for its causer argument
    (@cite{beavers-zubair-2013} ex. (81), p. 40).

    The Hasse diagram:

    ```
              any (U)
             /        \
       eventuality   individual (U_I)
        (U_V)
        /     \
     event   state
     (U_E)   (U_S)
    ```

    Verbs select for the SMALLEST sort their causer must satisfy:

    - `break`-roots (kada-): `any` — no sortal restriction
    - `destroy`-roots: `eventuality` — must be a state or event
    - `murder`-roots (minimara-): `event` — must be an event (forces
      agentivity since events have agents in the relevant sense)

    The causer-suppression operator requires the suppressed causer
    position to resolve to `individual`. Suppression is well-formed
    iff `individual ≤ s` — only `any` and `individual` itself
    satisfy this. -/
inductive CauserSort where
  /-- U_E in B&Z's notation: the causer must be an event. -/
  | event
  /-- U_S: the causer must be a state. **Predicted but not lexically
      attested**: B&Z 2013 fn. 40 (p. 40) note they have not discussed
      verbs lexically selecting a stative causer, suggesting *bloom*-type
      ICOS verbs (cf. @cite{levin-hovav-1995} p. 97) as a possible case
      for future work. Kept as a constructor so the lattice retains the
      structure (81) advertises. -/
  | state
  /-- U_V = U_E ∪ U_S: the causer must be an eventuality. -/
  | eventuality
  /-- U_I: the causer must be an individual. -/
  | individual
  /-- U: no sortal restriction. -/
  | any
  deriving DecidableEq, Repr, Fintype

namespace CauserSort

/-- The Finset of atoms a sort covers. The subsort order is
    `Finset.Subset` pulled back through this map. -/
def toAtoms : CauserSort → Finset CauserSortAtom
  | event       => {CauserSortAtom.event}
  | state       => {CauserSortAtom.state}
  | eventuality => {CauserSortAtom.event, CauserSortAtom.state}
  | individual  => {CauserSortAtom.individual}
  | any         => {CauserSortAtom.event, CauserSortAtom.state,
                    CauserSortAtom.individual}

instance : LE CauserSort := ⟨fun s t => s.toAtoms ⊆ t.toAtoms⟩

instance : DecidableRel (α := CauserSort) (· ≤ ·) := fun s t =>
  inferInstanceAs (Decidable (s.toAtoms ⊆ t.toAtoms))

instance : PartialOrder CauserSort where
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm s t hst hts := by
    have h : s.toAtoms = t.toAtoms := Finset.Subset.antisymm hst hts
    revert h; cases s <;> cases t <;> decide

/-- Join: the smallest named sort whose atoms include both inputs.
    Each case is a specific (s, t) pair; no overlapping wildcards. -/
def sup : CauserSort → CauserSort → CauserSort
  -- top absorbs everything
  | any, _ | _, any => any
  -- individual is incomparable with eventuality-shaped sorts;
  -- joining individual with any of those collapses to top
  | individual, individual => individual
  | individual, event       | event,       individual => any
  | individual, state       | state,       individual => any
  | individual, eventuality | eventuality, individual => any
  -- joins among eventuality-shaped sorts
  | event,       event       => event
  | state,       state       => state
  | eventuality, eventuality => eventuality
  | event,       state       | state,       event       => eventuality
  | event,       eventuality | eventuality, event       => eventuality
  | state,       eventuality | eventuality, state       => eventuality

instance : Max CauserSort := ⟨sup⟩

instance : SemilatticeSup CauserSort where
  sup := sup
  le_sup_left  a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide

/-- The well-formedness condition for the B&Z 2013 causer-suppression
    operator (their ex. (77)): the suppressed causer position resolves
    to `individual`, so the verb's selected sort must admit
    `individual` values.

    This is the *predictive engine* of B&Z 2013: the lattice structure
    determines which roots anticausativize, by structural type-checking
    rather than by stipulation. -/
abbrev admitsIndividual (s : CauserSort) : Prop := individual ≤ s

/-- The well-formedness condition for B&Z's volitive operator (their
    ex. (71), p. 35): `⟦+∅_vol⟧ = λP...λv ∈ U_E λe[...]` requires the
    penultimate argument to be an event. After causer suppression the
    surviving subject is sortally `individual`, so the volitive cannot
    apply — the formal content of "anticausatives are always
    involitive" (@cite{beavers-zubair-2013} §8). -/
abbrev admitsVolitive (s : CauserSort) : Prop := event ≤ s

end CauserSort

end Semantics.Causation
