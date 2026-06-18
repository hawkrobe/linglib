import Linglib.Core.Order.Relation
import Linglib.Syntax.Clause.Basic
import Linglib.Semantics.Tense.Reichenbach

/-!
# Sequence of tense: the cross-cutting licensing interface
[kauf-zeijlstra-2018] [ogihara-2019] [egressy-2026]

Past-under-past embeddings have a simultaneous and a backward-shifted reading
(and, with an intervening future, a forward-shifted one). Rival accounts —
relational/feature ([kauf-zeijlstra-2018]), deletion ([ogihara-2019]), res-movement
de re, clause-size ([egressy-2026]) — disagree only about *when each reading is
licensed*, not about what a reading is. This file is the seam.

## What a reading is (no enum)

A reading is which comparison atom the embedded reference time bears to its
anchor. `Tense.embeddedFrame` puts the anchor at the matrix event time, so the
three readings are exactly the overhaul's frame predicates: `.lt`/`isPast` =
back-shifted, `.eq`/`isPresent` = simultaneous, `.gt`/`isFuture` = forward.

## What a theory provides

A theory is one `LocalLicense` — a relation reading, off an immediately
containing clause and the clause it contains, which atoms are licensed. Both
syntactic and semantic theories emit the same `Finset Ordering`, so they are
peers; `profile` folds the relation **pairwise** along the c-command chain
(adjacency-local, so an intervening tense re-anchors). Clause size enters only
through the **framework-neutral** `Clause.Size` (`Syntax/Clause`), never
`Minimalist` machinery.

Double-access (a two-anchor present) and modal-base orientation (Klecha) do not
fit one cell against one anchor; they are deliberately *out* of this interface
and handled by separate substrate.
-/

namespace SequenceOfTense

open Core.Order

/-- A node in an embedding chain: a clause's morphological tense as a relative
    comparison cell (past = `notAfter`, the ≤ of [kauf-zeijlstra-2018]) and its
    framework-neutral `Clause.Size`. Not a `Minimalist.ComplementSize` — a
    Minimalist clause *provides* its size via `ComplementSize.toClauseSize`. -/
structure Node where
  /-- The clause's tense as a relative comparison cell to its anchor. -/
  tense : Finset Ordering
  /-- The clause's framework-neutral size (`Clause.Size`). -/
  size  : Clause.Size

/-- The cross-cutting interface: given a containing clause and the clause it
    immediately contains, which comparison atoms hold between the contained
    reference time and its anchor. A theory **is** a value of this type. -/
abbrev LocalLicense := Node → Node → Finset Ordering

/-- Compose a license pairwise along the c-command chain (matrix first): the
    licensed reading-set at each embedding level. Adjacency-local — not a fold
    or product — so an intervening tense re-anchors and blocking propagates
    ([ogihara-1996]'s past-under-*will*-under-past). -/
def profile (L : LocalLicense) : Node → List Node → List (Finset Ordering)
  | _, []        => []
  | a, c :: rest => L a c :: profile L c rest

/-! ### Reading availability (the atoms — no `Reading` enum) -/

/-- The simultaneous reading is licensed iff the `eq` atom is. -/
def Simultaneous   (s : Finset Ordering) : Prop := Ordering.eq ∈ s
/-- The backward-shifted reading is licensed iff the `lt` atom is. -/
def Backshifted    (s : Finset Ordering) : Prop := Ordering.lt ∈ s
/-- The forward-shifted reading is licensed iff the `gt` atom is. -/
def ForwardShifted (s : Finset Ordering) : Prop := Ordering.gt ∈ s

instance (s : Finset Ordering) : Decidable (Simultaneous s) :=
  inferInstanceAs (Decidable (Ordering.eq ∈ s))
instance (s : Finset Ordering) : Decidable (Backshifted s) :=
  inferInstanceAs (Decidable (Ordering.lt ∈ s))
instance (s : Finset Ordering) : Decidable (ForwardShifted s) :=
  inferInstanceAs (Decidable (Ordering.gt ∈ s))

/-! ### Realization: the atoms are the overhaul's frame predicates

For an embedded frame whose perspective time is the matrix event time
(`Tense.embeddedFrame`), the licensed atom is its `R`-vs-`P` comparison, and the
three named readings are exactly `ReichenbachFrame.isPast/isPresent/isFuture`. -/

variable {T : Type*} [LinearOrder T]

theorem isPast_iff_atom (f : Time.ReichenbachFrame T) :
    f.isPast ↔ compare f.referenceTime f.perspectiveTime = Ordering.lt := by
  simp [Time.ReichenbachFrame.isPast, holds, Tense.past, before]

theorem isPresent_iff_atom (f : Time.ReichenbachFrame T) :
    f.isPresent ↔ compare f.referenceTime f.perspectiveTime = Ordering.eq := by
  simp [Time.ReichenbachFrame.isPresent]

theorem isFuture_iff_atom (f : Time.ReichenbachFrame T) :
    f.isFuture ↔ compare f.referenceTime f.perspectiveTime = Ordering.gt := by
  simp [Time.ReichenbachFrame.isFuture, holds, Tense.future, after]

/-! ### License schemas

Reusable `LocalLicense` constructors that the rival accounts instantiate. The
*specific* boundary (e.g. Egressy's `Say`) is a study's commitment; the schemas
are shared. -/

/-- Relational schema ([kauf-zeijlstra-2018]): the clause's own relative tense,
    size-blind. Past = `notAfter` (≤) yields `{lt, eq}` = back-shift ∨ sim. -/
def relationalLicense : LocalLicense := fun _ c => c.tense

/-- Generic *size gate*: an opaque clause (size not below `boundary`) loses the
    simultaneous (`eq`) atom; a transparent one keeps the full relative tense.
    This is the size half of a clause-size SOT account; it is **not** by itself
    the [egressy-2026] license, which also requires an agreeing past (see
    `LocalLicense.gate` and `Studies.Egressy2026`). On uniformly past-under-past
    data the two coincide; they diverge once an intervening future appears. -/
def sizeGatedLicense (boundary : Clause.Size) : LocalLicense :=
  fun _ c => if Clause.transparentTo c.size boundary then c.tense else c.tense.erase .eq

/-- Refine a license by an extra gate: keep its reading set, but drop the
    simultaneous atom `.eq` wherever the gate fails. A theory composes its
    licensing conditions as successive gates — the SOT rule is a size gate
    refined by an agreeing-past gate, i.e. `(sizeGatedLicense b).gate agreeingPast`. -/
def LocalLicense.gate (L : LocalLicense) (g : Node → Node → Bool) : LocalLicense :=
  fun a c => if g a c then L a c else (L a c).erase Ordering.eq

/-! ### Pragmatic narrowing (layer 2: a constraint on the grammatical reading set)

Grammar (a `LocalLicense`) emits the *grammatically available* reading set; a
pragmatic inference then *narrows* it — direct perception (one cannot perceive a
past event), a cessation implicature (a past stative implicates non-overlap with
now), etc. A narrowing is **intersection with a context-conditioned constraint**
(a further point-algebra relation), so it can only *remove* readings, never
license a new one — the grammar/pragmatics boundary, free from
`Finset.inter_subset_left` rather than a stipulated law. The context `C` is
whatever the inference consults (polarity, perception-directness, …). -/

/-- A pragmatic narrowing: the point-algebra constraint it imposes, as a function
    of the context the inference consults. -/
abbrev Narrowing (C : Type*) := C → Finset Ordering

/-- Narrow a grammatically-licensed reading set: intersect with the constraint. -/
def Narrowing.apply {C : Type*} (n : Narrowing C) (ctx : C) (s : Finset Ordering) :
    Finset Ordering := s ∩ n ctx

/-- Pragmatics filters, never licenses: narrowing only removes readings. -/
theorem Narrowing.apply_subset {C : Type*} (n : Narrowing C) (ctx : C)
    (s : Finset Ordering) : n.apply ctx s ⊆ s :=
  Finset.inter_subset_left

/-! ### Worked example: the schemas diverge on an opaque past clause

A concrete demonstration that the interface carries weight: on an opaque past
clause (grade `5`, boundary `5`), the relational schema licenses the simultaneous
reading but the size-gated one does not. -/

/-- A matrix past clause (size below any boundary used here). -/
def exMatrix : Node := ⟨notAfter, 0⟩
/-- An opaque past complement: grade `5`, not below boundary `5`. -/
def exOpaquePast : Node := ⟨notAfter, 5⟩
/-- A transparent past complement: grade `0`, below boundary `5`. -/
def exTransparentPast : Node := ⟨notAfter, 0⟩

example : Simultaneous (relationalLicense exMatrix exOpaquePast) := by decide
example : ¬ Simultaneous (sizeGatedLicense 5 exMatrix exOpaquePast) := by decide

/-- The size-gated profile over a chain `[opaque, transparent]`: the opaque
    level is back-shift only (`before`), the transparent level keeps both
    (`notAfter`). -/
example :
    profile (sizeGatedLicense 5) exMatrix [exOpaquePast, exTransparentPast]
      = [before, notAfter] := by decide

end SequenceOfTense
