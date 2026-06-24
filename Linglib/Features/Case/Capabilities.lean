import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Case.Basic

/-!
# Case — carrier capabilities
[blake-1994] [corbett-2006]

The typeclass mixin for carriers that bear grammatical case — the case
analogue of `HasPerson` (`Features/Person/Capabilities.lean`). `caseOf`
extracts the carrier's analytical case value; carriers that store UD
realization (`UD.MorphFeatures`) lift through `Case.fromUD`.

`Compatible` is the **case-concord** relation: symmetric, agree-or-wildcard
slot compatibility (NP-internal agreement in case, e.g. Slavic/Latin
adjective–noun). It is *not* case **government/assignment** — the asymmetric,
head-to-dependent relation by which case enters an NP in the first place —
which lives in `Syntax/Case/Dependent.lean` (Marantz dependent case) and
`Syntax/Case/Licensing.lean` (Kalin licensing). Unlike person/number/gender,
case is a *non-canonical* agreement feature ([corbett-2006]): the controller of
case concord is itself the target of some other case relation; Blake's
treatment of case assignment and concord ([blake-1994]) is the typological
anchor.

The carrier is single-valued (`Option Case`), so syncretism (one form
realizing several cases), case-stacking/Suffixaufnahme, and coordinate case
resolution are out of scope — a faithful treatment of those would carry a
`Finset Case` and check nonempty intersection. The present consumer
(`Studies/WechslerZlatic2000.lean`, concord) treats concord case as
single-valued, for which this carrier is adequate.
-/

set_option autoImplicit false

/-- A carrier of grammatical case. `none` = the carrier does not mark
    case. -/
class HasCase (α : Type*) where
  /-- The analytical case value, if marked. -/
  caseOf : α → Option Case

export HasCase (caseOf)

instance : HasCase UD.MorphFeatures :=
  ⟨fun mf => mf.case_.map Case.fromUD⟩

instance : HasCase Case := ⟨some⟩

/-- `Option Case` is the free case-bearer: `some c` bears `c`, `none` is
    caseless. -/
instance : HasCase (Option Case) := ⟨id⟩

namespace HasCase

variable {α β : Type*} [HasCase α] [HasCase β]

/-- Two carriers are case-compatible: the slot values are compatible in
    the flat information order (`Compat`) — if both mark case, the values
    agree; unmarked carriers are wildcards. The concord-checking
    relation. -/
abbrev Compatible (a : α) (b : β) : Prop :=
  Compat (α := Flat Case) (caseOf a) (caseOf b)

end HasCase

/-- φ-compatibility entails case compatibility: the `HasCase` mixin
    never diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`) — the case analogue of
    `UD.MorphFeatures.compatible_hasPerson`. -/
theorem UD.MorphFeatures.compatible_hasCase {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasCase.Compatible f1 f2 :=
  Features.compat_of_clause_map Case.fromUD (UD.MorphFeatures.compatible_case h)
