import Linglib.Features.Logophoricity
import Linglib.Syntax.Pronoun.Basic
import Linglib.Syntax.Pronoun.Capabilities

/-!
# Logophoric pronouns — the pronominal carrier of perspectival orientation
[sells-1987]

The **pronoun** member of the cross-categorial logophoric series: `LogophoricPronoun` `extends`
the general `Pronoun` (`Syntax/Pronoun/Basic.lean`) with its [sells-1987] orientation — the minimum
perspectival role (`pivot`/`self`/`source`, `Features/Logophoricity.lean`) an antecedent must fill
to license it. Ewe *yè* is one such object: a logophoric pronoun licensed only by a `self` (an
attitude holder); long-distance *zibun* is another, licensed by any `pivot`.

This is *one carrier* of the series, not its home: logophoricity is word-class-neutral (the
`Logophoric` capability and the `LogophoricRole` taxonomy live in `Features/Logophoricity.lean`).
Verbal logophoric marking (Gokana) or a logophoric long-distance reflexive would be sibling
carriers — a different word-class object supplying its own `instance : Logophoric That` — read by the
same `[Logophoric α]` generic code.

The licensing is **orthogonal to `Bound`** (`Syntax/Pronoun/Capabilities.lean`): a form's
perspectival orientation is not its Principle A/B/C role. *zibun* below is a Principle-A reflexive
(`Bound.IsAnaphor`) whose logophoric licensing is nonetheless the *pivot* orientation, not
configurational binding — [sells-1987]'s thesis that logophoric anaphora is role-oriented, made
concrete by carrying both axes on one object (`zibun_anaphor_yet_pivot_oriented`).

## Main declarations

* `LogophoricPronoun` — the lexical object (`extends Pronoun` + `requiredRole`).
* `instance : Logophoric LogophoricPronoun` — the pronoun carrier of the series.
* `Proform` / `Bound` instances routing the object through the Pronoun API.
* `ye`, `zibun` — worked [sells-1987] entries; licensing derived from the hierarchy.
-/

set_option autoImplicit false

open Features.Logophoricity (LogophoricRole Logophoric)

/-- A single logophoric pronoun — the general `Pronoun` (surface `form` + φ-features) plus its
    [sells-1987] orientation: the minimum perspectival role an antecedent must fill to license it
    (`self` for a logophoric pronoun proper, `pivot` for a long-distance reflexive). Carries no
    denotation of its own; its perspectival anchor is the `LogophoricRole` an embedding context's
    shift makes available (cf. `Core/Context/Shifts.lean`'s `attitudeShift`/`perspectiveShift`). -/
structure LogophoricPronoun extends Pronoun where
  /-- The minimum [sells-1987] role an antecedent must fill to license this form. -/
  requiredRole : LogophoricRole
  deriving Repr, DecidableEq

/-- A logophoric pronoun is a `Proform` (form + φ via its `Pronoun` core). -/
instance : Proform LogophoricPronoun :=
  ⟨fun p => p.toPronoun.form, fun p => p.toPronoun.toWord.phi⟩

/-- Its binding class is the `Pronoun` core's, defaulting an undeclared shell to `.pronoun` —
    independent of its logophoric orientation. -/
instance : Bound LogophoricPronoun :=
  ⟨fun p => p.toPronoun.bindingClass.getD .pronoun⟩

/-- The logophoric pronoun is a carrier of the word-class-neutral `Logophoric` capability. -/
instance : Logophoric LogophoricPronoun := ⟨LogophoricPronoun.requiredRole⟩

/-! ### Worked entries ([sells-1987]) -/

/-- Ewe *yè* — a dedicated logophoric pronoun. Its antecedent must be at least a `self` (an
    attitude holder): [sells-1987] "antecedent must be at least a self". Principle-B by default
    (no declared anaphor shell); the logophoric orientation, not the binding class, does the work. -/
def ye : LogophoricPronoun :=
  { form := "yè", person := some .third, requiredRole := .self }

/-- Japanese long-distance *zibun* — a perspectival reflexive. Its antecedent need only be a
    `pivot` (any point-of-view centre): [sells-1987] "antecedent must be a pivot". Morphologically a
    Principle-A reflexive (`bindingClass := .reflexive`), so its licensing axis (pivot) and its
    binding axis (anaphor) are distinct — the orthogonality the `Logophoric`/`Bound` split encodes. -/
def zibun : LogophoricPronoun :=
  { form := "zibun", bindingClass := some .reflexive, requiredRole := .pivot }

/-! ### Licensing, derived from the hierarchy -/

/-- *yè* is licensed by a `self` antecedent — it reaches its own requirement. -/
theorem ye_licensed_by_self : Logophoric.LicensedBy ye .self := by decide

/-- *yè* is licensed by a `source` antecedent — a reporter is also a self (`self ≤ source`). -/
theorem ye_licensed_by_source : Logophoric.LicensedBy ye .source := by decide

/-- *yè* is **not** licensed by a bare `pivot` antecedent: a point-of-view centre that is not an
    attitude holder fails *yè*'s `self` requirement (`¬ self ≤ pivot`). The discriminating case
    that makes the capability non-vacuous. -/
theorem ye_not_licensed_by_pivot : ¬ Logophoric.LicensedBy ye .pivot := by decide

/-- Long-distance *zibun* is licensed by any `pivot` — the weakest centre suffices. -/
theorem zibun_licensed_by_pivot : Logophoric.LicensedBy zibun .pivot := by decide

/-- **Orthogonality of orientation and binding**: *zibun* is a Principle-A anaphor
    (`Bound.IsAnaphor`) yet its logophoric licensing is the *pivot* orientation, not its binding
    class — [sells-1987]'s role-oriented anaphora, carried as two independent axes on one object. -/
theorem zibun_anaphor_yet_pivot_oriented :
    Bound.IsAnaphor zibun ∧ Logophoric.requiredRole zibun = LogophoricRole.pivot :=
  ⟨Or.inl rfl, rfl⟩

/-- Generic consumer of the capability: *every* logophoric pronoun is licensed by a `source`
    antecedent, via the carrier-independent `Logophoric.source_licenses`. Validates that the
    abstraction is usable over `[Logophoric α]`, not just on these entries. -/
theorem any_logophoric_licensed_by_source (p : LogophoricPronoun) :
    Logophoric.LicensedBy p .source :=
  Logophoric.source_licenses p
