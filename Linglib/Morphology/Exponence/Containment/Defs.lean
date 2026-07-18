import Linglib.Morphology.Exponence.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Fin.Basic

/-!
# Vocabularies over containment hierarchies: rules and specificity
[bobaljik-2012] [starke-2009] [caha-2009] [kiparsky-1973]

The carrier for the realizational engine of [bobaljik-2012]'s
comparative-suppletion generalizations, over an arbitrary `n`-grade
containment hierarchy. An `SpanRule` realizes the initial span `[0, spans]`
of the hierarchy, optionally conditioned on a higher head. One carrier
carries two `Exponence` views: the **Subset** reading (`SpanRule`,
applicability is threshold containment) is DM Elsewhere insertion; the
**Superset** reading (`SupersetRule`, applicability is constituent
containment) is nanosyntax spellout, dual à la `OrderDual`.

## Main declarations

* `SpanRule` — exponent, exponed span `[0, spans]`, optional conditioning head
* `SpanRule.threshold`, `AppliesAt`, `MoreSpecific` — Subset applicability
  and its `moreSpecific_iff_threshold_le` reflection
* `SpanRule.Matches`, `SupersetRule` — Superset applicability and its
  `matches_imp_iff_spans_le` reflection
* `Terminal`, `Adjacent`, `Antihomophonous`, `Grounded`, `ContextFree` —
  well-formedness conditions on vocabularies
-/

namespace Morphology.Containment

open Morphology.Exponence

variable {n : ℕ} {F : Type*}

/-! ### Rules of exponence and derived specificity -/

/-- A **rule of exponence** ([bobaljik-2012]) over an `n`-grade containment
hierarchy. The rule realizes the initial span `[0, spans]` — the bare root
when `spans = 0`, a root+heads portmanteau when `spans > 0` — and applies
only when its optional conditioning head `context` is present. Latin
([bobaljik-2012] (204)): `bon` is `⟨bon, 0, none⟩`, `mel-` is
`⟨mel, 0, some 1⟩`, the portmanteau `opt-` is `⟨opt, 1, some 2⟩`. -/
structure SpanRule (n : ℕ) (F : Type*) where
  /-- The phonological exponent inserted for the span. -/
  exponent : F
  /-- Upper end of the exponed initial span `[0, spans]`. -/
  spans : Fin n
  /-- Head whose presence conditions the rule, if any. -/
  context : Option (Fin n)
  deriving DecidableEq, Repr

namespace SpanRule

/-- The least grade at which the rule is applicable: everything the
rule mentions — exponed span and conditioning context — must be
contained in the structure. -/
def threshold (it : SpanRule n F) : Fin n :=
  max it.spans (it.context.getD it.spans)

/-- A rule applies at grade `g` when grade `g`'s structure contains
everything the rule mentions. -/
def AppliesAt (it : SpanRule n F) (g : Fin n) : Prop :=
  it.threshold ≤ g

instance (it : SpanRule n F) (g : Fin n) : Decidable (it.AppliesAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A rule `it` is at least as specific as `jt` when it applies in a
subset of the contexts `jt` applies in (Pāṇinian specificity). -/
def MoreSpecific (it jt : SpanRule n F) : Prop :=
  ∀ ⦃g : Fin n⦄, it.AppliesAt g → jt.AppliesAt g

/-- Over a linear containment hierarchy, applicability sets are nested
upward sets, so derived specificity is threshold comparison — the
Elsewhere ordering ([kiparsky-1973]) is total. -/
theorem moreSpecific_iff_threshold_le {it jt : SpanRule n F} :
    it.MoreSpecific jt ↔ jt.threshold ≤ it.threshold :=
  ⟨λ h => h (le_refl it.threshold), λ h _ hg => le_trans h hg⟩

end SpanRule

/-! ### Well-formedness conditions on vocabularies

Each generalization below hypothesizes exactly the conditions it
needs; vocabularies violating a condition witness the corresponding
unattested pattern (see the worked examples in
`Studies/Bobaljik2012.lean`). -/

/-- Every rule expones the bare root (no portmanteaux). -/
def Terminal (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, (it.spans : ℕ) = 0

instance (v : List (SpanRule n F)) : Decidable (Terminal v) := by
  unfold Terminal; infer_instance

/-- Conditioning heads are adjacent to the exponed span —
[bobaljik-2012]'s (tentatively adopted) adjacency condition on
contextual allomorphy. -/
def Adjacent (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ c : Fin n, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1

instance (v : List (SpanRule n F)) : Decidable (Adjacent v) := by
  unfold Adjacent; infer_instance

/-- Distinct rules carry distinct exponents — [bobaljik-2012]'s Antihomophony
assumption (44), closing the loophole where a surface-ABA pattern is really an
ABC with accidental A ≡ C homophony. -/
def Antihomophonous (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ jt ∈ v, it.exponent = jt.exponent → it = jt

instance [DecidableEq F] (v : List (SpanRule n F)) : Decidable (Antihomophonous v) := by
  unfold Antihomophonous; infer_instance

/-- [bobaljik-2012]'s markedness condition (202): a context-sensitive rule of
exponence involving a node requires a context-free rule involving that node.
Under the threshold encoding, this is downward closure of the vocabulary's
threshold set. -/
def Grounded (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ k : Fin n, k < it.threshold → ∃ jt ∈ v, jt.threshold = k

instance (v : List (SpanRule n F)) : Decidable (Grounded v) := by
  unfold Grounded; infer_instance

/-- The nanosyntax restriction, in the pointer-free idealization of
[caha-2009]: entries store bare constituents, with no DM-style
contextual environment. -/
def ContextFree (v : List (SpanRule n F)) : Prop :=
  ∀ it ∈ v, it.context = none

instance (v : List (SpanRule n F)) : Decidable (ContextFree v) := by
  unfold ContextFree; infer_instance

/-! ### The Subset reading: DM Elsewhere insertion

The containment engine implements `Morphology.Exponence`
directly: applicability is threshold containment (the upper set
`Set.Ici threshold`) and derived specificity is threshold comparison. -/

instance : Exponence (SpanRule n F) (Fin n) F :=
  ⟨SpanRule.exponent, fun it i => it.threshold ≤ i⟩

instance : Preorder (SpanRule n F) := Exponence.toPreorder

instance (g : Fin n) : DecidablePred (fun it : SpanRule n F => Exponence.Applies (F := F) it g) :=
  fun it => inferInstanceAs (Decidable (it.threshold ≤ g))

/-- Subset applicability is threshold containment. -/
@[simp] theorem SpanRule.applies_iff {it : SpanRule n F} {g : Fin n} :
    Exponence.Applies (F := F) it g ↔ it.threshold ≤ g :=
  Iff.rfl

/-- Containment specificity is the shared core's specificity order. -/
theorem SpanRule.le_iff {it jt : SpanRule n F} :
    it ≤ jt ↔ it.MoreSpecific jt :=
  Iff.rfl

/-! ### The Superset reading: nanosyntax spellout

One carrier, a dual view: the entry can spell out grade `g` when its
stored constituent contains `g` (the down-set `Set.Iic spans`), and
smallest-match selection is Pāṇinian specificity under superset
matching. A distinct type synonym so the two readings carry different
`Exponence` instances on one carrier, mirroring `OrderDual`. -/

/-- The **Superset Principle** ([starke-2009]): an entry can spell out
grade `g` when the constituent it stores contains grade `g`'s
structure. Anti-monotone in `g`, dually to `AppliesAt`. -/
def SpanRule.Matches (it : SpanRule n F) (g : Fin n) : Prop :=
  g ≤ it.spans

instance (it : SpanRule n F) (g : Fin n) : Decidable (it.Matches g) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem SpanRule.Matches.anti {it : SpanRule n F} {g g' : Fin n}
    (h : it.Matches g') (hg : g ≤ g') : it.Matches g :=
  le_trans hg h

/-- Minimize Junk derived, dually to
`SpanRule.moreSpecific_iff_threshold_le`: an entry matches in a
subset of the structures another matches in iff it stores the smaller
constituent — smallest-match selection is Pāṇinian specificity under
superset matching. -/
theorem SpanRule.matches_imp_iff_spans_le {it jt : SpanRule n F} :
    (∀ ⦃g : Fin n⦄, it.Matches g → jt.Matches g) ↔ it.spans ≤ jt.spans :=
  ⟨λ h => h (le_refl it.spans), λ h _ hg => le_trans hg h⟩

/-- The **Superset** reading of an exponence rule: an entry spells out
grade `g` when its stored constituent contains `g` (the down-set
`Set.Iic spans`), dually to the Subset reading of `SpanRule`. -/
def SupersetRule (n : ℕ) (F : Type*) := SpanRule n F

instance : Exponence (SupersetRule n F) (Fin n) F :=
  ⟨SpanRule.exponent, fun it i => i ≤ SpanRule.spans it⟩

instance : Preorder (SupersetRule n F) := Exponence.toPreorder

instance (g : Fin n) :
    DecidablePred (fun it : SupersetRule n F => Exponence.Applies (F := F) it g) :=
  fun it => inferInstanceAs (Decidable (g ≤ SpanRule.spans it))

/-- Read an exponence rule under the Superset reading. -/
def SpanRule.superset (it : SpanRule n F) : SupersetRule n F := it

/-- Superset applicability is constituent containment. -/
@[simp] theorem SupersetRule.applies_iff {it : SupersetRule n F} {g : Fin n} :
    Exponence.Applies (F := F) it g ↔ g ≤ SpanRule.spans it :=
  Iff.rfl

/-- Minimize Junk is the Superset reading's specificity order: smaller
span = more specific. -/
theorem SupersetRule.le_iff {it jt : SupersetRule n F} :
    it ≤ jt ↔ SpanRule.spans it ≤ SpanRule.spans jt :=
  Set.Iic_subset_Iic

/-- **Subset/Superset duality** over context-free vocabularies (the
nanosyntax idealization): DM-style Subset specificity of `it` over `jt`
is Superset specificity of `jt` over `it`. With contextual restrictions
the Subset order compares thresholds, not spans, and the duality is
only one-directional. -/
theorem SpanRule.subset_le_iff_superset_le {it jt : SpanRule n F}
    (hit : it.context = none) (hjt : jt.context = none) :
    it ≤ jt ↔ jt.superset ≤ it.superset := by
  rw [SpanRule.le_iff, SpanRule.moreSpecific_iff_threshold_le,
    SupersetRule.le_iff]
  unfold SpanRule.threshold SpanRule.superset
  rw [hit, hjt]
  simp

end Morphology.Containment
