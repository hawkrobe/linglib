import Mathlib.Tactic.TypeStar

/-!
# Fission (Distributed Morphology)

Fission is the postsyntactic DM operation that splits a single terminal
node into multiple positions of exponence, each independently subject
to Vocabulary Insertion ([noyer-1992], [halle-1997]; adopted in
[halle-marantz-1993]). The classical motivation is [noyer-1992]'s
analysis of Afro-Asiatic prefix-conjugation agreement, where a single
AGR node surfaces as one, two, or three separate affixes.
[arregi-nevins-2012]'s Plural Fission splits the number feature
[−singular] off the person features of second/third-person plural
pronominal clitics in Basque auxiliaries (their §3.3.4), yielding the
plural exponent at a second terminal-of-exponence.

A `FissionRule` is parameterized over the fissioned feature bundle, the
structural context licensing Fission, and the realization output.
Conditions are `Prop`-valued with carried `DecidablePred` witnesses,
matching the `ImpoverishmentRule` shape in
`Linglib/Morphology/DM/Impoverishment.lean`.

## Main declarations

* `FissionRule Bundle Ctx Out` — the generic rule structure
* `FissionRule.apply` — partial application returning `Option Out`
* `FissionRule.apply_eq_some_iff`, `FissionRule.apply_eq_none_iff`,
  `FissionRule.isSome_apply` — the characterization API

## Implementation notes

The realization output `Out` is opaque: this interface stipulates the
fissioned exponents via `realize` rather than deriving them from
iterated Vocabulary Insertion discharging features against a residue,
as in [noyer-1992]'s original mechanism. Consumed by
`Studies/MunozPerez2026.lean` (Chilean Spanish stylistic applicatives).

## Todo

* Derive `realize` from a vocabulary: iterate insertion over the
  feature residue so the number of exponents is a theorem, not a
  parameter. Noyer's Tamazight Berber prefix conjugation (one-to-three
  affix fission) is the canonical stress test.
* Toward a second consumer: [arregi-nevins-2012]'s Plural Fission is a
  feature-pair split with the residue copied into *both* output nodes
  (their §3.3.4), so hosting it needs a two-node output and a computed
  residue rather than an opaque `realize`. (Their Ergative/Dative
  Doubling is not Fission: a post-Linearization Generalized-Reduplication
  repair of the T-Noninitiality constraint.)
-/

namespace Morphology.DM

/-- A Fission rule is parameterized over:
* `Bundle` — the fissioned morphological feature bundle (e.g., φ-features);
* `Ctx`    — the structural context licensing Fission;
* `Out`    — the realization output.

Both `contextOk` and `bundleOk` are `Prop`-valued with carried
`DecidablePred` witnesses, matching the `ImpoverishmentRule` template
(see `Impoverishment.lean`). -/
structure FissionRule (Bundle Ctx Out : Type*) where
  /-- The structural condition licensing Fission. -/
  contextOk : Ctx → Prop
  /-- Decidability witness for `contextOk`. -/
  decContext : DecidablePred contextOk
  /-- The condition on the fissioned bundle (e.g., [+PART, +SING]). -/
  bundleOk : Bundle → Prop
  /-- Decidability witness for `bundleOk`. -/
  decBundle : DecidablePred bundleOk
  /-- Realization: map each licensed bundle to its output. -/
  realize : Bundle → Out

namespace FissionRule

variable {Bundle Ctx Out : Type*} {rule : FissionRule Bundle Ctx Out}
  {p : Bundle} {c : Ctx} {out : Out}

instance (rule : FissionRule Bundle Ctx Out) (c : Ctx) :
    Decidable (rule.contextOk c) := rule.decContext c

instance (rule : FissionRule Bundle Ctx Out) (p : Bundle) :
    Decidable (rule.bundleOk p) := rule.decBundle p

/-- Apply Fission: yield the realization when both the structural and
bundle conditions hold; otherwise `none`. -/
def apply (rule : FissionRule Bundle Ctx Out) (p : Bundle) (c : Ctx) :
    Option Out :=
  if rule.contextOk c ∧ rule.bundleOk p then some (rule.realize p) else none

theorem apply_pos (hc : rule.contextOk c) (hb : rule.bundleOk p) :
    rule.apply p c = some (rule.realize p) :=
  if_pos ⟨hc, hb⟩

theorem apply_neg (h : ¬(rule.contextOk c ∧ rule.bundleOk p)) :
    rule.apply p c = none :=
  if_neg h

@[simp]
theorem apply_eq_some_iff :
    rule.apply p c = some out ↔
      (rule.contextOk c ∧ rule.bundleOk p) ∧ rule.realize p = out := by
  unfold apply; split <;> simp_all

@[simp]
theorem apply_eq_none_iff :
    rule.apply p c = none ↔ ¬(rule.contextOk c ∧ rule.bundleOk p) := by
  unfold apply; split <;> simp_all

theorem isSome_apply :
    (rule.apply p c).isSome ↔ rule.contextOk c ∧ rule.bundleOk p := by
  unfold apply; split <;> simp_all

end FissionRule

end Morphology.DM
