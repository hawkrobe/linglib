import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Fusion (Distributed Morphology)

Fusion is the postsyntactic DM operation that merges two adjacent terminal
nodes into a single terminal bearing both feature bundles, which a single
Vocabulary Item then spells out ([halle-marantz-1993]'s Tns+Agr fusion in
English; French *du* = P[de] fused with D[le] is the portmanteau case,
[kalin-bjorkman-etal-2026] §4.4). It is the inverse misalignment from
Fission: fission yields more positions of exponence than syntactic
terminals, fusion fewer.

A `FusionRule` follows the `FissionRule`/`ImpoverishmentRule` template —
`Prop`-valued conditions with carried decidability witnesses. Unlike
fission's opaque realization output, fusion's output is a bundle that
continues to Vocabulary Insertion, and `portmanteau_needs_fusion` is the
payoff: an exponent whose vocabulary items all draw on both input bundles
is insertable only at the fused node.

## Main declarations

* `FusionRule Bundle Ctx` — the generic rule structure
* `FusionRule.apply` — partial application returning `Option Bundle`, with
  the `apply_eq_some_iff`/`apply_eq_none_iff`/`isSome_apply`
  characterization API
* `portmanteau_needs_fusion` — a cross-terminal exponent wins at neither
  unfused node
-/

namespace DistributedMorphology

/-- A Fusion rule is parameterized over:
* `Bundle` — the morphological feature bundles of the fusing terminals;
* `Ctx`    — the structural context licensing Fusion (adjacency of the
  two terminals under one head).

Both conditions are `Prop`-valued with carried decidability witnesses,
matching the `FissionRule`/`ImpoverishmentRule` template. -/
structure FusionRule (Bundle Ctx : Type*) where
  /-- The structural condition licensing Fusion. -/
  contextOk : Ctx → Prop
  /-- Decidability witness for `contextOk`. -/
  decContext : DecidablePred contextOk
  /-- The condition on the two fusing bundles (structurally higher first). -/
  bundlesOk : Bundle → Bundle → Prop
  /-- Decidability witness for `bundlesOk`. -/
  decBundles : ∀ p, DecidablePred (bundlesOk p)
  /-- The fused bundle — the union of the inputs in the intended instances. -/
  fuse : Bundle → Bundle → Bundle

namespace FusionRule

variable {Bundle Ctx : Type*} {rule : FusionRule Bundle Ctx}
  {p q out : Bundle} {c : Ctx}

instance (rule : FusionRule Bundle Ctx) (c : Ctx) :
    Decidable (rule.contextOk c) := rule.decContext c

instance (rule : FusionRule Bundle Ctx) (p q : Bundle) :
    Decidable (rule.bundlesOk p q) := rule.decBundles p q

/-- Apply Fusion: yield the fused bundle when both the structural and
bundle conditions hold; otherwise `none`. -/
def apply (rule : FusionRule Bundle Ctx) (p q : Bundle) (c : Ctx) :
    Option Bundle :=
  if rule.contextOk c ∧ rule.bundlesOk p q then some (rule.fuse p q) else none

theorem apply_pos (hc : rule.contextOk c) (hb : rule.bundlesOk p q) :
    rule.apply p q c = some (rule.fuse p q) :=
  if_pos ⟨hc, hb⟩

theorem apply_neg (h : ¬(rule.contextOk c ∧ rule.bundlesOk p q)) :
    rule.apply p q c = none :=
  if_neg h

@[simp]
theorem apply_eq_some_iff :
    rule.apply p q c = some out ↔
      (rule.contextOk c ∧ rule.bundlesOk p q) ∧ rule.fuse p q = out := by
  unfold apply; split <;> simp_all

@[simp]
theorem apply_eq_none_iff :
    rule.apply p q c = none ↔ ¬(rule.contextOk c ∧ rule.bundlesOk p q) := by
  unfold apply; split <;> simp_all

theorem isSome_apply :
    (rule.apply p q c).isSome ↔ rule.contextOk c ∧ rule.bundlesOk p q := by
  unfold apply; split <;> simp_all

end FusionRule

section Portmanteau

open VI

variable {F E : Type*} [BEq F]

/-- A portmanteau exponent needs fusion: when every vocabulary item
carrying the exponent draws on features missing from each unfused bundle,
the Subset Principle can select it at neither unfused node — only the
fused bundle contains its item's features (`subsetPrinciple_winner_mem`). -/
theorem portmanteau_needs_fusion {items : List (FeatureVI F E)}
    {p q : List F} {e : E}
    (he : ∀ i ∈ items, i.exponent = e →
      i.features.all (p.contains ·) = false ∧
      i.features.all (q.contains ·) = false) :
    subsetPrinciple items p ≠ some e ∧ subsetPrinciple items q ≠ some e := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    obtain ⟨i, hi, rfl, happ⟩ := subsetPrinciple_winner_mem h
  · simp [(he i hi rfl).1] at happ
  · simp [(he i hi rfl).2] at happ

end Portmanteau

end DistributedMorphology
