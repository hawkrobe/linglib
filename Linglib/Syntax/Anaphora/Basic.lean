/-!
# Anaphor — Hankamer & Sag's deep/surface anaphora theory

[hankamer-sag-1976]'s theory of (unbounded) anaphoric processes. The organizing
distinction is **control** (pragmatic/deictic vs syntactic) — the conceptual
entry point of H&S's argument — with **depth** (deep vs surface) as the
conclusion. A **deep** anaphor is interpreted at an underlying/semantic level,
can be pragmatically (deictically) controlled, and needs only a coherent semantic
referent (definite pronouns, *do it*, null complement anaphora, *pro*). A
**surface** anaphor is derived by deletion under identity with a surface
antecedent, so it requires a coherent *syntactic* antecedent (VP-ellipsis,
sluicing, gapping, argument ellipsis). Pragmatic controllability is the conceptual
cut, *not* a reliable test on its own: [landau-2026], following [merchant-2001],
holds the reliable classic diagnostics to be extraction and agreement — this file
models extraction and Landau's EIR test (`Syntax/Anaphora/Diagnostic.lean`).

`Depth` is the genus, not an ellipsis classification: ellipsis ⊊ surface anaphora
⊊ anaphora, and the deep values (*do so*, NCA, *pro*) are precisely the
*non-ellipsis* anaphors. Ellipsis-specific machinery (deletion domains,
`[E]`-feature, ellipsis-type taxonomy) lives in `Syntax/Minimalist/Ellipsis/` and
*consumes* this axis — an `EllipsisType` is a `HasDepth` carrier with depth
`.surface`.

This is the **unbounded**-anaphora axis, orthogonal to (and a sibling of) the
binding-theoretic Principle-A/B/C axis (`Features.BindingClass` / the `Bound`
capability): H&S explicitly set aside bounded anaphora (reflexivization) as a
separate, always-syntactic process. A reflexive is a `Bound.IsAnaphor`; *do so*
is an `Anaphor.Depth.deep`.

Other H&S diagnostics are *not* modeled here: the missing-antecedent test (itself
judged unreliable by [landau-2026]), the coherent-semantic-entity requirement on
deep anaphora, and the Backwards Anaphora Constraint.

## Main declarations

* `Anaphor.Depth` — deep/surface (the conclusion).
* `Anaphor.Control` — pragmatic/syntactic (H&S's organizing distinction).
* `Anaphor.Depth.HasInternalStructure` / `Anaphor.Depth.control` — the structural
  property and the depth→control map; `allowsPragmaticControl_iff_…` proves the
  typology's two correlated properties coincide by construction.
* `Anaphor.HasDepth` — the carrier capability (the depth-axis analogue of `Bound`).
-/

namespace Anaphor

/-- Hankamer & Sag's deep/surface classification of (unbounded) anaphoric
    processes [hankamer-sag-1976]. -/
inductive Depth where
  | deep
  | surface
  deriving DecidableEq, Repr

/-- How an anaphoric relation is controlled [hankamer-sag-1976]: a `pragmatic`
    (deictic) anaphor can be controlled by the nonlinguistic context with no
    linguistic antecedent; a `syntactic` anaphor requires a coherent linguistic
    antecedent in surface structure. This is H&S's organizing distinction; depth
    is the conclusion drawn from it. -/
inductive Control where
  | pragmatic
  | syntactic
  deriving DecidableEq, Repr

namespace Depth

/-- The defining structural property: surface anaphora project *syntactically
    present* internal structure (deletion under identity), deep anaphora do not.
    Every account of the distinction ([hankamer-sag-1976], [merchant-2001],
    [landau-2026]) shares this much; they differ on the *level* (H&S: surface
    structure; Merchant/Landau: LF — the difference EIR turns on). -/
def HasInternalStructure : Depth → Prop
  | .surface => True
  | .deep    => False

instance : DecidablePred HasInternalStructure := fun d =>
  match d with
  | .surface => isTrue trivial
  | .deep    => isFalse (fun h => h)

-- The value lemmas are subsumed by `hasInternalStructure_iff_surface` on the simp
-- set, so they carry no `@[simp]` (kept for direct `exact` use).
theorem hasInternalStructure_surface : HasInternalStructure .surface := trivial

theorem not_hasInternalStructure_deep : ¬ HasInternalStructure .deep := fun h => h

@[simp] theorem hasInternalStructure_iff_surface (d : Depth) :
    HasInternalStructure d ↔ d = .surface := by
  cases d <;> simp [HasInternalStructure]

/-- The control type a depth determines [hankamer-sag-1976]: deep anaphora allow
    pragmatic (deictic) control; surface anaphora are syntactically controlled
    (deletion under identity with a surface antecedent). -/
def control : Depth → Control
  | .deep    => .pragmatic
  | .surface => .syntactic

/-- A depth *allows pragmatic control* iff it is deep — the conceptual cut H&S
    start from, here a consequence of `control`, not a separate stipulation. -/
def AllowsPragmaticControl (d : Depth) : Prop := d.control = .pragmatic

instance : DecidablePred AllowsPragmaticControl := fun d =>
  inferInstanceAs (Decidable (d.control = .pragmatic))

/-- The depth typology's two correlated properties coincide *by construction*: a
    depth allows pragmatic control iff it lacks internal structure (is deep). This
    is definitional given the 2-element typology — the *empirical* content is which
    anaphors get which depth, tested against data in the consuming study, not this
    biconditional. -/
@[simp] theorem allowsPragmaticControl_iff_not_hasInternalStructure (d : Depth) :
    AllowsPragmaticControl d ↔ ¬ HasInternalStructure d := by
  cases d <;> simp [AllowsPragmaticControl, control, HasInternalStructure]

end Depth

/-! ### The `HasDepth` capability -/

/-- A carrier whose every element has a Hankamer & Sag `Anaphor.Depth` — the
    depth-axis analogue of `Bound` (the binding-class axis). An ellipsis-type
    record, a paper's datum struct, or a syntactic object each supplies its own
    instance. -/
class HasDepth (α : Type _) where
  /-- The deep/surface depth of every element. -/
  depth : α → Depth

/-- `a` is a deep anaphor (no internal structure; pragmatic control). -/
def HasDepth.IsDeep {α : Type _} [HasDepth α] (a : α) : Prop :=
  HasDepth.depth a = .deep

/-- `a` is a surface anaphor (deletion under identity; syntactic control). -/
def HasDepth.IsSurface {α : Type _} [HasDepth α] (a : α) : Prop :=
  HasDepth.depth a = .surface

/-- The element's structural property, via its depth. -/
def HasDepth.HasInternalStructure {α : Type _} [HasDepth α] (a : α) : Prop :=
  (HasDepth.depth a).HasInternalStructure

instance {α : Type _} [HasDepth α] (a : α) : Decidable (HasDepth.IsDeep a) := by
  unfold HasDepth.IsDeep; infer_instance

instance {α : Type _} [HasDepth α] (a : α) : Decidable (HasDepth.IsSurface a) := by
  unfold HasDepth.IsSurface; infer_instance

instance {α : Type _} [HasDepth α] (a : α) :
    Decidable (HasDepth.HasInternalStructure a) := by
  unfold HasDepth.HasInternalStructure; infer_instance

/-- `IsSurface` is exactly having internal structure. -/
@[simp] theorem HasDepth.hasInternalStructure_iff_isSurface
    {α : Type _} [HasDepth α] (a : α) :
    HasDepth.HasInternalStructure a ↔ HasDepth.IsSurface a := by
  unfold HasDepth.HasInternalStructure HasDepth.IsSurface
  exact Depth.hasInternalStructure_iff_surface _

end Anaphor
