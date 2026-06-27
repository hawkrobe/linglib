/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Nat
import Linglib.Phonology.Feature
import Linglib.Features.Basic

/-!
# Segments

A **segment** is a partial binary specification of phonological `Feature`s —
i.e. a feature bundle. Its `spec` field is `Features.Bundle Feature (fun _ => Bool)`
in unfolded form (`Feature → Option Bool`), so the shared bundle algebra
(`Features.Bundle.merge`/`set`/`delete`) operates on it directly while the
`Option` face keeps the ergonomic dot-notation.

## Main definitions

* `Segment` — a feature bundle over `Feature`
* `Segment.Specified` / `Segment.HasValue` — the valuation API
* `Segment.ofSpecs` / `Segment.matchesPattern` — natural-class construction and membership
* `Segment.applyChanges` — SPE structural change, via `Features.Bundle.merge`
* `Segment.IsVowel`, `IsConsonant`, `IsStop`, … — the natural-class predicates
* `Sonority` — the abstract sonority scale (a `LinearOrder`), and
  `SonorityClass` — the finer 8-level Parker refinement, both grounded in a
  segment's features

[hayes-2009] [chomsky-halle-1968] [clements-1990] [parker-2002]
-/

namespace Phonology

/-! ### The segment bundle -/

/-- A segment: a `Features.Bundle Feature (fun _ => Bool)` (in unfolded
    `Feature → Option Bool` form) — a partial binary-feature specification
    (`none` = unspecified). -/
structure Segment where
  spec : Feature → Option Bool

/-- Is feature `f` specified (either [+F] or [−F])? -/
def Segment.Specified (s : Segment) (f : Feature) : Prop :=
  (s.spec f).isSome = true

instance (s : Segment) : DecidablePred (Segment.Specified s) := fun _ =>
  inferInstanceAs (Decidable (_ = true))

/-- Does feature `f` have value `v`? -/
def Segment.HasValue (s : Segment) (f : Feature) (v : Bool) : Prop :=
  s.spec f = some v

instance (s : Segment) (f : Feature) (v : Bool) :
    Decidable (Segment.HasValue s f v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Decidable equality on segments via exhaustive feature comparison.
    Enables `decide` on segment-level goals and OT tableaux
    over `List Segment` candidates. -/
instance : DecidableEq Segment := fun s1 s2 =>
  if h : (Feature.allFeatures.all fun f => s1.spec f == s2.spec f) = true
  then isTrue (by
    cases s1; cases s2; congr; funext f
    exact eq_of_beq (List.all_eq_true.mp h f (allFeatures_complete f)))
  else isFalse (fun heq => by
    subst heq
    exact h (List.all_eq_true.mpr fun f _ => beq_self_eq_true (s1.spec f)))

/-! ### Pattern matching and feature changes -/

/-- Build a segment from a list of (feature, value) pairs.
    Unmentioned features are unspecified (`none`), giving natural-class
    semantics: `ofSpecs [(continuant, false)]` matches all [-cont] segments. -/
def Segment.ofSpecs (specs : List (Feature × Bool)) : Segment where
  spec f := match specs.find? (λ p => p.1 == f) with
    | some (_, v) => some v
    | none => none

/-- Bool: does segment `s` match natural-class pattern `p`? True when every
    feature specified in `p` agrees with `s`; unspecified features in `p`
    match anything. -/
def Segment.matchesPattern (s : Segment) (p : Segment) : Bool :=
  Feature.allFeatures.all λ f =>
    match p.spec f with
    | none => true
    | some v => s.spec f == some v

/-- Prop wrapper around `matchesPattern` (mirrors `Segment.HasValue`). Lets
    consumers write mathlib-style universally-quantified theorems with
    Decidable inference via the Bool computation. -/
def Segment.MatchesPattern (s p : Segment) : Prop := s.matchesPattern p = true

instance (s p : Segment) : Decidable (Segment.MatchesPattern s p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Merge feature changes from `change` into `s`: features specified in
    `change` override `s`'s values; unspecified features in `change` are
    preserved. Implements the SPE structural change `A → B` (when `B` is a
    partial bundle) as the shared `Features.Bundle.merge`. -/
def Segment.applyChanges (s change : Segment) : Segment :=
  ⟨Features.Bundle.merge change.spec s.spec⟩

/-- Two segments are equal iff their `spec` functions agree on every feature. -/
@[ext] theorem Segment.ext {s t : Segment} (h : ∀ f, s.spec f = t.spec f) :
    s = t := by
  cases s; cases t; congr; funext f; exact h f

/-- Every segment matches itself as a pattern. -/
@[simp] theorem Segment.matchesPattern_self (s : Segment) :
    s.matchesPattern s = true := by
  unfold Segment.matchesPattern
  rw [List.all_eq_true]
  intro f _
  cases s.spec f
  · rfl
  · exact beq_self_eq_true _

/-- Applying the empty change list is the identity. -/
@[simp] theorem Segment.applyChanges_ofSpecs_nil (s : Segment) :
    s.applyChanges (Segment.ofSpecs []) = s := by
  ext f; simp [Segment.applyChanges, Segment.ofSpecs, Features.Bundle.merge]

/-- Applying the same change twice equals applying it once. -/
@[simp] theorem Segment.applyChanges_idem (s change : Segment) :
    (s.applyChanges change).applyChanges change = s.applyChanges change := by
  ext f
  simp only [Segment.applyChanges, Features.Bundle.merge]
  cases change.spec f <;> rfl

/-! ### Natural-class predicates

Language-neutral natural-class membership predicates, by the SPE feature
decompositions standard since [chomsky-halle-1968] and codified in textbook
form by [hayes-2009]. Pure substrate: they project information already encoded
in a segment's feature bundle, consumed by per-language Fragment files rather
than redefined locally. -/

/-- A segment is a vowel iff it is [+syllabic]. -/
def Segment.IsVowel (s : Segment) : Prop := s.HasValue .syllabic true

instance (s : Segment) : Decidable s.IsVowel := by
  unfold Segment.IsVowel; infer_instance

/-- A segment is a consonant iff it is [+consonantal]. -/
def Segment.IsConsonant (s : Segment) : Prop := s.HasValue .consonantal true

instance (s : Segment) : Decidable s.IsConsonant := by
  unfold Segment.IsConsonant; infer_instance

/-- A segment is an oral stop iff it is [+cons, -son, -cont]. -/
def Segment.IsStop (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant false

instance (s : Segment) : Decidable s.IsStop := by
  unfold Segment.IsStop; infer_instance

/-- A segment is a fricative iff it is [+cons, -son, +cont]. -/
def Segment.IsFricative (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant true

instance (s : Segment) : Decidable s.IsFricative := by
  unfold Segment.IsFricative; infer_instance

/-- A segment is a nasal iff it is [+nasal]. -/
def Segment.IsNasal (s : Segment) : Prop := s.HasValue .nasal true

instance (s : Segment) : Decidable s.IsNasal := by
  unfold Segment.IsNasal; infer_instance

/-- A segment is a liquid iff it is [+cons, +son] and one of
[+lateral], [+trill], [+tap] — admitting the lateral /l/, the trill /r/,
and the flap /ɾ/ under a single textbook class. -/
def Segment.IsLiquid (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant true ∧
    (s.HasValue .lateral true ∨ s.HasValue .trill true ∨ s.HasValue .tap true)

instance (s : Segment) : Decidable s.IsLiquid := by
  unfold Segment.IsLiquid; infer_instance

/-- A segment is a glide iff it is [-cons, -syllabic, +approximant]. -/
def Segment.IsGlide (s : Segment) : Prop :=
  s.HasValue .consonantal false ∧ s.HasValue .syllabic false ∧
    s.HasValue .approximant true

instance (s : Segment) : Decidable s.IsGlide := by
  unfold Segment.IsGlide; infer_instance

/-! ### Underspecification

A segment is **underspecified** for a feature `f` when its spec returns `none`.
These segment-level operations are thin lifts of the shared `Features.Bundle`
algebra. Three-valued (`+ / − / ∅`) specification is standard in [keating-1988],
[inkelas-orgun-1995], and [steriade-1995]; `fillFeature` uses `merge`
(default-fill, preserving existing values) per [kiparsky-1982] [archangeli-1988],
while `setFeature` overrides. The Latin coda /l/ analysis in [sen-2015] Ch 2 is a
worked example. -/

namespace Segment

/-! ### Underspecification predicate -/

/-- A segment is **unspecified** for feature `f` iff its spec returns `none`. -/
def Unspecified (s : Segment) (f : Feature) : Prop := s.spec f = none

instance (s : Segment) (f : Feature) : Decidable (s.Unspecified f) :=
  inferInstanceAs (Decidable (_ = none))

/-- Specification and unspecification are mutually exclusive and exhaustive. -/
theorem specified_iff_not_unspecified (s : Segment) (f : Feature) :
    s.Specified f ↔ ¬ s.Unspecified f := by
  unfold Specified Unspecified
  cases s.spec f <;> simp

/-! ### Operations -/

/-- Remove the specification of feature `f` from `s` (lift of
    `Features.Bundle.delete`). The result is unspecified for `f` and agrees
    with `s` on every other feature. -/
def unsetFeature (s : Segment) (f : Feature) : Segment :=
  ⟨Features.Bundle.delete f s.spec⟩

/-- Set feature `f` to value `v`, overriding any existing specification
    (lift of `Features.Bundle.set`). For default-fill semantics that only
    assigns when `f` is currently unspecified, use `fillFeature`. -/
def setFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨Features.Bundle.set f v s.spec⟩

/-- Fill feature `f` with value `v` only if `s` is currently unspecified
    for `f`; existing specifications are preserved. This implements the
    default-fill semantics of feature-filling rules in lexical phonology
    [kiparsky-1982] [archangeli-1988]. -/
def fillFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨Features.Bundle.merge s.spec
    (Function.update (fun _ => none : Feature → Option Bool) f (some v))⟩

/-- Categorical feature spreading from context: the target `s`, when
    unspecified for `f`, takes the `f`-value of `ctx`; already-specified
    targets and features other than `f` are untouched. When `ctx` is
    itself unspecified for `f`, the target stays unspecified.

    This is a [keating-1988] *context rule*: the target acquires a categorical
    feature value from its neighbour and that value blocks further
    interactions. It is **distinct from** her gradient phonetic interpolation
    (her unspecified /h/ example), in which an unspecified segment stays
    unspecified and the phonetics builds a continuous trajectory through it;
    gradient phonetic interpolation is out of scope at this categorical-featural
    substrate. -/
def fillFromContext (s : Segment) (f : Feature) (ctx : Segment) : Segment :=
  ⟨Features.Bundle.merge s.spec
    (Function.update (fun _ => none : Feature → Option Bool)
       f (ctx.spec f))⟩

/-! ### Effect on the modified feature -/

@[simp] theorem unsetFeature_unspecified (s : Segment) (f : Feature) :
    (s.unsetFeature f).Unspecified f :=
  Function.update_self _ _ _

@[simp] theorem setFeature_hasValue (s : Segment) (f : Feature) (v : Bool) :
    (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFeature_hasValue_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (v : Bool) :
    (s.fillFeature f v).HasValue f v := by
  simp only [Segment.fillFeature, Segment.HasValue, Features.Bundle.merge,
    show s.spec f = none from h, Function.update_self]

theorem fillFeature_spec_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (v : Bool) :
    (s.fillFeature f v).spec f = some w := by
  simp only [Segment.fillFeature, Features.Bundle.merge,
    show s.spec f = some w from h]

theorem fillFromContext_spec_self_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = ctx.spec f := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s.spec f = none from h, Function.update_self]

theorem fillFromContext_spec_self_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = some w := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s.spec f = some w from h]

/-! ### Spec preserved on other features -/

@[simp] theorem unsetFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) :
    (s.unsetFeature f).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem setFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.fillFeature f v).spec g = s.spec g := by
  simp only [Segment.fillFeature, Features.Bundle.merge,
    Function.update_of_ne (Ne.symm h)]
  cases s.spec g <;> rfl

@[simp] theorem fillFromContext_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx).spec g = s.spec g := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    Function.update_of_ne (Ne.symm h)]
  cases s.spec g <;> rfl

end Segment

/-! ### Sonority -/

/-- The abstract sonority hierarchy ([clements-1990]): what the synchronic
    grammar operates on, ordering segments from least to most sonorous.

    | Rank | Class     |
    |------|-----------|
    |  0   | Stop      |
    |  1   | Fricative |
    |  2   | Nasal     |
    |  3   | Liquid    |
    |  4   | Glide     |
    |  5   | Vowel     |

    For the finer 8-level scale that splits obstruents by voice, see
    `SonorityClass`. -/
inductive Sonority where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace Sonority

/-- Numeric rank (0 = least sonorous). -/
def rank : Sonority → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h => by cases a <;> cases b <;> simp_all [rank]

/-- The sonority of a segment, read off its features
    ([hayes-2009], [clements-1990]). -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then .fricative else .stop
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

end Sonority

/-! ### The Parker sonority scale -/

/-- The 8-level Parker sonority partition ([parker-2002]) — a refinement of
    `Sonority` that splits obstruents by [±continuant] and [±voice]. This is the
    sonority *scale*; it is distinct from the natural-class predicates above
    (`Segment.IsVowel` &c.), which are feature membership.

    Crucially [parker-2002] ranks voiced stops above voiceless fricatives
    (`vds = 3 > vlf = 2`) — his intensity-based default universal, reversible in
    particular languages. The finer granularity is needed for sonority-
    conditioned gradient phenomena such as Tarifit intrusive vowels
    ([afkir-zellou-2025]). -/
inductive SonorityClass where
  | vls    -- voiceless stops: [−son, −cont, −voice]
  | vds    -- voiced stops: [−son, −cont, +voice]
  | vlf    -- voiceless fricatives: [−son, +cont, −voice]
  | vdf    -- voiced fricatives: [−son, +cont, +voice]
  | nasal  -- nasals: [+son, −approx]
  | liquid -- liquids/taps: [+son, +approx, +cons]
  | glide  -- glides: [+son, +approx, −cons, −syll]
  | vowel  -- vowels: [+son, +approx, −cons, +syll]
  deriving DecidableEq, Repr

namespace SonorityClass

/-- Parker's default universal 8-level ranking ([parker-2002]): voiced stops
    (`vds = 3`) outrank voiceless fricatives (`vlf = 2`). -/
def parkerSonority : SonorityClass → Nat
  | .vls => 1 | .vlf => 2 | .vds => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-- Classify a segment on the Parker 8-level scale: as `Sonority.ofSegment`,
    but additionally splitting obstruents by [±voice] ([parker-2002]). -/
def ofSegment (s : Segment) : SonorityClass :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then
      if s.HasValue .voice true then .vdf else .vlf
    else
      if s.HasValue .voice true then .vds else .vls
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-- Coarsen to the substance-free `Sonority`, collapsing the voicing split. -/
def toSonority : SonorityClass → Sonority
  | .vls | .vds => .stop
  | .vlf | .vdf => .fricative
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

end SonorityClass

/-- Parker sonority of a segment (convenience). -/
def parkerSonorityOf (s : Segment) : Nat :=
  (SonorityClass.ofSegment s).parkerSonority

/-- Parker sonority is strictly monotone: the ranking is a total order. -/
theorem parker_strictly_monotone (a b : SonorityClass) (h : a ≠ b) :
    SonorityClass.parkerSonority a < SonorityClass.parkerSonority b ∨
    SonorityClass.parkerSonority a > SonorityClass.parkerSonority b := by
  cases a <;> cases b <;> simp_all [SonorityClass.parkerSonority]

end Phonology
