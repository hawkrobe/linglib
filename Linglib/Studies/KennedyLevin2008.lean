module

public import Linglib.Core.Algebra.Order.Interval.Set.Group
public import Linglib.Core.Order.Interval.Set.ProjIcc
public import Linglib.Semantics.Degree.Basic
public import Linglib.Studies.HayKennedyLevin1999

/-!
# Kennedy and Levin (2008): Measure of Change

This file formalizes Kennedy and Levin's account of variable telicity in degree achievements.
Following Kennedy and McNally, a comparative such as *wider than the carpet* measures on the part
of its adjective's scale from the comparative standard up, which Kennedy and Levin call a difference
function. A degree achievement is built on a measure of change, the difference function at the
degree its argument has when the event begins, applied when it ends. The scale of a measure of
change always has a least degree and inherits any greatest degree of the adjective's scale, so
Interpretive Economy admits a minimum standard for every degree achievement, giving the atelic
comparative reading, and a maximum standard, giving the telic reading, exactly when the adjective's
scale is closed above; the telic reading entails the atelic one and is preferred. *Widen* thus has
no telic reading and never means *become wide*.

The account agrees with Hay, Kennedy and Levin's difference values on both readings and on
*completely* and *slightly*, and differs on measure phrases, which require at least their degree of
change here and exactly that degree there. The English fragment's degree achievements take the
Vendler class that Interpretive Economy gives their base scales.

## Implementation notes

* The difference function of `m` at `d` is `Set.projIci d ∘ m`, onto the ray `Set.Ici d` whose `⊥`
  and `⊤` are the derived zero and the inherited maximum, and the measure of change for `x` over
  an event from `i` to `f` is `Set.projIci (m x i) (m x f)`. The paper applies `m` to the initial
  and final intervals of the event. The amount of change is the distance above the derived zero,
  the positive part of the difference (`Set.coe_projIci_sub`).
* The minimum standard is read strictly, `⊥ < ·`, after the prose and Kennedy's positive form,
  though the verbal positive form is printed with `⪰`. An argument that begins with the greatest
  degree meets the maximum standard without changing, so the theorems relating the two readings
  assume it does not.
* An ordered additive group with a greatest element is trivial, so the comparison with Hay,
  Kennedy and Levin's additive difference values is stated against a maximal degree `top`, as
  their study does, not `⊤`.
* As printed, the denotation of *slightly* in (34b) has both relations reversed; the file follows
  the prose, a degree above the minimum and at most a small one.

## TODO

* Derive the telicity of the two readings from their truth conditions rather than from the
  standard. The atelic reading lacks `Aspect.HasSubintervalProperty`, since nothing changes over
  a point interval, so the atelic half needs a subinterval property relative to a minimal
  duration.

## References

* [C. Kennedy and B. Levin, *Measure of Change: The Adjectival Core of Degree Achievements*
  (2008)][kennedy-levin-2008]
* [C. Kennedy and L. McNally, *Scale Structure, Degree Modification, and the Semantics of Gradable
  Predicates* (2005)][kennedy-mcnally-2005]
* [J. Hay, C. Kennedy and B. Levin, *Scalar Structure Underlies Telicity in “Degree
  Achievements”* (1999)][hay-kennedy-levin-1999]
* [C. Kennedy, *Vagueness and Grammar: The Semantics of Relative and Absolute Gradable Adjectives*
  (2007)][kennedy-2007]
-/

@[expose] public section

namespace KennedyLevin2008

open Degree Aspect Set

/-! ### Difference functions (23)–(24) -/

section Difference

variable {E δ : Type*} [LinearOrder δ] (μ : E → δ) (a b : E)

/-- At the minimum standard, the difference function at `b`'s degree holds of `a` exactly
when `a` has more of the property than `b` ((23)–(24)). -/
theorem comparative_iff : ⊥ < projIci (μ b) (μ a) ↔ comparativeSem μ a b .positive := by
  rw [bot_lt_projIci, comparativeSem_positive]

/-- At a maximum standard, a comparative would hold exactly when the positive form does,
unless the standard already has the greatest degree (fn. 16). -/
theorem comparative_eq_top_iff [OrderTop δ] (h : μ b ≠ ⊤) :
    projIci (μ b) (μ a) = ⊤ ↔ μ a = ⊤ := by
  rw [projIci_eq_top, or_iff_right h]

end Difference

/-! ### The measure of change and its readings (25)–(27) -/

section Readings

variable {α δ T : Type*} [LinearOrder δ] (m : α → T → δ) (x : α) (i f : T)

/-- Interpretive Economy admits the minimum standard on the scale of a measure of change, the
maximum exactly when the adjective's scale has a greatest degree, and never the contextual
standard (§7.3.3). -/
theorem admits_iff {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔
      s = .minEndpoint ∨ s = .maxEndpoint ∧ (Boundedness.ofOrder δ).HasMax := by
  rw [Boundedness.ofOrder_Ici, Boundedness.admits_withMin_iff]

/-- Without a greatest degree only the minimum standard is admitted, so *widen* has no telic
reading and does not mean *become wide* ((6)). -/
theorem admits_iff_of_noMaxOrder [NoMaxOrder δ] {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔ s = .minEndpoint := by
  simp [admits_iff]

/-- The preferred standard on the scale of a measure of change is the maximum when the
adjective's scale has one, and the minimum otherwise. -/
theorem defaultStandard_eq :
    (Boundedness.ofOrder (Ici (m x i))).defaultStandard =
      if (Boundedness.ofOrder δ).HasMax then .maxEndpoint else .minEndpoint := by
  rw [Boundedness.ofOrder_Ici, Boundedness.defaultStandard_withMin]

/-- The minimum-standard reading has the truth conditions of the comparative, the argument
ending the event with more of the property than it began with ((27)). -/
theorem minStandard_iff : ⊥ < projIci (m x i) (m x f) ↔ comparativeSem (m x) f i .positive :=
  comparative_iff (m x) f i

variable [OrderTop δ]

/-- Unless the argument begins with the greatest degree, the maximum-standard reading holds
exactly when it ends with that degree, as the positive form of the adjective requires ((27)). -/
theorem maxStandard_iff (h : m x i ≠ ⊤) : projIci (m x i) (m x f) = ⊤ ↔ m x f = ⊤ :=
  comparative_eq_top_iff (m x) f i h

/-- Unless the argument begins with the greatest degree, the telic reading entails the atelic
one. -/
theorem minStandard_of_maxStandard (h : m x i ≠ ⊤) (hmax : projIci (m x i) (m x f) = ⊤) :
    ⊥ < projIci (m x i) (m x f) := by
  rw [bot_lt_projIci, (maxStandard_iff m x i f h).1 hmax]
  exact h.lt_top

end Readings

/-! ### Measure phrases and degree modifiers (32)–(34) -/

section Modifiers

open HayKennedyLevin1999

variable {α δ T : Type*} [AddCommGroup δ] [LinearOrder δ] [IsOrderedAddMonoid δ]
  (m : α → T → δ) (x : α) (i f : T)

/-- The minimum-standard reading is the reading of [hay-kennedy-levin-1999] with the
difference value "some amount". -/
theorem minStandard_iff_describes_someAmount :
    ⊥ < projIci (m x i) (m x f) ↔ Describes m x someAmount i f := by
  rw [bot_lt_projIci, describes_iff_sub_mem, someAmount, mem_Ioi, sub_pos]

omit [IsOrderedAddMonoid δ] in
/-- Against a maximal degree `top` above the initial degree, the maximum-standard reading, which
*completely* also gives ((34a)), is the reading of [hay-kennedy-levin-1999] with *completely*. -/
theorem maxStandard_iff_describes_completely {top : δ} (h : m x i < top) :
    (projIci (m x i) (m x f) : δ) = top ↔ Describes m x (completely top (m x i)) i f := by
  rw [coe_projIci, describes_iff_sub_mem, completely, mem_singleton_iff, sub_left_inj,
    max_eq_iff]
  exact ⟨fun h' ↦ h'.elim (fun h' ↦ absurd h'.1 h.ne) And.left,
    fun h' ↦ .inr ⟨h', h' ▸ h.le⟩⟩

/-- *Slightly*, a positive change up to a small degree `s` ((34b)), is the reading of
[hay-kennedy-levin-1999] with *slightly*. -/
theorem slightly_iff_describes_slightly (s : Ici (m x i)) :
    ⊥ < projIci (m x i) (m x f) ∧ projIci (m x i) (m x f) ≤ s ↔
      Describes m x (slightly ((s : δ) - m x i)) i f := by
  rw [bot_lt_projIci, ← Subtype.coe_le_coe, coe_projIci, max_le_iff, describes_iff_sub_mem,
    slightly, mem_Ioc, sub_pos, sub_le_sub_iff_right]
  exact and_congr_right fun _ ↦ and_iff_right s.2

/-- For a positive degree `n`, the amount of change is at least `n`, as a measure phrase requires
((32)–(33)), exactly when the event is described by the difference values of at least `n`. -/
theorem measurePhrase_iff {n : δ} (hn : 0 < n) :
    n ≤ (projIci (m x i) (m x f) : δ) - m x i ↔ Describes m x (Ici n) i f := by
  rw [coe_projIci_sub, posPart_def, le_sup_iff, or_iff_left hn.not_ge, describes_iff_sub_mem,
    mem_Ici]

/-- The exact difference value that [hay-kennedy-levin-1999] give a measure phrase entails
the at-least reading. -/
theorem le_of_describes_measurePhrase {n : δ} (hn : 0 < n)
    (h : Describes m x (measurePhrase n) i f) :
    n ≤ (projIci (m x i) (m x f) : δ) - m x i :=
  (measurePhrase_iff m x i f hn).2 (describes_iff_sub_mem.2 (describes_iff_sub_mem.1 h).ge)

end Modifiers

/-! ### The English degree achievements -/

/-- For any measure function into a dimension's degrees, a degree achievement on the dimension
is by default an accomplishment when the preferred standard on the scale of its measure of
change is the maximum, and an activity otherwise. -/
theorem defaultVendlerClass_eq {α T : Type*} (d : ScalarDimension) (m : α → T → d.degree)
    (x : α) (i : T) :
    d.defaultVendlerClass =
      if (Boundedness.ofOrder (Ici (m x i))).defaultStandard = .maxEndpoint then .accomplishment
      else .activity := by
  simp only [Boundedness.ofOrder_Ici, Boundedness.ofOrder_degreeShape]
  rfl

/-- `daVerbs` lists the fragment's degree achievements. -/
def daVerbs : List Verb :=
  [English.Verbs.bend.toVerb, English.Verbs.boil.toVerb,
   English.Verbs.rust.toVerb, English.Verbs.increase.toVerb,
   English.Verbs.clean.toVerb, English.Verbs.dry.toVerb, English.Verbs.straighten.toVerb,
   English.Verbs.flatten.toVerb, English.Verbs.open_.toVerb,
   English.Verbs.lengthen.toVerb, English.Verbs.widen.toVerb,
   English.Verbs.cool.toVerb, English.Verbs.warm.toVerb]

/-- Every degree achievement's Vendler class is the default of its base scale. -/
theorem da_vendler_classes_agree :
    ∀ v ∈ daVerbs, v.vendlerClass = v.changeScale.map (·.defaultVendlerClass) := by
  decide

/-- The adjective–verb pairs of the fragment are *clean*, *dry*, *straight*, *flat* and *open*
with closed scales, and *long*, *wide*, *cool* and *warm* with open ones. -/
def pairs : List (GradableAdjective × Verb) :=
  [(English.Adjectives.clean, English.Verbs.clean.toVerb),
   (English.Adjectives.dry, English.Verbs.dry.toVerb),
   (English.Adjectives.straight, English.Verbs.straighten.toVerb),
   (English.Adjectives.flat, English.Verbs.flatten.toVerb),
   (English.Adjectives.open_, English.Verbs.open_.toVerb),
   (English.Adjectives.long, English.Verbs.lengthen.toVerb),
   (English.Adjectives.wide, English.Verbs.widen.toVerb),
   (English.Adjectives.cool, English.Verbs.cool.toVerb),
   (English.Adjectives.warm, English.Verbs.warm.toVerb)]

/-- A degree achievement measures on its adjective's scale. -/
theorem adjective_verb_scales :
    ∀ p ∈ pairs, p.2.changeScale = some p.1.scaleType := by
  decide

/-- A degree achievement takes *in X* exactly when its scale is closed above, and *for X*
otherwise ((1), (6)). -/
theorem inX_iff_hasMax (b : Boundedness) :
    (inXPrediction b.defaultVendlerClass = .accept ↔ b.HasMax) ∧
      (forXPrediction b.defaultVendlerClass = .accept ↔ ¬ b.HasMax) := by
  cases b <;> decide

/-- On the fragment, *bend*, *boil*, *clean*, *dry*, *straighten*, *flatten* and *open* take
*in X*, and *rust*, *increase*, *lengthen*, *widen*, *cool* and *warm* take *for X*. -/
theorem diagnostics :
    ∀ v ∈ daVerbs, ∃ b ∈ v.changeScale,
      (v.vendlerClass.map inXPrediction = some .accept ↔ b.HasMax) ∧
        (v.vendlerClass.map forXPrediction = some .accept ↔ ¬ b.HasMax) := by
  decide

end KennedyLevin2008
