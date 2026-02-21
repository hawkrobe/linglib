import Linglib.Core.Scale
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Maximal Informativity and Temporal *in*-Adverbials

Rouillard (2026) "Maximal informativity accounts for the distribution of
temporal *in*-adverbials" (*Linguistics and Philosophy* 49:1–56).

## Core Contribution

Temporal *in*-adverbials (TIAs) lead a double life:
- **E-TIAs** ("wrote a paper *in three days*"): measure event durations.
  Acceptable only with telic VPs.
- **G-TIAs** ("hasn't been sick *in three days*"): measure gap durations.
  Negative polarity items: acceptable only in negative perfects.

Both distributional restrictions derive from a single principle:

**Maximal Informativity Principle (MIP)**: for some constituent of the LF
in which a TIA appears, the numeral in the TIA's measure phrase must be
capable of being maximally informative. If no number can be maximally
informative (information collapse), the TIA is blocked.

## Architecture

```
Mereology (CUM, DIV, QUA)  ──▷  scalar properties of derived TIA meanings
         │                                    │
     telicity                            informativity
         │                                    │
         ▼                                    ▼
E-TIA licensing ◁───── MIP ─────▷ G-TIA polarity sensitivity
                                         │
                              open PTS + closed runtime
                                 (from Time.lean)
```

## Sections

1. Maximal informativity (max⊨)
2. Measure functions and `pts` (prior time spans)
3. E-TIA semantics: `in` as event-level map function
4. G-TIA semantics: `in` as perfect-level identity map
5. The MIP as a licensing condition
6. Information collapse theorems
7. Bridge: Kennedy open/closed scales ↔ TIA licensing

## References

- Rouillard, V. (2026). Maximal informativity accounts for the distribution
  of temporal *in*-adverbials. *L&P* 49:1–56.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Krifka, M. (1998). The origins of telicity.
- Fox, D. & Hackl, M. (2006). The universal density of measurement.
- Beck, S. & Rullmann, H. (1999). A flexible approach to exhaustivity in questions.
- Kennedy, C. (2007). Vagueness and grammar.
-/

namespace Semantics.Montague.Sentence.MaximalInformativity

open Core.Time
open Semantics.Lexical.Verb.ViewpointAspect
open Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Maximal Informativity
-- ════════════════════════════════════════════════════

variable {W Time : Type*} [LinearOrder Time]

-- Re-export maximal informativity from Core.Scale (canonical definitions).
-- Fox & Hackl (2007) §4 / Rouillard (2026) eq. (75).
open Core.Scale (IsMaxInf HasMaxInf InformationCollapse)

-- ════════════════════════════════════════════════════
-- § 2. Scalarity (specialized to ℕ-indexed families)
-- ════════════════════════════════════════════════════

open Core.Scale in
/-- Upward scalarity for ℕ-indexed families.
    Specialization of `Core.Scale.IsUpwardMonotone` to ℕ.
    Rouillard (2026) p. 24: outputs of (77) are totally ordered by entailment,
    smaller values entail larger ones.
    Beck & Rullmann (1999): the maximally informative number is the smallest
    value returning a true proposition. -/
abbrev UpwardScalar (P : ℕ → W → Prop) : Prop :=
  IsUpwardMonotone P

open Core.Scale in
/-- Downward scalarity for ℕ-indexed families.
    Specialization of `Core.Scale.IsDownwardMonotone` to ℕ. -/
abbrev DownwardScalar (P : ℕ → W → Prop) : Prop :=
  IsDownwardMonotone P

/-- Upward scalar properties have maximally informative elements:
    the smallest true value is max⊨ (it entails all others).
    This is the abstract version of Rouillard's argument for why
    E-TIAs with telic VPs are acceptable. -/
theorem upwardScalar_hasMaxInf (P : ℕ → W → Prop) (hUS : UpwardScalar P)
    (w : W) (n : ℕ) (hn : P n w) (hMin : ∀ m, m < n → ¬ P m w) :
    IsMaxInf P n w := by
  refine ⟨hn, fun m hm w' hn' => ?_⟩
  by_cases h : n ≤ m
  · exact hUS n m h w' hn'
  · push_neg at h; exact absurd hm (hMin m h)

/-- Bimonotone ℕ-families (both upward and downward scalar) make every
    value true at every world where any value is true.
    Rouillard (2026) p. 25: the property in (80) is both upward and downward
    scalar — equivalently, it is a constant function. This is information
    collapse. Derived from `Core.Scale.bimonotone_constant`. -/
theorem biscalar_constant_collapse (P : ℕ → W → Prop)
    (hDS : DownwardScalar P) (hUS : UpwardScalar P)
    (w : W) (n : ℕ) (hn : P n w) :
    ∀ m, P m w := by
  intro m
  exact ((Core.Scale.bimonotone_constant P hUS hDS) n m w).mp hn

-- ════════════════════════════════════════════════════
-- § 3. Measure Functions and Prior Time Spans
-- ════════════════════════════════════════════════════

/-- A temporal measure function: assigns positive durations to intervals.
    Rouillard (2026) §2.2.2, eq. (5)–(7): μ is additive over non-overlapping
    times and positive. -/
structure MeasureFun (Time : Type*) [LinearOrder Time] where
  /-- The measure of an interval in some unit φ -/
  μ : Interval Time → ℕ
  /-- Any interval can be extended to a superinterval with a given larger measure.
      Rouillard (2026): temporal measure units (days, hours) are additive, so
      any interval can be padded to achieve any target measure ≥ current. -/
  extensible : ∀ (i : Interval Time) (m : ℕ), μ i ≤ m →
    ∃ j : Interval Time, i.subinterval j ∧ μ j = m
  /-- Any interval can be subdivided to a subinterval with a given smaller measure.
      Rouillard (2026): temporal measure units are additive, so any interval
      can be trimmed to achieve any target measure ≤ current. -/
  subdivisible : ∀ (i : Interval Time) (m : ℕ), m ≤ μ i →
    ∃ j : Interval Time, j.subinterval i ∧ μ j = m

/-- Prior time span: the maximal interval right-bounded by t with measure n.
    Rouillard (2026) eq. (50):
    pts(n, φ, t¹) := max⊑ᵢ(λt².t² ∈ S ∧ ∃t³[μ_φ(t³) = n ∧ rb(t¹, t²) ∧ t² ⊑ᵢ t³])
    Simplified: pts(n, μ, s) is the interval consisting of every moment
    inclusively ordered between s and the moment n φ-units prior to s. -/
def pts (n : ℕ) (μ : MeasureFun Time) (s : Time)
    (interval : Interval Time) : Prop :=
  μ.μ interval = n ∧ interval.finish = s

-- ════════════════════════════════════════════════════
-- § 4. E-TIA Semantics
-- ════════════════════════════════════════════════════

/-- The preposition *in* as an event-level adverbial (E-TIA reading).
    Rouillard (2026) eq. (62): ⟦in⟧ := λM_σi λt λx_σ . M(x) ⊑ᵢ t.
    For E-TIAs, M = τ (runtime function): the event's runtime is included
    in the time denoted by the measure phrase.

    Type: (e → Interval Time) → Time → (e → Prop)
    Instantiation for E-TIA: M = Eventuality.τ -/
def inETIA (e : Eventuality Time) (bound : Interval Time) : Prop :=
  e.τ.subinterval bound

/-- E-TIA derived property: for each number n, the property that at world w
    there exists a P-event whose runtime is included in an n-unit time
    ending at g(1).
    Rouillard (2026) eq. (77):
    λnλw.∃t[μ_d(t) = n ∧ ∃e[P(e)(w) ∧ τ_w(e) ⊑ᵢ g(1) ∧ τ_w(e) ⊑ᵢ t]] -/
def eTIAProperty (P : EventPred W Time) (μ : MeasureFun Time)
    (g1 : Interval Time) : ℕ → W → Prop :=
  fun n w => ∃ t : Interval Time, μ.μ t = n ∧
    ∃ e : Eventuality Time, P w e ∧ e.τ.subinterval g1 ∧ e.τ.subinterval t

-- ════════════════════════════════════════════════════
-- § 5. G-TIA Semantics
-- ════════════════════════════════════════════════════

/-- G-TIA derived property: for each number n, the property that at world w
    an event's runtime is included in the prior time span pts(n, d, s).
    Rouillard (2026) eq. (94), revised with open PTS (101):
    λnλw.∃e[P(e)(w) ∧ τ_w(e) ⊑ᵢ o(pts(n, d, s))] -/
def gTIAProperty (P : EventPred W Time) (μ : MeasureFun Time)
    (s : Time) : ℕ → W → Prop :=
  fun n w => ∃ interval : Interval Time,
    pts n μ s interval ∧
    ∃ e : Eventuality Time, P w e ∧ e.τ.subinterval interval

-- ════════════════════════════════════════════════════
-- § 6. The Maximal Informativity Principle
-- ════════════════════════════════════════════════════

/-- **Maximal Informativity Principle (MIP)**.
    Rouillard (2026) eq. (92):
    Given a numeral N, a measure word M, an index j, and a map function F,
    a constituent of the form [ [ N M ] j … [ in F ] tⱼ ] is licensed only
    if it is contained in a constituent γ such that, for some w¹,
    max⊨(w¹, λnλw². ⟦γ[N ↦ proₖ]⟧) = ⟦N⟧.

    The TIA is licensed iff the numeral can be maximally informative
    in some constituent γ containing it. -/
def MIP_Licensed (derivedProp : ℕ → W → Prop) (n : ℕ) : Prop :=
  ∃ w : W, IsMaxInf derivedProp n w

/-- E-TIA is MIP-licensed iff the derived E-TIA property has a maximally
    informative numeral at some world. -/
def ETIA_Licensed (P : EventPred W Time) (μ : MeasureFun Time)
    (g1 : Interval Time) (n : ℕ) : Prop :=
  MIP_Licensed (eTIAProperty P μ g1) n

/-- G-TIA is MIP-licensed (in positive environment) iff the derived G-TIA
    property has a maximally informative numeral at some world. -/
def GTIA_Licensed_Pos (P : EventPred W Time) (μ : MeasureFun Time)
    (s : Time) (n : ℕ) : Prop :=
  MIP_Licensed (gTIAProperty P μ s) n

/-- G-TIA under negation: the negated G-TIA property. -/
def gTIAPropertyNeg (P : EventPred W Time) (μ : MeasureFun Time)
    (s : Time) : ℕ → W → Prop :=
  fun n w => ¬ gTIAProperty P μ s n w

/-- G-TIA is MIP-licensed under negation. -/
def GTIA_Licensed_Neg (P : EventPred W Time) (μ : MeasureFun Time)
    (s : Time) (n : ℕ) : Prop :=
  MIP_Licensed (gTIAPropertyNeg P μ s) n

-- ════════════════════════════════════════════════════
-- § 7. Information Collapse and Licensing Theorems
-- ════════════════════════════════════════════════════

/-- **Subinterval property for event predicates** (mereological version).
    Rouillard (2026) eq. (82): SUB(P) iff every part of a P-event's runtime
    that is also the runtime of some event is the runtime of a P-event.
    States and activities have this property; accomplishments/achievements lack it. -/
def HasSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∀ (e₂ : Eventuality Time), e₂.τ = t →
    P w e₂

/-- **Closed subinterval property** (CSUB).
    Rouillard (2026) eq. (111): for any portion t of a P-event's runtime,
    the closed counterpart c(t) is the runtime of some P-event.
    Stronger than SUB: prevents gaps in the runtime of atelic events. -/
def HasClosedSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∃ (e₂ : Eventuality Time), e₂.τ = t ∧ P w e₂

/-- **E-TIA Information Collapse for Atelic VPs**.
    When a VP predicate has the subinterval property (is atelic/DIV),
    the E-TIA property is both upward and downward monotone (constant),
    so no numeral is maximally informative → the E-TIA is blocked.
    Rouillard (2026) §4.1.1: the interaction of the subinterval property
    with E-TIAs results in information collapse.

    Proof: For any world w where eTIAProperty holds at n, we show it holds
    at m for arbitrary m. Given P-event e at w:
    - If m ≤ μ(τ(e)): subdivide τ(e) to get j ⊆ τ(e) with μ(j) = m.
      By SUB, ⟨j⟩ is a P-event. Since j ⊆ τ(e) ⊆ g1, j ⊆ g1.
    - If m ≥ μ(τ(e)): extend τ(e) to get j ⊇ τ(e) with μ(j) = m.
      Same event e works. -/
theorem eTIA_atelic_collapse (P : EventPred W Time) (μ : MeasureFun Time)
    (g1 : Interval Time) (hSub : HasSubintervalProp P) :
    Core.Scale.IsConstant (α := ℕ) (eTIAProperty P μ g1) := by
  suffices h : ∀ n m w, eTIAProperty P μ g1 n w → eTIAProperty P μ g1 m w from
    fun n m w => ⟨h n m w, h m n w⟩
  intro n m w ⟨_, _, e, hP, hg1, _⟩
  rcases le_total m (μ.μ e.τ) with hle | hge
  · obtain ⟨j, hj_sub, hj_μ⟩ := μ.subdivisible e.τ m hle
    exact ⟨j, hj_μ, ⟨j⟩, hSub e w hP j hj_sub ⟨j⟩ rfl,
      ⟨le_trans hg1.1 hj_sub.1, le_trans hj_sub.2 hg1.2⟩, ⟨le_refl _, le_refl _⟩⟩
  · obtain ⟨j, hj_sup, hj_μ⟩ := μ.extensible e.τ m hge
    exact ⟨j, hj_μ, e, hP, hg1, hj_sup⟩

/-- **Quantized predicates yield upward scalar E-TIA properties**.
    Rouillard (2026) §4.1.1: when P is QUA (telic), the E-TIA property in
    (77) is upward scalar — propositions from smaller n entail those from
    larger n. The maximally informative number is the smallest n returning
    a true proposition (= the actual duration of the event).

    This is the structural explanation for why E-TIAs are acceptable with
    telic VPs: there exists a unique maximally informative number.
    Proof: The same event e works. Extend the containing time t (with
    μ(t) = n) to j ⊇ t with μ(j) = m ≥ n via `MeasureFun.extensible`.
    Since τ(e) ⊆ t ⊆ j, the witness transfers. -/
theorem eTIA_telic_upwardScalar (P : EventPred W Time) (μ : MeasureFun Time)
    (g1 : Interval Time) :
    UpwardScalar (eTIAProperty P μ g1) := by
  intro n m hnm w ⟨t, hμ, e, hP, hg1, hsub⟩
  obtain ⟨j, hj_sup, hj_μ⟩ := μ.extensible t m (by omega)
  exact ⟨j, hj_μ, e, hP, hg1,
    ⟨le_trans hj_sup.1 hsub.1, le_trans hsub.2 hj_sup.2⟩⟩

-- ════════════════════════════════════════════════════
-- § 8. G-TIA Polarity from Open Intervals
-- ════════════════════════════════════════════════════

/-- **No smallest open PTS can include a closed runtime**.
    Rouillard (2026) §4.2.2, key insight: given dense time, if event runtimes
    are closed and PTSs are open, there can never be a smallest open interval
    to *include* a closed time — because by density, there is always a moment
    between the open boundary and the closed boundary, giving a smaller PTS.

    This is the structural reason why G-TIAs in positive environments suffer
    information collapse: the G-TIA property is downward scalar with no minimum.

    Proof: By density (`DenselyOrdered`), find m with pts_open.left < m <
    runtime.start. The open interval ]m, pts_open.right[ still contains
    runtime (m < runtime.start and runtime.finish ≤ pts_open.right) and
    is strictly contained in pts_open (pts_open.left < m). -/
theorem no_smallest_open_including_closed
    [DenselyOrdered Time]
    (runtime : Interval Time) -- closed event runtime
    (pts_open : Interval.GInterval Time) -- open PTS
    (_h_open : pts_open.isOpen)
    (h_contains : runtime.subinterval pts_open.toInterval)
    (h_nontrivial : pts_open.left < runtime.start) :
    ∃ pts' : Interval.GInterval Time,
      pts'.isOpen ∧
      runtime.subinterval pts'.toInterval ∧
      pts'.toInterval.subinterval pts_open.toInterval ∧
      pts'.left ≠ pts_open.left := by
  obtain ⟨m, hm_left, hm_right⟩ := DenselyOrdered.dense _ _ h_nontrivial
  have hm_valid : m ≤ pts_open.right :=
    le_trans (le_of_lt hm_right) (le_trans runtime.valid h_contains.2)
  exact ⟨⟨m, pts_open.right, .open_, .open_, hm_valid⟩,
    ⟨rfl, rfl⟩,
    ⟨le_of_lt hm_right, h_contains.2⟩,
    ⟨le_of_lt hm_left, le_refl _⟩,
    hm_left.ne'⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge: Kennedy Scales ↔ TIA Licensing
-- ════════════════════════════════════════════════════

/-! The analogy between Kennedy's (2007) scale typology for gradable adjectives
    and Rouillard's (2026) TIA licensing is structural — both use
    `Core.Scale.Boundedness` to classify their scales, and
    `Boundedness.isLicensed` derives the same licensing prediction from
    the classification:

    | Kennedy (Adjectives)              | Rouillard (TIAs)                     |
    |------------------------------------|--------------------------------------|
    | Open scale (tall, expensive)       | Atelic VP / DIV predicate            |
    | → context-dependent threshold      | → information collapse, no max⊨     |
    | → RGA: "??completely tall"         | → E-TIA blocked: "*was sick in 3d"  |
    |                                    |                                      |
    | Closed scale (full, empty)         | Telic VP / QUA predicate             |
    | → scale-structure standard (max/min)| → upward scalar, max⊨ exists       |
    | → AGA: "completely full" ✓         | → E-TIA licensed: "wrote in 3d" ✓  |
    |                                    |                                      |
    | Interpretive Economy               | Maximal Informativity Principle       |
    | → maximize conventional meaning    | → maximize numeral contribution      |

    Kennedy's `Boundedness.open_` (= Krifka's DIV),
    and Kennedy's `Boundedness.closed` (= Krifka's QUA).

    For G-TIAs, the relevant "scale" is the PTS: open PTSs behave like
    open scales (no inherent bound → no maximum standard), while closed
    runtimes behave like closed scales (inherent bound → standard exists). -/

open Core.Scale

/-- Vendler class determines scale boundedness via the Kennedy–Rouillard
    isomorphism (`Core.Scale`).
    Telic VPs → closed/bounded (max⊨ exists).
    Atelic VPs → open/unbounded (information collapse). -/
def scaleBoundedness : VendlerClass → Boundedness
  | .accomplishment | .achievement => .closed
  | .state | .activity => .open_

/-- Telic VPs map to closed/bounded scales (E-TIA licensed). -/
theorem telic_closed (c : VendlerClass) (h : c.telicity = .telic) :
    scaleBoundedness c = .closed := by
  cases c <;> simp [VendlerClass.telicity, scaleBoundedness] at * <;> assumption

/-- Atelic VPs map to open/unbounded scales (E-TIA blocked). -/
theorem atelic_open (c : VendlerClass) (h : c.telicity = .atelic) :
    scaleBoundedness c = .open_ := by
  cases c <;> simp [VendlerClass.telicity, scaleBoundedness] at * <;> assumption

/-- Telic VPs are licensed: telicity → closed boundedness → `isLicensed`. -/
theorem telic_predicts_licensing (c : VendlerClass) (h : c.telicity = .telic) :
    (scaleBoundedness c).isLicensed = true := by
  rw [telic_closed c h]; rfl

/-- Atelic VPs are blocked: atelicity → open boundedness → ¬`isLicensed`. -/
theorem atelic_predicts_blocking (c : VendlerClass) (h : c.telicity = .atelic) :
    (scaleBoundedness c).isLicensed = false := by
  rw [atelic_open c h]; rfl

-- ════════════════════════════════════════════════════
-- § 10. Revised Perfect (PERF quantifies over open intervals)
-- ════════════════════════════════════════════════════

/-- **Revised PERFECT**: the perfect's domain of quantification is restricted
    to open intervals (S ∩ O in Rouillard's notation).
    Rouillard (2026) eq. (107):
    ⟦PERF⟧ := λI_it λt¹.∃t² ∈ S ∩ O[rb(t¹, t²) ∧ I(t²)]

    This revision is the key to deriving G-TIA polarity sensitivity:
    - In positive environments, the smallest open PTS to include a closed
      runtime cannot exist (by density), so no number is maximally informative.
    - In negative environments, the *largest* open PTS to *exclude* a closed
      runtime always exists (the one abutting the runtime's boundary),
      so a maximally informative number exists. -/
def PERF_open (p : IntervalPred W Time) : PointPred W Time :=
  λ s => ∃ pts : Interval Time, RB pts s.time ∧ p s.world pts
  -- The openness constraint is enforced at the level of the G-TIA
  -- semantics rather than structurally in PERF, since the basic Interval
  -- type is always closed. The semantic effect is captured in
  -- gTIAProperty and the no_smallest_open_including_closed theorem.

-- ════════════════════════════════════════════════════
-- § 11. Numeral Semantics Bridge
-- ════════════════════════════════════════════════════

/-! E-TIA expressions are upward monotone in the numeral (Rouillard 2026 §3):
    "wrote a paper in three days" entails "wrote a paper in four days"
    because τ(e) ⊑ t with |t| = 3 implies τ(e) ⊑ t' with |t'| = 4.

    This upward monotonicity is a property of the *expression* "in n days"
    (due to the containment semantics of *in*), NOT of the numeral itself.
    The numeral "three" can be exact (Kennedy 2015 de-Fregean type-shift:
    closed scale → Class B → exact meaning), and the expression is still
    upward monotone because containment is monotone in the interval size.

    Indeed, exact numerals are arguably REQUIRED: with LB numerals (|t| ≥ n),
    ∃t. |t| ≥ n ∧ τ(e) ⊑ t is trivially true for any event (pick a large
    enough interval). Only exact numerals (|t| = n) make "in n days"
    informative: it then asserts |τ(e)| ≤ n.

    The exact reading of the DURATION ("took exactly 3 days, not 2") arises
    via scalar implicature over the upward-monotone expression, parallel to
    Kennedy's analysis of "the glass is full" (endpoint standard + exactness). -/

/-- E-TIA expressions are upward monotone in the numeral: if the event fits
    in an n-unit time, it fits in an m-unit time for m ≥ n. This follows
    from the containment semantics of *in* (τ(e) ⊑ t), not from the
    numeral being lower-bounded. Compatible with Kennedy (2015) exact
    numerals on closed scales. -/
theorem eTIA_expression_upward_monotone (P : EventPred W Time) (μ : MeasureFun Time)
    (g1 : Interval Time) (n m : ℕ) (hnm : n ≤ m) (w : W)
    (h : eTIAProperty P μ g1 n w) :
    eTIAProperty P μ g1 m w :=
  eTIA_telic_upwardScalar P μ g1 n m hnm w h

-- ════════════════════════════════════════════════════
-- § 12. Mereology Bridge: DIV → Closed Subinterval Property
-- ════════════════════════════════════════════════════

/-! Rouillard's closed subinterval property (CSUB, eq. 111) is the temporal
    analog of Krifka/Champollion's DIV (divisive reference). DIV says every
    part of a P-entity is itself P; CSUB says the closed counterpart of every
    subinterval of a P-event's runtime is itself a P-event's runtime.

    The bridge: if an event predicate is DIV (in the mereological sense from
    `Mereology.lean`), then it has the closed subinterval property (in the
    temporal sense needed for G-TIA polarity). -/

/-- DIV event predicates have the (plain) subinterval property.
    If P is downward-closed under the part-of relation on events,
    then any subinterval of a P-event's runtime that is itself some
    event's runtime is a P-event's runtime. -/
theorem div_implies_subintervalProp (P : EventPred W Time) :
    (∀ (e₁ e₂ : Eventuality Time) (w : W),
      P w e₁ → e₂.τ.subinterval e₁.τ → P w e₂) →
    HasSubintervalProp P := by
  intro hDiv e₁ w hP t hsub e₂ hτ
  have : e₂.τ = t := by simp [Eventuality.τ]; exact hτ
  exact hDiv e₁ e₂ w hP (this ▸ hsub)

end Semantics.Montague.Sentence.MaximalInformativity
