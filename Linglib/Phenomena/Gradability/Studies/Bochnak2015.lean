import Linglib.Theories.Semantics.Comparison.Delineation

/-!
# @cite{bochnak-2015} Degree Semantics Parameter and Washo

@cite{bochnak-2015} *The Degree Semantics Parameter and cross-linguistic
variation* (*Semantics and Pragmatics* 8(6): 1–48, doi:10.3765/sp.8.6)
argues that Washo (Hokan isolate, California/Nevada) systematically
lacks degree morphology: no comparatives, no measure phrases, no degree
adverbs, no equatives, no superlatives. The proposal is that Washo
gradable predicates are degree-free vague predicates in the
@cite{klein-1980} style — type ⟨e, t⟩ relative to a contextually-
supplied comparison class, with no degree variable. This positions
Washo as an empirical attestation of the negative setting of
@cite{beck-2009}'s Degree Semantics Parameter (DSP), and as a
counterexample to the universalist (English-projective) view that all
natural-language gradable predicates introduce degree arguments.

## Why this paper grounds linglib's substrate

Linglib's @cite{klein-1980}/@cite{kennedy-2007} comparison hierarchy
(`Theories/Semantics/Comparison/Hierarchy.lean`) already proves
**`degree_characterization`**: degree semantics is exactly the monotone
fragment of Klein's delineation framework. @cite{bochnak-2015}'s Washo
data sits inside this monotone fragment (Washo *tall*, *long*, *bent*
are single-criterion monotone predicates), so the empirical interest is
NOT that Washo motivates the strict-generality results
(`delineation_strictly_more_general`, `nlDel_not_degree_representable`)
— those are about non-monotone *clever*-style predicates, a different
phenomenon. The empirical interest is that Bochnak shows the
truth-conditional equivalence of degree-based and Klein-based
comparatives does NOT entail a particular LEXICAL TYPE: a language can
have monotone delineations as its lexical entries WITHOUT exposing
degrees in those entries' types or admitting degree morphology.

## Sections

1. The Degree Semantics Parameter as a typed parameter on languages
   (Bochnak eq. 7, after @cite{beck-2009}).
2. English vs Washo lexical-entry TYPES (eqs. 1, 5/11) — the central
   contrast is at the level of types, not denotations.
3. The conjoined-comparison construction (eq. 14, eq. 27) and its
   per-context truth conditions; existential closure recovers
   @cite{klein-1980}'s `comparativeSem`.
4. **Absolute-standard incompatibility** (eq. 23–24a/b/c): all three
   sub-cases mechanically derived. This is one of @cite{bochnak-2015}'s
   two diagnostics that conjoined comparison is implicit
   (@cite{kennedy-2007}'s sense).
5. **Crisp-judgment effect** under the Similarity Constraint (eqs. 20–22):
   stipulated as a felicity predicate distinct from truth conditions
   (the constraint is pragmatic per @cite{klein-1980}, @cite{fara-2000}).
   The granularity threshold is a linglib modeling choice, not from
   the paper.

## §2.2 Consistency Constraints — substrate in `Delineation.lean §13`

@cite{bochnak-2015}'s eq. (28a/b) Consistency Constraints — his
"strongest formal result" per the linguistics audit — are substrate-
level. `Delineation.lean §13` houses `IsSoundDelineation` (CC-b shape,
generalising eq. 28b to abstract scalar relations `R` per the paper's
"the scalar concept encoded by G" wording) and `IsCompleteDelineation`
(the converse direction, NOT in Bochnak — closer to
@cite{burnett-2017}'s *Plenitude* / *Granularity* axioms). CC-a (eq. 28a)
is exactly `IsMonotoneDelineation _ Set.univ` — no separate substrate
needed.

The §3 comparison-entailment theorem factors through
`comparativeSem_iff_of_sound_and_complete`: the equivalence
`comparativeSem del a b ↔ height b < height a` is a one-line corollary
firing via typeclass synthesis from `instSoundMeasureDelineation` /
`instCompleteMeasureDelineation`. The smuggled-measure workaround
flagged by the 0.230.434 audit is closed.

The load-bearing **footnote-11** caveat (single shared comparison
class) is formalised as `cc_b_requires_shared_class` in §6 below —
paper-anchored here since the footnote is Bochnak-specific.

## Future work still flagged

- §3–§4 van Rooij-style degree-free alternative analysis. Bochnak
  ultimately rejects it on parsimony grounds (§4: requires unifying
  differential MPs and crisp-judgment witnesses). A faithful
  formalization should engage @cite{van-rooy-2003} (and successors not
  yet in the bib) and prove Bochnak's parsimony argument.
- §4.3 Wellwood (2014) *much*-based middle-ground analysis and the
  Washo *t'e:k'e'* counterevidence (eqs. 64–68). Bochnak's most
  original cross-linguistic argument lives here.

-/

namespace Phenomena.Gradability.Studies.Bochnak2015

open Semantics.Comparison.Delineation

-- ════════════════════════════════════════════════════
-- § 1. The Degree Semantics Parameter
-- ════════════════════════════════════════════════════

/-- @cite{beck-2009} (DSP), as adopted by @cite{bochnak-2015} eq. 7.
    The DSP records whether a language's gradable lexicon introduces
    degree arguments. `true` for English-type, `false` for Washo-type.
    A language-level setting per @cite{bochnak-2015}, not per-predicate. -/
def DegreeSemanticsParameter : Type := Bool

/-- English: positive DSP setting (degree arguments + degree morphology). -/
def english : DegreeSemanticsParameter := true

/-- Washo: negative DSP setting per @cite{bochnak-2015}. -/
def washo : DegreeSemanticsParameter := false

/-- Motu (Austronesian, Papua New Guinea): also negative DSP per
    @cite{beck-2009}'s appendix and @cite{stassen-1985} typology.
    Bochnak's eq. 6 records the conjoined-comparison construction. -/
def motu : DegreeSemanticsParameter := false

theorem english_pos : english = true := rfl
theorem washo_neg : washo = false := rfl
theorem motu_neg : motu = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. English vs Washo Lexical-Entry Types
-- ════════════════════════════════════════════════════

/-! @cite{bochnak-2015}'s central proposal is at the level of LEXICAL
    TYPES, not denotations:

    - English `[[tall]]` (eq. 1): type ⟨d, ⟨e, t⟩⟩ — takes a degree
      argument that comparative/measure morphology binds.
    - Washo `[[tall_Washo]]^c` (eq. 5/11): type ⟨e, t⟩ relative to a
      comparison class. **No degree argument; no measure function in
      the denotation.**

    Bochnak (p. 6:4): *"The semantics in (5) contains no measure
    function, and no degree variable at all."*

    In linglib types: English entries have shape `ℕ → E → Prop`
    (degree-saturated ⟨e,t⟩); Washo entries have shape
    `ComparisonClass E → E → Prop` — the type signature of any
    Klein-style delineation (`Delineation.lean` line 72ff).

    We define `tallEnglish` to demonstrate the English shape. We do
    NOT define a `tallWasho` constant: the Washo lexicon's entry IS
    just an arbitrary delineation; theorems below quantify over
    `del : ComparisonClass E → E → Prop` to keep the no-measure
    discipline visible at the type level. -/

/-- @cite{bochnak-2015} eq. 1: standard English-style degree-based
    `[[tall]] = λdλx. height(x) ≽ d`. Type ⟨d, ⟨e, t⟩⟩. -/
def tallEnglish {E : Type*} (height : E → ℕ) (d : ℕ) (x : E) : Prop :=
  height x ≥ d

-- ════════════════════════════════════════════════════
-- § 3. Conjoined Comparison (@cite{bochnak-2015} eq. 14, eq. 27)
-- ════════════════════════════════════════════════════

/-- @cite{bochnak-2015} eq. 14: the Washo conjoined-comparison
    construction juxtaposes a positive form and a negated antonymic
    form (typically with the negation suffix *-eːs*). Bochnak argues
    NO comparative morpheme is involved — overt or covert.

    @cite{bochnak-2015} eq. 27 gives the truth conditions for a
    specific context `C`: x is more G than y iff x counts as G in C
    and y does not. Per-context Boolean conjunction of the lexical
    delineation and its negation. -/
def washoConjoined {E : Type*}
    (del : ComparisonClass E → E → Prop)
    (C : ComparisonClass E) (x y : E) : Prop :=
  del C x ∧ ¬ del C y

/-- @cite{klein-1980}'s existential `comparativeSem` is the existential
    closure of the Washo conjoined construction over comparison classes.
    @cite{bochnak-2015}'s eq. 27 is the per-context form; Klein's is the
    "exists a discriminating context" form. -/
theorem washoConjoined_witnesses_comparativeSem {E : Type*}
    (del : ComparisonClass E → E → Prop)
    {C : ComparisonClass E} {x y : E}
    (h : washoConjoined del C x y) : comparativeSem del x y :=
  ⟨C, h⟩

/-- Truth-conditional equivalence to height comparison **for a
    measure-induced delineation**. The Washo LEXICON exposes no
    degree variable (§2 above), but its truth conditions in a
    measure-induced model coincide with English's `-er`. The
    cross-linguistic divergence is at the level of TYPE and
    construction, not truth-conditional content.

    **Substrate-grounded derivation.** Now factors through
    `Delineation.lean §13`'s `IsSoundDelineation` /
    `IsCompleteDelineation` typeclasses (paper-anchored in
    `ConsistencyConstraints.lean` to @cite{bochnak-2015} §2.2 eq. 28).
    The `instSoundMeasureDelineation` and `instCompleteMeasureDelineation`
    instances fire by typeclass synthesis; the equivalence is a
    one-line corollary of `comparativeSem_iff_of_sound_and_complete`.
    The lexical entry no longer needs to expose `height` for the
    comparison entailment to go through — `height` participates only
    via instance synthesis. -/
theorem comparativeSem_measureDelineation_iff_degree {E : Type*}
    (height : E → ℕ) (a b : E) :
    comparativeSem (measureDelineation height) a b ↔
      height b < height a :=
  comparativeSem_iff_of_sound_and_complete (R := fun a b => height b < height a)

-- ════════════════════════════════════════════════════
-- § 4. Test 1: Absolute-Standard Incompatibility (eq. 23–24)
-- ════════════════════════════════════════════════════

/-! @cite{bochnak-2015} eq. 23 (English) and eq. 24 (Washo, three
    sub-cases) record the diagnostic: conjoined comparison fails with
    absolute-standard predicates. The minimal scenario uses two
    slightly bent rods where one is more bent than the other; ALL
    three Washo conjoined attempts fail:

    - eq. 24a: *bent ∧ straight* — fails because *straight* requires
      zero curvature, but both rods are bent.
    - eq. 24b: *bent ∧ ¬bent* — fails because *both* rods are bent.
    - eq. 24c: *straight ∧ ¬straight* — fails because *both* rods are
      bent (so neither is straight, but the form requires one to be).

    These failures are construction-level (the conjoined form requires
    an antonym OR negation to hold absolutely), not pragmatic. We
    derive all three sub-cases mechanically. -/

/-- @cite{kennedy-2007} **min-standard** absolute-degree predicate:
    holds iff the measure exceeds the scale's bottom endpoint (here `0`).
    Models *bent*, *wet*, *dirty*. The standard is fixed at the scale
    endpoint, not contextually supplied — so this predicate has no
    `ComparisonClass` parameter, unlike Klein-style delineations. -/
def bentPred {E : Type*} (curvature : E → ℕ) (x : E) : Prop :=
  curvature x > 0

/-- @cite{kennedy-2007} **max-standard** absolute-degree predicate:
    holds iff the measure is at the scale endpoint (`0` for curvature).
    Models *straight*, *dry*, *clean*. The lexical antonym of
    `bentPred`. -/
def straightPred {E : Type*} (curvature : E → ℕ) (x : E) : Prop :=
  curvature x = 0

/-- @cite{bochnak-2015} eq. 24a: *bent ∧ straight* fails when both
    rods have nonzero curvature. -/
theorem eq24a_bent_straight_fails {E : Type*}
    (curvature : E → ℕ) (x y : E)
    (_hx : bentPred curvature x) (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ straightPred curvature y) := by
  rintro ⟨_, h⟩
  exact absurd h (Nat.pos_iff_ne_zero.mp hy)

/-- @cite{bochnak-2015} eq. 24b: *bent ∧ ¬bent* fails when both rods
    are bent — the second conjunct is false. -/
theorem eq24b_bent_notbent_fails {E : Type*}
    (curvature : E → ℕ) (x y : E)
    (_hx : bentPred curvature x) (hy : bentPred curvature y) :
    ¬ (bentPred curvature x ∧ ¬ bentPred curvature y) := by
  rintro ⟨_, h⟩
  exact h hy

/-- @cite{bochnak-2015} eq. 24c: *straight ∧ ¬straight* fails when
    both rods are bent — the first conjunct is false. -/
theorem eq24c_straight_notstraight_fails {E : Type*}
    (curvature : E → ℕ) (x y : E)
    (hx : bentPred curvature x) (_hy : bentPred curvature y) :
    ¬ (straightPred curvature x ∧ ¬ straightPred curvature y) := by
  rintro ⟨h, _⟩
  exact absurd h (Nat.pos_iff_ne_zero.mp hx)

/-- The English degree-based comparative SUCCEEDS in the same scenario
    where all three Washo conjoined attempts fail. Witnesses Bochnak's
    diagnostic that conjoined comparison is *implicit*: same model,
    conjoined fails on every antonym pairing, comparative succeeds. -/
theorem english_more_bent_succeeds {E : Type*}
    (curvature : E → ℕ) (x y : E)
    (hmore : curvature x > curvature y) :
    ∃ d, tallEnglish curvature d x ∧ ¬ tallEnglish curvature d y := by
  exact ⟨curvature x, le_refl _, by simp [tallEnglish]; omega⟩

-- ════════════════════════════════════════════════════
-- § 5. Test 2: Crisp Judgment Effect (eq. 20–22)
-- ════════════════════════════════════════════════════

/-! @cite{bochnak-2015} eq. 20 records the **Similarity Constraint**
    (parenthetically attributed in the paper to @cite{klein-1980} and
    @cite{fara-2000}): when `x` and `y` differ only minimally in the
    property `G`, speakers are unable or unwilling to judge `x is G ∧
    y is not G` as true.

    This is a FELICITY constraint, not a truth-conditional one. The
    Washo conjoined construction inherits it (eq. 21: the ladder
    example is judged infelicitous in a minimal-difference context),
    which is @cite{bochnak-2015}'s second diagnostic that Washo
    comparison is *implicit* in @cite{kennedy-2007}'s sense.
    @cite{bochnak-2015} eq. 22 (the *wewš* "almost" hedge) shows the
    construction can be salvaged in crisp contexts via hedges.

    Linglib stipulates the Similarity Constraint as a felicity
    predicate distinct from the truth conditions established in §3.
    The empirical content is Bochnak's claim that Washo speakers obey
    it where English `-er` users do not.

    **Modeling-choice flag.** The granularity threshold `ε` and the
    specific `ε ≥ 2` instantiation in `crisp_judgment_blocks_conjoined`
    are linglib's parameterization; @cite{bochnak-2015} gives no
    numerical `ε`. The Lean theorem captures the SHAPE of the
    constraint, not the paper's quantitative content. -/

/-- The granularity-`ε` distinguishability predicate underlying the
    Similarity Constraint: `x` and `y` are crisply distinguishable on
    measure `μ` at granularity `ε` iff their measure difference is at
    least `ε`. -/
def crisplyDistinguishable {E : Type*}
    (μ : E → ℕ) (ε : ℕ) (x y : E) : Prop :=
  μ x ≥ μ y + ε ∨ μ y ≥ μ x + ε

/-- The conjoined-comparison felicity predicate. Felicitous on measure
    `μ` at granularity `ε` only if `x` exceeds `y` AND the pair is
    crisply distinguishable. SEPARATES truth conditions (the height
    inequality) from felicity (the granularity threshold). -/
def conjoinedFelicitous {E : Type*}
    (μ : E → ℕ) (ε : ℕ) (x y : E) : Prop :=
  μ y < μ x ∧ crisplyDistinguishable μ ε x y

/-- @cite{bochnak-2015} eq. 21 (the ladder scenario) made formal under
    linglib's `ε ≥ 2` modeling: a 1-unit measure difference cannot
    satisfy the Similarity Constraint, so the conjoined form is
    infelicitous. -/
theorem crisp_judgment_blocks_conjoined {E : Type*}
    (μ : E → ℕ) (ε : ℕ) (x y : E)
    (hgap : ε ≥ 2) (hclose : μ x = μ y + 1) :
    ¬ conjoinedFelicitous μ ε x y := by
  rintro ⟨_, h | h⟩ <;> omega

/-- @cite{bochnak-2015} eq. 22 (the *wewš* "almost" hedge) shows the
    conjoined form CAN be salvaged in crisp contexts via hedges.
    Formally: a sufficiently large measure gap restores felicity even
    at large `ε`. The hedge effectively raises the granularity
    threshold the speaker considers crisp. -/
theorem large_gap_restores_felicity {E : Type*}
    (μ : E → ℕ) (ε : ℕ) (x y : E)
    (hbigger : μ x ≥ μ y + ε) (hpos : μ y < μ x) :
    conjoinedFelicitous μ ε x y :=
  ⟨hpos, Or.inl hbigger⟩

-- ════════════════════════════════════════════════════
-- § 6. Footnote 11: shared-class requirement (counterexample)
-- ════════════════════════════════════════════════════

/-- @cite{bochnak-2015} fn 11 (p. 6:16): the comparison entailment
    requires a SINGLE comparison class shared by both conjuncts of the
    conjoined construction. Weakening to "exists `C₁` that makes `x`
    positive AND exists `C₂` (possibly distinct) that makes `y`
    negative" does NOT suffice.

    Counterexample model: `Entity := Bool`. The delineation `del C x :=
    x = true ∧ true ∈ C` makes `true` positive in any CC containing
    `true`, and `false` negative everywhere. Soundness w.r.t.
    `R a b := a = true ∧ b = false` holds (the only positive
    discrimination is `x = true ∧ y = false`). But the SPLIT-CC weakened
    form admits `(x, y) = (true, true)` via `C₁ := {true}` and
    `C₂ := {false}` — `del C₁ true ∧ ¬ del C₂ true` holds, while
    `R true true = false`.

    Paper-anchored here (rather than substrate-level) because the
    footnote-11 caveat is Bochnak-specific: it explains why eq. (27)
    threads a single shared `C` through both conjuncts. -/
theorem cc_b_requires_shared_class :
    ∃ (Entity : Type) (del : ComparisonClass Entity → Entity → Prop)
      (R : Entity → Entity → Prop),
      IsSoundDelineation del R ∧
      ∃ (C₁ C₂ : ComparisonClass Entity) (x y : Entity),
        del C₁ x ∧ ¬ del C₂ y ∧ ¬ R x y := by
  refine ⟨Bool,
          fun C x => x = true ∧ true ∈ C,
          fun a b => a = true ∧ b = false, ?_, ?_⟩
  · -- IsSoundDelineation: shared-CC version is sound for our R
    refine ⟨?_⟩
    intro C x y ⟨hxT, htC⟩ hneg
    subst hxT
    refine ⟨rfl, ?_⟩
    by_contra hyne_false
    have hyT : y = true := by
      cases y with
      | true => rfl
      | false => exact absurd rfl hyne_false
    exact hneg ⟨hyT, htC⟩
  · -- Split-CC weakening fails: x=y=true witnesses the gap
    refine ⟨{true}, {false}, true, true, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro ⟨_, h⟩
      rw [Set.mem_singleton_iff] at h
      exact Bool.noConfusion h
    · intro ⟨_, h⟩
      exact Bool.noConfusion h

end Phenomena.Gradability.Studies.Bochnak2015
