import Linglib.Semantics.Entailment.StrawsonEntailment
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Semantics.Polarity.Licensing
import Linglib.Semantics.Degree.Comparative
import Linglib.Studies.VonFintel1999
import Linglib.Fragments.English.PolarityItems
import Linglib.Semantics.Polarity.Item

/-!
# [gajewski-2011] — Licensing strong NPIs

  Gajewski, J. R. (2011). Licensing strong NPIs. Natural Language
  Semantics 19(2), 109–148.

The paper's central puzzle: the standard Zwarts/Ladusaw picture says
strong NPIs (`either`, `in weeks`, punctual `until`) require an
**anti-additive** licenser, whereas weak NPIs (`any`, `ever`) need only
**downward entailment**. Once [von-fintel-1999] weakens DE to
Strawson-DE, the natural extension is to weaken AA to Strawson-AA
(SAA). But [rullmann-2003] and [gajewski-2011] observe that
SAA is *too weak*: vF's recalcitrants (`only`, conditionals, emotive
factives) are all SAA (Appendix 1) yet do *not* license strong NPIs.

Gajewski proposes that strong NPIs are sensitive to the licenser's
**direct scalar implicatures**, while weak NPIs are not. Strong NPIs
need DE assessed on the meaning *enriched with the licenser's direct
implicature*; AA was the wrong property — it only happened to coincide
with "DE + scalar endpoint" (Conjecture 48).

## What this study file covers

- §3.3 puzzle (eqs. 39-41): strong NPIs ungrammatical under SAA
  operators (`only`, conditionals, emotive factives). Documented in
  the section docstrings; the formal SAA results live in
  `StrawsonEntailment.lean`.
- Appendix 1 SAA proofs for vF's recalcitrants — formalized:
  `onlyFull_isStrawsonAA`, `sorryFull_isStrawsonAA`,
  `condNecessity_isStrawsonAA`, `superlative_isStrawsonAA` (all in
  `StrawsonEntailment.lean`). This file just cites them as
  `gaj2011_appendix1_*` for paper-citation indexing.
- Conjecture (eq. 48): a DE scalar item is AA iff it is the endpoint
  of its scale. Documented in §3.3 docstring; the conjecture is
  scale-theoretic and would need scale-side machinery to formalize.
- `IsIntolerant` predicate (eq. 80) and the Appendix 2 result
  AA ⊆ DE + Intolerant — both formalized below (demoted substrate),
  re-exported as `gaj2011_appendix2_AA_implies_intolerant`.
- `wouldFull_isStrawsonAA` — Gajewski Appendix 1's actual `would`-with-
  non-vacuity-presupposition SAA result (in
  `Semantics/Entailment/StrawsonEntailment.lean`).
- Strong-NPI registry consistency theorem
  (`gaj2011_strongNPIs_excluded_from_strawson_only_contexts`) —
  Gajewski's headline empirical claim made `decide`-checkable over the
  Fragment registry.
- Hoeksema S-comparative SAA bridge
  (`bridge_hoeksema_gtOverSet_strawsonAA`) — the positive test case
  for Gajewski's framework: classically AA → strong NPIs predicted ✓.

## §4 framework — both halves now in skeleton

- Conditions 1, 2 (eqs. 59, 66): formalized below (demoted substrate)
  using `Exhaustification.exhMW` (Spector 2016) as the `O(F, G)` operator.
  Trivial-ALT bridges proved (`condition1_with_no_alts_iff_de`,
  `condition2_with_no_alts_iff_de`). `only`'s satisfaction of Cond 1, 2
  in the trivial limit cited below.
- Conditions 3, 4 (eqs. 93, 94): formalized below (demoted substrate)
  via `KPOperator` over `PartialProp`. `only` satisfies Cond 3 ✓, fails
  Cond 4 ✗ (`gaj2011_only_condition3_yes_condition4_no`).

## What's still genuinely deferred

- **Empirical Cond 2 failure for `only`** under attested ALT-1 sets
  (Chierchia's "highest-scopal-item only" alternatives generated from
  the strong NPI in scope). The substrate `Exhaustification.exhMW` and
  `Exhaustification.exhIE` provide the O-operator; the Chierchia-side
  ALT-1 generator (matching `Studies/Chierchia2006.lean`'s
  `PSIProfile` framework) needs to be wired up. Concrete witness for
  `only`'s Cond 2 failure would require this.
- The Intolerance-based account of `few` licensing strong NPIs in
  context (§4.3 eqs. 71-78). Requires scale truncation + context.
- Strong Functional Application (eq. 52) and Scalar Enrichment (eq. 53)
  as compositional rules — Conditions 1, 2 currently take alts as a
  free parameter rather than as the output of compositional rules.
- [crnic-2014] "Non-monotonicity in NPI licensing": direct
  challenge to the Strawson-DE picture, the natural sequel paper.
-/

namespace Gajewski2011

open Entailment
/-! ## Demoted substrate — Intolerance + Karttunen-Peters Conditions

Folded in from the former `Entailment/Intolerance` and
`Entailment/PresuppositionLicensing` (single-consumer formalisations,
per the anchoring rule): the Intolerance predicate ([gajewski-2011] eq. 80)
and the Karttunen-Peters / Chierchia Conditions 1-4 (§4.1, §4.4) were
consumed only by this study. -/

/-- A GQ-typed function is **trivial** if it is constantly true or
    constantly false. -/
def IsTrivial {α : Type*} (f : Set α → Prop) : Prop :=
  (∀ x : Set α, f x) ∨ (∀ x : Set α, ¬ f x)

/-- [gajewski-2011] eq. 80: a function `f : Set α → Prop` is
    **Intolerant** iff it is trivial, OR for every `x`, at most one of
    `f x` and `f xᶜ` holds.

    [horn-1989]: Intolerant functions are "above the midpoint of
    their scale" — they cannot accept both a property and its
    complement. -/
def IsIntolerant {α : Type*} (f : Set α → Prop) : Prop :=
  IsTrivial f ∨ ∀ x : Set α, ¬ f x ∨ ¬ f xᶜ

/-- [gajewski-2011] Appendix 2 (p. 143): an anti-additive GQ is Intolerant.

    Proof sketch (Gajewski's): suppose `f` is AA and not trivial. For
    arbitrary `a`, suppose `f a = True` and `f aᶜ = True`. Then
    `f (a ∪ aᶜ) ↔ f a ∧ f aᶜ` gives `f Set.univ = True`. Since AA
    implies DE, every `y ⊆ Set.univ` has `f y = True` — contradicting
    non-triviality. So either `¬f a` or `¬f aᶜ`. -/
theorem antiAdditive_implies_intolerant {α : Type*} (f : Set α → Prop)
    (hAA : IsAntiAdditive f) : IsIntolerant f := by
  by_cases hTriv : IsTrivial f
  · exact Or.inl hTriv
  · refine Or.inr ?_
    intro x
    by_contra hNeither
    push Not at hNeither
    obtain ⟨hfx, hfxc⟩ := hNeither
    -- Now f x = True and f xᶜ = True. Show f Set.univ = True via AA.
    have hUnion : x ∪ xᶜ = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      exact Classical.em (y ∈ x)
    have hfUniv : f Set.univ := by
      rw [← hUnion]
      exact (isAntiAdditive_iff_gq.mp hAA x xᶜ).mpr ⟨hfx, hfxc⟩
    -- By DE (which AA implies), every y has f y — contradicting
    -- non-triviality.
    apply hTriv
    left
    intro y
    exact hAA.antitone (Set.subset_univ y) hfUniv

/-- A **Karttunen-Peters operator**: a function from an argument set to
    a presuppositional proposition (truth + presup). The presupposition
    may depend on the argument (per K&P 1979's heritage function). -/
abbrev KPOperator (W : Type*) : Type _ := Set W → Semantics.Presupposition.PartialProp W

/-- The truth-conditional projection of a K&P operator. -/
def KPOperator.truth {W : Type*} (op : KPOperator W) : Set W → Set W :=
  fun arg w => (op arg).assertion w

/-- The presuppositional projection of a K&P operator (parameterized by
    the argument). -/
def KPOperator.opPresup {W : Type*} (op : KPOperator W) : Set W → W → Prop :=
  fun arg w => (op arg).presup w

/-- The full meaning of a K&P operator: assertion *and* presupposition.
    What's checked for Condition 4 (strong NPI licensing). -/
def KPOperator.full {W : Type*} (op : KPOperator W) : Set W → Set W :=
  fun arg w => (op arg).assertion w ∧ (op arg).presup w

/-- [gajewski-2011] eq. 93: **Condition 3** (weak NPI licensing).

    A K&P operator licenses weak NPIs in its argument position iff its
    truth-conditional projection is DE (Antitone) in the argument. The
    operator's own presupposition does NOT enter the licensing check —
    weak NPIs ignore the licenser's presupposition. -/
def Condition3 {W : Type*} (op : KPOperator W) : Prop :=
  Antitone op.truth

/-- [gajewski-2011] eq. 94: **Condition 4** (strong NPI licensing).

    A K&P operator licenses strong NPIs in its argument position iff
    `assertion ∧ operator-presupposition` is DE in the argument. The
    operator's presupposition CAN destroy DE-ness; if it does, the
    operator licenses weak but not strong NPIs. -/
def Condition4 {W : Type*} (op : KPOperator W) : Prop :=
  Antitone op.full

/-- Trivially: an operator with no presupposition (always-`True`) makes
    Condition 3 and Condition 4 equivalent. -/
theorem condition3_iff_condition4_of_trivial_presup {W : Type*}
    (op : KPOperator W) (h : ∀ (arg : Set W) (w : W), (op arg).presup w) :
    Condition3 op ↔ Condition4 op := by
  constructor
  · intro h3 p q hpq w hfull
    exact ⟨h3 hpq hfull.1, h p w⟩
  · intro h4 p q hpq w hassert
    exact (h4 hpq ⟨hassert, h q w⟩).1

/- Note on Condition 4 vs Condition 3 implication:

   Adding more conjuncts to a meaning can destroy DE-ness in the
   licensee position — that is precisely the Gajewski point. So
   Condition 4 does not imply Condition 3 in general, nor vice versa.
   They are *independent* DE checks on different conjunctions of the
   K&P content. -/

-- ============================================================================
-- §2 Conditions 1, 2 — implicature-based licensing (Chierchia line)
-- ============================================================================

/-!
## Conditions 1, 2 — the implicature-based licensing line

Whereas Conditions 3, 4 (above) handle presuppositions via the K&P
framework, Conditions 1, 2 (Gajewski eqs. 59, 66) handle scalar
implicatures via [chierchia-2004]'s O-operator and
alternative-set machinery. The two frameworks make parallel
predictions for `only`: weak NPIs licensed (Condition 1 / Condition 3)
but strong NPIs blocked (Condition 2 / Condition 4) — once the
implicatures (Cond 1/2) or presuppositions (Cond 3/4) of the licenser
are factored in, DE-ness is destroyed.

The substrate's O-operator is `Exhaustification.exhMW` (Spector 2016,
based on minimal worlds) or its equivalent `exhIE` (innocent-exclusion
based, agree under closure under conjunction; see Spector Theorem 9).
We use `exhMW` because its trivial-ALT case is `exhMW ∅ φ = φ` cleanly,
which simplifies the empty-implicature reduction.

Gajewski's ALT vs ALT-1 distinction (eqs. 54, 55) is encoded as
two parameters to Condition 2: the standard alternative set ALT and
the restricted ALT-1 (Chierchia's "highest-scopal-item only").
-/

/-- [gajewski-2011] eq. 59: **Condition 1** (weak NPI licensing).

    Operator `op` licenses weak NPIs in its argument position iff
    `O(op(γ), op(ALT(γ)))` is DE in γ, where `alts γ` generates the
    alternative set against which `op(γ)` is exhaustified.

    `Exhaustification.exhMW` plays the role of Gajewski's `O(F, G)`. -/
def Condition1 {W : Type*} (op : Set W → Set W)
    (alts : Set W → Set (Set W)) : Prop :=
  Antitone (fun γ => Exhaustification.exhMW (alts γ) (op γ))

/-- [gajewski-2011] eq. 66: **Condition 2** (strong NPI licensing).

    Adds a parallel DE check against ALT-1 — the restricted alternative
    set (Chierchia's "highest-scopal-item only", eq. 55). Strong NPIs
    are licensed iff *both* DE checks pass: `O(op(γ), op(ALT(γ)))` AND
    `O(op(γ), op(ALT-1(γ)))`. -/
def Condition2 {W : Type*} (op : Set W → Set W)
    (alts altsOne : Set W → Set (Set W)) : Prop :=
  Condition1 op alts ∧
  Antitone (fun γ => Exhaustification.exhMW (altsOne γ) (op γ))

/-- Trivial-ALT lemma: with no alternatives, `exhMW` collapses to the
    prejacent. Spector 2016's minimality reduces to `True` when there
    are no alternatives to be minimal-with-respect-to. -/
theorem exhMW_empty_eq {W : Type*} (φ : Set W) :
    Exhaustification.exhMW (∅ : Set (Set W)) φ = φ := by
  ext u
  unfold Exhaustification.exhMW Exhaustification.ltALT Exhaustification.leALT
  simp

/-- **Trivial-ALT bridge for Cond 1**: Condition 1 with no alternatives
    reduces to classical DE. -/
theorem condition1_with_no_alts_iff_de {W : Type*} (op : Set W → Set W) :
    Condition1 op (fun _ => ∅) ↔ Antitone op := by
  unfold Condition1
  have h : (fun γ => Exhaustification.exhMW (∅ : Set (Set W)) (op γ)) = op := by
    funext γ
    exact exhMW_empty_eq (op γ)
  rw [h]

/-- **Trivial-ALT bridge for Cond 2**: with no alternatives in either
    ALT or ALT-1, Condition 2 reduces to classical DE. The empirical
    discriminative power of Cond 2 vs Cond 1 only emerges with
    non-trivial ALT-1 (Chierchia's "highest-scopal-item only"). -/
theorem condition2_with_no_alts_iff_de {W : Type*} (op : Set W → Set W) :
    Condition2 op (fun _ => ∅) (fun _ => ∅) ↔ Antitone op := by
  unfold Condition2
  rw [condition1_with_no_alts_iff_de]
  constructor
  · exact fun ⟨h, _⟩ => h
  · intro h
    refine ⟨h, ?_⟩
    have heq : (fun γ => Exhaustification.exhMW (∅ : Set (Set W)) (op γ)) = op := by
      funext γ; exact exhMW_empty_eq (op γ)
    rw [heq]; exact h

/-- **Bridge to Conditions 3, 4**: when `op`'s K&P-form has no
    presupposition (so the operator is presupposition-free), Conditions
    3 and 4 collapse, AND Condition 1 with no alternatives reduces to
    classical DE. Hence presuppositionless + alternative-free ⇒ all
    four Gajewski conditions reduce to classical DE.

    This is the structural reason Gajewski's framework matters: both
    presuppositions (the K&P side) AND implicatures (the Chierchia
    side) can destroy DE-ness in the licensee position; the four
    conditions track which side does what. -/
theorem all_conditions_reduce_to_DE_when_trivial {W : Type*}
    (op : KPOperator W)
    (hPresup : ∀ arg w, (op arg).presup w)
    (hOpFnDE : Antitone op.truth) :
    Condition1 op.truth (fun _ => ∅) ∧
    Condition3 op ∧
    Condition4 op := by
  refine ⟨?_, hOpFnDE, ?_⟩
  · exact (condition1_with_no_alts_iff_de op.truth).mpr hOpFnDE
  · -- Cond 4: assert ∧ presup is DE; presup is trivial, so equals assertion
    intro p q hpq w hfull
    exact ⟨hOpFnDE hpq hfull.1, hPresup p w⟩


/-! ## §1 Background — recapitulating Zwarts and von Fintel

The paper's §2 establishes:
- `IsAntiAdditive f := ∀ p q, f (p ∪ q) ↔ f p ∧ f q`
  (eq. 10; in linglib: `Semantics/Entailment/AntiAdditivity.lean`).
- `IsDownwardEntailing f := Antitone f` (eq. 4; in linglib:
  `Semantics/Entailment/Polarity.lean`).
- AA ⇒ DE (eq. 11): standard textbook proof — already in linglib as
  `IsAntiAdditive.antitone`.
- Zwarts: strong NPIs (`either`, `in weeks`, until) need AA licensers (eq. 8).
- vF: presuppositions are factored out by replacing DE with **Strawson-DE**
  (eq. 22; in linglib: `Semantics/Entailment/StrawsonEntailment.lean`).
-/

/-! ## §3.3 The puzzle — Strawson-AA is too weak

[gajewski-2011] (following [rullmann-2003] and
[gajewski-2005]) observes that *all* of vF's Strawson-DE
recalcitrants are also
**Strawson-AA**. The Appendix 1 proofs are formalized in
`StrawsonEntailment.lean`; we cite them here as paper-anchored theorems.

> (37) Only-Bill (A ∨ B) ⇒_S Only-Bill A ∧ Only-Bill B.
> (38) Only-Bill A ∧ Only-Bill B ⇒_S Only-Bill (A ∨ B).
>      [Both directions go through under Strawson entailment;
>       hence `only` is SAA.] (p. 120)

Yet strong NPIs are *ungrammatical* under all of these SAA operators
(exs. 39-41):

> (39) a. Only John has ever seen anyone. ✓
>      b. *Only John has seen Mary in weeks.
>      c. *Only John likes pancakes, either.
>      d. *Only John arrived until his birthday.
> (40) a. If Bill has ever seen anyone, he is keeping it a secret. ✓
>      b. *If Bill has seen Mary in weeks, he is keeping it a secret.
>      c. *If Bill likes pancakes, either, he is keeping it a secret.
>      d. *If Bill arrived until Friday, he is keeping it a secret.
> (41) a. Mary is sorry that she ever talked to anyone. ✓
>      b. *Mary is sorry that she has talked to Bill in weeks.
>      c. *Mary is sorry that she likes pancakes, either.
>      d. *Mary is sorry that she arrived until Friday.

Conclusion (p. 121): "Strawson anti-additivity is too weak to account
for the distribution of strong NPIs. Hence it appears that
presuppositions must be taken into account when we assess the licensing
of strong NPIs."

The 2x2 puzzle (eq. 44):

>            | Standard entailment | Strawson entailment
>      DE    | ???                 | Weak NPIs
>      AA    | Strong NPIs         | ???

vF's Strawson move correctly characterizes weak NPIs but the natural
extension to AA does not characterize strong NPIs. Gajewski proposes
the single distinction is whether the NPI attends to the licenser's
non-truth-conditional meaning.
-/

/-! ### Substrate index

The four SAA proofs live in `Semantics/Entailment/StrawsonEntailment.lean`:

- `onlyFull_isStrawsonAA` — Gajewski body §3.3 eqs. 37-38 (p. 120).
  (Appendix 1 sketches `sorry` and `would`; the `only` case is body text.)
- `sorryFull_isStrawsonAA` — Appendix 1 (p. 142).
- `condNecessity_isStrawsonAA` — Appendix 1 covers full `would` with
  non-vacuity presup; the substrate's `condNecessity` is the
  *idle-ordering* simpler case (see `wouldFull_isStrawsonAA` for the
  Gajewski-faithful version with non-vacuity definedness).
- `superlative_isStrawsonAA` — *not in Gajewski's text*. The body's
  "all SAA" claim (p. 120) is gestural; the superlative case is an
  extension of Gajewski's pattern.
-/

/-- The collected Gajewski headline: all four vF-recalcitrant operators
    come out Strawson-AA, yet (per exs. 39-41) none license strong NPIs.
    The substrate proves SAA; the empirical "no strong-NPI licensing"
    side is documented in the docstrings above (it requires a strong-NPI
    licensing predicate Gajewski's full theory builds compositionally). -/
theorem gaj2011_recalcitrants_all_strawsonAA :
    -- §2 only
    IsStrawsonAntiAdditive (onlyFull (· = World.w0))
        (fun scope _w => ∃ w', w' = World.w0 ∧ scope w') ∧
    -- §3 sorry
    IsStrawsonAntiAdditive
        (sorryFull (fun (w : World) => ({w} : Set World))
                   (fun (_ : World) => ({World.w1} : Set World)))
        (fun p w => ∀ w' ∈ ({w} : Set World), p w') ∧
    -- §4.1 conditional
    IsStrawsonAntiAdditive
        (fun α => condNecessity (fun (_ : World) =>
            ({World.w0, World.w1} : Set World)) α (fun _ => True))
        (fun _ _ => True) ∧
    -- §4.2 superlative
    IsStrawsonAntiAdditive (superlativeAssert World.w0)
        (superlativePresup World.w0) :=
  ⟨onlyFull_isStrawsonAA _,
   sorryFull_isStrawsonAA _ _,
   condNecessity_isStrawsonAA _ _,
   superlative_isStrawsonAA _⟩

/-! ## §4.3 The Intolerance-based intermediate category (eq. 80, Appendix 2)

For readers unconvinced by the §4 implicature-based account, Gajewski
offers an alternative: **DE + Intolerant** as an intermediate category
between DE and AA. The conjecture (eq. 84): `AA ⊂ DE + Intolerant ⊂ DE`.

Intolerance comes from [horn-1989]: a function is intolerant if it
does not map both `x` and `xᶜ` to truth — i.e., it "locates" itself on
one side of the midpoint of its scale.

The substrate-level definitions (`IsTrivial`, `IsIntolerant`; GQ-typed
anti-additivity and DE-ness are the `Set α → Prop` instances of
`IsAntiAdditive` and `Antitone`) and the Appendix 2 proof
(`antiAdditive_implies_intolerant`) are defined above (demoted substrate).

The reverse strict inclusion (`AA ⊊ DE + Intolerant`, ex. 84) — i.e.
exhibiting a DE+Intolerant function that is *not* AA — is asserted by
Gajewski but not proved; would need a witness function. Open.
-/

/-- Re-export the substrate Appendix 2 result for paper-citation indexing. -/
theorem gaj2011_appendix2_AA_implies_intolerant {α : Type*}
    (f : Set α → Prop)
    (hAA : Entailment.IsAntiAdditive f) :
    IsIntolerant f :=
  antiAdditive_implies_intolerant f hAA

/-! ## §4.1 Conjecture (eq. 48): DE scalar item is AA iff endpoint of scale

[gajewski-2011] (p. 123): "A DE scalar item is AA iff it is the
endpoint of its scale."

This is the load-bearing conjecture that lets Gajewski reduce strong-NPI
licensing to "DE + endpoint-of-scale." `no NP` is the strong endpoint of
the negative-existential scale ⟨no, few, not many, ...⟩; `few NP` is
*just above* `no NP`, so on context-dependent scale truncation `few NP`
can act as the endpoint — explaining why `few` sometimes licenses strong
NPIs (exs. 71-73, contra Zwarts):

> (71) He was one of the few dogs I'd met in years that I really liked.
> (72) Few Americans have ever been to Spain. Few Canadians have either.
> (73) He invited few people until he knew she liked them.

Formalizing the conjecture requires scale-side machinery (Horn scales,
context-dependent truncation à la Chierchia 2004 axiom (i)). Deferred.
-/

/-! ## Cross-framework relationships

- [von-fintel-1999]: provides the Strawson-DE substrate. Gajewski's
  Appendix 1 SAA proofs use exactly the operators vF defined; see
  `Studies/VonFintel1999.lean`.
- [kadmon-landman-1993]: K&L's widening + strengthening account of
  `any` precedes the Strawson framework; Gajewski's intolerance comes
  from [horn-1989], not from K&L. K&L's `LicensingMechanism`
  (`byStrengthening`/`byGenericIndefinite`/`byOtherMechanism`) is too
  coarse to predict the SAA-but-not-AA pattern.
- [chierchia-2013] ch. 3 takes Gajewski's analysis as input and
  reconstructs strong-NPI licensing within the broader exhaustification
  framework.
- [crnic-2014] challenges Strawson-based analyses with a
  non-monotonicity reanalysis; engages directly with this paper.
- [hoeksema-1983] S-comparative is anti-additive (per
  `bridge_hoeksema_gtOverSet_strawsonDE` in VonFintel1999) — hence,
  per the Zwarts-classical theory, predicted to license strong NPIs.
  Empirically borne out (Hoeksema's data).
-/

/-! ## §4.4 Karttunen-Peters Conditions 3, 4 applied to `only`

[gajewski-2011] eqs. 93-94 (p. 134) state two licensing conditions
in the K&P two-dimensional ⟨truth, presup⟩ framework:

- **Condition 3** (weak NPIs): the truth-conditional content alone must
  be DE in the licensee position.
- **Condition 4** (strong NPIs): truth-conditional content *plus the
  operator's presupposition* must be DE.

The predicates `Condition3` and `Condition4` are defined above (demoted
substrate). Here we apply
them to `only` and verify the empirical match: weak NPIs licensed
(Condition 3 ✓), strong NPIs blocked (Condition 4 ✗).
-/

open Entailment
open Semantics.Presupposition (PartialProp)

/-- The K&P operator for `only x`: assertion = "no y ≠ x has scope",
    presupposition = "some y has x and scope" (Horn 1996). Built directly
    from `onlyPartialProp` in StrawsonEntailment. -/
def onlyKP (x : World → Prop) : KPOperator World :=
  fun scope => onlyPartialProp x scope

/-- Ex. 19a (p. 115) confirmed: `only` satisfies Condition 3 — its
    truth-conditional assertion is *classically DE* in the scope.

    Proof: `(∀ y, x y ∨ ¬ q y) → (∀ y, x y ∨ ¬ p y)` for any `p ⊆ q` —
    if `q y` fails, so does `p y` (contrapositive of `p ⊆ q`). -/
theorem only_satisfies_condition3 (x : World → Prop) :
    Condition3 (onlyKP x) := by
  intro p q hpq w h y
  rcases h y with hxy | hnq
  · left; exact hxy
  · right; intro hpy; exact hnq (hpq hpy)

/-- Ex. 19a + ex. 39b (pp. 115, 120): `only` does **NOT** satisfy
    Condition 4 — the existence presupposition of `only` is upward
    entailing in scope, so the conjunction `assertion ∧ presupposition`
    is not DE.

    Witness: `p = ∅`, `q = {w0}`, focus on `w0`. At `w0`:
    - `(onlyKP (· = w0)).full q w0` holds: assertion holds (only w0 ∈ q),
      presup holds (∃ y = w0 ∧ q w0).
    - `(onlyKP (· = w0)).full p w0` fails: presup `∃ y, y = w0 ∧ p y`
      requires `p w0`, which is false (p = ∅).
    - DE would require: q ⊇ p ∧ full q w0 → full p w0. Fails. -/
theorem only_violates_condition4 :
    ¬ Condition4 (onlyKP (· = World.w0)) := by
  intro hCond4
  let p : Set World := fun _ => False
  let q : Set World := fun w => w = .w0
  have hle : p ≤ q := fun _ h => h.elim
  have hfull_q : (onlyKP (· = World.w0)).full q World.w0 := by
    refine ⟨?_, ?_⟩
    · intro y; by_cases h : y = World.w0
      · left; exact h
      · right; intro hy; cases h hy
    · exact ⟨World.w0, rfl, rfl⟩
  have hfull_p : (onlyKP (· = World.w0)).full p World.w0 := hCond4 hle hfull_q
  obtain ⟨_, _, hp_w0⟩ := hfull_p.2
  exact hp_w0

/-- [gajewski-2011] headline (K&P/presupposition side): `only` is
    the canonical case of "Condition 3 ✓ but Condition 4 ✗" — licenses
    weak NPIs (`any`, `ever`) but blocks strong NPIs (`either`,
    `in weeks`, `until`), because its existence presupposition is UE
    in the scope and destroys DE-ness of the conjunction. -/
theorem gaj2011_only_condition3_yes_condition4_no :
    Condition3 (onlyKP (· = World.w0)) ∧
    ¬ Condition4 (onlyKP (· = World.w0)) :=
  ⟨only_satisfies_condition3 _, only_violates_condition4⟩

/-! ## §4.1 Conditions 1, 2 — the implicature side (Chierchia line)

Parallel to §4.4's K&P-based Conditions 3, 4: Conditions 1, 2 (eqs.
59, 66) handle the implicature side via Spector 2016's `exhMW`
operator, treated as Gajewski's `O(F, G)`. The substrate substrate's
`Exhaustification.exhMW` lives in
`Semantics/Exhaustification/Operators/Basic.lean`.

The substrate's trivial-ALT bridge theorem
(`condition1_with_no_alts_iff_de`) shows: with no alternatives,
Condition 1 reduces to classical DE. So `only` (whose assertion is
classically DE) satisfies Condition 1 with empty alternatives —
parallel to its satisfaction of Condition 3.

The full Gajewski analysis under Conditions 1, 2 requires non-trivial
ALT-1 sets (Chierchia's "highest-scopal-item only", eq. 55). The
[chierchia-2006] (file
`Studies/Chierchia2006.lean`) and
[chierchia-2013] formalizations would supply concrete ALT-1
generators. Concrete `only` proofs under Conditions 1, 2 with
non-trivial ALTs are deferred until that infrastructure is wired in.
-/

/-- `only`'s assertion satisfies Condition 1 with empty alternatives
    (which reduces to classical DE — and we proved
    `only_satisfies_condition3` ≡ classical DE on the assertion). This
    is the implicature-side parallel of `only_satisfies_condition3`. -/
theorem only_satisfies_condition1_no_alts (x : World → Prop) :
    Condition1 (onlyKP x).truth (fun _ => ∅) :=
  (condition1_with_no_alts_iff_de _).mpr (only_satisfies_condition3 x)

/-- `only`'s assertion satisfies Condition 2 with no alternatives in
    either ALT or ALT-1 (degenerate trivial case — both DE checks pass
    because they collapse to classical DE on the assertion).

    The substrate proves this is the *trivial limit* of Condition 2.
    The empirical Gajewski result — that `only` *fails* Condition 2 on
    the **attested** ALT-1 (Chierchia's "highest-scopal-item only"
    alternatives generated from the strong NPI in scope) — requires a
    scalar-alternative generator that lives in
    `Studies/Chierchia2006.lean`'s `PSIProfile`
    framework or equivalent. Wiring up a concrete ALT-1 generator
    that demonstrates the empirical Cond 2 failure for `only` is
    deferred to a follow-up study file (likely an extension of
    `Chierchia2006.lean` or a new `Chierchia2013.lean` since the
    relevant framework is Chierchia 2013 ch. 3). -/
theorem only_satisfies_condition2_no_alts (x : World → Prop) :
    Condition2 (onlyKP x).truth (fun _ => ∅) (fun _ => ∅) :=
  (condition2_with_no_alts_iff_de _).mpr (only_satisfies_condition3 x)

/-! ## Hoeksema S-comparative — the positive test case

[hoeksema-1983]'s S-comparative is *classically* anti-additive
(`Semantics/Degree/Comparative.lean::gtOverSet_isAntiAdditive`),
hence by `antiAdditive_implies_strawsonAA` it is also Strawson-AA.
This is the **positive test** for Gajewski's framework: an AA operator
licenses strong NPIs (Hoeksema's data confirms — "Mary is taller than
anyone is", "in years"-style strong NPIs grammatical in than-S
comparatives). Contrast vF's recalcitrants which are SAA-but-not-AA
and hence don't license strong NPIs. -/
theorem bridge_hoeksema_gtOverSet_strawsonAA
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonAntiAdditive (Core.Order.Comparison.gt.overSet μ) defined :=
  antiAdditive_implies_strawsonAA _
    (Degree.gtOverSet_isAntiAdditive μ) _

/-! ## Strong-NPI registry consistency

Gajewski's headline empirical claim: strong NPIs are ungrammatical under
operators that are only Strawson-DE/SAA (not classically AA). The
Fragment registry encodes this through:

- `Fragments/English/PolarityItems.lean`: strong NPIs (`liftAFinger`,
  `budgeAnInch`, `inYears`, `until_`, `either_npi`) all list
  `licensingContexts := [.negation, .nobody]` — i.e., classical-AA
  contexts only.
- `Semantics/Polarity/Licensing.lean::IsStrawsonOnly`: the four
  Strawson-only contexts (`.onlyFocus`, `.adversative`,
  `.sinceTemporal`, `.superlative`) carry `classicalSignature := none`.

Gajewski's prediction: no strong NPI lists any Strawson-only
context. The substrate makes this `decide`-checkable.
-/

open Semantics.Polarity (PolarityType LicensingContext)
open Semantics.Polarity.Licensing
  (contextProperties IsStrawsonOnly LicensedBySignature)
open English.PolarityItems
  (any ever yet anymore atAll inTheLeast aSingle whatsoever
   liftAFinger budgeAnInch inYears until_ either_npi)

/-- [gajewski-2011] headline made registry-checkable: no strong
    NPI in the English Fragment is licensed in any Strawson-only
    context. The four enumerated strong NPIs all restrict their
    licensing to classical-AA contexts (`.negation`, `.nobody`,
    `.withoutClause`), excluding `.onlyFocus`, `.adversative`,
    `.sinceTemporal`, `.superlative`. -/
theorem gaj2011_strongNPIs_excluded_from_strawson_only_contexts :
    ∀ ctx : LicensingContext, IsStrawsonOnly ctx →
      ctx ∉ liftAFinger.licensingContexts ∧
      ctx ∉ budgeAnInch.licensingContexts ∧
      ctx ∉ inYears.licensingContexts ∧
      ctx ∉ until_.licensingContexts ∧
      ctx ∉ either_npi.licensingContexts := by
  intro ctx hStrawson
  cases ctx <;> simp_all [IsStrawsonOnly, liftAFinger, budgeAnInch, inYears,
    until_, either_npi, contextProperties]

/-- The registry agrees with signature-derived licensing on the strong
NPIs: every context a strong NPI lists supplies anti-additive strength
(`strengthSufficient` of the row's Strawson DE strength against the
item's derived [zwarts-1998] class). -/
theorem gaj2011_strong_npis_licensedBySignature :
    ∀ e ∈ [liftAFinger, budgeAnInch, inYears, until_, either_npi],
      ∀ c ∈ e.licensingContexts, LicensedBySignature e c := by decide

/-- Same agreement for the weak NPIs, gated to the strength-keyed
mechanisms: the FC and entropy rows in *any*'s list are licensed by their
mechanism, not by DE strength. -/
theorem gaj2011_weak_npis_licensedBySignature :
    ∀ e ∈ [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever],
      ∀ c ∈ e.licensingContexts,
        ((contextProperties c).mechanism = .byStrengthening ∨
         (contextProperties c).mechanism = .byStrawsonDE) →
        LicensedBySignature e c := by decide

-- The strength cut as a derived prediction (Gajewski's few-contrast):
-- *few* (weak DE) licenses *any* but not *in years*; *nobody*
-- (anti-additive) licenses both.
example : LicensedBySignature any .few := by decide
example : ¬ LicensedBySignature inYears .few := by decide
example : LicensedBySignature inYears .nobody := by decide

end Gajewski2011
