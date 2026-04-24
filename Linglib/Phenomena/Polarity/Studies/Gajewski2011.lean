import Linglib.Theories.Semantics.Entailment.StrawsonEntailment
import Linglib.Theories.Semantics.Entailment.Intolerance
import Linglib.Theories.Semantics.Entailment.PresuppositionLicensing
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Phenomena.Polarity.Studies.VonFintel1999
import Linglib.Fragments.English.PolarityItems
import Linglib.Core.Lexical.PolarityItem

/-!
# @cite{gajewski-2011} — Licensing strong NPIs

  Gajewski, J. R. (2011). Licensing strong NPIs. Natural Language
  Semantics 19(2), 109–148.

The paper's central puzzle: the standard Zwarts/Ladusaw picture says
strong NPIs (`either`, `in weeks`, punctual `until`) require an
**anti-additive** licenser, whereas weak NPIs (`any`, `ever`) need only
**downward entailment**. Once @cite{von-fintel-1999} weakens DE to
Strawson-DE, the natural extension is to weaken AA to Strawson-AA
(SAA). But @cite{rullmann-2003} and @cite{gajewski-2011} observe that
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
  AA ⊆ DE + Intolerant — both formalized in
  `Theories/Semantics/Entailment/Intolerance.lean`. Re-exported here as
  `gaj2011_appendix2_AA_implies_intolerant`.
- `wouldFull_isStrawsonAA` — Gajewski Appendix 1's actual `would`-with-
  non-vacuity-presupposition SAA result (in
  `Theories/Semantics/Entailment/StrawsonEntailment.lean`).
- Strong-NPI registry consistency theorem
  (`gaj2011_strongNPIs_excluded_from_strawson_only_contexts`) —
  Gajewski's headline empirical claim made `decide`-checkable over the
  Fragment registry.
- Hoeksema S-comparative SAA bridge
  (`bridge_hoeksema_sComparative_strawsonAA`) — the positive test case
  for Gajewski's framework: classically AA → strong NPIs predicted ✓.

## §4 framework — both halves now in skeleton

- Conditions 1, 2 (eqs. 59, 66): formalized in
  `Theories/Semantics/Entailment/PresuppositionLicensing.lean` using
  `Exhaustification.exhMW` (Spector 2016) as the substrate's `O(F, G)`.
  Trivial-ALT bridges proved (`condition1_with_no_alts_iff_de`,
  `condition2_with_no_alts_iff_de`). `only`'s satisfaction of Cond 1, 2
  in the trivial limit cited below.
- Conditions 3, 4 (eqs. 93, 94): formalized in PresuppositionLicensing.lean
  via `KPOperator` over `PrProp`. `only` satisfies Cond 3 ✓, fails
  Cond 4 ✗ (`gaj2011_only_condition3_yes_condition4_no`).

## What's still genuinely deferred

- **Empirical Cond 2 failure for `only`** under attested ALT-1 sets
  (Chierchia's "highest-scopal-item only" alternatives generated from
  the strong NPI in scope). The substrate `Exhaustification.exhMW` and
  `Exhaustification.exhIE` provide the O-operator; the Chierchia-side
  ALT-1 generator (matching `Phenomena/Polarity/Studies/Chierchia2006.lean`'s
  `PSIProfile` framework) needs to be wired up. Concrete witness for
  `only`'s Cond 2 failure would require this.
- The Intolerance-based account of `few` licensing strong NPIs in
  context (§4.3 eqs. 71-78). Requires scale truncation + context.
- Strong Functional Application (eq. 52) and Scalar Enrichment (eq. 53)
  as compositional rules — Conditions 1, 2 currently take alts as a
  free parameter rather than as the output of compositional rules.
- @cite{crnic-2014} "Non-monotonicity in NPI licensing": direct
  challenge to the Strawson-DE picture, the natural sequel paper.
-/

namespace Phenomena.Polarity.Studies.Gajewski2011

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.StrawsonEntailment

/-! ## §1 Background — recapitulating Zwarts and von Fintel

The paper's §2 establishes:
- `IsAntiAdditive f := ∀ p q, f (p ∪ q) ↔ f p ∧ f q`
  (eq. 10; in linglib: `Theories/Semantics/Entailment/AntiAdditivity.lean`).
- `IsDownwardEntailing f := Antitone f` (eq. 4; in linglib:
  `Theories/Semantics/Entailment/Polarity.lean`).
- AA ⇒ DE (eq. 11): standard textbook proof — already in linglib as
  `IsAntiAdditive.antitone`.
- Zwarts: strong NPIs (`either`, `in weeks`, until) need AA licensers (eq. 8).
- vF: presuppositions are factored out by replacing DE with **Strawson-DE**
  (eq. 22; in linglib: `Theories/Semantics/Entailment/StrawsonEntailment.lean`).
-/

/-! ## §3.3 The puzzle — Strawson-AA is too weak

@cite{gajewski-2011} (following @cite{rullmann-2003} and
@cite{gajewski-2005}) observes that *all* of vF's Strawson-DE
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

The four SAA proofs live in `Theories/Semantics/Entailment/StrawsonEntailment.lean`:

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

Intolerance comes from @cite{horn-1989}: a function is intolerant if it
does not map both `x` and `xᶜ` to truth — i.e., it "locates" itself on
one side of the midpoint of its scale.

The substrate-level definitions (`IsTrivial`, `IsIntolerant`,
`IsAntiAdditiveGQ`, `IsDownwardEntailingGQ`) and the Appendix 2 proof
(`antiAdditiveGQ_implies_intolerant`) live in
`Theories/Semantics/Entailment/Intolerance.lean`.

The reverse strict inclusion (`AA ⊊ DE + Intolerant`, ex. 84) — i.e.
exhibiting a DE+Intolerant function that is *not* AA — is asserted by
Gajewski but not proved; would need a witness function. Open.
-/

/-- Re-export the substrate Appendix 2 result for paper-citation indexing. -/
theorem gaj2011_appendix2_AA_implies_intolerant {α : Type*}
    (f : Set α → Prop)
    (hAA : Semantics.Entailment.Intolerance.IsAntiAdditiveGQ f) :
    Semantics.Entailment.Intolerance.IsIntolerant f :=
  Semantics.Entailment.Intolerance.antiAdditiveGQ_implies_intolerant f hAA

/-! ## §4.1 Conjecture (eq. 48): DE scalar item is AA iff endpoint of scale

@cite{gajewski-2011} (p. 123): "A DE scalar item is AA iff it is the
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

- @cite{von-fintel-1999}: provides the Strawson-DE substrate. Gajewski's
  Appendix 1 SAA proofs use exactly the operators vF defined; see
  `Phenomena/Polarity/Studies/VonFintel1999.lean`.
- @cite{kadmon-landman-1993}: K&L's widening + strengthening account of
  `any` precedes the Strawson framework; Gajewski's intolerance comes
  from @cite{horn-1989}, not from K&L. K&L's `LicensingMechanism`
  (`byStrengthening`/`byGenericIndefinite`/`byOtherMechanism`) is too
  coarse to predict the SAA-but-not-AA pattern.
- @cite{chierchia-2013} ch. 3 takes Gajewski's analysis as input and
  reconstructs strong-NPI licensing within the broader exhaustification
  framework.
- @cite{crnic-2014} challenges Strawson-based analyses with a
  non-monotonicity reanalysis; engages directly with this paper.
- @cite{hoeksema-1983} S-comparative is anti-additive (per
  `bridge_hoeksema_sComparative_strawsonDE` in VonFintel1999) — hence,
  per the Zwarts-classical theory, predicted to license strong NPIs.
  Empirically borne out (Hoeksema's data).
-/

/-! ## §4.4 Karttunen-Peters Conditions 3, 4 applied to `only`

@cite{gajewski-2011} eqs. 93-94 (p. 134) state two licensing conditions
in the K&P two-dimensional ⟨truth, presup⟩ framework:

- **Condition 3** (weak NPIs): the truth-conditional content alone must
  be DE in the licensee position.
- **Condition 4** (strong NPIs): truth-conditional content *plus the
  operator's presupposition* must be DE.

The substrate predicates `Condition3` and `Condition4` live in
`Theories/Semantics/Entailment/PresuppositionLicensing.lean`. Here we apply
them to `only` and verify the empirical match: weak NPIs licensed
(Condition 3 ✓), strong NPIs blocked (Condition 4 ✗).
-/

open Semantics.Entailment.PresuppositionLicensing
open Core.Presupposition (PrProp)

/-- The K&P operator for `only x`: assertion = "no y ≠ x has scope",
    presupposition = "some y has x and scope" (Horn 1996). Built directly
    from `onlyPrProp` in StrawsonEntailment. -/
def onlyKP (x : World → Prop) : KPOperator World :=
  fun scope => onlyPrProp x scope

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

/-- @cite{gajewski-2011} headline (K&P/presupposition side): `only` is
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
`Theories/Semantics/Exhaustification/Operators/Basic.lean`.

The substrate's trivial-ALT bridge theorem
(`condition1_with_no_alts_iff_de`) shows: with no alternatives,
Condition 1 reduces to classical DE. So `only` (whose assertion is
classically DE) satisfies Condition 1 with empty alternatives —
parallel to its satisfaction of Condition 3.

The full Gajewski analysis under Conditions 1, 2 requires non-trivial
ALT-1 sets (Chierchia's "highest-scopal-item only", eq. 55). The
@cite{chierchia-2006} (file
`Phenomena/Polarity/Studies/Chierchia2006.lean`) and
@cite{chierchia-2013} formalizations would supply concrete ALT-1
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
    `Phenomena/Polarity/Studies/Chierchia2006.lean`'s `PSIProfile`
    framework or equivalent. Wiring up a concrete ALT-1 generator
    that demonstrates the empirical Cond 2 failure for `only` is
    deferred to a follow-up study file (likely an extension of
    `Chierchia2006.lean` or a new `Chierchia2013.lean` since the
    relevant framework is Chierchia 2013 ch. 3). -/
theorem only_satisfies_condition2_no_alts (x : World → Prop) :
    Condition2 (onlyKP x).truth (fun _ => ∅) (fun _ => ∅) :=
  (condition2_with_no_alts_iff_de _).mpr (only_satisfies_condition3 x)

/-! ## Hoeksema S-comparative — the positive test case

@cite{hoeksema-1983}'s S-comparative is *classically* anti-additive
(`Theories/Semantics/Degree/Comparative.lean::sComparative_isAntiAdditive`),
hence by `antiAdditive_implies_strawsonAA` it is also Strawson-AA.
This is the **positive test** for Gajewski's framework: an AA operator
licenses strong NPIs (Hoeksema's data confirms — "Mary is taller than
anyone is", "in years"-style strong NPIs grammatical in than-S
comparatives). Contrast vF's recalcitrants which are SAA-but-not-AA
and hence don't license strong NPIs. -/
theorem bridge_hoeksema_sComparative_strawsonAA
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonAntiAdditive (Semantics.Degree.Comparative.sComparative μ) defined :=
  antiAdditive_implies_strawsonAA _
    (Semantics.Degree.Comparative.sComparative_isAntiAdditive μ) _

/-! ## Strong-NPI registry consistency

Gajewski's headline empirical claim: strong NPIs are ungrammatical under
operators that are only Strawson-DE/SAA (not classically AA). The
Fragment registry encodes this through:

- `Fragments/English/PolarityItems.lean`: strong NPIs (`liftAFinger`,
  `budgeAnInch`, `inYears`, `until_`, `either_npi`) all list
  `licensingContexts := [.negation, .nobody]` — i.e., classical-AA
  contexts only.
- `Core/Lexical/PolarityItem.lean::ContextProperties.isStrawsonOnly`:
  the four Strawson-only contexts (`.onlyFocus`, `.adversative`,
  `.sinceTemporal`, `.superlative`) carry `isStrawsonOnly := true`.

Gajewski's prediction: no strong NPI lists any `isStrawsonOnly`
context. The substrate makes this `decide`-checkable.
-/

open Core.Lexical.PolarityItem (PolarityType LicensingContext contextProperties)
open Fragments.English.PolarityItems
  (liftAFinger budgeAnInch inYears until_ either_npi)

/-- @cite{gajewski-2011} headline made registry-checkable: no strong
    NPI in the English Fragment is licensed in any Strawson-only
    context. The four enumerated strong NPIs all restrict their
    licensing to classical-AA contexts (`.negation`, `.nobody`,
    `.withoutClause`), excluding `.onlyFocus`, `.adversative`,
    `.sinceTemporal`, `.superlative`. -/
theorem gaj2011_strongNPIs_excluded_from_strawson_only_contexts :
    ∀ ctx : LicensingContext, (contextProperties ctx).isStrawsonOnly = true →
      ctx ∉ liftAFinger.licensingContexts ∧
      ctx ∉ budgeAnInch.licensingContexts ∧
      ctx ∉ inYears.licensingContexts ∧
      ctx ∉ until_.licensingContexts ∧
      ctx ∉ either_npi.licensingContexts := by
  intro ctx hStrawson
  cases ctx <;> simp_all [liftAFinger, budgeAnInch, inYears, until_, either_npi,
    contextProperties]

end Phenomena.Polarity.Studies.Gajewski2011
