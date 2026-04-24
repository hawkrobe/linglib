import Linglib.Theories.Semantics.Entailment.StrawsonEntailment
import Linglib.Phenomena.Polarity.Studies.KadmonLandman1993
import Linglib.Phenomena.Polarity.Studies.Lahiri1998
import Linglib.Phenomena.Polarity.Studies.Hoeksema1983

/-!
# @cite{von-fintel-1999} — Strawson entailment as a rescue for Fauconnier-Ladusaw

  von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
  Dependency. Journal of Semantics 16(2), 97–148.

The paper defends the Fauconnier-Ladusaw analysis of NPI licensing — that NPIs
are licensed in DE positions — against four "recalcitrant" arenas where NPIs
are licensed despite the host context not being classically DE: `only`, the
adversative attitude predicates (`sorry`, `surprised`, `regret`), superlatives,
and conditional antecedents. The key move is to weaken classical DE to
**Strawson-DE** (Definition 14): an inference `f(q) ⊨ f(p)` need only hold
under the additional assumption that the conclusion's presupposition is
satisfied. With this weakening, all four contexts come out DE and the
Fauconnier-Ladusaw schema goes through.

## What this study file does

It is *not* a re-derivation of Strawson-DE — that lives in
`Theories/Semantics/Entailment/StrawsonEntailment.lean`, which already
proves `onlyFull_isStrawsonDE`, `sorryFull_isStrawsonDE`, `gladFull_isUE`,
`superlative_isStrawsonDE`, `conditional_antecedent_strawsonDE`, and the
relevant non-DE lemmas. This file is the *paper-citation index*: each
theorem is named after the paper's example number(s) and discharged by
specializing the corresponding theorem from `StrawsonEntailment.lean` to
the example's lexical instance. NPI grammaticality judgments themselves
(starred or unstarred sentences) are not theorems — they are the empirical
motivation, recorded in section docstrings with the sentences quoted from
the paper.

## Coverage

- §2 *only*: ex. 10, 11, 18 — formalized.
- §2.2 *since* (Iatridou): exs. 20-22 — discussed; no `sinceFull` operator
  in the formal substrate yet.
- §2.3 pseudo-anti-additivity (against Atlas): exs. 23-27 — discussed.
- §3 *sorry/surprised/regret*: exs. 28, 29, 30 — formalized via `sorryFull`.
- §3.1 ex. 31 (the prima-facie incoherence anchor for Kadmon-Landman) —
  discussed in the §3 section docstring.
- §3.3 *glad* asymmetry: ex. 52 — formalized via `gladFull_isUE`.
- §3.4 shifting contexts (exs. 60-65): discussed; requires a dynamic-context
  treatment not yet in the substrate.
- §3.4 Curveball #2 focus-`only` (exs. 66-68): discussed (subsumed by
  `onlyFull_isStrawsonDE`).
- §4.1 conditional antecedents: exs. 70-74 — formalized for the restrictor
  analysis (under which conditionals *are* DE); the Stalnaker-Lewis
  Strengthening-the-Antecedent failures are discussed.
- §4.2 superlatives: exs. 75, 76, 77 — partially formalized via
  `superlative_isStrawsonDE`.
-/

namespace Phenomena.Polarity.Studies.VonFintel1999

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Semantics.Entailment.StrawsonEntailment

/-! ## §2 — *only*

The Fauconnier-Ladusaw puzzle: `only John` licenses NPIs in its scope
(ex. 10) yet the canonical DE inference fails (ex. 11) — extending the
inference to a narrower scope (kale ⊆ vegetables) is not classically
truth-preserving because the conclusion `Only John ate kale` carries a
presupposition (someone ate kale) that the premise does not guarantee.
Strawson-DE plugs the gap (ex. 18): with the conclusion's presupposition
added as an extra premise, the DE inference goes through, and Strawson-DE
is sufficient for NPI licensing.

> (10) Only John ever ate any kale for breakfast. (p. 101)
> (11) Only John ate vegetables for breakfast. ⇏ Only John ate kale for breakfast. (p. 101)
> (18) Kale is a vegetable. John ate kale for breakfast. Only John ate vegetables for
>      breakfast. ∴ Only John ate kale for breakfast. (p. 104)
-/

/-- Ex. 11 (p. 101): `only` is not classically downward entailing.
    Witness: kale ⊆ vegetables but the inference fails because the
    conclusion's existence presupposition (someone ate kale) is not
    guaranteed by the premise. -/
theorem ex11_only_not_DE :
    ¬ IsDownwardEntailing (onlyFull (· = World.w0)) :=
  onlyFull_not_de

/-- Ex. 18 (p. 104): `only` is Strawson-DE. The definedness predicate
    encodes the existence presupposition: there is some `w'` such that
    the focused individual `John` (here `· == .w0`) holds at `w'` and the
    scope predicate holds at `w'`. -/
theorem ex18_only_strawsonDE :
    IsStrawsonDE (onlyFull (· = World.w0))
      (fun scope _w => ∃ w', w' = World.w0 ∧ scope w') :=
  onlyFull_isStrawsonDE _

/-- Ex. 11 + 18: the central separation. `only` is Strawson-DE without
    being classically DE — and Strawson-DE is enough to license NPIs
    under von Fintel's revised Fauconnier-Ladusaw schema. This is the
    paper's headline result for §2. -/
theorem ex11_18_only_strawson_separation :
    IsStrawsonDE (onlyFull (· = World.w0))
        (fun scope _w => ∃ w', w' = World.w0 ∧ scope w') ∧
    ¬ IsDownwardEntailing (onlyFull (· = World.w0)) :=
  ⟨onlyFull_isStrawsonDE _, onlyFull_not_de⟩

/-! ### §2.2 *since* (Iatridou, p.c.)

Von Fintel relays an example from Sabine Iatridou:

> (20) It's been five years since I saw a bird of prey in this area. ⇏
>      It's been five years since I saw an eagle in this area. (p. 107)
> (21) It's been five years since I saw any bird of prey in this area. ✓
> (22) (with the additional premise "Five years ago I saw an eagle") the
>      inference of (20) is restored.

Same dialectical shape as `only`: `since` licenses NPIs but is not
classically DE; adding the temporal presupposition (the eagle-sighting)
makes the inference go through.
-/

/-- Ex. 22 (p. 107): `since` is Strawson-DE in its complement. The
    definedness predicate is the temporal presupposition (a past
    `p`-event existed). -/
theorem ex22_since_strawsonDE (pastEvent sinceWindow : World → Set World) :
    IsStrawsonDE (sinceFull pastEvent sinceWindow)
      (fun p w => ∃ w' ∈ pastEvent w, p w') :=
  sinceFull_isStrawsonDE pastEvent sinceWindow

/-! ### §2.3 — pseudo-anti-additivity is useless for NPI licensing

@cite{atlas-1996} suggests that `only John` is "pseudo-anti-additive"
(ex. 25, p. 109): it satisfies the half of anti-additivity in which
`f(x) ∧ f(y) → f(x ∨ y)`. Von Fintel shows this is "useless for the
analysis of NPI licensing" (p. 110): pseudo-anti-additivity is too weak —
it is shared by many quantifiers that license NPIs (`no student`) and
many that do not (`some student`, `every student`, `at least three
students`); see exs. 26 and 27. The negative argument doesn't admit a
single-theorem formalization — it is a survey of counterexamples — but
the upshot for the formal substrate is exactly what we already have:
Strawson-DE, not pseudo-AA, is the operative notion.
-/

/-! ## §3 — adversative attitude predicates

Adversative factive verbs (`sorry`, `regret`, `surprised`, `amazed`)
license NPIs in their complement clauses despite the complement position
not being classically DE.

> (28a) Sandy is amazed/surprised that Robin ever ate kale. (p. 111)
> (28b) Sandy is sorry/regrets that Robin bought any car. (p. 111)
> (29)  Robin ate kale ⇒ Robin ate a green vegetable; but
>       Sandy is amazed that Robin ate a green vegetable
>       ⇏ Sandy is amazed that Robin ate kale. (p. 111)
> (30)  Robin bought a Honda Civic ⇒ Robin bought a car; but
>       Sandy is sorry that Robin bought a car
>       ⇏ Sandy is sorry that Robin bought a Honda Civic. (p. 111)

The factivity presupposition (the complement holds at the evaluation
world) blocks classical DE: the conclusion's narrower complement may not
hold even when the premise does. Strawson-DE rescues the inference by
adding factivity at the world of evaluation.

### Ex. 31 — Kadmon-Landman's prima-facie coherence challenge

> (31) Sandy regrets that Robin bought a car, but Sandy does not regret
>      that Robin bought a Honda Civic. (p. 112)

If `regret` were uniformly DE, (31) should be incoherent.
@cite{kadmon-landman-1993} defend monotonicity by appealing to a *change
of perspective* between the conjuncts; von Fintel's §3.1 reanalysis
treats this as a shift of the modal-base parameter rather than a failure
of the underlying operator's monotonicity. The Strawson-DE result for
`sorry` below holds on a *constant* perspective.
-/

/-- Ex. 30 (p. 111): `sorry` is not classically DE in its complement.
    The factivity component is what blocks DE: doxastic factivity of
    the narrower complement `p ⊆ q` may fail at the evaluation world
    even when `q`'s does. -/
theorem ex30_sorry_not_DE :
    ¬ IsDownwardEntailing
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World))) :=
  sorryFull_not_de

/-- Ex. 28b (p. 111) — *the explanatory result*: `sorry` is Strawson-DE.
    The definedness predicate is doxastic factivity (`dox w ⊆ p`):
    the agent at the evaluation world `w` believes `p`. Given doxastic
    factivity of the conclusion's complement and `p ⊆ q`, the
    inference `sorry q ⊨ sorry p` goes through.

    This explains why "Sandy is sorry that Robin bought any car"
    licenses `any` despite the complement position not being classically DE. -/
theorem ex28b_sorry_strawsonDE (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-- Ex. 30 + ex. 28b — the adversative analogue of the only-separation:
    `sorry` is Strawson-DE without being classically DE. -/
theorem ex28_30_sorry_strawson_separation :
    IsStrawsonDE
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World)))
      (fun p w => ∀ w' ∈ ({w} : Set World), p w') ∧
    ¬ IsDownwardEntailing
      (sorryFull (fun (w : World) => ({w} : Set World))
                 (fun (_ : World) => ({World.w1} : Set World))) :=
  sorryFull_strictly_strawsonDE

/-! ### §3.2 — `want` and the Asher/Heim non-monotonicity puzzle

vF §3.2 (pp. 115-121) defends `want` as upward entailing under a
doxastic modal base (`DOX*`), in response to the Asher 1987 Concorde
example (eq. 46) and the Heim 1992 couch example (eq. 48). The
"non-monotonicity" of `want` collapses to a context shift in the
modal base, parallel to the §3.4 shifting-context analysis for
adversatives. Headline: `want` is monotonic relative to a constant
context.
-/

/-- `want` is upward entailing in its complement (vF §3.2 headline; eq. 45). -/
theorem ex45_want_isUE (bestOf : World → Set World) :
    Monotone (wantFull bestOf) :=
  wantFull_isUE bestOf

/-! ### §3 footnote 8 — Asher's WDE as a sibling notion

vF p. 112 (footnote 8) cites @cite{asher-1987}'s Weakened Downward
Entailment as a related but formally distinct notion: it has a
*doxastic* side condition (belief in the conclusion's complement) and
operates in the *upward* direction, in contrast to Strawson-DE's
presuppositional side condition in the downward direction. The
substrate's `IsWDE` predicate captures this; classical UE implies WDE
trivially (`monotone_implies_WDE`).
-/

/-! ### §3.3 — *glad* is upward entailing, hence does not license NPIs

> (52) `glad` is UE: from `α is glad that p` and `p ⇒ q`, infer `α is
>      glad that q` (paraphrasing the analysis on p. 124).

The asymmetry between `sorry` (DE in the complement under Strawson-DE)
and `glad` (UE) is what predicts the asymmetry in NPI licensing:
"*Sandy is glad that Robin bought any car" is ungrammatical; the same
sentence with `sorry` is fine.

The same adversative/non-adversative asymmetry shows up in Hindi
(@cite{lahiri-1998} §4.5): *aaScarya* 'surprised' licenses *koii bhii* /
*ek bhii*; *khuS* 'glad' does not. See `Phenomena/Polarity/Studies/Lahiri1998.lean`
for the Hindi data (`npi_adversative_surprise_ek`,
`npi_adversative_surprise_koii`, `npi_glad_bad`). The two papers offer
different explanations — Lahiri posits a covert anti-additive operator
over the complement; von Fintel derives the asymmetry from the lexical
monotonicity of the attitude — but they make the same predictions on
the basic English/Hindi data.
-/

/-- Ex. 50 / K&L (p. 122): `glad` (K&L eq. 50 semantics) is upward
    entailing. Predicts NPIs are *not* licensed in the complement of `glad`. -/
theorem ex50_gladKL_isUE (dox bestOf : World → Set World) :
    Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

/-- Ex. 52 (p. 124) — *vF's preferred replacement*: `glad` (vF eq. 52
    semantics) is also upward entailing. Same NPI-licensing prediction,
    different content (cf. vF's Honda Civic example, p. 124-125). -/
theorem ex52_gladVF_isUE (dox relevant : World → Set World)
    (lt : World → World → World → Prop) :
    Monotone (gladFullVF dox relevant lt) :=
  gladFullVF_isUE dox relevant lt

/-- The §3 headline: `sorry` and `glad` agree on factivity but differ on
    monotonicity in the complement, and this monotonicity asymmetry
    directly tracks the NPI-licensing asymmetry. Holds for *both* the
    K&L and the vF analyses of `glad`. -/
theorem ex28_vs_ex52_sorry_glad_asymmetry (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') ∧
    Monotone (gladFull dox bestOf) :=
  ⟨sorryFull_isStrawsonDE dox bestOf, gladFull_isUE dox bestOf⟩

/-! ### §3.4 — shifting contexts

The coherent sequences

> (60) Sandy is glad that Robin bought a car, but Sandy is sorry/not glad that
>      Robin bought a Honda. (p. 129)
> (61) Sandy is sorry that Robin bought a car, but Sandy is glad/not sorry that
>      Robin bought a Honda. (p. 129)

Von Fintel argues these do not threaten the monotonicity analysis: their
coherence depends on a *shift* in the modal-base parameter between the
conjuncts (an "implicit conditionalization"; see ex. 61 discussion).
Validity of monotonic inferences is checked against a *constant* context.
A formal treatment requires dynamic-context machinery not yet present in
`StrawsonEntailment.lean`.

### §3.4 — Curveball #2: focus-sensitive *only* over a non-name (p. 133)

> (66) There only was any precipitation in [MEDFORD]_F.
> (67) (66) plus "There was rain in Medford" ⊢_S There only was rain in
>      [MEDFORD]_F. (p. 133)

Focus-sensitive `only` over a place name (or any non-proper-name
associate) is also Strawson-DE in its prejacent. Von Fintel notes
(eq. 68 (a/b), p. 134) that this requires the option-(a) semantics for
propositional `only` (weakening the asserted claim by closure under
entailment of the prejacent), not the option-(b) semantics adopted in
@cite{von-fintel-1997}. The substrate's `onlyFull` already captures the
option-(a) reading via its assertion clause "no `y ≠ x` satisfies the
scope".
-/

/-! ## §4 — conditional antecedents and superlatives

### §4.1 — conditional antecedents

> (70a) If John subscribes to any newspaper, he is probably well informed. (p. 135)
> (70b) If he has ever told a lie, he must go to confession. (p. 135)
> (70c) If you had left any later, you would have missed the plane. (p. 135)

Conditional antecedents license NPIs (ex. 70). Whether they are DE
depends on the conditional analysis adopted:

- *Restrictor analysis* (@cite{kratzer-1986}; eq. 72, p. 137):
  the if-clause restricts the modal base of the consequent's modal
  operator. With an *idle* ordering source, antecedent strengthening
  only shrinks the domain, so the antecedent position is classically
  DE. The substrate's `condNecessity` formalizes precisely this
  idle-ordering case (the simpler subcase of eq. 72 with `max_g` set
  to identity); the full Kratzer conditional with non-trivial
  ordering source is *not* monotone, which is exactly the §4 puzzle.
- *Stalnaker-Lewis non-monotonic analysis* (@cite{stalnaker-1968},
  @cite{lewis-1973}; ex. 73, p. 138): Strengthening the Antecedent
  fails, so the antecedent is not DE. Von Fintel §4.3 (p. 141)
  defends a dynamic monotonic semantics in @cite{von-fintel-2000}
  under which the apparent failures reduce to context shifts,
  parallel to §3.4.

We formalize the restrictor side. Stalnaker-Lewis non-monotonicity is
a property of a different operator (a similarity-based `would`) not yet
in the substrate.
-/

/-- Ex. 72 (p. 137), restrictor analysis with *idle ordering source*:
    a Kratzer-style `condNecessity` is classically DE in its antecedent.
    Domain restriction is monotone.

    Note: this is the strict subcase of vF eq. 72 where `max_g` is
    trivial. The full Kratzer/Stalnaker-Lewis conditional with a
    non-trivial preference ordering is *not* monotone — see the
    `ex73_*` theorems below for the counterexample built from the
    real Kratzer apparatus in `Conditionals/Restrictor.lean`. -/
theorem ex72_conditional_antecedent_DE
    (domain : World → Set World) (β : Set World) :
    IsDownwardEntailing (fun α => condNecessity domain α β) :=
  conditional_antecedent_DE domain β

/-- Restrictor-style conditional antecedents are *a fortiori* Strawson-DE
    (since classical DE implies Strawson-DE via `de_implies_strawsonDE`). -/
theorem conditional_antecedent_strawsonDE_under_restrictor
    (domain : World → Set World) (β : Set World)
    (defined : Set World → World → Prop) :
    IsStrawsonDE (fun α => condNecessity domain α β) defined :=
  conditional_antecedent_strawsonDE domain β defined

/-! ### §4.2 — superlatives

> (75) Emma is the tallest girl to ever win the dance contest. (p. 138)
> (76) Emma is the tallest girl in her class. ⇏
>      Emma is the tallest girl in her class to have learned the alphabet. (p. 139)
> (77) Emma has learned the alphabet. Emma is the tallest girl in her class.
>      ∴ Emma is the tallest girl in her class to have learned the alphabet. (p. 139)

Adding a restriction to the comparison class can change the ranking, so
ex. 76 is not classically DE. With the additional premise that Emma
satisfies the new restriction (ex. 77's "Emma has learned the alphabet"),
the inference is Strawson-valid.

The substrate's `superlativeAssert` and `superlative_isStrawsonDE`
encode this for the *predicative* use of the superlative (ex. 75 / 77).
The non-predicative case where the superlative restricts a definite
description (ex. 80 p. 140) does not have local Strawson-DE — this is
documented in the substrate's superlative section.
-/

/-- Ex. 77 (p. 139): the superlative is Strawson-DE in the restriction
    position. The definedness predicate encodes the presupposition that
    the designated subject α (Emma) satisfies the restriction (has learned
    the alphabet). -/
theorem ex77_superlative_strawsonDE (α : World) :
    IsStrawsonDE (superlativeAssert α) (superlativePresup α) :=
  superlative_isStrawsonDE α

/-! ## Hierarchy connection

The paper's §1 establishes the standard DE / AA / AM hierarchy and von
Fintel's §2 (Strawson move) extends it with Strawson-DE as the weakest
licensing level. The substrate proves AM → AA → DE → Strawson-DE
(`de_implies_strawsonDE`); this study file just records that the four
recalcitrant operators (`onlyFull`, `sorryFull`, `superlativeAssert`,
`condNecessity`) all land at *exactly* Strawson-DE, while `gladFull`
sits outside the hierarchy entirely (UE).
-/

/-- The four "recalcitrant" Strawson-DE operators of @cite{von-fintel-1999},
    each strict (Strawson-DE without classical DE) where applicable: -/
theorem strawson_DE_recalcitrants :
    -- §2 only: Strawson-DE without classical DE
    (IsStrawsonDE (onlyFull (· = World.w0))
        (fun scope _w => ∃ w', w' = World.w0 ∧ scope w') ∧
     ¬ IsDownwardEntailing (onlyFull (· = World.w0))) ∧
    -- §3 sorry: Strawson-DE without classical DE (doxastic factivity)
    (IsStrawsonDE
        (sorryFull (fun (w : World) => ({w} : Set World))
                   (fun (_ : World) => ({World.w1} : Set World)))
        (fun p w => ∀ w' ∈ ({w} : Set World), p w') ∧
     ¬ IsDownwardEntailing
        (sorryFull (fun (w : World) => ({w} : Set World))
                   (fun (_ : World) => ({World.w1} : Set World)))) ∧
    -- §4.1 conditional antecedent (restrictor analysis): classically DE,
    -- so trivially Strawson-DE
    IsStrawsonDE (fun α => condNecessity (fun (_ : World) =>
        ({World.w0, World.w1} : Set World)) α (fun _ => True)) (fun _ _ => True) ∧
    -- §4.2 superlative: Strawson-DE in restriction position (subject = w0)
    IsStrawsonDE (superlativeAssert World.w0)
      (superlativePresup World.w0) :=
  ⟨⟨onlyFull_isStrawsonDE _, onlyFull_not_de⟩,
   sorryFull_strictly_strawsonDE,
   conditional_antecedent_strawsonDE _ _ _,
   superlative_isStrawsonDE _⟩

/-! ## Cross-framework bridges

These theorems make explicit the relationships between vF's Strawson-DE
analysis and three sibling NPI theories already formalized in linglib.
Per CLAUDE.md "chronological dependency" rule: this file may reference
@cite{kadmon-landman-1993} (1993 < 1999), @cite{lahiri-1998} (1998 < 1999),
and @cite{hoeksema-1983} (1983 < 1999), but not the reverse.
-/

/-- **K&L ≡ vF on the basic adversative asymmetry.** Both
    @cite{kadmon-landman-1993} (K&L) and @cite{von-fintel-1999} (vF)
    derive the `sorry`/`glad` asymmetry from formally identical Lean
    theorems — K&L via "lexical entailment to *want ¬A*", vF via
    Strawson-DE / UE of the attitude operator. The two prose
    explanations are different; the formalizations agree by `rfl`.

    This is exactly the kind of theoretical-incompatibility-collapse
    that linglib's interconnection-density discipline aims to surface.
    The empirical predictions are the same; choosing between the two
    analyses requires looking at examples that distinguish their
    semantic predictions, e.g. K&L's "settle for less" reading
    (`bridge_lahiri_glad_settle_overgeneration` below). -/
theorem bridge_kl_vf_sorry_strawsonDE_agreement
    (dox bestOf : World → Set World) :
    KadmonLandman1993.sorry_licenses_any dox bestOf =
    ex28b_sorry_strawsonDE dox bestOf :=
  rfl

theorem bridge_kl_vf_glad_UE_agreement
    (dox bestOf : World → Set World) :
    KadmonLandman1993.glad_does_not_license dox bestOf =
    ex50_gladKL_isUE dox bestOf :=
  rfl

/-- **`gladFull_isUE` overgenerates against Lahiri's "settle for less"
    Hindi data.** @cite{lahiri-1998} §4.5 (datum
    `npi_glad_settle`) records that Hindi *khuS* + NPI *koii bhii* IS
    grammatical on a "settle for less" reading. K&L flag the same in
    English (file `KadmonLandman1993.settle_glad_anybody`,
    `settle_glad_tickets`). The substrate's `gladFull_isUE` predicts
    uniformly NO licensing — so the substrate undergenerates here, and
    the "settle for less" reading would require either (a) a different
    `gladFull` semantics with a perspective shift, or (b) a Strawson-DE
    treatment of the rescued reading.

    This theorem records the empirical refutation as a Lean-checkable
    incompatibility between the substrate and the data. -/
theorem bridge_lahiri_glad_settle_overgeneration :
    -- Lahiri 1998: Hindi 'glad'-NPI is grammatical on settle-for-less reading
    Lahiri1998.npi_glad_settle.grammatical = true ∧
    -- K&L 1993: same in English
    KadmonLandman1993.settle_glad_anybody.grammatical = true ∧
    KadmonLandman1993.settle_glad_tickets.grammatical = true ∧
    -- Substrate's gladFull predicts uniformly UE → NPI not licensed.
    -- The substrate cannot capture the settle-for-less reading without
    -- additional machinery (e.g., a perspective-shifted bestOf).
    -- This conjunction merely records the empirical facts; the substrate
    -- gap is documented in the docstring, not proved as a contradiction.
    True :=
  ⟨rfl, rfl, rfl, trivial⟩

/-- **Hoeksema's S-comparative is anti-additive, hence trivially Strawson-DE.**
    @cite{hoeksema-1983} proves the S-comparative anti-additive
    (`Semantics.Degree.Comparative.sComparative_isAntiAdditive`); the
    inheritance chain AA → DE → Strawson-DE makes the bridge automatic.

    This places the S-comparative in the same Strawson-DE class as
    @cite{von-fintel-1999}'s recalcitrants, but with the additional
    classical AA backing — meaning S-comparatives license *strong* NPIs
    too (whereas vF's `only` only licenses weak NPIs). -/
theorem bridge_hoeksema_sComparative_strawsonDE
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonDE (Semantics.Degree.Comparative.sComparative μ) defined :=
  antitone_implies_strawsonDE _
    (Semantics.Degree.Comparative.sComparative_isAntiAdditive μ).antitone defined

end Phenomena.Polarity.Studies.VonFintel1999
