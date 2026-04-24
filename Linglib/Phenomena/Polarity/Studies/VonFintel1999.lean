import Linglib.Theories.Semantics.Entailment.StrawsonEntailment

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
    ¬ IsDownwardEntailing (onlyFull (· == World.w0)) :=
  onlyFull_not_de

/-- Ex. 18 (p. 104): `only` is Strawson-DE. The definedness predicate
    encodes the existence presupposition: there is some `w'` such that
    the focused individual `John` (here `· == .w0`) holds at `w'` and the
    scope predicate holds at `w'`. -/
theorem ex18_only_strawsonDE :
    IsStrawsonDE (onlyFull (· == World.w0))
      (fun scope _w => ∃ w', (w' == World.w0) = true ∧ scope w') :=
  onlyFull_isStrawsonDE _

/-- Ex. 11 + 18: the central separation. `only` is Strawson-DE without
    being classically DE — and Strawson-DE is enough to license NPIs
    under von Fintel's revised Fauconnier-Ladusaw schema. This is the
    paper's headline result for §2. -/
theorem ex11_18_only_strawson_separation :
    IsStrawsonDE (onlyFull (· == World.w0))
        (fun scope _w => ∃ w', (w' == World.w0) = true ∧ scope w') ∧
    ¬ IsDownwardEntailing (onlyFull (· == World.w0)) :=
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
makes the inference go through. Not formalized here because no
`sinceFull` operator exists in `StrawsonEntailment.lean`. Adding one is
mechanical — the structure mirrors `onlyFull` with a temporal predicate
in place of the existential presupposition.
-/

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
    The factivity component is what blocks DE: a narrower complement
    `p ⊆ q` may fail to hold at the evaluation world even when `q` does. -/
theorem ex30_sorry_not_DE :
    ¬ IsDownwardEntailing (sorryFull (fun _ => [World.w1])) :=
  sorryFull_not_de

/-- Ex. 28b (p. 111) — *the explanatory result*: `sorry` is Strawson-DE.
    The definedness predicate is factivity at the evaluation world
    (`p w`). Given factivity of the conclusion's complement and `p ⊆ q`,
    the inference `sorry q ⊨ sorry p` goes through.

    This explains why "Sandy is sorry that Robin bought any car" licenses
    `any` despite the complement position not being classically DE. -/
theorem ex28b_sorry_strawsonDE (bestOf : World → List World) :
    IsStrawsonDE (sorryFull bestOf) (fun p w => p w) :=
  sorryFull_isStrawsonDE bestOf

/-- Ex. 30 + ex. 28b — the adversative analogue of the only-separation:
    `sorry` is Strawson-DE without being classically DE. -/
theorem ex28_30_sorry_strawson_separation :
    IsStrawsonDE (sorryFull (fun _ => [World.w1])) (fun p w => p w) ∧
    ¬ IsDownwardEntailing (sorryFull (fun _ => [World.w1])) :=
  sorryFull_strictly_strawsonDE

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

/-- Ex. 52 (p. 124): `glad` is upward entailing in its complement. This
    predicts that NPIs are *not* licensed in the complement of `glad`
    — the empirical pattern that distinguishes `glad` from its adversative
    cousins. -/
theorem ex52_glad_isUE (bestOf : World → List World) :
    ∀ p q : Set World, (∀ w, p w → q w) →
      ∀ w, gladFull bestOf p w → gladFull bestOf q w :=
  gladFull_isUE bestOf

/-- The §3 headline: `sorry` and `glad` agree on factivity but differ on
    monotonicity in the complement, and this monotonicity asymmetry
    directly tracks the NPI-licensing asymmetry. -/
theorem ex28_vs_ex52_sorry_glad_asymmetry (bestOf : World → List World) :
    IsStrawsonDE (sorryFull bestOf) (fun p w => p w) ∧
    (∀ p q : Set World, (∀ w, p w → q w) →
      ∀ w, gladFull bestOf p w → gladFull bestOf q w) :=
  ⟨sorryFull_isStrawsonDE bestOf, gladFull_isUE bestOf⟩

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

    Caveat: the substrate's `condNecessity` is the strict subcase of vF
    eq. 72 where `max_g` reduces to the identity (totally realistic
    ordering source). The full Kratzer/Lewis conditional with a
    non-trivial preference ordering is *not* monotone, which is exactly
    the §4 puzzle this paper navigates around (cf. §4.3 + the
    @cite{von-fintel-2000} dynamic semantics). A faithful formalization
    of full eq. 72 awaits a Stalnaker-Lewis `would` operator in the
    substrate. -/
theorem ex72_conditional_antecedent_DE_idle
    (domain : World → List World) (β : Set World) :
    IsDownwardEntailing (fun α => condNecessity domain α β) :=
  conditional_antecedent_DE domain β

/-- Restrictor-style conditional antecedents are *a fortiori* Strawson-DE
    (since classical DE implies Strawson-DE via `de_implies_strawsonDE`). -/
theorem conditional_antecedent_strawsonDE_under_restrictor
    (domain : World → List World) (β : Set World)
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
    the subject (Emma) satisfies the restriction (has learned the
    alphabet). -/
theorem ex77_superlative_strawsonDE (subject : World → Bool) :
    IsStrawsonDE (superlativeAssert subject) (superlativePresup subject) :=
  superlative_isStrawsonDE subject

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
    (IsStrawsonDE (onlyFull (· == World.w0))
        (fun scope _w => ∃ w', (w' == World.w0) = true ∧ scope w') ∧
     ¬ IsDownwardEntailing (onlyFull (· == World.w0))) ∧
    -- §3 sorry: Strawson-DE without classical DE
    (IsStrawsonDE (sorryFull (fun _ => [World.w1])) (fun p w => p w) ∧
     ¬ IsDownwardEntailing (sorryFull (fun _ => [World.w1]))) ∧
    -- §4.1 conditional antecedent (restrictor analysis): classically DE,
    -- so trivially Strawson-DE
    IsStrawsonDE (fun α => condNecessity (fun _ => [World.w0, World.w1]) α
        (fun _ => True)) (fun _ _ => True) ∧
    -- §4.2 superlative: Strawson-DE in restriction position
    IsStrawsonDE (superlativeAssert (· == World.w0))
      (superlativePresup (· == World.w0)) :=
  ⟨⟨onlyFull_isStrawsonDE _, onlyFull_not_de⟩,
   sorryFull_strictly_strawsonDE,
   conditional_antecedent_strawsonDE _ _ _,
   superlative_isStrawsonDE _⟩

end Phenomena.Polarity.Studies.VonFintel1999
