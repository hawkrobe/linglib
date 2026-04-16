import Linglib.Theories.Semantics.Attitudes.EmbeddingConstraints
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Phenomena.Questions.Embedding

/-!
# @cite{elliott-etal-2017} Predicates of Relevance and Theories of Question Embedding

*Journal of Semantics* 34(3): 547–554, doi:10.1093/jos/ffx008.

## The Puzzle

Two architectures for clause-embedding predicates:

1. **Question-to-proposition** (Karttunen 1977 @cite{karttunen-1977},
   Lahiri @cite{lahiri-2002}). Treat propositional embedding as primitive
   and reduce question embedding via a meaning postulate. Karttunen's classic
   postulate for `know`:
   ```
   ⟦know⟧ʷ(Q)(x)  ↔  ∀p ∈ Q. p(w) → ⟦know⟧ʷ(p)(x)
   ```
2. **Proposition-to-question** (Uegaki @cite{uegaki-2015},
   Theiler-Roelofsen-Aloni @cite{theiler-etal-2018},
   Roelofsen-Uegaki @cite{roelofsen-uegaki-2020}).
   Treat question embedding as primitive and lift propositions into singleton
   questions via a propositional analogue of @cite{partee-1987}'s `IDENT`:
   ```
   ID := λp_st. {p}     -- "ID" of @cite{elliott-etal-2017}
   ```

@cite{elliott-etal-2017} argue that **Predicates of Relevance** (PoRs) like
`care`, `matter`, `be relevant` decisively favour the second architecture.
The argument: PoRs embed both declaratives and interrogatives, but their
interrogative meaning **cannot** be reduced to a universal generalisation
over their declarative meaning, because PoR-`that` carries an existence +
belief presupposition that two competing answers cannot jointly satisfy.

## What This Study Verifies

- The Karttunen-style universal reduction (`IsKarttunenReducible`).
- A predicate satisfying the universal reduction must be C-distributive
  (so the existential and universal reductions cannot be empirically
  separated by polar questions modulo verum/falsum) — but the conjunction
  of universal reduction with a polar-incompatible presupposition entails
  vacuous falsity for polar questions, contradicting PoR data.
- The propositional ID type-shift (`idQ`), an instance of the schematic
  `propIdent` from `Theories/Semantics/Composition/TypeShifting`.
- An Elliott-style `care` lexical entry parametrised by an existence
  presupposition and a per-alternative belief presupposition; the
  contradictory-belief predicate forces vacuous falsity under universal
  reduction.
- Cross-link from the empirical `care_d` / `matter_d` data in
  `Phenomena.Questions.Embedding` to this study.

The closely related Roelofsen-Uegaki refinement of this entry
(doxastic support + bouletic settlement) lives in
`Theories/Semantics/Attitudes/EmbeddingConstraints.careSem`; we keep
Elliott's presupposition-componentwise version separate so it stays
recoverable from the original paper.
-/

namespace Phenomena.Questions.Studies.Elliott2017

open Semantics.Attitudes.CDistributivity (QuestionDen IsCDistributive)
open Semantics.Attitudes.EmbeddingConstraints (DoxState BouState careSem)
open Phenomena.Questions.Embedding (care_d matter_d EmbeddingDatum)

-- A. The Karttunen-style universal reduction (eq. 8)

-- UNVERIFIED: @cite{elliott-etal-2017} eq. 8
/--
**Karttunen-style universal reduction.** A predicate `V` is *Karttunen-reducible*
iff its question semantics is the universal generalisation of its declarative
semantics over the answer set:

```
⟦V⟧ʷ(Q)(x)  ↔  ∀p ∈ Q. ⟦V⟧ʷ(p)(x)
```

This is the @cite{karttunen-1977} schema for `know`, weakly-exhaustive style.
@cite{elliott-etal-2017} argue this schema cannot extend to PoRs.

The veridicality factor (`p(w) →`) of the original Karttunen postulate is
absorbed here into the propositional component `V_prop`, since for PoRs
that factor is itself part of what's at issue.
-/
def IsKarttunenReducible {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (Q : QuestionDen W) (w : W),
    V_question x Q w = true ↔ ∀ p ∈ Q, V_prop x p w = true

/--
**Vacuous-falsity prediction.** If `V` satisfies the universal Karttunen
reduction and its propositional kernel cannot simultaneously hold of two
specific answers `p₁` and `p₂`, then `V_question x [p₁, p₂] w = false`.

Applied to `care` with Elliott's belief presupposition (`Bel_x(p) ∨ Bel_x(¬p)`),
the polar question `Q = {p, ¬p}` instantiates `p₁ = p`, `p₂ = ¬p`, and the
incompatibility hypothesis follows from the consistency of `x`'s beliefs.
The theorem then predicts that `Mary cares whether Sue is sick` is *always*
false — contradicting the data in @cite{elliott-etal-2017} (4)–(6).
-/
theorem karttunen_predicts_vacuous_falsity {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hKR : IsKarttunenReducible V_prop V_question)
    (x : E) (p₁ p₂ : BProp W) (w : W)
    (hIncompat : ¬ (V_prop x p₁ w = true ∧ V_prop x p₂ w = true)) :
    V_question x [p₁, p₂] w = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have hAll := (hKR x [p₁, p₂] w).mp h
  refine hIncompat ⟨hAll p₁ ?_, hAll p₂ ?_⟩
  · simp
  · simp

/--
**Karttunen reduction is strictly stronger than C-distributivity for
non-empty questions.** Universal reduction (`∀p ∈ Q. V_prop p`) implies
the existential reading (`∃p ∈ Q. V_prop p`) when `Q` is non-empty.
The converse fails: a predicate can be true of a question via a single
witness without being true of every answer — which is precisely why the
existential C-distributivity, not the universal Karttunen reduction, is
the right direction-of-fit for proposition-to-question architectures.
-/
theorem karttunen_implies_witness_nonempty {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hKR : IsKarttunenReducible V_prop V_question)
    (x : E) (Q : QuestionDen W) (w : W) (hNE : Q ≠ [])
    (hV : V_question x Q w = true) :
    ∃ p ∈ Q, V_prop x p w = true := by
  have hAll := (hKR x Q w).mp hV
  match Q, hNE with
  | p :: _, _ => exact ⟨p, List.mem_cons_self, hAll p List.mem_cons_self⟩

-- B. The propositional ID type-shift (eq. 10)

-- UNVERIFIED: @cite{elliott-etal-2017} eq. 10
/--
**Propositional ID type-shift.** `idQ p = [p]` realises @cite{partee-1987}'s
`IDENT` one type-theoretic level up: from entity ↦ singleton property to
proposition ↦ singleton question. This is `ID` of @cite{elliott-etal-2017}.

The Hamblin/Karttunen list realisation here is the concrete counterpart of
the schematic `propIdent : F.Denot Ty.prop → F.Denot (Ty.prop ⇒ Ty.t)`
in `Semantics.Composition.TypeShifting`.
-/
def idQ {W : Type*} (p : BProp W) : QuestionDen W := [p]

/-- The defining property of `idQ`: membership is identity with the
underlying proposition. -/
@[simp] theorem mem_idQ {W : Type*} (p q : BProp W) :
    q ∈ idQ p ↔ q = p := by
  simp [idQ]

/--
**ID inverts the singleton answer set.** Any predicate that is C-distributive
agrees with its propositional kernel on `idQ`-shifted complements:

```
V_question x (idQ p) w = V_prop x p w
```

This is the formal expression of "propositional embedding is question
embedding via ID" — the (→) half of the proposition-to-question architecture.
-/
theorem cDist_agrees_on_idQ {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hCD : IsCDistributive V_prop V_question)
    (x : E) (p : BProp W) (w : W) :
    V_question x (idQ p) w = V_prop x p w := by
  cases hVp : V_prop x p w
  · -- V_prop = false. Show V_question = false.
    cases hVq : V_question x (idQ p) w
    · rfl
    · exfalso
      obtain ⟨q, hq_mem, hq⟩ := (hCD x (idQ p) w).mp hVq
      rw [(mem_idQ p q).mp hq_mem, hVp] at hq
      exact Bool.false_ne_true hq
  · -- V_prop = true. Show V_question = true.
    exact (hCD x (idQ p) w).mpr ⟨p, (mem_idQ p p).mpr rfl, hVp⟩

-- C. Elliott's care semantics with explicit presuppositions (eq. 9)

-- UNVERIFIED: @cite{elliott-etal-2017} eq. 9
/--
**Elliott's `care` lexical entry.** The paper's eq. (9) decomposes
`⟦care⟧ʷ(Q)(x)` into three components:

- *Existence presupposition*: some answer in `Q` is true at `w`.
- *Belief presupposition*: for every alternative in `Q`, the attitude
  holder has settled beliefs (believes either `p` or `¬p`).
- *Asserted content*: a relevance/utility condition over the alternatives.

We parametrise each component so the lexical entry is recoverable from any
choice of doxastic backgrounds and relevance metric.
-/
def elliottCareSem {W E : Type*}
    (existencePresup : QuestionDen W → W → Bool)
    (beliefPresup : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    existencePresup Q w &&
    Q.all (fun p => beliefPresup x p w) &&
    relevance x Q w

/--
**Elliott's `care` cannot be Karttunen-reduced** in any non-trivial way.
If we instantiate the propositional kernel as `λp. elliottCareSem … x [p] w`
and the belief presupposition as a *consistent* belief state — meaning
`beliefPresup x p w` and `beliefPresup x (¬p) w` cannot both hold — then
`care` of the polar question `{p, ¬p}` is forced false by
`karttunen_predicts_vacuous_falsity`, contradicting the licit reading of
`Mary cares whether Sue is sick`.
-/
theorem elliottCare_not_karttunen_reducible {W E : Type*}
    (existencePresup : QuestionDen W → W → Bool)
    (beliefPresup : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    (notP : BProp W → BProp W)
    (x : E) (p : BProp W) (w : W)
    (hConsistent : ¬ (beliefPresup x p w = true ∧ beliefPresup x (notP p) w = true))
    (hKR : IsKarttunenReducible
              (fun y q v => elliottCareSem existencePresup beliefPresup relevance y [q] v)
              (elliottCareSem existencePresup beliefPresup relevance)) :
    elliottCareSem existencePresup beliefPresup relevance x [p, notP p] w = false := by
  apply karttunen_predicts_vacuous_falsity _ _ hKR x p (notP p) w
  intro ⟨h1, h2⟩
  -- Both singleton care meanings hold, so both belief presuppositions hold.
  -- That contradicts `hConsistent`.
  apply hConsistent
  refine ⟨?_, ?_⟩
  · simp only [elliottCareSem, List.all_cons, List.all_nil, Bool.and_true,
               Bool.and_eq_true] at h1
    exact h1.1.2
  · simp only [elliottCareSem, List.all_cons, List.all_nil, Bool.and_true,
               Bool.and_eq_true] at h2
    exact h2.1.2

-- D. Empirical anchor: connection to the embedding datum table

/-- `care` is responsive: it embeds both interrogatives (subordination)
and declaratives. Verified directly from the datum in
`Phenomena.Questions.Embedding`. -/
theorem care_is_responsive :
    care_d.subordination = true ∧ care_d.embedsDeclarative = true := by
  decide

/-- `matter` is responsive in the same sense as `care`. -/
theorem matter_is_responsive :
    matter_d.subordination = true ∧ matter_d.embedsDeclarative = true := by
  decide

/-- @cite{elliott-etal-2017}'s judgement (4)/(5)/(6) summary, recorded as
data: PoRs are responsive *and* their question meaning is *not* the
universal reduction of their declarative meaning. The first conjunct is
the `EmbeddingDatum`; the second conjunct is the theoretical content
captured by `elliottCare_not_karttunen_reducible`. -/
structure PoRJudgement where
  datum : EmbeddingDatum
  responsive : datum.subordination = true ∧ datum.embedsDeclarative = true
  resistsUniversalReduction : Bool

def careJudgement : PoRJudgement :=
  { datum := care_d
    responsive := care_is_responsive
    resistsUniversalReduction := true }

def matterJudgement : PoRJudgement :=
  { datum := matter_d
    responsive := matter_is_responsive
    resistsUniversalReduction := true }

-- E. Bridge to the Roelofsen-Uegaki refinement

/--
The @cite{roelofsen-uegaki-2020} refinement of Elliott's `care` lives at
`Semantics.Attitudes.EmbeddingConstraints.careSem`. It collapses Elliott's
existence + belief presuppositions into a *doxastic support* condition
(`DOX ⊆ ⋃Q`) and a *bouletic settlement* condition (`BOU ⊆ p ∨ BOU ∩ p = ∅`).

Both formulations agree on the empirical core: PoR-`whether` is licit
even though no single answer satisfies the propositional kernel.
The Roelofsen-Uegaki version additionally satisfies P-to-Q Entailment
(see `EmbeddingConstraints.care_satisfies_ptoq`), placing `care` in the
`P-to-Q ⧹ C-distributivity` cell of the constraint hierarchy.
-/
example {W E : Type*}
    (dox : E → W → DoxState W)
    (bou : E → W → BouState W)
    (doxSupports : DoxState W → QuestionDen W → Bool)
    (settled : BouState W → BProp W → Bool) :
    E → QuestionDen W → W → Bool :=
  Semantics.Attitudes.EmbeddingConstraints.careSem dox bou doxSupports settled

end Phenomena.Questions.Studies.Elliott2017
