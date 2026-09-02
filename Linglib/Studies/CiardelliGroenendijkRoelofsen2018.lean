import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Resolution

/-!
# Ciardelli, Groenendijk & Roelofsen 2018: Inquisitive Semantics

The substrate of `Semantics/Questions/` is the formalisation of
[ciardelli-groenendijk-roelofsen-2018] (*Inquisitive Semantics*, Oxford Surveys
in Semantics and Pragmatics 6): every Chapter 2–3 definition has a direct
substrate counterpart. This file records the correspondence — the table below
maps each definition and fact to its substrate identifier — and proves the one
chapter-2 fact stated over two contents at once, `update_nonInquisitive`
(Fact 2.36, the book's "update without inquisitiveness yields standard
results").

## Substrate identification table

### Chapter 2 — Basic notions

| [ciardelli-groenendijk-roelofsen-2018]    | substrate                        |
|-----|-----|
| Def 2.1 Information state `s ⊆ W`              | `Set W` (mathlib)                |
| Def 2.2 Enhancement `t ⊆ s`                    | set inclusion                    |
| Def 2.3 Issue (non-empty downward-closed set of states) | `Question W`        |
| Def 2.4 Resolution `s ∈ I`                     | `s ∈ I.props` ≡ `Support.supports s I` |
| Def 2.5 Issues over a state `⋃I = s`           | `info I = s`                     |
| Def 2.6 Refinement `I ⊆ J`                     | `(I : Question W) ≤ J`           |
| Def 2.7 Alternatives in an issue (max elts)    | `Question.alt`              |
| Fact 2.8 Multi-alts iff proper (finite case)   | `isInquisitive_of_two_alternatives` (one direction; full equivalence under `Q.props.Finite`) |
| Def 2.9 Proposition (non-empty downward-closed)| `Question W` (same as Issue) |
| Def 2.10 Informative content `info(P) := ⋃P`   | `Question.info`             |
| Def 2.11 Issue embodied by P                   | `P` itself                       |
| Def 2.12 Truth `w ∈ info(P)`                   | `w ∈ info P`                     |
| Def 2.13 Support `s ∈ P`                       | `Support.supports s P`           |
| Fact 2.14 Truth = singleton support            | `mem_info_iff_singleton_mem`     |
| Def 2.15 Informative / Inquisitive             | `isInformative` / `isInquisitive` |
| Def 2.16 Alternatives in a proposition         | `Question.alt`              |
| Fact 2.17 Inquisitive iff multi-alts (finite)  | (specialisation of Fact 2.8)     |
| Fact 2.18 (i) Non-inquisitive ↔ `info(P) ∈ P`  | `info_mem_iff_not_isInquisitive` |
| Fact 2.18 (ii) Non-informative ↔ `info(P) = W` | `not_not` on `isInformative`'s definition |
| Fact 2.18 (iii) Tautology ↔ `W ∈ P`            | `eq_top_iff_univ_mem`            |
| Fact 2.19 Non-inquisitive characterizations    | (1↔2) `info_mem_iff_eq_ofSet_info`; (4) `mem_iff_subset_info` |
| Def 2.20–2.22 Entailment `P ⊨ Q ↔ P ⊆ Q`       | substrate's `≤` (`le_def`)       |
| Fact 2.23 Entailment as support preservation   | by `le_def`                      |
| Def 2.24 Tautology `⊤ := ℘(W)`, contradiction `⊥ := {∅}` | `top` / `bot`           |
| Fact 2.25 Partial order on propositions        | `inferInstance : CompleteLattice` |
| Def 2.26 Context (= proposition)               | `Question W`                |
| Def 2.27 `info(C) := ⋃C`                       | `Question.info`             |
| Def 2.28-2.32 Informed/inquisitive contexts    | `isInformative` / `isInquisitive` |
| Def 2.30 Initial / absurd contexts             | `⊤` / `⊥`                       |
| Def 2.35 Update `C[P] := C ∩ P`                | `C ⊓ P` (substrate's `inf`, `rfl` on `props`) |
| Fact 2.36 Update reduces to standard on non-inquisitive | `update_nonInquisitive` (this file) |

### Chapter 3 — Basic operations

| [ciardelli-groenendijk-roelofsen-2018]    | substrate                        |
|-----|-----|
| Fact 3.1 Meet `⋂Σ = {s \| s ∈ P ∀ P ∈ Σ}`      | `sInf` / `mem_sInf`              |
| Fact 3.2 Join `⋃Σ = {s \| s ∈ P ∃ P ∈ Σ}`      | `sSup` / `mem_sSup`              |
| Fact 3.3 Relative pseudo-complement `P ⇒ Q`    | substrate's Heyting `⇨` (`mem_himp`) |
| Fact 3.4 Absolute pseudo-complement `P*`       | substrate's `Pᶜ`                 |
| Fact 3.5 `P* = ℘(¬info(P))`                    | `compl_eq`                       |
| Def 3.8-3.9 Decision set `D(P) := P ∪ P*`      | derived from `inqDisj P Pᶜ`      |
| Def 3.13 Projection `!P := ℘(info(P))`         | `proj` (`rfl`)                   |
| Def 3.13 Projection `?P := P ∪ P*`             | `nonInfo` (`nonInfo_eq_sup_compl`) |
| Fact 3.14 Division `P = !P ⊓ ?P`               | `proj_inf_nonInfo`               |
| Fact 3.15 `!P = P**`                           | `proj_eq_compl_compl`            |

### Chapter 5 — Questions

| [ciardelli-groenendijk-roelofsen-2018]    | substrate                        |
|-----|-----|
| §5.1 Polar `?Mab := Mab ∨ ¬Mab`                | `Question.polar` (`polar_eq_sup`) |
| §5.2 Alternative `Mab ∨ Mac`                   | `declarative Mab ⊔ declarative Mac` |
| §5.3 Open disjunctive `?(Mab ∨ Mac)`           | `nonInfo (ofSet Mab ⊔ declarative Mac)` |
| §5.4.1 Mention-all wh `∀x?Pax`                 | (substrate's [karttunen-1977] `which` modulo `?`) |
| §5.4.2 Mention-some wh `∃xLax`                 | `Question.which` (`mem_which`)   |
| §5.5.1 Conjoined `Q ∧ Q'`                      | `Q ⊓ Q'` (`inf_eq_conj`)         |
| §5.5.2 Disjoined `Q ∨ Q'`                      | `Q ⊔ Q'` (`sup_eq_inqDisj`)      |
| §5.5.3 Conditional `if A, Q ↦ A → Q`           | substrate's Heyting `A ⇨ Q`      |

## What this file does NOT cover

* **Ch 4** First-order syntax (the `InqB` logical language): the substrate
  is at the meaning side (`Question W`); the syntactic translation
  layer is not formalised here.
* **Ch 6** Disjunction, clause typing, intonation: partial coverage in
  `Semantics/Mood/` and the focus studies (`Studies/Rooth1992.lean`).
* **Ch 7** Conditionals: the substrate exposes `⇨` via the
  `HeytingAlgebra` instance; the chapter's empirical analysis lives in
  `Semantics/Conditionals/` and study files there.
* **Ch 8** Inquisitive epistemic logic / `know` and `wonder`: see
  `Semantics/Attitudes/` and `Studies/TheilerRoelofsenAloni2018.lean`.
* **Ch 9** Comparison with alternative and partition semantics: see
  `Studies/GroenendijkStokhof1984.lean` and `Semantics/Questions/`.

## References

* [I. Ciardelli, J. Groenendijk, F. Roelofsen, *Inquisitive Semantics*
  (2018)][ciardelli-groenendijk-roelofsen-2018]
-/

namespace CiardelliGroenendijkRoelofsen2018

variable {W : Type*}

open Question

/-- [ciardelli-groenendijk-roelofsen-2018] Fact 2.36 (Update without
    inquisitiveness yields standard results): when context and proposition
    are both non-inquisitive, the inquisitive update `C ⊓ P` is again
    non-inquisitive and its informative content is the standard
    intersection of the inputs' informative contents. (The informative
    half holds without the non-inquisitiveness assumptions — substrate
    `info_inf`; the CGR-specific content is declarativity
    preservation.) -/
theorem update_nonInquisitive (C P : Question W) (hC : C.info ∈ C)
    (hP : P.info ∈ P) :
    (C ⊓ P).info ∈ C ⊓ P ∧ (C ⊓ P).info = C.info ∩ P.info := by
  refine ⟨?_, info_inf C P⟩
  show (C ⊓ P).info ∈ (C ⊓ P).props
  rw [info_inf]
  exact ⟨C.downward_closed C.info hC _ Set.inter_subset_left,
    P.downward_closed P.info hP _ Set.inter_subset_right⟩

end CiardelliGroenendijkRoelofsen2018
