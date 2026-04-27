import Linglib.Core.Question.Basic
import Linglib.Core.Question.Hamblin
import Linglib.Theories.Semantics.Questions.Resolution

/-!
# @cite{ciardelli-groenendijk-roelofsen-2018}: Inquisitive Semantics
@cite{frege-1918} @cite{hintikka-1962} @cite{stalnaker-1978} @cite{hamblin-1973} @cite{karttunen-1977} @cite{groenendijk-stokhof-1984} @cite{puncochar-2019}

Substrate-audit study file for @cite{ciardelli-groenendijk-roelofsen-2018}
*Inquisitive Semantics* (OUP, Oxford Surveys in Semantics and
Pragmatics 6). The substrate of `Core/Question/` IS this paper's
formalisation: every CGR Chapter-2 and Chapter-3 definition has a
direct counterpart in `Core.Question`. This file's job is to make the
correspondence explicit, by (a) docstring-mapping each CGR definition
to its substrate identifier and (b) re-proving the key CGR facts on
the substrate so that the substrate is verifiably faithful to CGR.

Unique among `Studies/` files: this is **not** a paper *replication*
(building the paper's machinery from scratch and showing it agrees
with the substrate) — it is a paper *audit* (confirming the substrate
already implements the paper).

## Substrate identification table

### Chapter 2 — Basic notions

| @cite{ciardelli-groenendijk-roelofsen-2018}    | substrate                        |
|-----|-----|
| Def 2.1 Information state `s ⊆ W`              | `Set W` (mathlib)                |
| Def 2.2 Enhancement `t ⊆ s`                    | set inclusion                    |
| Def 2.3 Issue (non-empty downward-closed set of states) | `Core.Question W`        |
| Def 2.4 Resolution `s ∈ I`                     | `s ∈ I.props` ≡ `Support.supports s I` |
| Def 2.5 Issues over a state `⋃I = s`           | `info I = s`                     |
| Def 2.6 Refinement `I ⊆ J`                     | `(I : Question W) ≤ J`           |
| Def 2.7 Alternatives in an issue (max elts)    | `Core.Question.alt`              |
| Fact 2.8 Multi-alts iff proper (finite case)   | `isInquisitive_of_two_alternatives` (one direction; full equivalence under `Q.props.Finite`) |
| Def 2.9 Proposition (non-empty downward-closed)| `Core.Question W` (same as Issue) |
| Def 2.10 Informative content `info(P) := ⋃P`   | `Core.Question.info`             |
| Def 2.11 Issue embodied by P                   | `P` itself                       |
| Def 2.12 Truth `w ∈ info(P)`                   | `w ∈ info P`                     |
| Def 2.13 Support `s ∈ P`                       | `Support.supports s P`           |
| Fact 2.14 Truth = singleton support            | `truth_iff_singleton_support`    |
| Def 2.15 Informative / Inquisitive             | `isInformative` / `isInquisitive` |
| Def 2.16 Alternatives in a proposition         | `Core.Question.alt`              |
| Fact 2.17 Inquisitive iff multi-alts (finite)  | (specialisation of Fact 2.8)     |
| Fact 2.18 Non-inquisitive ↔ `info(P) ∈ P`      | `isDeclarative_iff_not_isInquisitive` (substrate uses `isDeclarative` for "non-inquisitive") |
| Fact 2.19 Non-inquisitive characterizations    | `isDeclarative_iff_eq_declarative_info` |
| Def 2.20–2.22 Entailment `P ⊨ Q ↔ P ⊆ Q`       | substrate's `≤` (`le_def`)       |
| Fact 2.23 Entailment as support preservation   | by `le_def`                      |
| Def 2.24 Tautology `⊤ := ℘(W)`, contradiction `⊥ := {∅}` | `top` / `bot`           |
| Fact 2.25 Partial order on propositions        | `inferInstance : CompleteLattice` |
| Def 2.26 Context (= proposition)               | `Core.Question W`                |
| Def 2.27 `info(C) := ⋃C`                       | `Core.Question.info`             |
| Def 2.28-2.32 Informed/inquisitive contexts    | `isInformative` / `isInquisitive` |
| Def 2.30 Initial / absurd contexts             | `⊤` / `⊥`                       |
| Def 2.35 Update `C[P] := C ∩ P`                | `C ⊓ P` (substrate's `inf`)      |
| Fact 2.36 Update reduces to standard on non-inquisitive | `update_non_inquisitive_eq_intersection` |

### Chapter 3 — Basic operations

| @cite{ciardelli-groenendijk-roelofsen-2018}    | substrate                        |
|-----|-----|
| Fact 3.1 Meet `⋂Σ = {s \| s ∈ P ∀ P ∈ Σ}`      | `sInf` / `sInfContent`           |
| Fact 3.2 Join `⋃Σ = {s \| s ∈ P ∃ P ∈ Σ}`      | `sSup` / `sSupContent`           |
| Fact 3.3 Relative pseudo-complement `P ⇒ Q`    | substrate's Heyting `⇨` (HeytingAlgebra instance) |
| Fact 3.4 Absolute pseudo-complement `P*`       | substrate's `Pᶜ`                 |
| Fact 3.5 `P* = ℘(¬info(P))`                    | `compl_eq`                       |
| Def 3.8-3.9 Decision set `D(P) := P ∪ P*`      | derived from `inqDisj P Pᶜ`      |
| Def 3.13 Projection `!P := ℘(info(P))`         | `proj`                           |
| Def 3.13 Projection `?P := P ∪ P*`             | `nonInfo`                        |
| Fact 3.14 Division `P = !P ⊓ ?P`               | `proj_inf_nonInfo`               |
| Fact 3.15 `!P = P**`, `?P = P ∪ P*`            | `proj_eq_compl_compl`            |

### Chapter 5 — Questions

| @cite{ciardelli-groenendijk-roelofsen-2018}    | substrate                        |
|-----|-----|
| §5.1 Polar `?Mab := Mab ∨ ¬Mab`                | `Core.Question.polar`            |
| §5.2 Alternative `Mab ∨ Mac`                   | `declarative Mab ⊔ declarative Mac` |
| §5.3 Open disjunctive `?(Mab ∨ Mac)`           | `nonInfo (declarative Mab ⊔ declarative Mac)` |
| §5.4.1 Mention-all wh `∀x?Pax`                 | (substrate's @cite{karttunen-1977} `which` modulo `?`) |
| §5.4.2 Mention-some wh `∃xLax`                 | `Core.Question.which` (Hamblin disjunction)   |
| §5.5.1 Conjoined `Q ∧ Q'`                      | `Q ⊓ Q'` (substrate's `inf`)     |
| §5.5.2 Disjoined `Q ∨ Q'`                      | `Q ⊔ Q'` (substrate's `sup`)     |
| §5.5.3 Conditional `if A, Q ↦ A → Q`           | substrate's Heyting `A ⇨ Q`      |

## What this file does NOT cover

* **Ch 4** First-order syntax (the `InqB` logical language): the substrate
  is at the meaning side (`Core.Question W`); the syntactic translation
  layer is not formalised here.
* **Ch 6** Disjunction, clause typing, intonation: partial coverage in
  `Theories/Semantics/Mood/` and `Phenomena/Focus/`.
* **Ch 7** Conditionals: the substrate exposes `⇨` via the
  `HeytingAlgebra` instance; @cite{ciardelli-groenendijk-roelofsen-2018}
  Ch 7's full empirical analysis lives in
  `Theories/Semantics/Conditionals/` and study files there.
* **Ch 8** Inquisitive epistemic logic / `know` and `wonder`: see
  `Theories/Semantics/Attitudes/` and `Phenomena/Complementation/Studies/TheilerRoelofsenAloni2018.lean`.
* **Ch 9** Comparison with alternative semantics, partition semantics,
  inquisitive indifference: covered piecemeal in
  `Phenomena/Questions/Studies/{Hamblin1973_TODO, GroenendijkStokhof1984}.lean`
  (alt and partition) and `Theories/Semantics/Questions/` (as topical
  bridges).
-/

namespace Phenomena.Questions.Studies.CiardelliGroenendijkRoelofsen2018

universe u
variable {W : Type u}

open Core Core.Question Semantics.Questions.Resolution

/-! ### §2.4.1 Truth and support

@cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.14: a proposition is
true at a world iff it is supported by the singleton state. The
substrate-level proof uses `info` and `downward_closed`. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.14 (Truth and
    support): `P` is true at `w` iff `P` is supported by `{w}`. -/
theorem truth_iff_singleton_support (P : Question W) (w : W) :
    w ∈ info P ↔ ({w} : Set W) ∈ P := by
  constructor
  · rintro ⟨q, hq, hwq⟩
    exact P.downward_closed q hq {w} (Set.singleton_subset_iff.mpr hwq)
  · intro h
    exact ⟨{w}, h, rfl⟩

/-! ### §2.4.2 Informative and inquisitive propositions

@cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.18: substrate has
`isDeclarative` for "non-inquisitive". Re-state Fact 2.18's three
disjuncts under substrate names. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.18 (i):
    non-inquisitive iff `info(P) ∈ P`. The substrate's
    `isDeclarative` IS this condition by definition. -/
theorem CGR_2_18_non_inquisitive_iff (P : Question W) :
    ¬ P.isInquisitive ↔ P.isDeclarative :=
  (isDeclarative_iff_not_isInquisitive P).symm

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.18 (ii):
    non-informative iff `info(P) = W`. The substrate's `isInformative`
    is "informative content excludes some world", so non-informative is
    the negation. -/
theorem CGR_2_18_non_informative_iff (P : Question W) :
    ¬ P.isInformative ↔ P.info = Set.univ := by
  unfold isInformative
  exact not_not

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.18 (iii):
    `P` is a tautology iff `W ∈ P`. -/
theorem CGR_2_18_tautology_iff (P : Question W) :
    P = ⊤ ↔ Set.univ ∈ P := by
  constructor
  · rintro rfl; exact Set.mem_univ _
  · intro hUniv
    apply le_antisymm le_top
    intro q _
    exact P.downward_closed Set.univ hUniv q (Set.subset_univ _)

/-! ### §2.4.2 Fact 2.19 — Non-inquisitive characterizations

@cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.19 lists four
equivalent characterizations of non-inquisitivity. The substrate has
the `isDeclarative_iff_eq_declarative_info` form (corresponding to
characterization 2 in the chain). The other directions follow. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.19 (1↔2):
    non-inquisitive iff `P = ℘(info(P))` (the principal-ideal
    characterization). The substrate-level
    `isDeclarative_iff_eq_declarative_info` IS this. -/
theorem CGR_2_19_eq_declarative_info (P : Question W) :
    P.isDeclarative ↔ P = declarative P.info :=
  isDeclarative_iff_eq_declarative_info P

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.19 (4):
    non-inquisitive iff `P` is supported by `s` exactly when `P` is
    true at every world in `s` (truth-conditional support). Direct
    consequence of `truth_iff_singleton_support` + downward closure. -/
theorem CGR_2_19_truth_conditional (P : Question W)
    (h : P.isDeclarative) (s : Set W) :
    s ∈ P ↔ ∀ w ∈ s, w ∈ info P := by
  have heq := (isDeclarative_iff_eq_declarative_info P).mp h
  constructor
  · intro hs w hw
    exact ⟨s, hs, hw⟩
  · intro hAll
    rw [heq, mem_declarative]
    intro w hw
    exact hAll w hw

/-! ### §2.5 Contexts and update

@cite{ciardelli-groenendijk-roelofsen-2018} Def 2.35: update is
`C[P] := C ∩ P` — the substrate's lattice meet `⊓`. Fact 2.36: when
both `C` and `P` are non-inquisitive (i.e., declaratives), the update
reduces to the standard intersection on informative content. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Def 2.35: update IS the
    substrate meet operation. Tautology — substrate-`⊓` was defined
    pointwise on `props`. Stated as a theorem to anchor the
    substrate's `inf` to CGR's `[·]` notation. -/
theorem CGR_2_35_update_eq_inf (C P : Question W) :
    (C ⊓ P).props = C.props ∩ P.props := rfl

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 2.36 (Update
    without inquisitiveness reproduces standard results): if both `C`
    and `P` are non-inquisitive, then their update is again
    non-inquisitive, with informative content equal to the standard
    intersection of the inputs' informative contents. -/
theorem CGR_2_36_update_non_inquisitive
    (C P : Question W) (hC : C.isDeclarative) (hP : P.isDeclarative) :
    (C ⊓ P).isDeclarative ∧ (C ⊓ P).info = C.info ∩ P.info := by
  -- Step 1: info commutes with meet on declaratives.
  have hInfo : (C ⊓ P).info = C.info ∩ P.info := by
    apply le_antisymm
    · exact info_inf_subset C P
    · intro w ⟨hwC, hwP⟩
      have hCsing : ({w} : Set W) ∈ C := (truth_iff_singleton_support C w).mp hwC
      have hPsing : ({w} : Set W) ∈ P := (truth_iff_singleton_support P w).mp hwP
      exact ⟨{w}, ⟨hCsing, hPsing⟩, rfl⟩
  refine ⟨?_, hInfo⟩
  -- Step 2: declarativity. We need (C ⊓ P).info ∈ (C ⊓ P).props.
  show (C ⊓ P).info ∈ (C ⊓ P).props
  rw [hInfo]
  refine ⟨?_, ?_⟩
  · -- C.info ∩ P.info ⊆ C.info, and C.info ∈ C by hC, so by downward
    -- closure C.info ∩ P.info ∈ C.
    exact C.downward_closed C.info hC _ Set.inter_subset_left
  · exact P.downward_closed P.info hP _ Set.inter_subset_right

/-! ### §3.1.2 Algebraic operations on inquisitive propositions

@cite{ciardelli-groenendijk-roelofsen-2018} Facts 3.1, 3.2, 3.5 and
the projection-related Facts 3.13–3.15. The substrate already
provides these as `sInf`, `sSup`, `compl_eq`, `proj`, `nonInfo`, and
their respective theorems. The bridge theorems below give the CGR
formulations directly on the substrate's vocabulary. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 3.1 (Meet):
    arbitrary meet has support iff every member supports.
    Substrate-side: `sInfContent` is defined this way; restate to
    expose the CGR membership iff. -/
theorem CGR_3_1_meet (S : Set (Question W)) (s : Set W) :
    s ∈ sInf S ↔ ∀ P ∈ S, s ∈ P := mem_sInf_props

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 3.2 (Join):
    arbitrary join has support iff some member supports (or `s = ∅`).
    The substrate-side `mem_sSup_props` exposes the disjunctive
    structure. The CGR formulation special-cases the empty family to
    `{∅} = ⊥`; the substrate gets this from the `s = ∅` clause. -/
theorem CGR_3_2_join (S : Set (Question W)) (s : Set W) :
    s ∈ sSup S ↔ s = ∅ ∨ ∃ P ∈ S, s ∈ P := mem_sSup_props

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 3.5 (Absolute
    pseudo-complement, alternative characterization): `P* = ℘(¬info(P))`.
    The substrate's `compl_eq` IS this — `Pᶜ = declarative (info P)ᶜ`,
    and `declarative q = ℘(q)` (principal ideal). -/
theorem CGR_3_5_pseudo_complement (P : Question W) :
    Pᶜ = declarative (P.info)ᶜ := compl_eq P

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Def 3.13 (Projection
    operators): `!P := ℘(info(P))` is the substrate's `proj`; `?P` is
    `nonInfo P := P ⊔ Pᶜ`. -/
theorem CGR_3_13_proj_eq (P : Question W) :
    P.proj = declarative P.info := rfl

theorem CGR_3_13_nonInfo_eq (P : Question W) :
    nonInfo P = P ⊔ Pᶜ := nonInfo_eq_sup_compl P

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 3.14 (Division):
    every proposition decomposes uniquely as the meet of its non-inquisitive
    projection and its non-informative projection. Substrate's
    `proj_inf_nonInfo`. -/
theorem CGR_3_14_division (P : Question W) :
    P = P.proj ⊓ nonInfo P :=
  (proj_inf_nonInfo P).symm

/-- @cite{ciardelli-groenendijk-roelofsen-2018} Fact 3.15 (Projection
    operators in algebraic terms): `!P = P**`. Substrate's
    `proj_eq_compl_compl`. -/
theorem CGR_3_15_proj_eq_compl_compl (P : Question W) :
    P.proj = Pᶜᶜ := proj_eq_compl_compl P

/-! ### §5.1 Polar questions

@cite{ciardelli-groenendijk-roelofsen-2018} §5.1: the polar question
`?Mab` (Is Alice married to Bob?) is the inquisitive disjunction of
the proposition `Mab` and its complement. The substrate primitive
`polar` IS this construction. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} §5.1: substrate
    identification of the polar question. The substrate's `polar p`
    expands to `declarative p ⊔ declarative pᶜ`, matching CGR's
    definition `?p := p ∨ ¬p` since on declarative propositions `¬p`
    reduces to `declarative pᶜ`. -/
theorem CGR_5_1_polar_eq (p : Set W) :
    polar p = declarative p ⊔ declarative pᶜ := polar_eq_sup p

/-! ### §5.4 Wh-questions

@cite{ciardelli-groenendijk-roelofsen-2018} §5.4.2: the mention-some
wh-question `∃xLax` (What is something Alice likes?) is the
inquisitive disjunction (= Hamblin disjunction) of declaratives
`{|Lad| | d ∈ D}↓`. The substrate primitive `which D P` IS this
construction. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} §5.4.2 substrate
    identification: the mention-some wh-question denotation `∃xLax`
    matches the substrate's `which D L` Hamblin disjunction. The
    `↓` notation in CGR is downward closure, which is automatic in
    the substrate (`Question` is a `LowerSet`). -/
theorem CGR_5_4_2_which_resolution
    {E : Type*} (D : Set E) (P : E → Set W) (s : Set W) :
    s ∈ which D P ↔ s = ∅ ∨ ∃ e ∈ D, s ⊆ P e := mem_which

/-! ### §5.5 Question coordination

@cite{ciardelli-groenendijk-roelofsen-2018} §5.5: question conjunction
and disjunction are uniformly the lattice meet and join, exactly as
they are for declaratives. The substrate's `⊓`/`⊔` IS this. The
identification is automatic — there's no separate "question conjunction"
operator. -/

/-- @cite{ciardelli-groenendijk-roelofsen-2018} §5.5.1: question
    conjunction reduces to substrate `⊓`. The CGR claim is that the
    InqB translation of "Q and Q'" is `μ ∧ μ'` — same operator as for
    declaratives. The substrate's `Question.conj = ⊓` IS this. -/
theorem CGR_5_5_1_conj_eq_inf (Q Q' : Question W) :
    Q ⊓ Q' = conj Q Q' := inf_eq_conj Q Q'

/-- @cite{ciardelli-groenendijk-roelofsen-2018} §5.5.2: question
    disjunction reduces to substrate `⊔`. -/
theorem CGR_5_5_2_disj_eq_sup (Q Q' : Question W) :
    Q ⊔ Q' = inqDisj Q Q' := sup_eq_inqDisj Q Q'

/-! ### Closing observation

The substrate-side coverage of @cite{ciardelli-groenendijk-roelofsen-2018}
Chapters 2, 3, and 5 is essentially complete: every CGR primitive has
a direct substrate counterpart with matching semantics. The only
non-trivial added structure on the substrate side is the
`SetLike (Question W) (Set W)` instance and the
`CompleteDistribLattice` registration — both of which are mathlib-style
ergonomic upgrades that don't change the underlying mathematics.

This audit is **load-bearing**: it documents that the substrate's
`Core.Question W = LowerSet (Set W)` design is the @cite{ciardelli-groenendijk-roelofsen-2018}
inquisitive proposition, with the same algebraic and order-theoretic
structure. Future substrate refactors should preserve these
identifications. -/

end Phenomena.Questions.Studies.CiardelliGroenendijkRoelofsen2018
