import Linglib.Core.Logic.Modal.QBSML.FreeChoice
import Linglib.Core.Logic.Modal.QBSML.StandardTranslation
import Linglib.Core.Logic.Modal.BSML.Scenarios

/-!
# [aloni-vanormondt-2023]: QBSML applied to modified numerals + split disjunction

[aloni-vanormondt-2023] [aloni-2022]

Aloni & van Ormondt 2023 introduces QBSML, the first-order extension of
Aloni 2022's BSML, and applies it to a battery of inferences arising from
modified numerals analysed as disjunctions:
  `at least n φ ↦ n ∨ more`,  `at most n φ ↦ n ∨ less`.

The framework's central facts (paper §5):

| Fact | Statement |
|------|-----------|
| 3   | `[Pa ∨ Pb]⁺ ⊨_epi ◇Pa ∧ ◇Pb` (ignorance, R state-based) |
| 4   | `[∀xPx ∨ Qx]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)` (obviation; counterexample on paper Fig. 14) |
| 5   | `card(s)=1 ⇒ M, s ⊨ [∀x(Px ∨ Qx)]⁺ ⇒ M, s ⊨ ∃xPx ∧ ∃xQx` (distribution under full information) |
| 6   | `[∀x(Px ∨ Qx)]⁺ ⊨_epi ∃x◇Px ∧ ∃x◇Qx` (distribution° on epistemic models) |
| 7   | `[□(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (□-free choice) |
| 8   | `[◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` (◇-free choice; ≡ Aloni 2022 NS FC at first-order) |
| 9   | `[∀x◇(Px ∨ Qx)]⁺ ⊨ ∀x◇Px ∧ ∀x◇Qx` (universal FC; [chemla-2009]) |
| 10  | `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` (negation behaviour; ignorance disappears) |

Facts 3 and 5–10 are universal substrate theorems in
`Core/Logic/Modal/QBSML/FreeChoice.lean` (framework substrate with multiple
paper-anchored consumers — this file and `Studies/Yan2023.lean`); this file
instantiates the unconditional ones at a concrete model (`avoModel`).
Fact 4 is the paper's Fig. 14 countermodel, proved here. Facts 1–2 and
Proposition 4.1 live in `Core/Logic/Modal/QBSML/{Enrichment,Properties}.lean`
(the modal-free Proposition 4.1 against mathlib `Formula.Realize` is
instantiated here at `avoModel`, the translation discharged by `rfl`).
Fact 3 needs the individual constants of [aloni-vanormondt-2023]
Definition 4.1 — `QBSMLFormula.predc` atoms, interpreted world-relatively
via `QBSMLModel.cInterp`.

## What is deferred

- **`Decidable` instance for `QBSML.eval`**: well-defined, but of limited
  use — the split-disjunction clauses quantify over pairs of subteams of
  the index space (`2^12 × 2^12` already at this file's model sizes), so
  kernel `decide` is infeasible for the interesting claims; the Fact 4
  countermodel is therefore proved by hand.

## Atoms and worlds

The concrete model reuses `Core.Logic.Modal.BSML.{FCAtom, PowerSet2World}`
from the existing FreeChoice substrate, ensuring AvO 2023 + Aloni 2022 both
target the same world space.
-/

namespace AloniVanOrmondt2023

open Core.Logic.Modal.QBSML
open FirstOrder Language
open Core.Logic.Modal.BSML (FCAtom PowerSet2World QVar)

/-! ### Predicates and variables -/

/-- Two unary predicates `P` and `Q`: provides the non-degenerate disjunction
    `Pa ∨ Qa` matching the paper's `Pa ∨ Pb` schema (where the `a, b` are
    domain elements rather than predicate-instances). With monadic predicates
    over a 2-element domain, `Pa ∨ Qa` and `Pa ∨ Pb` are equally non-trivial
    instantiations of split disjunction. -/
inductive QPred | P | Q
  deriving DecidableEq, Repr

instance : Fintype QPred where
  elems := {.P, .Q}
  complete := by intro p; cases p <;> simp

/-! ### The concrete model -/

/-- Universal-access deontic-style model on `PowerSet2World`.

    The interpretation is the `monadicStructure` of the valuation
    `V w P d := w.holds d`: both predicates hold of `d` at `w` iff `w`
    models the atom `d`. The disjunction `Px ∨ Qx` is non-degenerate at the
    *formula* level even though at this model the two interpretations
    coincide. A model with divergent P and Q extensions would discriminate
    further; this minimal model suffices for the substrate-instantiation
    tests below.

    Universal access (`access _ = univ`) means R is indisputable on every
    state but **not** state-based — same shape as `Aloni2022.deonticModel`. -/
def avoModel : QBSMLModel PowerSet2World FCAtom FCAtom QPred where
  access := λ _ => Finset.univ
  interp := λ w => monadicStructure id (λ _ d => w.holds d)

/-! ### Formulas -/

/-- The atomic formula `Px`. -/
def Px {Const : Type*} : QBSMLFormula QVar Const QPred := .pred .P .x

/-- The atomic formula `Qx`. -/
def Qx {Const : Type*} : QBSMLFormula QVar Const QPred := .pred .Q .x

/-- Disjunction `Px ∨ Qx` — paper's `Pa ∨ Pb`-shape with two distinct
    predicate-instances. -/
def PxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .disj Px Qx

/-- The negation premise `¬(Px ∨ Qx)` corresponding to the paper's
    `¬(Pa ∨ Pb)` schema. -/
def negPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .neg PxOrQx

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` corresponding to the paper's
    `◇(Pa ∨ Pb)` schema. -/
def possPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .poss PxOrQx

/-- The □-FC premise `□(Px ∨ Qx)` (paper's Fact 7 schema; `□` derived). -/
def necPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := PxOrQx.nec

/-- The universal-FC premise `∀x◇(Px ∨ Qx)` (paper's Fact 9 schema). -/
def univPossPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .univ .x possPxOrQx

/-- The distribution premise `∀x(Px ∨ Qx)` (paper's Facts 4–6 schema). -/
def univPxOrQx {Const : Type*} : QBSMLFormula QVar Const QPred := .univ .x PxOrQx

theorem Px_isNEFree {Const : Type*} : (Px (Const := Const)).IsNEFree := .pred _ _
theorem Qx_isNEFree {Const : Type*} : (Qx (Const := Const)).IsNEFree := .pred _ _

/-! ### Fact 10 (negation): `[¬(Pa ∨ Pb)]⁺ ⊨ ¬Pa ∧ ¬Pb` -/

/-- **Fact 10 (Negation behaviour)** at `avoModel`:

    Enriched negation `[¬(Px ∨ Qx)]⁺` entails the conjunction of negated
    disjuncts `¬Px ∧ ¬Qx`. One-line invocation of the substrate's
    `negationStrip_Q` (`Core/Logic/Modal/QBSML/FreeChoice.lean`).
    Mirrors `Aloni2022.aloni2022_fact11_dual_prohibition` style — substrate
    theorem, model + NE-free witnesses applied. -/
theorem fact10_negation
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel negPxOrQx.enrich s) :
    support avoModel (.neg Px) s ∧ support avoModel (.neg Qx) s :=
  negationStrip_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-! ### Facts 7 and 8 (free choice): `[□/◇(Pa ∨ Pb)]⁺ ⊨ ◇Pa ∧ ◇Pb` -/

/-- **Fact 8 (Narrow-Scope free choice / ◇-FC)** at `avoModel`:

    Enriched possibility-disjunction `[◇(Px ∨ Qx)]⁺` entails `◇Px ∧ ◇Qx`.
    One-line invocation of `narrowScopeFC_Q`. The first-order analogue of
    `Aloni2022.aloni2022_fact4_NS_FC` — same template, lifted to QBSML's
    monadic predicate language. -/
theorem fact8_narrowScopeFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel possPxOrQx.enrich s) :
    support avoModel (.poss Px) s ∧ support avoModel (.poss Qx) s :=
  narrowScopeFC_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-- **Fact 7 (□-free choice)** at `avoModel`: `[□(Px ∨ Qx)]⁺` entails
    `◇Px ∧ ◇Qx`, with the derived `□`. One-line invocation of `boxFC_Q`. -/
theorem fact7_boxFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel necPxOrQx.enrich s) :
    support avoModel (.poss Px) s ∧ support avoModel (.poss Qx) s :=
  boxFC_Q avoModel Px Qx s Px_isNEFree Qx_isNEFree h

/-! ### Facts 9 and 5 (universal FC and distribution) -/

/-- **Fact 9 (Universal free choice)** at `avoModel`:

    `[∀x◇(Px ∨ Qx)]⁺` entails `∀x◇Px ∧ ∀x◇Qx`. One-line invocation of
    `universalFC_Q` — the [chemla-2009]-attested pattern. -/
theorem fact9_universalFC
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (h : support avoModel univPossPxOrQx.enrich s) :
    support avoModel (.univ .x (.poss Px)) s ∧
    support avoModel (.univ .x (.poss Qx)) s :=
  universalFC_Q avoModel Px Qx .x s Px_isNEFree Qx_isNEFree h

/-- **Fact 5 (Distribution at maximal information)** at `avoModel`: on any
    singleton state, `[∀x(Px ∨ Qx)]⁺` entails `∃xPx ∧ ∃xQx`. One-line
    invocation of `distribution_Q`. -/
theorem fact5_distribution
    (i : Index PowerSet2World QVar FCAtom)
    (h : support avoModel univPxOrQx.enrich {i}) :
    support avoModel (.exi .x Px) {i} ∧ support avoModel (.exi .x Qx) {i} :=
  distribution_Q avoModel Px Qx .x i Px_isNEFree Qx_isNEFree h

/-! ### Proposition 4.1 at the concrete model -/

/-- The (unenriched) universal premise `∀x(Px ∨ Qx)` translates into mathlib
    first-order syntax, and its support is classical `Formula.Realize` at
    every index — [aloni-vanormondt-2023] Proposition 4.1 instantiated at
    `avoModel`. The translation hypothesis is discharged by `rfl`: the
    compiler computes. -/
theorem univPxOrQx_classical
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (v : Index PowerSet2World QVar FCAtom → QVar → FCAtom)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support avoModel univPxOrQx s ↔
      ∀ i ∈ s, avoModel.RealizeAt i.world
        (Formula.all₁ QVar.x
          ((monadicRel QPred.P).formula₁ (Term.var QVar.x) ⊔
            (monadicRel QPred.Q).formula₁ (Term.var QVar.x))) (v i) :=
  support_iff_forall_realizeAt avoModel rfl s v hv

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` translates into the modal layer
    over the monadic signature, and its support is Kripke satisfaction at
    every index — the **full** [aloni-vanormondt-2023] Proposition 4.1
    (modals included) at `avoModel`, the translation discharged by `rfl`. -/
theorem possPxOrQx_classical
    (s : Finset (Index PowerSet2World QVar FCAtom))
    (v : Index PowerSet2World QVar FCAtom → QVar → FCAtom)
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support avoModel possPxOrQx s ↔
      ∀ i ∈ s,
        (ModalFormula.dia
          (.sup (.ofFormula ((monadicRel QPred.P).formula₁ (Term.var QVar.x)))
            (.ofFormula
              ((monadicRel QPred.Q).formula₁ (Term.var QVar.x))))).Realize
          avoModel i.world (v i) :=
  support_iff_forall_realize avoModel rfl s v hv

/-- The closed standard translation of `∀x(Px ∨ Qx)`: quantifiers
    relativized to the individual sort, predicates world-relativized to the
    current-world variable `Sum.inr 0`. -/
def stUnivPxOrQx : (stLang FCAtom QPred).Formula (QVar ⊕ ℕ) :=
  Formula.all₁ (Sum.inl QVar.x)
    ((stIndiv.formula₁ (Term.var (Sum.inl QVar.x))).imp
      ((stRel QPred.P).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x)) ⊔
        (stRel QPred.Q).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x))))

/-- The closure is a genuine sentence: the compiler computes the
    free-variable finset. -/
theorem stUnivPxOrQx_closed :
    (stClose 0 stUnivPxOrQx).freeVarFinset = ∅ := by decide

/-- Support of `∀x(Px ∨ Qx)` at a singleton forces its sort-guarded closed
    standard translation as a **sentence** of `avoModel.stStructure` — the
    compactness-ready form, with every translation step (`toModal?`, `st?`,
    the free-variable check) computed by the compiler. -/
theorem univPxOrQx_sentence
    (i : Index PowerSet2World QVar FCAtom) (v : QVar → FCAtom)
    (hv : ∀ y, i.assign y = some (v y))
    (h : support avoModel univPxOrQx {i}) :
    letI := avoModel.stStructure
    (PowerSet2World ⊕ FCAtom) ⊨
      (stClose 0 stUnivPxOrQx).toSentence stUnivPxOrQx_closed :=
  models_toSentence_of_support avoModel rfl rfl stUnivPxOrQx_closed hv h

/-- Conversely, the sentence yields support at some singleton — sentencehood
    of the translation makes `∀x(Px ∨ Qx)`'s support assignment- and
    state-independent. -/
theorem support_of_stUnivPxOrQx_sentence
    (h : letI := avoModel.stStructure
         (PowerSet2World ⊕ FCAtom) ⊨
           (stClose 0 stUnivPxOrQx).toSentence stUnivPxOrQx_closed) :
    ∃ (i : Index PowerSet2World QVar FCAtom) (v : QVar → FCAtom),
      (∀ y, i.assign y = some (v y)) ∧ support avoModel univPxOrQx {i} :=
  haveI : Nonempty FCAtom := ⟨.a⟩
  exists_support_of_models_toSentence avoModel rfl rfl stUnivPxOrQx_closed h

/-! ### Frame condition: avoModel is indisputable on every state -/

/-- `avoModel`'s universal accessibility makes R indisputable on every state
    (every world sees the same `Finset.univ`). Mirrors
    `Aloni2022.deonticModel_indisputable_on_team` for the QBSML carrier.

    Indisputability vs state-basedness (paper §4.1.1, Definition 4.10):
    - Indisputable: all worlds in s↓ see the same accessible set (R constant).
    - State-based: every w ∈ s↓ sees exactly s↓ (R(w) = s↓).

    State-basedness is strictly stronger and is the precondition for the
    epistemic facts: Fact 3 (`ignorance_Q`) and Fact 6 (`distributionEpi_Q`),
    which therefore stay substrate-level (universal access is not
    state-based). Facts 7, 8 and 10 need no frame condition at all — they
    hold on every model. -/
theorem avoModel_indisputable
    (s : Finset (Index PowerSet2World QVar FCAtom)) :
    avoModel.IsIndisputable s := by
  intro _ _ _ _; rfl

/-! ### Fact 4 (obviation): the Fig. 14 countermodel

The paper's Fig. 14: a single index at the world where `Pa` and `Qb` both
hold, with an empty assignment and reflexive-only access. Its universal
`x`-extension supports the enriched disjunction by splitting *horizontally*
(`x/a` supports `Px`, `x/b` supports `Qx`), so the enriched premise holds;
but `∀x(◇Px ∧ ◇Qx)` fails because the `x/b` index cannot see any world
where `P` holds of `b`. -/

/-- The Fig. 14 domain: exactly the paper's two objects. (The third
    `FCAtom` atom would give the universal extension an `x/c` index
    supporting neither disjunct, breaking the premise — the paper notes the
    split works "because the domain contains two objects".) -/
inductive Fig14Atom | a | b
  deriving DecidableEq, Repr

instance : Fintype Fig14Atom where
  elems := {.a, .b}
  complete := by intro d; cases d <;> simp

/-- Fig. 14 valuation: `P` holds exactly of `a`, and `Q` exactly of `b`,
    wherever the world carries the corresponding atom — so `P` and `Q` have
    *divergent* extensions, unlike `avoModel`'s. -/
def fig14V (w : PowerSet2World) : QPred → Fig14Atom → Prop
  | .P, d => d = .a ∧ w.holds .a
  | .Q, d => d = .b ∧ w.holds .b

/-- The Fig. 14 model: reflexive-only access at the `both` world. -/
def fig14Model : QBSMLModel PowerSet2World Fig14Atom Fig14Atom QPred where
  access := λ _ => {PowerSet2World.both}
  interp := λ w => monadicStructure id (fig14V w)

/-- The Fig. 14 index: the `both` world with the empty assignment. -/
def fig14Index : Index PowerSet2World QVar Fig14Atom :=
  (PowerSet2World.both, fun _ => none)

/-- The Fig. 14 state: the single-index state of the counterexample. -/
def fig14State : Finset (Index PowerSet2World QVar Fig14Atom) := {fig14Index}

/-- The Fig. 14 state supports the enriched premise `[∀x(Px ∨ Qx)]⁺`: its
    universal extension splits into the `x/a` half supporting `[Px]⁺` and
    the `x/b` half supporting `[Qx]⁺` (paper Fig. 15). -/
theorem fig14_premise : support fig14Model univPxOrQx.enrich fig14State := by
  refine ⟨?_, Finset.singleton_nonempty _⟩
  show support fig14Model PxOrQx.enrich
    (State.extendUniversal fig14State QVar.x)
  refine ⟨⟨{fig14Index.update .x .a}, {fig14Index.update .x .b},
    ?_, ⟨?_, Finset.singleton_nonempty _⟩, ⟨?_, Finset.singleton_nonempty _⟩⟩,
    ⟨fig14Index.update .x .a, ?_⟩⟩
  · show ({fig14Index.update .x .a} ∪ {fig14Index.update .x .b} : Finset _)
      = State.extendUniversal fig14State QVar.x
    decide
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨.a, rfl, rfl, rfl⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨.b, rfl, rfl, rfl⟩
  · decide

/-- The Fig. 14 state does **not** support `∀x(◇Px ∧ ◇Qx)`: at the `x/b`
    index the only accessible world is `both`, where `P` holds of `a` alone
    (paper Fig. 16's failing substate). -/
theorem fig14_conclusion_fails :
    ¬ support fig14Model (.univ .x (.conj (.poss Px) (.poss Qx)))
      fig14State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ := h.1 (fig14Index.update .x .b) (by decide)
  have hX' : X ⊆ ({PowerSet2World.both} : Finset PowerSet2World) := hX
  have hXeq : X = {PowerSet2World.both} := by
    rcases Finset.subset_singleton_iff.mp hX' with h0 | h0
    · obtain ⟨y, hy⟩ := hne
      rw [h0] at hy
      exact absurd hy (Finset.notMem_empty y)
    · exact h0
  subst hXeq
  obtain ⟨d, hd, hP⟩ := hsupp
    (PowerSet2World.both, (fig14Index.update .x .b).assign)
    (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  rw [show (fig14Index.update QVar.x Fig14Atom.b).assign QVar.x
      = some Fig14Atom.b from rfl, Option.some.injEq] at hd
  subst hd
  exact Fig14Atom.noConfusion hP.1

/-- **Fact 4 (obviation)** of [aloni-vanormondt-2023]: the universal
    quantifier obviates the free-choice/ignorance effect —
    `[∀x(Px ∨ Qx)]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)`, witnessed by the Fig. 14
    countermodel. -/
theorem fact4_obviation :
    ∃ (M : QBSMLModel PowerSet2World Fig14Atom Fig14Atom QPred)
      (s : Finset (Index PowerSet2World QVar Fig14Atom)),
      support M univPxOrQx.enrich s ∧
      ¬ support M (.univ .x (.conj (.poss Px) (.poss Qx))) s :=
  ⟨fig14Model, fig14State, fig14_premise, fig14_conclusion_fails⟩

end AloniVanOrmondt2023
