import Linglib.Logic.Team.QBSML.FreeChoice
import Linglib.Logic.Team.QBSML.Compactness
import Linglib.Logic.Team.BSML.Scenarios

/-!
# [aloni-vanormondt-2023]: modified numerals and split disjunction

Aloni & van Ormondt 2023 introduce QBSML, the first-order extension of
[aloni-2022]'s BSML, and analyse modified numerals as split disjunctions
(`at least n φ ↦ n ∨ more`, `at most n φ ↦ n ∨ less`), so that the
neglect-zero enrichment `[·]⁺` derives their ignorance, obviation,
distribution, free-choice and negation profile (paper §5). The universal
facts (3, 5–10) are substrate theorems in
`Logic/Team/QBSML/FreeChoice.lean`; this file instantiates them at a
concrete model and proves the paper's one countermodel claim.

## Main declarations

* `univAccessModel` — universal-access model over `BSML.TwoAtomWorld`.
* `fact3_ignorance` … `fact10_negation` — the paper's §5 facts, as
  instances of the substrate theorems.
* `fact4_obviation` — `[∀x(Px ∨ Qx)]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)`, by the paper's
  Fig. 14 countermodel.
* `support_univPxOrQx_iff`, `models_stUnivPxOrQxSentence_iff` —
  Proposition 4.1 at the concrete model, the translations computed by `rfl`.

## Implementation notes

`QBSML.eval` admits a `Decidable` instance in principle, but the
split-disjunction clause quantifies over pairs of subteams (`2^12 × 2^12`
at this file's model sizes), so kernel `decide` is infeasible for
whole-formula claims; the Fact 4 countermodel is proved by hand, with
`decide` confined to finite side conditions. The propositional facts (3, 7,
8, 10) are stated with the individual constants of the paper's
Definition 4.1 (`Formula.predc` atoms, world-relative
`KripkeStructure.cInterp`), the quantified facts with variable atoms — both
as in the paper. Atoms and worlds come from
`Logic/Team/BSML/Scenarios.lean`, so this file and `Studies/Aloni2022.lean`
target the same world space.
-/

namespace AloniVanOrmondt2023

open QBSML
open FirstOrder Language
open BSML (FCAtom TwoAtomWorld QVar)

/-! ### Predicates and variables -/

inductive Predicate | P | Q
  deriving DecidableEq, Repr, Fintype

/-! ### The concrete model -/

/-- Universal-access model on `TwoAtomWorld`: every world is accessible,
    and both predicates hold of `d` at `w` iff `w` models the atom `d`.
    Cf. `Aloni2022.deonticModel`. -/
def univAccessModel : Model TwoAtomWorld FCAtom FCAtom Predicate :=
  .ofMonadic (λ _ => Finset.univ) (λ _ => id) (λ w _ d => w.holds d)

/-! ### Formulas -/

def Pa : Formula QVar FCAtom Predicate := .predc .P .a

def Pb : Formula QVar FCAtom Predicate := .predc .P .b

def Px {Const : Type*} : Formula QVar Const Predicate := .pred .P .x

def Qx {Const : Type*} : Formula QVar Const Predicate := .pred .Q .x

/-- The universal-FC premise `∀x◇(Px ∨ Qx)` (paper's Fact 9 schema). -/
def univPossPxOrQx {Const : Type*} : Formula QVar Const Predicate :=
  .univ .x (.poss (.disj Px Qx))

/-- The distribution premise `∀x(Px ∨ Qx)` (paper's Facts 4–6 schema). -/
def univPxOrQx {Const : Type*} : Formula QVar Const Predicate :=
  .univ .x (.disj Px Qx)

theorem Pa_neFree : Pa.NEFree := .predc _ _
theorem Pb_neFree : Pb.NEFree := .predc _ _
theorem Px_neFree {Const : Type*} : (Px (Const := Const)).NEFree := .pred _ _
theorem Qx_neFree {Const : Type*} : (Qx (Const := Const)).NEFree := .pred _ _

variable {s : Finset (Index TwoAtomWorld QVar FCAtom)}
variable {i : Index TwoAtomWorld QVar FCAtom}
variable {v : Index TwoAtomWorld QVar FCAtom → QVar → FCAtom}

/-! ### Proposition 4.1 at the concrete model -/

/-- The (unenriched) universal premise `∀x(Px ∨ Qx)` translates into mathlib
    first-order syntax, and its support is classical `Formula.Realize` at
    every index — [aloni-vanormondt-2023] Proposition 4.1 instantiated at
    `univAccessModel`. The translation hypothesis is discharged by `rfl`: the
    compiler computes. -/
theorem support_univPxOrQx_iff
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support univAccessModel univPxOrQx s ↔
      ∀ i ∈ s, univAccessModel.RealizeAt i.world
        (Formula.all₁ QVar.x
          ((monadicRel Predicate.P).formula₁ (Term.var QVar.x) ⊔
            (monadicRel Predicate.Q).formula₁ (Term.var QVar.x))) (v i) :=
  support_iff_forall_realizeAt univAccessModel rfl s v hv

/-- The narrow-scope FC premise `◇(Px ∨ Qx)` translates into the modal layer
    over the monadic signature, and its support is Kripke satisfaction at
    every index — the **full** [aloni-vanormondt-2023] Proposition 4.1
    (modals included) at `univAccessModel`, the translation discharged by `rfl`. -/
theorem support_possPxOrQx_iff
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support univAccessModel (.poss (.disj Px Qx)) s ↔
      ∀ i ∈ s,
        (ModalFormula.dia
          (.sup (.ofFormula ((monadicRel Predicate.P).formula₁ (Term.var QVar.x)))
            (.ofFormula
              ((monadicRel Predicate.Q).formula₁ (Term.var QVar.x))))).Realize
          univAccessModel i.world (v i) :=
  support_iff_forall_realize univAccessModel rfl s v hv

/-- The closed standard translation of `∀x(Px ∨ Qx)`: quantifiers
    relativized to the individual sort, predicates world-relativized to the
    current-world variable `Sum.inr 0`. -/
def stUnivPxOrQx : (Language.correspondence FCAtom Predicate).Formula (QVar ⊕ ℕ) :=
  Formula.all₁ (Sum.inl QVar.x)
    ((corrIndiv.formula₁ (Term.var (Sum.inl QVar.x))).imp
      ((corrRel Predicate.P).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x)) ⊔
        (corrRel Predicate.Q).formula₂ (Term.var (Sum.inr 0))
          (Term.var (Sum.inl QVar.x))))

/-- The closure is a genuine sentence: the compiler computes the
    free-variable finset. -/
theorem stUnivPxOrQx_closed :
    (stClose 0 stUnivPxOrQx).freeVarFinset = ∅ := by decide

/-- The sort-guarded closed standard translation of `∀x(Px ∨ Qx)`, as a
    sentence. -/
def stUnivPxOrQxSentence : (Language.correspondence FCAtom Predicate).Sentence :=
  (stClose 0 stUnivPxOrQx).toSentence stUnivPxOrQx_closed

local instance : (Language.correspondence FCAtom Predicate).Structure (TwoAtomWorld ⊕ FCAtom) :=
  univAccessModel.corrStructure

/-- Truth of the standard-translation sentence in `univAccessModel.corrStructure`
    is support of `∀x(Px ∨ Qx)` at some singleton with a total assignment —
    the compactness-ready form of Proposition 4.1, every translation step
    (`toModal?`, `st?`, the free-variable check) computed by the compiler. -/
theorem models_stUnivPxOrQxSentence_iff :
    (TwoAtomWorld ⊕ FCAtom) ⊨ stUnivPxOrQxSentence ↔
      ∃ (i : Index TwoAtomWorld QVar FCAtom) (v : QVar → FCAtom),
        (∀ y, i.assign y = some (v y)) ∧ support univAccessModel univPxOrQx {i} :=
  haveI : Nonempty FCAtom := ⟨.a⟩
  ⟨exists_support_of_models_toSentence univAccessModel rfl rfl stUnivPxOrQx_closed,
    fun ⟨_, _, hv, h⟩ =>
      models_toSentence_of_support univAccessModel rfl rfl stUnivPxOrQx_closed hv h⟩

/-! ### Frame conditions -/

/-- `univAccessModel`'s universal accessibility makes R indisputable on every state
    (every world sees the same `Finset.univ`). Mirrors
    `Aloni2022.deonticModel_indisputable_on_team` for the QBSML carrier.

    Indisputability vs state-basedness (paper §4.1.1, Definition 4.10):
    - Indisputable: all worlds in s↓ see the same accessible set (R constant).
    - State-based: every w ∈ s↓ sees exactly s↓ (R(w) = s↓). -/
theorem univAccessModel_indisputable
    (s : Finset (Index TwoAtomWorld QVar FCAtom)) :
    univAccessModel.IsIndisputable s :=
  fun _ _ _ _ => rfl

/-- State-basedness is strictly stronger than indisputability; universal
    access delivers it exactly on states whose world projection exhausts
    `TwoAtomWorld`. The precondition for the epistemic Facts 3 and 6. -/
theorem univAccessModel_stateBased_of_full
    {s : Finset (Index TwoAtomWorld QVar FCAtom)}
    (hfull : State.worldProj s = Finset.univ) :
    univAccessModel.IsStateBased s :=
  fun _ _ => hfull.symm

/-- A state with full world projection: every world, paired with the empty
    assignment. Witnesses that the epistemic hypothesis of `fact3_ignorance`
    and `fact6_distributionEpi` is satisfiable. -/
def fullState : Finset (Index TwoAtomWorld QVar FCAtom) :=
  Finset.univ.image (fun w => (w, fun _ => none))

example : State.worldProj fullState = Finset.univ := by decide

example : univAccessModel.IsStateBased fullState := by decide

/-- On a proper-projection state, universal access is *not* state-based:
    the frame conditions genuinely separate. -/
example :
    ¬ univAccessModel.IsStateBased
      ({(TwoAtomWorld.both, fun _ => none)} :
        Finset (Index TwoAtomWorld QVar FCAtom)) := by
  decide

/-! ### The §5 facts -/

/-- **Fact 3** (ignorance), on states of full world projection. -/
theorem fact3_ignorance (hfull : State.worldProj s = Finset.univ)
    (h : support univAccessModel (Formula.enrich (.disj Pa Pb)) s) :
    support univAccessModel (.poss Pa) s ∧ support univAccessModel (.poss Pb) s :=
  ignorance univAccessModel (univAccessModel_stateBased_of_full hfull) h

/-- **Fact 5** (distribution at maximal information). -/
theorem fact5_distribution (h : support univAccessModel univPxOrQx.enrich {i}) :
    support univAccessModel (.exi .x Px) {i} ∧ support univAccessModel (.exi .x Qx) {i} :=
  distribution univAccessModel Px_neFree Qx_neFree h

/-- **Fact 6** (distribution◇), on states of full world projection. -/
theorem fact6_distributionEpi (hfull : State.worldProj s = Finset.univ)
    (h : support univAccessModel univPxOrQx.enrich s) :
    support univAccessModel (.exi .x (.poss Px)) s ∧
    support univAccessModel (.exi .x (.poss Qx)) s :=
  distributionEpi univAccessModel (univAccessModel_stateBased_of_full hfull) h

/-- **Fact 7** (□-free choice; `□` derived, `Formula.nec`). -/
theorem fact7_boxFC
    (h : support univAccessModel (Formula.enrich (Formula.nec (.disj Pa Pb))) s) :
    support univAccessModel (.poss Pa) s ∧ support univAccessModel (.poss Pb) s :=
  boxFC univAccessModel Pa_neFree Pb_neFree h

/-- **Fact 8** (◇-free choice); cf. `Aloni2022.aloni2022_fact4_NS_FC`. -/
theorem fact8_narrowScopeFC
    (h : support univAccessModel (Formula.enrich (.poss (.disj Pa Pb))) s) :
    support univAccessModel (.poss Pa) s ∧ support univAccessModel (.poss Pb) s :=
  narrowScopeFC univAccessModel Pa_neFree Pb_neFree h

/-- **Fact 9** (universal free choice), attested experimentally by
    [chemla-2009]. -/
theorem fact9_universalFC
    (h : support univAccessModel univPossPxOrQx.enrich s) :
    support univAccessModel (.univ .x (.poss Px)) s ∧
    support univAccessModel (.univ .x (.poss Qx)) s :=
  universalFC univAccessModel Px_neFree Qx_neFree h

/-- **Fact 10** (negation behaviour); cf.
    `Aloni2022.aloni2022_fact11_dual_prohibition`. -/
theorem fact10_negation
    (h : support univAccessModel (Formula.enrich (.neg (.disj Pa Pb))) s) :
    support univAccessModel (.neg Pa) s ∧ support univAccessModel (.neg Pb) s :=
  negationStrip univAccessModel Pa_neFree Pb_neFree h

/-! ### Fact 4 (obviation): the Fig. 14 countermodel

The paper's Fig. 14: a single index at the world `both` with the empty
assignment, every world seeing exactly `{both}`. -/

/-- The Fig. 14 domain: exactly the paper's two objects. (The third
    `FCAtom` atom would give the universal extension an `x/c` index
    supporting neither disjunct, breaking the premise — the paper notes the
    split works "because the domain contains two objects".) -/
inductive Fig14Atom | a | b
  deriving DecidableEq, Repr, Fintype

/-- Fig. 14 valuation: `P` holds exactly of `a` and `Q` exactly of `b` —
    divergent extensions, unlike `univAccessModel`'s. -/
def fig14V (w : TwoAtomWorld) : Predicate → Fig14Atom → Prop
  | .P, d => d = .a ∧ w.holds .a
  | .Q, d => d = .b ∧ w.holds .b

def fig14Model : Model TwoAtomWorld Fig14Atom Fig14Atom Predicate :=
  .ofMonadic (λ _ => {TwoAtomWorld.both}) (λ _ => id) fig14V

def fig14Index : Index TwoAtomWorld QVar Fig14Atom :=
  (TwoAtomWorld.both, fun _ => none)

def fig14State : Finset (Index TwoAtomWorld QVar Fig14Atom) := {fig14Index}

/-- The countermodel's `R` is state-based on its state — the epistemic
    reading Fact 4 assumes, so obviation is not an artifact of dropping the
    frame condition behind ignorance. -/
theorem fig14_stateBased : fig14Model.IsStateBased fig14State := by decide

/-- The universal extension splits into the `x/a` half supporting `[Px]⁺`
    and the `x/b` half supporting `[Qx]⁺` (paper Fig. 15). -/
theorem fig14_premise : support fig14Model univPxOrQx.enrich fig14State := by
  refine ⟨?_, Finset.singleton_nonempty _⟩
  show support fig14Model (Formula.disj Px Qx).enrich
    (State.extendUniversal fig14State QVar.x)
  refine ⟨⟨{fig14Index.update .x .a}, {fig14Index.update .x .b},
    ?_, ⟨?_, Finset.singleton_nonempty _⟩, ⟨?_, Finset.singleton_nonempty _⟩⟩,
    ⟨fig14Index.update .x .a, ?_⟩⟩
  · show ({fig14Index.update .x .a} ∪ {fig14Index.update .x .b} : Finset _)
      = State.extendUniversal fig14State QVar.x
    decide
  · intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨.a, rfl, rfl, rfl⟩
  · intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨.b, rfl, rfl, rfl⟩
  · decide

/-- At the `x/b` index the only accessible world is `both`, where `P`
    holds of `a` alone (paper Fig. 16's failing substate). -/
theorem fig14_conclusion_fails :
    ¬ support fig14Model (.univ .x (.conj (.poss Px) (.poss Qx)))
      fig14State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ := h.1 (fig14Index.update .x .b) (by decide)
  obtain rfl : X = {TwoAtomWorld.both} := hne.subset_singleton_iff.mp hX
  obtain ⟨d, hd, hP⟩ := hsupp
    (TwoAtomWorld.both, (fig14Index.update .x .b).assign)
    (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  obtain rfl := Option.some.inj hd
  exact Fig14Atom.noConfusion hP.1

/-- **Fact 4** (obviation): `[∀x(Px ∨ Qx)]⁺ ⊭ ∀x(◇Px ∧ ◇Qx)` — the
    universal quantifier obviates the free-choice/ignorance effect. -/
theorem fact4_obviation :
    ∃ (M : Model TwoAtomWorld Fig14Atom Fig14Atom Predicate)
      (s : Finset (Index TwoAtomWorld QVar Fig14Atom)),
      support M univPxOrQx.enrich s ∧
      ¬ support M (.univ .x (.conj (.poss Px) (.poss Qx))) s :=
  ⟨fig14Model, fig14State, fig14_premise, fig14_conclusion_fails⟩

end AloniVanOrmondt2023
