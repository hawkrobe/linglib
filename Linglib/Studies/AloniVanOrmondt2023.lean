import Linglib.Logic.Team.QBSML.FreeChoice
import Linglib.Logic.Team.BSML.Scenarios
import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Data.Examples.AloniVanOrmondt2023

/-!
# Aloni and van Ormondt (2023): modified numerals and split disjunction

Superlative modifiers (*at least n*, *at most n*) generate ignorance inferences
that comparative modifiers (*more than n*, *fewer than n*) do not, and the
inferences are obviated under universal quantifiers and modals, distribute
under universals, license free choice under modals, and vanish under negation
— exactly the profile of plain disjunction. Following Büring, superlative
modifiers are split disjunctions, `at least n ↦ n ∨ more` and
`at most n ↦ n ∨ less`, and the whole profile falls out of [aloni-2022]'s
neglect-zero enrichment `[·]⁺` once BSML is raised to the first-order QBSML.

The QBSML facts of §5 are the universal theorems of
`Logic/Team/QBSML/FreeChoice`; here the denotations (14) and (16) are the
split of `atLeastMeaning`/`atMostMeaning` in the numerals substrate, the
results (56)–(61) and (63) are the facts instantiated at a universal-access
model with the paper's `three`/`more` predicates, Fact 5 gives distribution
at full information, and the obviation claim (57) is the Fig. 14 countermodel.
The example rows record the inference profile the analysis answers to.

## References

* [aloni-vanormondt-2023]
* [aloni-2022]
* [chemla-2009]
-/

namespace AloniVanOrmondt2023

open QBSML BSML Numerals Data.Examples FirstOrder Language

/-! ### Superlative modifiers as disjunctions -/

/-- (14): *at least n* is *exactly n or more than n*. -/
theorem atLeast_iff_bare_or_moreThan (m n : ℕ) :
    atLeastMeaning m n ↔ bareMeaning m n ∨ moreThanMeaning m n := by
  simp only [atLeastMeaning_def, bareMeaning_def, moreThanMeaning_def, ge_iff_le]
  omega

/-- (16): *at most n* is *exactly n or fewer than n*. -/
theorem atMost_iff_bare_or_fewerThan (m n : ℕ) :
    atMostMeaning m n ↔ bareMeaning m n ∨ fewerThanMeaning m n := by
  simp only [atMostMeaning_def, bareMeaning_def, fewerThanMeaning_def]
  omega

/-- Superlative rows carry the ignorance inference in unembedded position and
    comparative rows never do (the contrast of (2)–(7)). -/
theorem modifier_rows :
    ∀ row ∈ Examples.all, ∀ m ∈ row.feature? "modifier", ∀ i ∈ row.feature? "inference",
      (m = "comparative" → i = "none") ∧
      (m = "superlative" → row.feature? "embedding" = none → i = "ignorance") := by
  decide +kernel

/-! ### The predicates and the models -/

/-- The paper's numeral predicates, `three(x)` and `more(x)`; the §5 facts are stated
    with `P` and `Q`, which these instantiate. -/
inductive Predicate
  | three
  | more
  deriving DecidableEq, Repr, Fintype

/-- Universal-access model on `TwoAtomWorld`: every world is accessible, and
    `three` and `more` hold of `d` at `w` iff `w` models the atom `d`. -/
def univAccessModel : Model TwoAtomWorld FCAtom FCAtom Predicate :=
  .ofMonadic (λ _ ↦ Finset.univ) (λ _ ↦ id) (λ w _ d ↦ w.holds d)

/-- `three ∨ more` for the individual `a` — (45b). -/
def threeOrMore : Formula QVar FCAtom Predicate :=
  .disj (.predc .three .a) (.predc .more .a)

def three {Const : Type*} : Formula QVar Const Predicate := .pred .three .x

def more {Const : Type*} : Formula QVar Const Predicate := .pred .more .x

theorem three_neFree {Const : Type*} : (three (Const := Const)).NEFree := .pred _ _
theorem more_neFree {Const : Type*} : (more (Const := Const)).NEFree := .pred _ _

variable {s : Finset (Index TwoAtomWorld QVar FCAtom)}
variable {i : Index TwoAtomWorld QVar FCAtom}
variable {v : Index TwoAtomWorld QVar FCAtom → QVar → FCAtom}

/-- Proposition 4.1 at the model: support of the NE-free `∀x(three(x) ∨ more(x))`
    is classical first-order truth at every index, the translation computed. -/
theorem classicality_univ (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support univAccessModel (.univ .x (.disj three more)) s ↔
      ∀ i ∈ s,
        (FirstOrder.Language.Formula.all₁ QVar.x
          ((monadicRel Predicate.three).formula₁ (FirstOrder.Language.Term.var QVar.x) ⊔
            (monadicRel Predicate.more).formula₁
              (FirstOrder.Language.Term.var QVar.x))).RealizeAt
          univAccessModel.interp i.world (v i) :=
  support_iff_forall_realizeAt univAccessModel rfl s v hv

/-- Universal access is indisputable on every state. -/
theorem univAccessModel_indisputable (s : Finset (Index TwoAtomWorld QVar FCAtom)) :
    univAccessModel.IsIndisputable s :=
  λ _ _ _ _ ↦ rfl

/-- Universal access is state-based exactly on states whose world projection is
    everything — the epistemic reading (56) and (58) assume. -/
theorem univAccessModel_stateBased_of_full (hfull : State.worldProj s = Finset.univ) :
    univAccessModel.IsStateBased s :=
  λ _ _ ↦ hfull.symm

/-- A state of full world projection with the empty assignment. -/
def fullState : Finset (Index TwoAtomWorld QVar FCAtom) :=
  Finset.univ.image (λ w ↦ (w, λ _ ↦ none))

example : univAccessModel.IsStateBased fullState := by decide

example :
    ¬ univAccessModel.IsStateBased
      ({(TwoAtomWorld.both, λ _ ↦ none)} : Finset (Index TwoAtomWorld QVar FCAtom)) := by
  decide

/-! ### The results (56)–(61) -/

/-- (56), Fact 3: `[three ∨ more]⁺ ⊨ ◇three ∧ ◇more` on an epistemic state. -/
theorem ignorance (hfull : State.worldProj s = Finset.univ)
    (h : support univAccessModel threeOrMore.enrich s) :
    support univAccessModel (.poss (.predc .three .a)) s ∧
      support univAccessModel (.poss (.predc .more .a)) s :=
  QBSML.ignorance univAccessModel (univAccessModel_stateBased_of_full hfull) h

/-- Fact 5, the full-knowledge distribution (51): at a state of maximal
    information, `[∀x(three(x) ∨ more(x))]⁺` supports `∃x three(x) ∧ ∃x more(x)`. -/
theorem distribution (h : support univAccessModel (Formula.univ .x (.disj three more)).enrich {i}) :
    support univAccessModel (.exi .x three) {i} ∧ support univAccessModel (.exi .x more) {i} :=
  QBSML.distribution univAccessModel three_neFree more_neFree h

/-- (58), Fact 6: distribution under partial information yields the modalized
    conclusion `∃x◇three(x) ∧ ∃x◇more(x)`. -/
theorem distributionEpi (hfull : State.worldProj s = Finset.univ)
    (h : support univAccessModel (Formula.univ .x (.disj three more)).enrich s) :
    support univAccessModel (.exi .x (.poss three)) s ∧
      support univAccessModel (.exi .x (.poss more)) s :=
  QBSML.distributionEpi univAccessModel (univAccessModel_stateBased_of_full hfull) h

/-- (59), Fact 7: `[□(three ∨ more)]⁺ ⊨ ◇three ∧ ◇more`. -/
theorem boxFreeChoice (h : support univAccessModel (Formula.enrich (Formula.nec threeOrMore)) s) :
    support univAccessModel (.poss (.predc .three .a)) s ∧
      support univAccessModel (.poss (.predc .more .a)) s :=
  QBSML.boxFC univAccessModel (.predc _ _) (.predc _ _) h

/-- (60), Fact 8: `[◇(three ∨ more)]⁺ ⊨ ◇three ∧ ◇more`. -/
theorem diamondFreeChoice (h : support univAccessModel (Formula.enrich (.poss threeOrMore)) s) :
    support univAccessModel (.poss (.predc .three .a)) s ∧
      support univAccessModel (.poss (.predc .more .a)) s :=
  QBSML.narrowScopeFC univAccessModel (.predc _ _) (.predc _ _) h

/-- (63), Fact 9: universal free choice, attested by [chemla-2009]. -/
theorem universalFreeChoice
    (h : support univAccessModel (Formula.univ .x (.poss (.disj three more))).enrich s) :
    support univAccessModel (.univ .x (.poss three)) s ∧
      support univAccessModel (.univ .x (.poss more)) s :=
  QBSML.universalFC univAccessModel three_neFree more_neFree h

/-- (61), Fact 10: under negation the enrichment is inert, `[¬(three ∨ more)]⁺ ⊨
    ¬three ∧ ¬more`, so (61a) is blocked by the simpler *fewer than three*. -/
theorem negation (h : support univAccessModel (Formula.enrich (.neg threeOrMore)) s) :
    support univAccessModel (.neg (.predc .three .a)) s ∧
      support univAccessModel (.neg (.predc .more .a)) s :=
  QBSML.negationStrip univAccessModel (.predc _ _) (.predc _ _) h

/-! ### Obviation: the Fig. 14 countermodel

A single index at the world `w_{PaQb}` with the empty assignment; that world alone
sees itself. The domain is the paper's two objects. -/

inductive Fig14Atom
  | a
  | b
  deriving DecidableEq, Repr, Fintype

/-- The Fig. 14 valuation: `three` holds of `a` where the atom `a` holds and `more`
    of `b` where `b` does, so `w_{Pa}`, `w_{Qb}`, `w_{PaQb}` and `w_∅` are
    `onlyA`, `onlyB`, `both` and `nothing`. -/
def fig14V (w : TwoAtomWorld) : Predicate → Fig14Atom → Prop
  | .three, d => d = .a ∧ w.holds .a
  | .more, d => d = .b ∧ w.holds .b

/-- The Fig. 14 model: only `w_{PaQb}` has an arrow, to itself. -/
def fig14Model : Model TwoAtomWorld Fig14Atom Fig14Atom Predicate :=
  .ofMonadic (λ w ↦ if w = .both then {TwoAtomWorld.both} else ∅) (λ _ ↦ id) fig14V

def fig14Index : Index TwoAtomWorld QVar Fig14Atom := (TwoAtomWorld.both, λ _ ↦ none)

def fig14State : Finset (Index TwoAtomWorld QVar Fig14Atom) := {fig14Index}

/-- The accessibility is state-based on the Fig. 14 state, so obviation is not an
    artefact of dropping the frame condition behind ignorance. -/
theorem fig14_stateBased : fig14Model.IsStateBased fig14State := by decide

/-- Fig. 15: the universal extension splits into the `x/a` index supporting
    `[three(x)]⁺` and the `x/b` index supporting `[more(x)]⁺`. -/
theorem fig14_premise :
    support fig14Model (Formula.univ .x (.disj three more)).enrich fig14State := by
  refine ⟨?_, Finset.singleton_nonempty _⟩
  show support fig14Model (Formula.disj three more).enrich
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

/-- Fig. 16: at the `x/b` index the only accessible world is `w_{PaQb}`, where
    `three` holds of `a` alone, so `◇three(x)` fails. -/
theorem fig14_conclusion_fails :
    ¬ support fig14Model (.univ .x (.conj (.poss three) (.poss more))) fig14State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ := h.1 (fig14Index.update .x .b) (by decide)
  have hX' : X ⊆ {TwoAtomWorld.both} := by
    simpa [fig14Model, Model.ofMonadic, Index.update, fig14Index] using hX
  obtain rfl : X = {TwoAtomWorld.both} := hne.subset_singleton_iff.mp hX'
  obtain ⟨d, hd, hP⟩ := hsupp (TwoAtomWorld.both, (fig14Index.update .x .b).assign)
    (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  obtain rfl := Option.some.inj hd
  exact Fig14Atom.noConfusion hP.1

/-- (57), Fact 4: `[∀x(three(x) ∨ more(x))]⁺ ⊭ ∀x(◇three(x) ∧ ◇more(x))` — the
    universal quantifier obviates ignorance. -/
theorem obviation :
    ∃ (M : Model TwoAtomWorld Fig14Atom Fig14Atom Predicate)
      (s : Finset (Index TwoAtomWorld QVar Fig14Atom)),
      support M (Formula.univ .x (.disj three more)).enrich s ∧
        ¬ support M (.univ .x (.conj (.poss three) (.poss more))) s :=
  ⟨fig14Model, fig14State, fig14_premise, fig14_conclusion_fails⟩

end AloniVanOrmondt2023
