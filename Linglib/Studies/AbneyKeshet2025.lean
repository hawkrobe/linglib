import Linglib.Core.Data.Fin.VecNotation
import Linglib.Logic.PIP.Felicity
import Linglib.Logic.PIP.Intensional
import Linglib.Data.Examples.AbneyKeshet2025

/-!
# Abney & Keshet (2025): Plural Intensional Presuppositional semantics

The paper gives PIP (`Logic/PIP/Basic.lean`) its formal definition — local variables, the
translation into set theory, the felicity operator with asymmetric conjunction, and
PIP-values (truth, felicity, local variables, label definitions), whose equality is
intersubstitutability — and a compositional fragment recasting the textbook rules of
interpretation as semantic operations. Indefinites, tense and the traces of determiners are
*restricted variables*, a variable paired with an assertion; the operation `FX` lifts a
predicate to take one, conjoining its assertion; quantifier raising inserts a summation
operator whose label is the quantifier's restriction or reference set (`SA`); and modals and
negation store their prejacent in a label through intensional functional application
(`IFA`). Summation, paycheck and strong donkey pronouns, quantificational and modal
subordination, anaphora out of negation, Partee's bathroom disjunction and presupposition
satisfaction across subordination then reduce to scope extension of indefinites, repetition
of subformulas through labels, and standard presupposition projection.

This file defines the fragment's typed metalanguage over PIP, its semantic operations,
lexicon and rules of interpretation as a typed tree, derives the paper's worked trees, and
proves the truth and felicity conditions of the applications on scenario models at a world
of evaluation `w₀`. Variables of the formal system range over all pluralities, so where the
paper reads a summation variable as a world that is a hypothesis on the assignment; for
negation as summation over worlds, `w ∉ Σw(…)`, the two readings come apart
(`not_realize_shop138`).

## Main definitions

* `Ty`, `Sem`, `lift` — semantic types, the metalanguage of λ-expressions over PIP terms
  and formulas, and `↑`-lifting to restricted variables.
* `NN`, `FA`, `AF`, `IFA`, `FX`, `PM`, `PA`, `SA` — the semantic operations; `Word`,
  `Word.sem` — the lexicon with its defined constants; `Tree`, `interp` — LF trees
  annotated with their operation, interpreted relative to the labels of the preceding
  discourse.
* `aRedDogBarked`, `chasedACat`, `aFarmerWhoOwnsADonkey`, `everyGirlWroteAPaper`, `sheX`,
  `theyP`, `mostOfThemUsedIt` — the paper's trees.
* `Scenario`, `Scenario.model` — intensional models with world-relative lexical relations.
* `indefOwned`, `shop139`, `shop138`, `bathroom143`, `everyMonarchy`, `discourse150a`,
  `wolfDiscourse`, `theyLoud` — the applications' PIP translations.

## Main statements

* `interp_aRedDogBarked`, `interp_chasedACat`, `interp_aFarmerWhoOwnsADonkey`,
  `interp_everyGirlWroteAPaper`, `interp_sheX`, `interp_theyP`, `interp_mostOfThemUsedIt`
  — the trees' meanings as the paper computes them.
* `value_aRedDogBarked` — the meaning of "a red dog barked" is intersubstitutable with
  its abbreviated form; `value_bvar_ne_var` — bracketing is not a matter of truth.
* `expandSelf_theyLoud` — a summation pronoun over a nuclear-scope label expands to the
  set of barking dogs.
* `realize_sigma_indefOwned` — a summation over a description with an external variable
  takes its value from that variable: paycheck pronouns.
* `felicitous_shop139_iff` — "He doesn't own a car. It is in the shop." is felicitous only
  where he owns a car, that is where the first sentence is false; `not_realize_shop138` —
  the double-negation translation is false in every model with a second atom.
* `felicitous_bathroom143_iff` — the bathroom disjunction is felicitous iff a bathroom
  here, if any, is unique.
* `realize_wolfDiscourse_iff` — modal subordination: the second modal quantifies over the
  accessible worlds where a wolf enters.
* `felicitous_everyMonarchy_iff`, `felicitous_discourse150a_iff` — a presupposition in the
  nuclear scope is satisfied pointwise by the restriction, within a sentence and across
  quantificational subordination.

## References

* [abney-keshet-2025]
* [keshet-abney-2024]
* [heim-kratzer-1998]
* [karttunen-1974]
* [keshet-2018]
* [roberts-1987]
-/

namespace AbneyKeshet2025

open PIP

/-- The variables of the fragment: the world `w`, the modal-base world `u`, and the indices
of the paper's trees. -/
inductive Var
  | w | u | d | b | c | x | z | o | g | p | s | s' | e | t | m | k
  deriving DecidableEq

/-- Formula labels, as in the paper's trees and translations. -/
inductive Lab
  | G | P | B | D | S | M | U | W | E | O | X | Y | R | K | C
  deriving DecidableEq

/-- Lexical relation symbols, by number of non-world arguments: the word senses of the
paper's examples. -/
inductive Lex : ℕ → Type
  | red : Lex 1
  | dog : Lex 1
  | barkEvt : Lex 1
  | hasAgent : Lex 2
  | hasPatient : Lex 2
  | hasGoal : Lex 2
  | chaseEvt : Lex 1
  | cat : Lex 1
  | farmer : Lex 1
  | donkey : Lex 1
  | ownEvt : Lex 1
  | girl : Lex 1
  | paper : Lex 1
  | writeEvt : Lex 1
  | barks : Lex 1
  | loud : Lex 1
  | diorama : Lex 1
  | made : Lex 2
  | student : Lex 1
  | umbrella : Lex 1
  | brought : Lex 3
  | useEvt : Lex 1
  | wolf : Lex 1
  | enters : Lex 1
  | tim : Lex 1
  | eats : Lex 2
  | car : Lex 1
  | owns : Lex 2
  | inShop : Lex 1
  | bathroom : Lex 1
  | here : Lex 1
  | funnyPlace : Lex 1
  | country : Lex 1
  | monarchy : Lex 1
  | monarchOf : Lex 2
  | cherish : Lex 2
  | fem : Lex 1

/-- Relation symbols: the lexical ones, accessibility between worlds, and the proportional
quantifier `most`. -/
inductive Sym : ℕ → Type
  | lex {n : ℕ} (c : Lex n) : Sym n
  | acc : Sym 1
  | most : Sym 2

/-- Terms of the fragment. -/
abbrev Tm := Term Var Lab Sym

/-- Formulas of the fragment. -/
abbrev Fm := Formula Var Lab Sym

/-- A one-place lexical predicate at the world `w`. -/
def pred₁ (c : Lex 1) (x : Tm) : Fm := .atom (.lex c) (.var .w) ![x]

/-- A two-place lexical predicate at the world `w`. -/
def pred₂ (c : Lex 2) (x y : Tm) : Fm := .atom (.lex c) (.var .w) ![x, y]

/-- A restricted variable: `[x] = x ∧ P(x)`, the common denotation of the indefinite
article, tense and the trace of a determiner (50). -/
def restricted (v : Var) (P : Tm → Fm) : Fm := .conj (.eq (.bvar v) (.var v)) (P (.var v))

/-- `β_w = Σu acc(w, u)`: the modal base. -/
def modalBase : Tm := .sigma .u (.atom .acc (.var .w) ![.var .u])

/-! ### The metalanguage and the semantic operations -/

/-- Semantic types: individuals, worlds, truth values, functions. -/
inductive Ty
  | e | s | t
  | fn (σ τ : Ty)

/-- The metalanguage of the fragment: PIP terms at `e` and `s`, formulas at `t`, and
functions between them, as which the paper's λ-expressions are read. -/
def Sem : Ty → Type
  | .e => Tm
  | .s => Tm
  | .t => Fm
  | .fn σ τ => Sem σ → Sem τ

/-- `↑`-lifting (84): a function whose result is a formula takes an additional assertion,
conjoined to its result; the lift is the identity on terms. -/
def lift : {τ : Ty} → Sem τ → Fm → Sem τ
  | .e, x, _ => x
  | .s, x, _ => x
  | .t, ψ, φ => .conj ψ φ
  | .fn _ _, f, φ => fun a => lift (f a) φ

/-- Nonbranching nodes. -/
def NN {τ : Ty} (φ : Sem τ) : Sem τ := φ

/-- Functional application. -/
def FA {σ τ : Ty} (φ : Sem (.fn σ τ)) (ψ : Sem σ) : Sem τ := φ ψ

/-- Reverse functional application. -/
def AF {σ τ : Ty} (φ : Sem σ) (ψ : Sem (.fn σ τ)) : Sem τ := ψ φ

/-- Intensional functional application (82): the body is stored in the label `Z` and the
set of worlds satisfying it is the argument. -/
def IFA (Z : Lab) (φ : Tm → Fm) (ψ : Fm) : Fm := .conj (φ (.sigma .w (.label Z))) (.labelDef Z ψ)

/-- Application to a restricted variable: the lifted predicate takes the index and the
assertion. -/
def FX {τ : Ty} (P : Sem (.fn .e τ)) (v : Var) (φ : Fm) : Sem τ := lift (P (.var v)) φ

/-- Predicate modification. -/
def PM (φ ψ : Tm → Fm) : Tm → Fm := fun a => .conj (φ a) (ψ a)

/-- Predicate abstraction `λxφ`, reading through the labels `A` of the preceding
discourse before substituting for `x` (123). -/
def PA (A : List (Lab × Fm)) (v : Var) (φ : Fm) : Tm → Fm := fun t => (φ.expand A).subst v t

/-- Summation with a label: `ΣxZ where Z ≡ φ`, the definition attached to the use. -/
def SA (v : Var) (Z : Lab) (φ : Fm) : Tm := .sigma v (.conj (.label Z) (.labelDef Z φ))

/-! ### The lexicon -/

/-- Terminals: lexical predicates, thematic roles, determiners, pronouns, and the defined
constants (88) with their indices and labels. -/
inductive Word
  | pred (c : Lex 1)
  | role (c : Lex 2)
  | every
  | most
  | a (v : Var)
  | tense (v : Var)
  | dTrace (v : Var)
  | dpTrace (v : Var)
  | core (v : Var)
  | ldpTrace (Z : Lab)
  | she
  | it
  | they
  | not (Z : Lab)
  | might (Z : Lab)
  | must (Z : Lab)
  | base

/-- The semantic type of a terminal. -/
def Word.ty : Word → Ty
  | .pred _ => .fn .e .t
  | .role _ => .fn .e (.fn .e .t)
  | .every => .fn .e (.fn .e .t)
  | .most => .fn .e (.fn .e .t)
  | .a _ => .fn (.fn .e .t) .t
  | .tense _ => .fn (.fn .e .t) .t
  | .dTrace _ => .fn (.fn .e .t) .t
  | .dpTrace _ => .e
  | .core _ => .e
  | .ldpTrace _ => .t
  | .she => .fn .e .e
  | .it => .fn .e .e
  | .they => .fn .e .e
  | .not _ => .fn .s .t
  | .might _ => .fn .s (.fn .s .t)
  | .must _ => .fn .s (.fn .s .t)
  | .base => .s

/-- The meaning of a terminal (87)–(88): a thematic role `λxλe(HAS-ROLE(e, x))`, `EVERY` as
inclusion, the restricted variables `A_x`, `T_x`, `D-T_x`, the simple variables `DP-T_x`
and `E_x`, the label of a labeled trace, pronouns `λz(z|Q(z))`, negation `λψ(w ∉ ψ)`, the
modals as relations to the modal base, and the base `β_w`. -/
def Word.sem : (α : Word) → Sem α.ty
  | .pred c => fun a => pred₁ c a
  | .role c => fun a e => pred₂ c e a
  | .every => fun a b => .subset a b
  | .most => fun a b => .atom .most (.var .w) ![a, b]
  | .a v => restricted v
  | .tense v => restricted v
  | .dTrace v => restricted v
  | .dpTrace v => .var v
  | .core v => .var v
  | .ldpTrace Z => .label Z
  | .she => fun z => .presup z (.conj (pred₁ .fem z) (.sg z))
  | .it => fun z => .presup z (.sg z)
  | .they => fun z => .presup z (.pl z)
  | .not _ => fun ψ => .neg (.mem (.var .w) ψ)
  | .might _ => fun β ψ => .some_ β ψ
  | .must _ => fun β ψ => .subset β ψ
  | .base => modalBase

/-! ### Trees and their interpretation -/

/-- An LF tree annotated with the semantic operation at each node (86), with the index of
a restricted variable and the label of a summation or intensional operator as data. -/
inductive Tree : Ty → Type
  | lex (α : Word) : Tree α.ty
  | nn {τ : Ty} (β : Tree τ) : Tree τ
  | fa {σ τ : Ty} (β : Tree (.fn σ τ)) (γ : Tree σ) : Tree τ
  | af {σ τ : Ty} (β : Tree σ) (γ : Tree (.fn σ τ)) : Tree τ
  | ifa (Z : Lab) (β : Tree (.fn .s .t)) (γ : Tree .t) : Tree .t
  | fx {τ : Ty} (β : Tree (.fn .e τ)) (v : Var) (γ : Tree .t) : Tree τ
  | pm (β γ : Tree (.fn .e .t)) : Tree (.fn .e .t)
  | pa (v : Var) (γ : Tree .t) : Tree (.fn .e .t)
  | sa (v : Var) (Z : Lab) (γ : Tree .t) : Tree .e

/-- The meaning of a tree, relative to the label definitions `A` of the preceding
discourse. -/
def interp (A : List (Lab × Fm)) : {τ : Ty} → Tree τ → Sem τ
  | _, .lex α => α.sem
  | _, .nn β => NN (interp A β)
  | _, .fa β γ => FA (interp A β) (interp A γ)
  | _, .af β γ => AF (interp A β) (interp A γ)
  | _, .ifa Z β γ => IFA Z (interp A β) (interp A γ)
  | _, .fx β v γ => FX (interp A β) v (interp A γ)
  | _, .pm β γ => PM (interp A β) (interp A γ)
  | _, .pa v γ => PA A v (interp A γ)
  | _, .sa v Z γ => SA v Z (interp A γ)

/-! ### The paper's trees -/

/-- (47): "a red dog barked". -/
def aRedDogBarked : Tree .t :=
  .fx (.fx (.lex (.role .hasAgent)) .d
      (.fa (.lex (.a .d)) (.pm (.lex (.pred .red)) (.lex (.pred .dog)))))
    .b (.fa (.lex (.tense .b)) (.nn (.lex (.pred .barkEvt))))

/-- (91)–(92): the meaning of (47). -/
theorem interp_aRedDogBarked :
    interp [] aRedDogBarked =
      .conj (.conj (pred₂ .hasAgent (.var .b) (.var .d))
          (restricted .d fun x => .conj (pred₁ .red x) (pred₁ .dog x)))
        (restricted .b (pred₁ .barkEvt)) := rfl

/-- (92) abbreviated: `HAS-AGENT(b, d) ∧ RED([d]) ∧ DOG(d) ∧ BARK-EVT([b])`. -/
def form92 : Fm :=
  .conj (.conj (.conj (pred₂ .hasAgent (.var .b) (.var .d)) (pred₁ .red (.bvar .d)))
      (pred₁ .dog (.var .d)))
    (pred₁ .barkEvt (.bvar .b))

variable {W E : Type}

/-- The meaning of (47) is intersubstitutable with its abbreviation (92): same truth,
felicity, local variables and label definitions. -/
theorem value_aRedDogBarked (M : Model Sym (Atom W E)) (g : Var → Set (Atom W E)) :
    (interp [] aRedDogBarked).value M g = form92.value M g := by
  rw [interp_aRedDogBarked]
  refine Value.ext (propext ?_) (propext ?_) rfl rfl
  · simp only [Formula.value, Formula.realize_conj, Formula.realize_atom, Formula.realize_eq,
      restricted, pred₁, pred₂, form92, Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var,
      Term.realize_bvar, and_assoc, true_and]
  · simp only [Formula.value, Formula.felicitous_conj, Formula.felicitous_atom,
      Formula.felicitous_eq, restricted, pred₁, pred₂, form92, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff, Term.felicitous_var,
      Term.felicitous_bvar, and_self, implies_true]

/-- `DOG([d])` and `DOG(d)` are truth-equivalent. -/
theorem realize_bvar_iff_var (M : Model Sym (Atom W E)) (g : Var → Set (Atom W E)) (c : Lex 1)
    (v : Var) : (pred₁ c (.bvar v)).Realize M g ↔ (pred₁ c (.var v)).Realize M g := by
  simp only [pred₁, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Term.realize_bvar]

/-- `DOG([d])` and `DOG(d)` are not intersubstitutable: their local variables differ. -/
theorem value_bvar_ne_var (M : Model Sym (Atom W E)) (g : Var → Set (Atom W E)) (c : Lex 1)
    (v : Var) : (pred₁ c (.bvar v)).value M g ≠ (pred₁ c (.var v)).value M g :=
  fun h => List.cons_ne_nil v [] (congrArg Value.locals h)

/-- (56): "chased a cat", a VP. -/
def chasedACat : Tree (.fn .e .t) :=
  .pm (.lex (.pred .chaseEvt))
    (.fx (.lex (.role .hasPatient)) .c (.fa (.lex (.a .c)) (.lex (.pred .cat))))

/-- (57): `λe(CHASE-EVT(e) ∧ HAS-PATIENT(e, c) ∧ CAT([c]))`. -/
theorem interp_chasedACat :
    interp [] chasedACat = fun e =>
      .conj (pred₁ .chaseEvt e)
        (.conj (pred₂ .hasPatient e (.var .c)) (restricted .c (pred₁ .cat))) := rfl

/-- (59): "a farmer who owns a donkey", with the relative pronoun's trace a simple
variable combined by `FA` and the clause abstracted by `PA`. -/
def aFarmerWhoOwnsADonkey : Tree .t :=
  .fa (.lex (.a .x)) (.pm (.lex (.pred .farmer))
    (.pa .z (.fx (.fa (.lex (.role .hasGoal)) (.lex (.dpTrace .z))) .o
      (.fa (.lex (.tense .o)) (.pm (.lex (.pred .ownEvt))
        (.fx (.lex (.role .hasPatient)) .d (.fa (.lex (.a .d)) (.lex (.pred .donkey)))))))))

/-- (65): `FARMER([x]) ∧ DONKEY([d]) ∧ OWNS([o], x, d)`, the relative pronoun's variable
replaced by the indefinite's index. -/
theorem interp_aFarmerWhoOwnsADonkey :
    interp [] aFarmerWhoOwnsADonkey =
      restricted .x fun y => .conj (pred₁ .farmer y)
        (.conj (pred₂ .hasGoal (.var .o) (.var .x))
          (restricted .o fun e => .conj (pred₁ .ownEvt e)
            (.conj (pred₂ .hasPatient e (.var .d)) (restricted .d (pred₁ .donkey))))) := by
  simp only [aFarmerWhoOwnsADonkey, interp, Word.sem, FA, FX, PM, PA, lift, restricted, pred₁,
    pred₂, Formula.expand, List.foldl_nil, Formula.subst, Term.subst, Term.bracket,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceCtorEq, reduceIte]

/-- (66): "every girl wrote a paper", quantifier raising leaving a restricted-variable
trace in the restriction and a labeled trace in the scope. -/
def everyGirlWroteAPaper : Tree .t :=
  .fa (.fa (.lex .every) (.sa .g .G (.fa (.lex (.dTrace .g)) (.lex (.pred .girl)))))
    (.sa .g .P (.fx (.fx (.lex (.role .hasAgent)) .g (.lex (.ldpTrace .G))) .u
      (.fa (.lex (.tense .u)) (.pm (.lex (.pred .writeEvt))
        (.fx (.lex (.role .hasPatient)) .p (.fa (.lex (.a .p)) (.lex (.pred .paper))))))))

/-- (79): `EVERY(ΣgG, ΣgP) where G ≡ GIRL([g]), P ≡ (G ∧ PAPER([p]) ∧ WROTE([u], g, p))`. -/
theorem interp_everyGirlWroteAPaper :
    interp [] everyGirlWroteAPaper =
      .subset (SA .g .G (restricted .g (pred₁ .girl)))
        (SA .g .P (.conj (.conj (pred₂ .hasAgent (.var .u) (.var .g)) (.label .G))
          (restricted .u fun e => .conj (pred₁ .writeEvt e)
            (.conj (pred₂ .hasPatient e (.var .p)) (restricted .p (pred₁ .paper)))))) := rfl

/-- (93): the simple pronoun "she_x". -/
def sheX : Tree .e := .fa (.lex .she) (.lex (.core .x))

/-- (94c): `x | FEM(x) ∧ SG(x)`. -/
theorem interp_sheX :
    interp [] sheX = .presup (.var .x) (.conj (pred₁ .fem (.var .x)) (.sg (.var .x))) := rfl

/-- (99): the summation pronoun "they^P_p" after (66). -/
def theyP : Tree .e := .fa (.lex .they) (.sa .p .Y (.lex (.ldpTrace .P)))

/-- (100): `(ΣpP) | PL(ΣpP)`, the label `Y` of the pronoun's summation defined as `P`. -/
theorem interp_theyP :
    interp [] theyP = .presup (SA .p .Y (.label .P)) (.pl (SA .p .Y (.label .P))) := rfl

/-- (118): the label definitions of "Almost every student brought an umbrella today",
`S ≡ STUDENT([s])`, `B ≡ (S ∧ UMBRELLA([u]) ∧ BROUGHT([b], s, u))`. -/
def defs118 : List (Lab × Fm) :=
  [(.S, restricted .s (pred₁ .student)),
   (.B, .conj (.label .S) (.conj (restricted .u (pred₁ .umbrella))
      (.atom (.lex .brought) (.var .w) ![.bvar .b, .var .s, .var .u])))]

/-- (121): "Most of them used it", the subordinate quantifier's restriction a labeled trace
of the preceding sentence abstracted by `PA` (122). -/
def mostOfThemUsedIt : Tree .t :=
  .fa (.fa (.lex .most)
      (.sa .s' .M (.fa (.lex (.dTrace .s')) (.pa .s (.lex (.ldpTrace .B))))))
    (.sa .s' .U (.fx (.fx (.lex (.role .hasAgent)) .s' (.lex (.ldpTrace .M))) .e
      (.fa (.lex (.tense .e)) (.pm (.lex (.pred .useEvt))
        (.fa (.lex (.role .hasPatient)) (.fa (.lex .it) (.lex (.core .u))))))))

/-- (128): `MOST(Σs′M, Σs′U)` with `M` the definition of `B` under `s ↦ s′` (127) and
`U ≡ M ∧ USED([e], s′, u)`. -/
theorem interp_mostOfThemUsedIt :
    interp defs118 mostOfThemUsedIt =
      .atom .most (.var .w) ![
        SA .s' .M (restricted .s' fun y => .conj (.conj (.eq (.bvar .s') y) (pred₁ .student y))
          (.conj (restricted .u (pred₁ .umbrella))
            (.atom (.lex .brought) (.var .w) ![.bvar .b, y, .var .u]))),
        SA .s' .U (.conj (.conj (pred₂ .hasAgent (.var .e) (.var .s')) (.label .M))
          (restricted .e fun e => .conj (pred₁ .useEvt e)
            (pred₂ .hasPatient e (.presup (.var .u) (.sg (.var .u))))))] := by
  simp only [mostOfThemUsedIt, interp, Word.sem, FA, FX, PM, PA, SA, lift, restricted, pred₁,
    pred₂, defs118, Formula.expand, List.foldl_cons, List.foldl_nil, Formula.substLabels,
    Term.substLabels, assignment, Formula.subst, Term.subst, Term.bracket, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, reduceCtorEq, reduceIte, Option.getD_some]

/-! ### Scenarios -/

/-- A scenario: accessibility between worlds, the proportional relation interpreting
`most`, and the lexical relations at each world, by arity. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  most : Set (Atom W E) → Set (Atom W E) → Prop
  rel₁ : Lex 1 → W → E → Prop
  rel₂ : Lex 2 → W → E → E → Prop
  rel₃ : Lex 3 → W → E → E → E → Prop

/-- The lexical relations of a scenario on tuples of atoms: true of entities only. -/
def Scenario.rel (S : Scenario W E) : ∀ {n : ℕ}, Lex n → W → (Fin n → Atom W E) → Prop
  | 1, c, w, as => ∃ e, as 0 = Sum.inr e ∧ S.rel₁ c w e
  | 2, c, w, as => ∃ e e', as 0 = Sum.inr e ∧ as 1 = Sum.inr e' ∧ S.rel₂ c w e e'
  | 3, c, w, as => ∃ e e' e'', as 0 = Sum.inr e ∧ as 1 = Sum.inr e' ∧ as 2 = Sum.inr e'' ∧
      S.rel₃ c w e e' e''
  | _ + 4, _, _, _ => False
  | 0, _, _, _ => False

/-- The model of a scenario: lexical symbols distributively over pluralities of entities,
accessibility between worlds, and `most` as the scenario's proportional relation. -/
def Scenario.model (S : Scenario W E) : Model Sym (Atom W E) where
  I r Wp ts := match r with
    | .lex c => (Model.intensional S.rel).I c Wp ts
    | .acc => ∃ w u, Wp = world w ∧ ts 0 = world u ∧ S.acc w u
    | .most => S.most (ts 0) (ts 1)

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W} {x₀ : E}

theorem felicitous_pred₁ (c : Lex 1) (t : Tm) :
    (pred₁ c t).Felicitous S.model h ↔ t.Felicitous S.model h := by
  simp only [pred₁, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_one,
    Matrix.cons_val_zero, true_and]

theorem felicitous_pred₂ (c : Lex 2) (s t : Tm) :
    (pred₂ c s t).Felicitous S.model h ↔ s.Felicitous S.model h ∧ t.Felicitous S.model h := by
  simp only [pred₂, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, true_and]

/-- `w ∈ τ` at the world `w₀`. -/
theorem realize_mem_world (hw : h .w = world w₀) (t : Tm) :
    (Formula.mem (.var .w) t).Realize S.model h ↔ Sum.inl w₀ ∈ t.realize S.model h := by
  simp only [Formula.realize_mem, Term.realize_var, hw, world, Set.singleton_eq_singleton_iff,
    exists_eq_left']

/-- The modal base at the world `w₀`: the worlds accessible from it. -/
theorem realize_modalBase (hw : h .w = world w₀) :
    modalBase.realize S.model h = {a | ∃ u, a = Sum.inl u ∧ S.acc w₀ u} := by
  ext a
  rw [modalBase, Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [Formula.realize_atom, Term.realize_var, Scenario.model, Matrix.cons_val_zero]
  constructor
  · rintro ⟨g', hg, ha, w, u, hw', hu, hacc⟩
    rw [hg (by decide), hw, world_inj] at hw'
    subst hw'
    rw [hu] at ha
    exact ⟨u, ha, hacc⟩
  · rintro ⟨u, rfl, hacc⟩
    exact ⟨Function.update h .u (world u), fun y hy => Function.update_of_ne hy.2 _ _,
      by simp [world], w₀, u, by rw [Function.update_of_ne (by decide), hw], by simp, hacc⟩

/-! ### Paycheck pronouns and negation: an indefinite related to an external variable -/

/-- `c₁_w([y]) ∧ c₂_w(x, y)`: an indefinite `[y]` of kind `c₁` standing in the relation `c₂`
to the external variable `x` — `D ≡ DIORAMA([d]) ∧ MADE(x, d)` (112), `O ≡ CAR([c]) ∧
OWNS(x, c)` (137). -/
def indefOwned (c₁ : Lex 1) (c₂ : Lex 2) (y : Var) : Fm :=
  .conj (pred₁ c₁ (.bvar y)) (pred₂ c₂ (.var .x) (.var y))

variable (c₁ : Lex 1) (c₂ : Lex 2) {y : Var}

theorem locals_indefOwned : (indefOwned c₁ c₂ y).locals = [y] := rfl

theorem felicitous_indefOwned : (indefOwned c₁ c₂ y).Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (of_decide_eq_true rfl)

theorem realize_indefOwned (hx : h .x = {Sum.inr x₀}) :
    (indefOwned c₁ c₂ y).Realize S.model h ↔
      ∃ w, h .w = world w ∧ (h y).Nonempty ∧
        ∀ a ∈ h y, ∃ e, a = Sum.inr e ∧ S.rel₁ c₁ w e ∧ S.rel₂ c₂ w x₀ e := by
  simp only [indefOwned, pred₁, pred₂, Formula.realize_conj, Formula.realize_atom,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Model.intensional_apply₂, Scenario.rel, Matrix.cons_val_zero,
    Matrix.cons_val_one, hx, Set.mem_singleton_iff, forall_eq, Set.singleton_nonempty, true_and]
  constructor
  · rintro ⟨⟨w, hw, hne, h₁⟩, w', hw', -, h₂⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw')
    refine ⟨w, hw, hne, fun a ha => ?_⟩
    obtain ⟨e, rfl, he⟩ := h₁ a ha
    obtain ⟨e₁, e₂, h₁', h₂', he₂⟩ := h₂ _ ha
    cases Sum.inr.inj h₁'
    cases Sum.inr.inj h₂'
    exact ⟨e, rfl, he, he₂⟩
  · rintro ⟨w, hw, hne, H⟩
    exact ⟨⟨w, hw, hne, fun a ha => (H a ha).imp fun e he => ⟨he.1, he.2.1⟩⟩, w, hw, hne,
      fun a ha => (H a ha).elim fun e he => ⟨x₀, e, rfl, he.1, he.2.2⟩⟩

/-- The summation over the indefinite takes its value from the external variable: the
paycheck pronoun `ΣdD` denotes the dioramas made by whatever `x` is (112). -/
theorem realize_sigma_indefOwned (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀})
    (hyw : y ≠ .w) (hyx : y ≠ .x) :
    (Term.sigma y (indefOwned c₁ c₂ y)).realize S.model h =
      {a | ∃ e, a = Sum.inr e ∧ S.rel₁ c₁ w₀ e ∧ S.rel₂ c₂ w₀ x₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    have hgx : g' .x = h .x := hg ⟨fun hm => hyx (List.mem_singleton.1 hm).symm, hyx.symm⟩
    have hgw : g' .w = h .w := hg ⟨fun hm => hyw (List.mem_singleton.1 hm).symm, hyw.symm⟩
    obtain ⟨w, hw', -, H⟩ := (realize_indefOwned S g' c₁ c₂ (hgx.trans hx)).1 hr
    obtain rfl := world_inj.1 (hw.symm.trans (hgw.symm.trans hw'))
    exact H a ha
  · rintro ⟨e, rfl, h₁, h₂⟩
    refine ⟨Function.update h y {Sum.inr e}, fun y' hy => Function.update_of_ne hy.2 _ _,
      by simp, (realize_indefOwned S _ c₁ c₂ (by rw [Function.update_of_ne hyx.symm, hx])).2
        ⟨w₀, by rw [Function.update_of_ne hyw.symm, hw], by simp, fun a ha => ?_⟩⟩
    simp only [Function.update_self, Set.mem_singleton_iff] at ha
    exact ⟨e, ha, h₁, h₂⟩

/-- The summation over worlds of the indefinite's description: the worlds where `x` has
such a thing. -/
theorem realize_sigmaW_indefOwned (hx : h .x = {Sum.inr x₀}) (hyw : y ≠ .w) (hyx : y ≠ .x) :
    (Term.sigma .w (indefOwned c₁ c₂ y)).realize S.model h =
      {a | ∃ w e, a = Sum.inl w ∧ S.rel₁ c₁ w e ∧ S.rel₂ c₂ w x₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    have hgx : g' .x = h .x := hg ⟨fun hm => hyx (List.mem_singleton.1 hm).symm, by decide⟩
    obtain ⟨w, hw', ⟨b, hb⟩, H⟩ := (realize_indefOwned S g' c₁ c₂ (hgx.trans hx)).1 hr
    rw [hw'] at ha
    obtain ⟨e, -, h₁, h₂⟩ := H b hb
    exact ⟨w, e, ha, h₁, h₂⟩
  · rintro ⟨w, e, rfl, h₁, h₂⟩
    refine ⟨Function.update (Function.update h .w (world w)) y {Sum.inr e}, fun y' hy => ?_,
      by rw [Function.update_of_ne hyw.symm]; simp [world],
      (realize_indefOwned S _ c₁ c₂ (by rw [Function.update_of_ne hyx.symm,
        Function.update_of_ne (by decide), hx])).2
        ⟨w, by rw [Function.update_of_ne hyw.symm, Function.update_self], by simp,
          fun a ha => ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, locals_indefOwned, List.mem_singleton] at hy
      rw [Function.update_of_ne hy.1, Function.update_of_ne hy.2]
    · simp only [Function.update_self, Set.mem_singleton_iff] at ha
      exact ⟨e, ha, h₁, h₂⟩

theorem felicitous_sgPronoun_indefOwned_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀})
    (hyw : y ≠ .w) (hyx : y ≠ .x) :
    (Term.sgPronoun y (indefOwned c₁ c₂ y)).Felicitous S.model h ↔
      ∃! e, S.rel₁ c₁ w₀ e ∧ S.rel₂ c₂ w₀ x₀ e := by
  rw [Term.felicitous_sgPronoun, realize_sigma_indefOwned S h c₁ c₂ hw hx hyw hyx,
    exists_eq_singleton_iff]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ fun g => felicitous_indefOwned S g c₁ c₂)

/-- `O ≡ CAR_w([c]) ∧ OWNS_w(x, c)` (137). -/
def ownCar : Fm := indefOwned .car .owns .c

/-- `NOT^O`: `w ∉ ΣwO` (136)–(137), "he doesn't own a car". -/
def notOwn : Fm := .neg (.mem (.var .w) (.sigma .w (.label .O)))

/-- (139): "He doesn't own a car. #It is in the shop." -/
def shop139 : Fm :=
  .conj (.conj notOwn (pred₁ .inShop (Term.sgPronoun .c (.label .O)))) (.labelDef .O ownCar)

/-- (138b): "It's not like he doesn't own a car. It is just in the shop." -/
def shop138 : Fm :=
  .conj (.conj (.neg (.mem (.var .w) (.sigma .w notOwn)))
      (pred₁ .inShop (Term.sgPronoun .c (.label .O))))
    (.labelDef .O ownCar)

theorem expandSelf_shop139 :
    shop139.expandSelf =
      .conj (.conj (.neg (.mem (.var .w) (.sigma .w ownCar)))
          (pred₁ .inShop (Term.sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := by
  rw [Formula.expandSelf, show shop139.defs = [(.O, ownCar)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, shop139, notOwn, Term.sgPronoun, pred₁, ownCar,
    indefOwned, pred₂, Formula.substLabels, Term.substLabels, assignment, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

theorem expandSelf_shop138 :
    shop138.expandSelf =
      .conj (.conj (.neg (.mem (.var .w) (.sigma .w (.neg (.mem (.var .w) (.sigma .w ownCar))))))
          (pred₁ .inShop (Term.sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := by
  rw [Formula.expandSelf, show shop138.defs = [(.O, ownCar)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, shop138, notOwn, Term.sgPronoun, pred₁, ownCar,
    indefOwned, pred₂, Formula.substLabels, Term.substLabels, assignment, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

/-- (139) is felicitous at `w₀` iff he owns a car there — iff its first sentence is false. -/
theorem felicitous_shop139_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀}) :
    shop139.expandSelf.Felicitous S.model h ↔ ∃ c, S.rel₁ .car w₀ c ∧ S.rel₂ .owns w₀ x₀ c := by
  rw [expandSelf_shop139]
  simp only [Formula.felicitous_conj, Formula.felicitous_neg, Formula.felicitous_mem,
    Formula.felicitous_labelDef, Formula.realize_neg, Term.felicitous_var, ownCar,
    Term.felicitous_sigma_of_forall _ _ fun g => felicitous_indefOwned S g .car .owns,
    realize_mem_world S h hw, realize_sigmaW_indefOwned S h _ _ hx (show Var.c ≠ Var.w by decide)
      (show Var.c ≠ Var.x by decide), Set.mem_ofPred_eq, Sum.inl.injEq, exists_and_left,
    exists_eq_left', felicitous_pred₁, felicitous_sgPronoun_indefOwned_iff S h _ _ hw hx
      (show Var.c ≠ Var.w by decide) (show Var.c ≠ Var.x by decide), implies_true, true_and,
    and_true]
  exact ⟨fun H => not_not.1 fun hn => hn (H hn).exists, fun H hn => absurd H hn⟩

/-- The double negation of (138b) sums `w` over all pluralities, of which every non-world
fails `w ∈ ΣwO`; so `w ∉ Σw(w ∉ ΣwO)` is false at any world once the model has a second
atom. -/
theorem not_realize_shop138 (hw : h .w = world w₀) (a₁ : Atom W E) (ha : a₁ ≠ Sum.inl w₀) :
    ¬ shop138.expandSelf.Realize S.model h := by
  rw [expandSelf_shop138]
  rintro ⟨⟨hneg, -⟩, -⟩
  refine hneg ((realize_mem_world S h hw _).2 ?_)
  rw [Term.mem_realize_sigma]
  refine ⟨Function.update h .w {Sum.inl w₀, a₁}, fun y hy => Function.update_of_ne hy.2 _ _,
    by simp, ?_⟩
  rintro ⟨a, hd, -⟩
  have hd' : ({Sum.inl w₀, a₁} : Set (Atom W E)) = {a} := hd
  exact ha ((Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert_of_mem _ (Set.mem_singleton a₁))).trans
    (Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert _ _)).symm)

/-! ### Negation and disjunction -/

/-- `X ≡ SG(b) ∧ BATHROOM_w([b]) ∧ HERE_w(b)` (143). -/
def bathroomX : Fm :=
  .conj (.sg (.var .b)) (.conj (pred₁ .bathroom (.bvar .b)) (pred₁ .here (.var .b)))

/-- (143): "Either there is no bathroom here or it's in a funny place",
`(w ∉ ΣwX ∨ FUNNY-PLACE_w(ΣbX | SG(ΣbX))) ∧ X ≡ …`. -/
def bathroom143 : Fm :=
  .conj (.disj (.neg (.mem (.var .w) (.sigma .w (.label .X))))
      (pred₁ .funnyPlace (Term.sgPronoun .b (.label .X))))
    (.labelDef .X bathroomX)

theorem locals_bathroomX : bathroomX.locals = [.b] := rfl

theorem felicitous_bathroomX : bathroomX.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem realize_bathroomX :
    bathroomX.Realize S.model h ↔
      ∃ w e, h .w = world w ∧ h .b = {Sum.inr e} ∧ S.rel₁ .bathroom w e ∧ S.rel₁ .here w e := by
  simp only [bathroomX, pred₁, Formula.realize_conj, Formula.realize_sg, Formula.realize_atom,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Scenario.rel, Matrix.cons_val_zero]
  constructor
  · rintro ⟨⟨a, hb⟩, ⟨w, hw, -, h₁⟩, w', hw', -, h₂⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw')
    obtain ⟨e, rfl, he⟩ := h₁ a (by rw [hb]; exact Set.mem_singleton a)
    obtain ⟨e', he', he''⟩ := h₂ _ (by rw [hb]; exact Set.mem_singleton _)
    cases Sum.inr.inj he'
    exact ⟨w, e, hw, hb, he, he''⟩
  · rintro ⟨w, e, hw, hb, h₁, h₂⟩
    refine ⟨⟨_, hb⟩, ⟨w, hw, ⟨_, by rw [hb]; exact Set.mem_singleton _⟩, fun a ha => ?_⟩,
      w, hw, ⟨_, by rw [hb]; exact Set.mem_singleton _⟩, fun a ha => ?_⟩ <;>
    · rw [hb] at ha
      exact ⟨e, ha, by assumption⟩

theorem realize_sigmaB_bathroomX (hw : h .w = world w₀) :
    (Term.sigma .b bathroomX).realize S.model h =
      {a | ∃ e, a = Sum.inr e ∧ S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_bathroomX]
  constructor
  · rintro ⟨g', hg, ha, w, e, hw', hb, h₁, h₂⟩
    rw [hg (by decide), hw, world_inj] at hw'
    subst hw'
    rw [hb] at ha
    exact ⟨e, ha, h₁, h₂⟩
  · rintro ⟨e, rfl, h₁, h₂⟩
    refine ⟨Function.update h .b {Sum.inr e}, fun y hy => Function.update_of_ne hy.2 _ _,
      by simp, w₀, e, ?_, by simp, h₁, h₂⟩
    rw [Function.update_of_ne (by decide), hw]

theorem realize_sigmaW_bathroomX :
    (Term.sigma .w bathroomX).realize S.model h =
      {a | ∃ w e, a = Sum.inl w ∧ S.rel₁ .bathroom w e ∧ S.rel₁ .here w e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_bathroomX]
  constructor
  · rintro ⟨g', -, ha, w, e, hw', -, h₁, h₂⟩
    rw [hw'] at ha
    exact ⟨w, e, ha, h₁, h₂⟩
  · rintro ⟨w, e, rfl, h₁, h₂⟩
    refine ⟨Function.update (Function.update h .w (world w)) .b {Sum.inr e}, fun y hy => ?_,
      by simp [world], w, e, by simp, by simp, h₁, h₂⟩
    simp only [Set.mem_ofPred_eq, locals_bathroomX, List.mem_singleton] at hy
    rw [Function.update_of_ne hy.1, Function.update_of_ne hy.2]

theorem expandSelf_bathroom143 :
    bathroom143.expandSelf =
      .conj (.disj (.neg (.mem (.var .w) (.sigma .w bathroomX)))
          (pred₁ .funnyPlace (Term.sgPronoun .b bathroomX)))
        (.labelDef .X bathroomX) := by
  rw [Formula.expandSelf, show bathroom143.defs = [(.X, bathroomX)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, bathroom143, Formula.disj, Term.sgPronoun, pred₁,
    bathroomX, Formula.substLabels, Term.substLabels, assignment, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

/-- (145): the bathroom disjunction is felicitous at `w₀` iff, if there is a bathroom here,
there is exactly one. -/
theorem felicitous_bathroom143_iff (hw : h .w = world w₀) :
    bathroom143.expandSelf.Felicitous S.model h ↔
      ((∃ e, S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e) →
        ∃! e, S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e) := by
  rw [expandSelf_bathroom143]
  simp only [Formula.felicitous_conj, Formula.felicitous_disj, Formula.felicitous_neg,
    Formula.felicitous_mem, Formula.felicitous_labelDef, Formula.realize_neg, not_not,
    Term.felicitous_var, Term.felicitous_sigma_of_forall _ _ (felicitous_bathroomX S),
    realize_mem_world S h hw, realize_sigmaW_bathroomX, Set.mem_ofPred_eq, Sum.inl.injEq,
    exists_and_left, exists_eq_left', felicitous_pred₁, Term.felicitous_sgPronoun,
    realize_sigmaB_bathroomX S h hw, exists_eq_singleton_iff, implies_true, true_and, and_true]

/-! ### Modal subordination -/

/-- `W ≡ WOLF_w([x]) ∧ ENTERS_w(x)` (133a). -/
def wolfW : Fm := .conj (pred₁ .wolf (.bvar .x)) (pred₁ .enters (.var .x))

/-- `E ≡ W ∧ TIM_w([t]) ∧ EATS_w(x, t)` (133b). -/
def wolfE : Fm :=
  .conj (.label .W) (.conj (pred₁ .tim (.bvar .t)) (pred₂ .eats (.var .x) (.var .t)))

/-- (133): "A wolf might enter. It would eat Tasty Tim first.", `MIGHT(β_w, ΣwW) ∧
MUST(β_w, ΣwW, ΣwE)` (129) with the second modal's restriction the first's nuclear scope. -/
def wolfDiscourse : Fm :=
  .conj (.conj (.some_ modalBase (.sigma .w (.label .W)))
      (.subset (.inter modalBase (.sigma .w (.label .W))) (.sigma .w (.label .E))))
    (.conj (.labelDef .W wolfW) (.labelDef .E wolfE))

/-- `E` with `W` expanded. -/
def wolfE' : Fm := .conj wolfW (.conj (pred₁ .tim (.bvar .t)) (pred₂ .eats (.var .x) (.var .t)))

theorem expandSelf_wolfDiscourse :
    wolfDiscourse.expandSelf =
      .conj (.conj (.some_ modalBase (.sigma .w wolfW))
          (.subset (.inter modalBase (.sigma .w wolfW)) (.sigma .w wolfE')))
        (.conj (.labelDef .W wolfW) (.labelDef .E wolfE')) := by
  rw [Formula.expandSelf, show wolfDiscourse.defs = [(.W, wolfW), (.E, wolfE)] from rfl,
    Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, wolfDiscourse, wolfW, wolfE, wolfE', modalBase,
    Formula.some_, pred₁, pred₂, Formula.substLabels, Term.substLabels, assignment,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceCtorEq, reduceIte, Option.getD_some]

theorem locals_wolfW : wolfW.locals = [.x] := rfl

theorem locals_wolfE' : wolfE'.locals = [.x, .t] := rfl

theorem realize_wolfW :
    wolfW.Realize S.model h ↔
      ∃ w, h .w = world w ∧ (h .x).Nonempty ∧
        ∀ a ∈ h .x, ∃ e, a = Sum.inr e ∧ S.rel₁ .wolf w e ∧ S.rel₁ .enters w e := by
  simp only [wolfW, pred₁, Formula.realize_conj, Formula.realize_atom, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Scenario.rel, Matrix.cons_val_zero]
  constructor
  · rintro ⟨⟨w, hw, hne, h₁⟩, w', hw', -, h₂⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw')
    refine ⟨w, hw, hne, fun a ha => ?_⟩
    obtain ⟨e, rfl, he⟩ := h₁ a ha
    obtain ⟨e', he', he''⟩ := h₂ _ ha
    cases Sum.inr.inj he'
    exact ⟨e, rfl, he, he''⟩
  · rintro ⟨w, hw, hne, H⟩
    exact ⟨⟨w, hw, hne, fun a ha => (H a ha).imp fun e he => ⟨he.1, he.2.1⟩⟩, w, hw, hne,
      fun a ha => (H a ha).imp fun e he => ⟨he.1, he.2.2⟩⟩

theorem realize_wolfE' :
    wolfE'.Realize S.model h ↔
      ∃ w, h .w = world w ∧ (h .x).Nonempty ∧ (h .t).Nonempty ∧
        (∀ a ∈ h .x, ∃ e, a = Sum.inr e ∧ S.rel₁ .wolf w e ∧ S.rel₁ .enters w e) ∧
        (∀ b ∈ h .t, ∃ t, b = Sum.inr t ∧ S.rel₁ .tim w t) ∧
        ∀ a ∈ h .x, ∀ b ∈ h .t, ∃ e t, a = Sum.inr e ∧ b = Sum.inr t ∧ S.rel₂ .eats w e t := by
  rw [wolfE', Formula.realize_conj, realize_wolfW]
  simp only [pred₁, pred₂, Formula.realize_conj, Formula.realize_atom, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Model.intensional_apply₂, Scenario.rel, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨w, hw, hne, H⟩, ⟨w₁, hw₁, hne', H₁⟩, w₂, hw₂, -, -, H₂⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw₁)
    obtain rfl := world_inj.1 (hw.symm.trans hw₂)
    exact ⟨w, hw, hne, hne', H, H₁, H₂⟩
  · rintro ⟨w, hw, hne, hne', H, H₁, H₂⟩
    exact ⟨⟨w, hw, hne, H⟩, ⟨w, hw, hne', H₁⟩, w, hw, hne, hne', H₂⟩

theorem realize_sigmaW_wolfW :
    (Term.sigma .w wolfW).realize S.model h =
      {a | ∃ w e, a = Sum.inl w ∧ S.rel₁ .wolf w e ∧ S.rel₁ .enters w e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_wolfW]
  constructor
  · rintro ⟨g', -, ha, w, hw', ⟨b, hb⟩, H⟩
    rw [hw'] at ha
    obtain ⟨e, -, h₁, h₂⟩ := H b hb
    exact ⟨w, e, ha, h₁, h₂⟩
  · rintro ⟨w, e, rfl, h₁, h₂⟩
    refine ⟨Function.update (Function.update h .w (world w)) .x {Sum.inr e}, fun y hy => ?_,
      by simp [world], w, by simp, by simp, fun a ha => ?_⟩
    · simp only [Set.mem_ofPred_eq, locals_wolfW, List.mem_singleton] at hy
      rw [Function.update_of_ne hy.1, Function.update_of_ne hy.2]
    · simp only [Function.update_self, Set.mem_singleton_iff] at ha
      exact ⟨e, ha, h₁, h₂⟩

theorem realize_sigmaW_wolfE' :
    (Term.sigma .w wolfE').realize S.model h =
      {a | ∃ w e t, a = Sum.inl w ∧ (S.rel₁ .wolf w e ∧ S.rel₁ .enters w e) ∧
        S.rel₁ .tim w t ∧ S.rel₂ .eats w e t} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_wolfE']
  constructor
  · rintro ⟨g', -, ha, w, hw', ⟨b, hb⟩, ⟨b', hb'⟩, H, H₁, H₂⟩
    rw [hw'] at ha
    obtain ⟨e, rfl, h₁, h₂⟩ := H b hb
    obtain ⟨t, rfl, ht⟩ := H₁ b' hb'
    obtain ⟨e', t', he', ht', het⟩ := H₂ _ hb _ hb'
    cases Sum.inr.inj he'
    cases Sum.inr.inj ht'
    exact ⟨w, e, t, ha, ⟨h₁, h₂⟩, ht, het⟩
  · rintro ⟨w, e, t, rfl, ⟨h₁, h₂⟩, ht, het⟩
    refine ⟨Function.update (Function.update (Function.update h .w (world w)) .x {Sum.inr e})
      .t {Sum.inr t}, fun y hy => ?_, by simp [world], w, by simp, by simp, by simp,
      fun a ha => ?_, fun b hb => ?_, fun a ha b hb => ?_⟩
    · simp only [Set.mem_ofPred_eq, locals_wolfE', List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hy
      rw [Function.update_of_ne hy.1.2, Function.update_of_ne hy.1.1, Function.update_of_ne hy.2]
    · simp only [Function.update_of_ne (show Var.x ≠ Var.t by decide), Function.update_self,
        Set.mem_singleton_iff] at ha
      exact ⟨e, ha, h₁, h₂⟩
    · simp only [Function.update_self, Set.mem_singleton_iff] at hb
      exact ⟨t, hb, ht⟩
    · simp only [Function.update_of_ne (show Var.x ≠ Var.t by decide), Function.update_self,
        Set.mem_singleton_iff] at ha hb
      exact ⟨e, t, ha, hb, het⟩

/-- (133) at `w₀`: some accessible world has a wolf entering, and in every accessible
world where a wolf enters, a wolf that enters eats Tim. -/
theorem realize_wolfDiscourse_iff (hw : h .w = world w₀) :
    wolfDiscourse.expandSelf.Realize S.model h ↔
      (∃ u e, S.acc w₀ u ∧ S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) ∧
        ∀ u, S.acc w₀ u → (∃ e, S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) →
          ∃ e t, (S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) ∧ S.rel₁ .tim u t ∧
            S.rel₂ .eats u e t := by
  rw [expandSelf_wolfDiscourse]
  simp only [Formula.realize_conj, Formula.realize_some, Formula.realize_subset,
    Term.realize_inter, Formula.realize_labelDef, and_true, realize_modalBase S h hw,
    realize_sigmaW_wolfW, realize_sigmaW_wolfE', Set.Nonempty, Set.subset_def, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, ⟨u, rfl, hacc⟩, w', e, ⟨⟩, he⟩, H⟩
    refine ⟨⟨u, e, hacc, he⟩, fun u hu ⟨e, he⟩ => ?_⟩
    obtain ⟨w', e', t, ⟨⟩, het⟩ := H _ ⟨⟨u, rfl, hu⟩, u, e, rfl, he⟩
    exact ⟨e', t, het⟩
  · rintro ⟨⟨u, e, hacc, he⟩, H⟩
    refine ⟨⟨_, ⟨u, rfl, hacc⟩, u, e, rfl, he⟩, ?_⟩
    rintro _ ⟨⟨u, rfl, hu⟩, w', e, ⟨⟩, he⟩
    obtain ⟨e', t, het⟩ := H u hu ⟨e, he⟩
    exact ⟨u, e', t, rfl, het⟩

/-! ### Summation pronouns -/

/-- (102)–(103): "Most dogs bark. They are loud.", `MOST(ΣdD, ΣdB) ∧ LOUD(ΣdB)` with
`D ≡ DOG([d])`, `B ≡ (D ∧ BARKS(d))`. -/
def theyLoud : Fm :=
  .conj (.conj (.atom .most (.var .w) ![.sigma .d (.label .D), .sigma .d (.label .B)])
      (pred₁ .loud (.sigma .d (.label .B))))
    (.conj (.labelDef .D (pred₁ .dog (.bvar .d)))
      (.labelDef .B (.conj (.label .D) (pred₁ .barks (.var .d)))))

/-- (104): the pronoun denotes the sum of the barking dogs. -/
theorem expandSelf_theyLoud :
    theyLoud.expandSelf =
      .conj (.conj (.atom .most (.var .w) ![.sigma .d (pred₁ .dog (.bvar .d)),
            .sigma .d (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d)))])
          (pred₁ .loud (.sigma .d (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d))))))
        (.conj (.labelDef .D (pred₁ .dog (.bvar .d)))
          (.labelDef .B (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d))))) := by
  rw [Formula.expandSelf, show theyLoud.defs = [(.D, pred₁ .dog (.bvar .d)),
    (.B, .conj (.label .D) (pred₁ .barks (.var .d)))] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, theyLoud, pred₁, Formula.substLabels,
    Term.substLabels, assignment, Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceCtorEq,
    reduceIte, Option.getD_some]

/-! ### Presupposition under quantification -/

/-- `K ≡ MONARCH-OF_w([k], m)`; `ΣkK | SG(ΣkK)` is "its monarch". -/
def monarchK : Fm := pred₂ .monarchOf (.bvar .k) (.var .m)

/-- `Z ∧ CHERISH_w(m, ΣkK | SG(ΣkK))`: the nuclear scope of "cherishes its monarch" over the
restriction `Z`, the pronoun's presupposition to be satisfied by `Z`. -/
def cherishBody (Z : Lab) : Fm :=
  .conj (.label Z) (pred₂ .cherish (.var .m) (Term.sgPronoun .k (.label .K)))

/-- `R ≡ SG(m) ∧ MONARCHY_w([m])`, with the singular restricted variable's `SG` as in (143). -/
def monarchyR : Fm := .conj (.sg (.var .m)) (pred₁ .monarchy (.bvar .m))

/-- (146a): "Every monarchy cherishes its monarch", `EVERY(ΣmR, ΣmS)` with `S ≡ R ∧
CHERISH(m, ΣkK | SG(ΣkK))`. -/
def everyMonarchy : Fm :=
  .conj (.subset (.sigma .m (.label .R)) (.sigma .m (.label .S)))
    (.conj (.labelDef .R monarchyR) (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody .R))))

/-- `C ≡ SG(m) ∧ COUNTRY_w([m])`. -/
def countryC : Fm := .conj (.sg (.var .m)) (pred₁ .country (.bvar .m))

/-- `M ≡ C ∧ MONARCHY_w(m)`: the reference set of "every European country was a monarchy". -/
def monarchyM : Fm := .conj (.label .C) (pred₁ .monarchy (.var .m))

/-- (150a): "Every European country was a monarchy. Most of them cherished their monarchs.",
the subordinate quantifier's restriction the first sentence's reference-set label `M`. -/
def discourse150a : Fm :=
  .conj (.conj (.subset (.sigma .m (.label .C)) (.sigma .m (.label .M)))
      (.atom .most (.var .w) ![.sigma .m (.label .M), .sigma .m (.label .S)]))
    (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM)
      (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody .M)))))

/-- The nuclear scope with the restriction and the pronoun's label expanded. -/
def cherishBody' (ρ : Fm) : Fm :=
  .conj ρ (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK))

/-- `M` with `C` expanded. -/
def monarchyM' : Fm := .conj countryC (pred₁ .monarchy (.var .m))

theorem expandSelf_everyMonarchy :
    everyMonarchy.expandSelf =
      .conj (.subset (.sigma .m monarchyR) (.sigma .m (cherishBody' monarchyR)))
        (.conj (.labelDef .R monarchyR)
          (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody' monarchyR)))) := by
  rw [Formula.expandSelf, show everyMonarchy.defs =
    [(.R, monarchyR), (.K, monarchK), (.S, cherishBody .R)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, everyMonarchy, cherishBody, cherishBody', monarchyR,
    monarchK, Term.sgPronoun, pred₁, pred₂, Formula.substLabels, Term.substLabels, assignment,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceCtorEq, reduceIte, Option.getD_some]

theorem expandSelf_discourse150a :
    discourse150a.expandSelf =
      .conj (.conj (.subset (.sigma .m countryC) (.sigma .m monarchyM'))
          (.atom .most (.var .w) ![.sigma .m monarchyM', .sigma .m (cherishBody' monarchyM')]))
        (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM')
          (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody' monarchyM'))))) := by
  rw [Formula.expandSelf, show discourse150a.defs =
    [(.C, countryC), (.M, monarchyM), (.K, monarchK), (.S, cherishBody .M)] from rfl,
    Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, discourse150a, cherishBody, cherishBody', countryC,
    monarchyM, monarchyM', monarchK, Term.sgPronoun, pred₁, pred₂, Formula.substLabels,
    Term.substLabels, assignment, Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceCtorEq,
    reduceIte, Option.getD_some]

theorem felicitous_monarchK : monarchK.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem realize_monarchK :
    monarchK.Realize S.model h ↔
      ∃ w, h .w = world w ∧ (h .k).Nonempty ∧ (h .m).Nonempty ∧
        ∀ a ∈ h .k, ∀ b ∈ h .m, ∃ e e', a = Sum.inr e ∧ b = Sum.inr e' ∧
          S.rel₂ .monarchOf w e e' := by
  simp only [monarchK, pred₂, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Term.realize_bvar, Scenario.model, Model.intensional_apply₂, Scenario.rel,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- "Its monarch" at a singular `m₀`: the monarchs of `m₀`. -/
theorem realize_sigmaK_monarchK {m₀ : E} (hw : h .w = world w₀) (hm : h .m = {Sum.inr m₀}) :
    (Term.sigma .k monarchK).realize S.model h =
      {a | ∃ e, a = Sum.inr e ∧ S.rel₂ .monarchOf w₀ e m₀} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_monarchK]
  constructor
  · rintro ⟨g', hg, ha, w, hw', -, -, H⟩
    rw [hg (by decide), hw, world_inj] at hw'
    subst hw'
    obtain ⟨e, e', he, he', hme⟩ := H a ha _ (by rw [hg (by decide), hm]; exact Set.mem_singleton _)
    cases Sum.inr.inj he'
    exact ⟨e, he, hme⟩
  · rintro ⟨e, rfl, he⟩
    refine ⟨Function.update h .k {Sum.inr e}, fun y hy => Function.update_of_ne hy.2 _ _,
      by simp, w₀, by rw [Function.update_of_ne (by decide), hw], by simp,
      by rw [Function.update_of_ne (by decide), hm]; simp, fun a ha b hb => ?_⟩
    simp only [Function.update_self, Function.update_of_ne (show Var.m ≠ Var.k by decide), hm,
      Set.mem_singleton_iff] at ha hb
    exact ⟨e, m₀, ha, hb, he⟩

theorem felicitous_sgPronoun_monarchK_iff {m₀ : E} (hw : h .w = world w₀)
    (hm : h .m = {Sum.inr m₀}) :
    (Term.sgPronoun .k monarchK).Felicitous S.model h ↔ ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  rw [Term.felicitous_sgPronoun, realize_sigmaK_monarchK S h hw hm, exists_eq_singleton_iff]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ (felicitous_monarchK S))

/-- Felicity of the nuclear-scope summation over a restriction `ρ` true exactly of the
singular `m` satisfying `Q`: the pronoun's presupposition, for each of them. -/
theorem felicitous_sigmaM_cherishBody'_iff {ρ : Fm} {Q : E → Prop} (hw : h .w = world w₀)
    (hlw : Var.w ∉ ρ.locals) (hρf : ∀ g, ρ.Felicitous S.model g)
    (hρ : ∀ g : Var → Set (Atom W E), g .w = world w₀ →
      (ρ.Realize S.model g ↔ ∃ m₀, g .m = {Sum.inr m₀} ∧ Q m₀)) :
    (Term.sigma .m (cherishBody' ρ)).Felicitous S.model h ↔
      ∀ m₀, Q m₀ → ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  rw [Term.felicitous_sigma]
  constructor
  · intro H m₀ hm
    have hg : Set.EqOn (Function.update h .m {Sum.inr m₀}) h
        {y | y ∉ (cherishBody' ρ).locals ∧ y ≠ Var.m} := fun y hy => Function.update_of_ne hy.2 _ _
    have hw' : Function.update h .m {Sum.inr m₀} .w = world w₀ := by
      rw [Function.update_of_ne (by decide), hw]
    obtain ⟨-, H'⟩ := H _ hg
    exact (felicitous_sgPronoun_monarchK_iff S _ hw' (Function.update_self ..)).1
      ((felicitous_pred₂ S _ _ _ _).1 (H' ((hρ _ hw').2 ⟨m₀, Function.update_self .., hm⟩))).2
  · intro H g' hg
    have hl : (cherishBody' ρ).locals = ρ.locals := by
      show ρ.locals ++ (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK)).locals = ρ.locals
      rw [show (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK)).locals = [] from rfl,
        List.append_nil]
    have hw' : g' .w = world w₀ := by rw [hg ⟨by rw [hl]; exact hlw, by decide⟩, hw]
    refine ⟨hρf g', fun hr => (felicitous_pred₂ S _ _ _ _).2 ⟨trivial, ?_⟩⟩
    obtain ⟨m₀, hm, hq⟩ := (hρ g' hw').1 hr
    exact (felicitous_sgPronoun_monarchK_iff S g' hw' hm).2 (H m₀ hq)

theorem felicitous_monarchyR : monarchyR.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem realize_monarchyR_iff (hw : h .w = world w₀) :
    monarchyR.Realize S.model h ↔ ∃ m₀, h .m = {Sum.inr m₀} ∧ S.rel₁ .monarchy w₀ m₀ := by
  simp only [monarchyR, pred₁, Formula.realize_conj, Formula.realize_sg, Formula.realize_atom,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Scenario.rel, Matrix.cons_val_zero, hw, world_inj]
  constructor
  · rintro ⟨⟨a, hm⟩, w, rfl, -, H⟩
    obtain ⟨e, rfl, he⟩ := H a (by rw [hm]; exact Set.mem_singleton a)
    exact ⟨e, hm, he⟩
  · rintro ⟨e, hm, he⟩
    exact ⟨⟨_, hm⟩, w₀, rfl, ⟨_, by rw [hm]; exact Set.mem_singleton _⟩,
      fun a ha => ⟨e, by rw [hm] at ha; exact ha, he⟩⟩

/-- (146a) is felicitous at `w₀` iff every monarchy there has exactly one monarch: the
restriction satisfies the presupposition of the nuclear scope pointwise. -/
theorem felicitous_everyMonarchy_iff (hw : h .w = world w₀) :
    everyMonarchy.expandSelf.Felicitous S.model h ↔
      ∀ m₀, S.rel₁ .monarchy w₀ m₀ → ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  rw [expandSelf_everyMonarchy]
  simp only [Formula.felicitous_conj, Formula.felicitous_subset, Formula.felicitous_labelDef,
    Formula.realize_labelDef, Term.felicitous_sigma_of_forall _ _ (felicitous_monarchyR S),
    implies_true, and_true, true_and,
    felicitous_sigmaM_cherishBody'_iff S h hw (by decide) (felicitous_monarchyR S)
      (fun g hg => realize_monarchyR_iff S g hg)]

theorem felicitous_countryC : countryC.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem felicitous_monarchyM' : monarchyM'.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem realize_countryC_iff (hw : h .w = world w₀) :
    countryC.Realize S.model h ↔ ∃ m₀, h .m = {Sum.inr m₀} ∧ S.rel₁ .country w₀ m₀ := by
  simp only [countryC, pred₁, Formula.realize_conj, Formula.realize_sg, Formula.realize_atom,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Scenario.rel, Matrix.cons_val_zero, hw, world_inj]
  constructor
  · rintro ⟨⟨a, hm⟩, w, rfl, -, H⟩
    obtain ⟨e, rfl, he⟩ := H a (by rw [hm]; exact Set.mem_singleton a)
    exact ⟨e, hm, he⟩
  · rintro ⟨e, hm, he⟩
    exact ⟨⟨_, hm⟩, w₀, rfl, ⟨_, by rw [hm]; exact Set.mem_singleton _⟩,
      fun a ha => ⟨e, by rw [hm] at ha; exact ha, he⟩⟩

theorem realize_monarchyM'_iff (hw : h .w = world w₀) :
    monarchyM'.Realize S.model h ↔
      ∃ m₀, h .m = {Sum.inr m₀} ∧ S.rel₁ .country w₀ m₀ ∧ S.rel₁ .monarchy w₀ m₀ := by
  rw [monarchyM', Formula.realize_conj, realize_countryC_iff S h hw]
  simp only [pred₁, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Scenario.model, Model.intensional_apply₁, Scenario.rel, Matrix.cons_val_zero,
    hw, world_inj]
  constructor
  · rintro ⟨⟨e, hm, he⟩, w, rfl, -, H⟩
    obtain ⟨e', he', he''⟩ := H _ (by rw [hm]; exact Set.mem_singleton _)
    cases Sum.inr.inj he'
    exact ⟨e, hm, he, he''⟩
  · rintro ⟨e, hm, he, he'⟩
    exact ⟨⟨e, hm, he⟩, w₀, rfl, ⟨_, by rw [hm]; exact Set.mem_singleton _⟩,
      fun a ha => ⟨e, by rw [hm] at ha; exact ha, he'⟩⟩

theorem realize_sigmaM_countryC (hw : h .w = world w₀) :
    (Term.sigma .m countryC).realize S.model h =
      {a | ∃ e, a = Sum.inr e ∧ S.rel₁ .country w₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    obtain ⟨e, hm, he⟩ := (realize_countryC_iff S g' (by rw [hg (by decide), hw])).1 hr
    rw [hm] at ha
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨Function.update h .m {Sum.inr e}, fun y hy => Function.update_of_ne hy.2 _ _, by simp,
      (realize_countryC_iff S _ (by rw [Function.update_of_ne (by decide), hw])).2
        ⟨e, Function.update_self .., he⟩⟩

theorem realize_sigmaM_monarchyM' (hw : h .w = world w₀) :
    (Term.sigma .m monarchyM').realize S.model h =
      {a | ∃ e, a = Sum.inr e ∧ S.rel₁ .country w₀ e ∧ S.rel₁ .monarchy w₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    obtain ⟨e, hm, he⟩ := (realize_monarchyM'_iff S g' (by rw [hg (by decide), hw])).1 hr
    rw [hm] at ha
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨Function.update h .m {Sum.inr e}, fun y hy => Function.update_of_ne hy.2 _ _, by simp,
      (realize_monarchyM'_iff S _ (by rw [Function.update_of_ne (by decide), hw])).2
        ⟨e, Function.update_self .., he⟩⟩

/-- (150a) is felicitous at `w₀` iff, granted its first sentence, every country that is a
monarchy has exactly one monarch: the label incorporated into the subordinate quantifier's
restriction satisfies the presupposition of its nuclear scope. -/
theorem felicitous_discourse150a_iff (hw : h .w = world w₀) :
    discourse150a.expandSelf.Felicitous S.model h ↔
      ((∀ e, S.rel₁ .country w₀ e → S.rel₁ .monarchy w₀ e) →
        ∀ m₀, S.rel₁ .country w₀ m₀ ∧ S.rel₁ .monarchy w₀ m₀ →
          ∃! e, S.rel₂ .monarchOf w₀ e m₀) := by
  rw [expandSelf_discourse150a]
  simp only [Formula.felicitous_conj, Formula.felicitous_subset, Formula.felicitous_atom,
    Formula.felicitous_labelDef, Formula.realize_labelDef, Formula.realize_subset,
    Term.felicitous_var, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.felicitous_sigma_of_forall _ _ (felicitous_countryC S),
    Term.felicitous_sigma_of_forall _ _ (felicitous_monarchyM' S), implies_true, and_true,
    true_and, realize_sigmaM_countryC S h hw, realize_sigmaM_monarchyM' S h hw, Set.subset_def,
    Set.mem_ofPred_eq,
    felicitous_sigmaM_cherishBody'_iff S h hw (by decide) (felicitous_monarchyM' S)
      (fun g hg => realize_monarchyM'_iff S g hg)]
  constructor
  · exact fun H hc => H fun a ⟨e, he, hc'⟩ => ⟨e, he, hc', hc e hc'⟩
  · intro H hc e he
    refine H (fun e' hc' => ?_) e he
    obtain ⟨e'', he'', -, hm⟩ := hc _ ⟨e', rfl, hc'⟩
    cases Sum.inr.inj he''
    exact hm

end AbneyKeshet2025
