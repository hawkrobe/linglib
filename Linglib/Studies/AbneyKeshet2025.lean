import Linglib.Logic.PIP.Basic
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
(`IFA`). Summation, paycheck
and strong donkey pronouns, quantificational and modal subordination, anaphora out of
negation, Partee's bathroom disjunction and presupposition satisfaction across subordination
then reduce to scope extension of indefinites, repetition of subformulas through labels, and
standard presupposition projection.

This file defines the fragment's typed metalanguage over PIP, its semantic operations,
lexicon and rules of interpretation as a typed tree, derives the paper's worked trees, and
proves the truth and felicity conditions of the applications on scenario models at a world
of evaluation `w₀`. Variables of the formal system range over all pluralities, so where the
paper reads a summation variable as a world that is a hypothesis on the assignment; for
negation as summation over worlds, `w ∉ Σw(…)`, the two readings come apart
(`not_sat_shop138`).

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
* `mem_sigma_indefOwned` — a summation over a description with an external variable takes
  its value from that variable: paycheck pronouns.
* `fel_shop139_iff` — "He doesn't own a car. It is in the shop." is felicitous only where
  he owns a car, that is where the first sentence is false; `not_sat_shop138` — the
  double-negation translation is false in every model with a second atom.
* `fel_bathroom143_iff` — the bathroom disjunction is felicitous iff a bathroom here, if
  any, is unique.
* `sat_wolfDiscourse_iff` — modal subordination: the second modal quantifies over the
  accessible worlds where a wolf enters.
* `fel_everyMonarchy_iff`, `fel_discourse150a_iff` — a presupposition in the nuclear
  scope is satisfied pointwise by the restriction, within a sentence and across
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

/-- Logical constants: the set relations of quantifiers and modals, membership, the
cardinality predicates, and accessibility. -/
inductive Logical
  | every | most | some | elem | might | must | sg | pl | fem | acc
  deriving DecidableEq

/-- Nonlogical constants: the word senses of the paper's examples. -/
inductive Lex
  | red | dog | barkEvt | hasAgent | hasPatient | hasGoal | chaseEvt | cat | farmer | donkey
  | ownEvt | girl | paper | writeEvt | barks | loud | diorama | made | student | umbrella
  | brought | useEvt | wolf | enters | tim | eats | car | owns | inShop | bathroom | here
  | funnyPlace | country | monarchy | monarchOf | cherish
  deriving DecidableEq

/-- Predicate symbols. -/
inductive Const
  | log (l : Logical)
  | lex (c : Lex)
  deriving DecidableEq

/-- Terms of the fragment. -/
abbrev Tm := Term Var Lab Const

/-- Formulas of the fragment. -/
abbrev Fm := Formula Var Lab Const

/-- A one-place lexical predicate with its world argument. -/
def pred₁ (c : Lex) (x : Tm) : Fm := .atom (.lex c) ![.var .w, x]

/-- A two-place lexical predicate with its world argument. -/
def pred₂ (c : Lex) (x y : Tm) : Fm := .atom (.lex c) ![.var .w, x, y]

/-- A restricted variable: `[x] = x ∧ P(x)`, the common denotation of the indefinite
article, tense and the trace of a determiner (50). -/
def restricted (v : Var) (P : Tm → Fm) : Fm := .conj (.eq (.bvar v) (.var v)) (P (.var v))

/-- `Σyφ | SG(Σyφ)`: a singular summation pronoun (97). -/
def sgPronoun (y : Var) (φ : Fm) : Tm := .presup (.sigma y φ) (.atom (.log .sg) ![.sigma y φ])

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

/-- Intensional functional application (82): the body is stored in the label `X` and the
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

/-- Summation with a label: `ΣxX where X ≡ φ`, the definition attached to the use. -/
def SA (v : Var) (Z : Lab) (φ : Fm) : Tm := .sigma v (.conj (.label Z) (.labelDef Z φ))

/-! ### The lexicon -/

/-- Terminals: lexical predicates, thematic roles, determiners, and the defined constants
(88) with their indices and labels. -/
inductive Word
  | pred (c : Lex)
  | role (c : Lex)
  | quant (l : Logical)
  | a (v : Var)
  | tense (v : Var)
  | dTrace (v : Var)
  | dpTrace (v : Var)
  | core (v : Var)
  | ldpTrace (Z : Lab)
  | she
  | it
  | pron (l : Logical)
  | not (Z : Lab)
  | might (Z : Lab)
  | must (Z : Lab)
  | base

/-- The semantic type of a terminal. -/
def Word.ty : Word → Ty
  | .pred _ => .fn .e .t
  | .role _ => .fn .e (.fn .e .t)
  | .quant _ => .fn .e (.fn .e .t)
  | .a _ => .fn (.fn .e .t) .t
  | .tense _ => .fn (.fn .e .t) .t
  | .dTrace _ => .fn (.fn .e .t) .t
  | .dpTrace _ => .e
  | .core _ => .e
  | .ldpTrace _ => .t
  | .she => .fn .e .e
  | .it => .fn .e .e
  | .pron _ => .fn .e .e
  | .not _ => .fn .s .t
  | .might _ => .fn .s (.fn .s .t)
  | .must _ => .fn .s (.fn .s .t)
  | .base => .s

/-- The meaning of a terminal (87)–(88): a thematic role `λxλe(HAS-ROLE(e, x))`, the
restricted variables `A_x`, `T_x`, `D-T_x`, the simple variables `DP-T_x` and `E_x`, the
label of a labeled trace, pronouns `λz(z|Q(z))`, negation `λψ(w ∉ ψ)`, the modals as
relations to the modal base, and the base `β_w = Σu acc(w, u)`. -/
def Word.sem : (α : Word) → Sem α.ty
  | .pred c => fun a => pred₁ c a
  | .role c => fun a e => pred₂ c e a
  | .quant l => fun a b => .atom (.log l) ![a, b]
  | .a v => restricted v
  | .tense v => restricted v
  | .dTrace v => restricted v
  | .dpTrace v => .var v
  | .core v => .var v
  | .ldpTrace Z => .label Z
  | .she => fun z => .presup z (.conj (.atom (.log .fem) ![z]) (.atom (.log .sg) ![z]))
  | .it => fun z => .presup z (.atom (.log .sg) ![z])
  | .pron l => fun z => .presup z (.atom (.log l) ![z])
  | .not _ => fun ψ => .neg (.atom (.log .elem) ![.var .w, ψ])
  | .might _ => fun β ψ => .atom (.log .some) ![β, ψ]
  | .must _ => fun β ψ => .atom (.log .every) ![β, ψ]
  | .base => .sigma .u (.atom (.log .acc) ![.var .w, .var .u])

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
theorem value_aRedDogBarked (M : Model Const (Atom W E)) (g : Var → Set (Atom W E)) :
    (interp [] aRedDogBarked).value M g = form92.value M g := by
  rw [interp_aRedDogBarked]
  refine Prod.ext (propext ?_) (Prod.ext (propext ?_) rfl)
  · simp only [Formula.value, Formula.sat_conj, Formula.sat_atom, Formula.sat_eq, restricted,
      pred₁, pred₂, form92, vecCons_map, vecEmpty_map, Term.val_var, Term.val_bvar, and_assoc,
      true_and]
  · simp only [Formula.value, Formula.fel_conj, Formula.fel_atom, Formula.fel_eq, restricted,
      pred₁, pred₂, form92, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      IsEmpty.forall_iff, Term.fel_var, Term.fel_bvar, and_self, implies_true]

/-- `DOG([d])` and `DOG(d)` are truth-equivalent. -/
theorem sat_bvar_iff_var (M : Model Const (Atom W E)) (g : Var → Set (Atom W E)) (c : Lex)
    (v : Var) : (pred₁ c (.bvar v)).sat M g ↔ (pred₁ c (.var v)).sat M g := by
  simp only [pred₁, Formula.sat_atom, vecCons_map, vecEmpty_map, Term.val_var, Term.val_bvar]

/-- `DOG([d])` and `DOG(d)` are not intersubstitutable: their local variables differ. -/
theorem value_bvar_ne_var (M : Model Const (Atom W E)) (g : Var → Set (Atom W E)) (c : Lex)
    (v : Var) : (pred₁ c (.bvar v)).value M g ≠ (pred₁ c (.var v)).value M g :=
  fun h => List.cons_ne_nil v [] (congrArg (fun p => p.2.2.1) h)

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
    pred₂, Formula.expand, List.foldr_nil, Formula.subst, Term.subst, Term.bracket, vecCons_map,
    vecEmpty_map, reduceCtorEq, reduceIte]

/-- (66): "every girl wrote a paper", quantifier raising leaving a restricted-variable
trace in the restriction and a labeled trace in the scope. -/
def everyGirlWroteAPaper : Tree .t :=
  .fa (.fa (.lex (.quant .every)) (.sa .g .G (.fa (.lex (.dTrace .g)) (.lex (.pred .girl)))))
    (.sa .g .P (.fx (.fx (.lex (.role .hasAgent)) .g (.lex (.ldpTrace .G))) .u
      (.fa (.lex (.tense .u)) (.pm (.lex (.pred .writeEvt))
        (.fx (.lex (.role .hasPatient)) .p (.fa (.lex (.a .p)) (.lex (.pred .paper))))))))

/-- (79): `EVERY(ΣgG, ΣgP) where G ≡ GIRL([g]), P ≡ (G ∧ PAPER([p]) ∧ WROTE([u], g, p))`. -/
theorem interp_everyGirlWroteAPaper :
    interp [] everyGirlWroteAPaper =
      .atom (.log .every) ![SA .g .G (restricted .g (pred₁ .girl)),
        SA .g .P (.conj (.conj (pred₂ .hasAgent (.var .u) (.var .g)) (.label .G))
          (restricted .u fun e => .conj (pred₁ .writeEvt e)
            (.conj (pred₂ .hasPatient e (.var .p)) (restricted .p (pred₁ .paper)))))] := rfl

/-- (93): the simple pronoun "she_x". -/
def sheX : Tree .e := .fa (.lex .she) (.lex (.core .x))

/-- (94c): `x | FEM(x) ∧ SG(x)`. -/
theorem interp_sheX :
    interp [] sheX =
      .presup (.var .x) (.conj (.atom (.log .fem) ![.var .x]) (.atom (.log .sg) ![.var .x])) :=
  rfl

/-- (99): the summation pronoun "they^P_p" after (66). -/
def theyP : Tree .e := .fa (.lex (.pron .pl)) (.sa .p .Y (.lex (.ldpTrace .P)))

/-- (100): `(ΣpP) | PL(ΣpP)`, the label `Y` of the pronoun's summation defined as `P`. -/
theorem interp_theyP :
    interp [] theyP =
      .presup (SA .p .Y (.label .P)) (.atom (.log .pl) ![SA .p .Y (.label .P)]) := rfl

/-- (118): the label definitions of "Almost every student brought an umbrella today",
`S ≡ STUDENT([s])`, `B ≡ (S ∧ UMBRELLA([u]) ∧ BROUGHT([b], s, u))`. -/
def defs118 : List (Lab × Fm) :=
  [(.S, restricted .s (pred₁ .student)),
   (.B, .conj (.label .S) (.conj (restricted .u (pred₁ .umbrella))
      (.atom (.lex .brought) ![.var .w, .bvar .b, .var .s, .var .u])))]

/-- (121): "Most of them used it", the subordinate quantifier's restriction a labeled trace
of the preceding sentence abstracted by `PA` (122). -/
def mostOfThemUsedIt : Tree .t :=
  .fa (.fa (.lex (.quant .most))
      (.sa .s' .M (.fa (.lex (.dTrace .s')) (.pa .s (.lex (.ldpTrace .B))))))
    (.sa .s' .U (.fx (.fx (.lex (.role .hasAgent)) .s' (.lex (.ldpTrace .M))) .e
      (.fa (.lex (.tense .e)) (.pm (.lex (.pred .useEvt))
        (.fa (.lex (.role .hasPatient)) (.fa (.lex .it) (.lex (.core .u))))))))

/-- (128): `MOST(Σs′M, Σs′U)` with `M` the definition of `B` under `s ↦ s′` (127) and
`U ≡ M ∧ USED([e], s′, u)`. -/
theorem interp_mostOfThemUsedIt :
    interp defs118 mostOfThemUsedIt =
      .atom (.log .most) ![
        SA .s' .M (restricted .s' fun y => .conj (.conj (.eq (.bvar .s') y) (pred₁ .student y))
          (.conj (restricted .u (pred₁ .umbrella))
            (.atom (.lex .brought) ![.var .w, .bvar .b, y, .var .u]))),
        SA .s' .U (.conj (.conj (pred₂ .hasAgent (.var .e) (.var .s')) (.label .M))
          (restricted .e fun e => .conj (pred₁ .useEvt e)
            (pred₂ .hasPatient e (.presup (.var .u) (.atom (.log .sg) ![.var .u])))))] := by
  simp only [mostOfThemUsedIt, interp, Word.sem, FA, FX, PM, PA, SA, lift, restricted, pred₁,
    pred₂, defs118, Formula.expand, List.foldr_cons, List.foldr_nil, Formula.substLabel,
    Term.substLabel, Formula.subst, Term.subst, Term.bracket, vecCons_map, vecEmpty_map,
    reduceCtorEq, reduceIte]

/-! ### Scenarios -/

/-- A scenario: accessibility between worlds, the proportional relation interpreting
`most`, and the one- and two-place lexical relations at each world. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  most : Set (Atom W E) → Set (Atom W E) → Prop
  rel₁ : Lex → W → E → Prop
  rel₂ : Lex → W → E → E → Prop

/-- The model of a scenario: the logical constants as relations between pluralities, the
lexical constants distributively over nonempty pluralities of entities at a world. -/
def Scenario.model (S : Scenario W E) : Model Const (Atom W E) where
  I c := fun {n} ts => match c, n, ts with
    | .log .every, 2, ts => ts 0 ⊆ ts 1
    | .log .some, 2, ts => (ts 0 ∩ ts 1).Nonempty
    | .log .most, 2, ts => S.most (ts 0) (ts 1)
    | .log .elem, 2, ts => ∃ a, ts 0 = {a} ∧ a ∈ ts 1
    | .log .must, 3, ts => ts 0 ∩ ts 1 ⊆ ts 2
    | .log .might, 3, ts => (ts 0 ∩ ts 1 ∩ ts 2).Nonempty
    | .log .sg, 1, ts => ∃ a, ts 0 = {a}
    | .log .pl, 1, ts => ∃ a b, a ≠ b ∧ a ∈ ts 0 ∧ b ∈ ts 0
    | .log .acc, 2, ts => ∃ w u, ts 0 = world w ∧ ts 1 = world u ∧ S.acc w u
    | .lex c, 2, ts => distr (S.rel₁ c) (ts 0) (ts 1)
    | .lex c, 3, ts => distr₂ (S.rel₂ c) (ts 0) (ts 1) (ts 2)
    | _, _, _ => False

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W} {x₀ : E}

theorem fel_pred₁ (c : Lex) (t : Tm) : (pred₁ c t).fel S.model h ↔ t.fel S.model h := by
  show (∀ i, (![Term.var Var.w, t] i).fel S.model h) ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Term.fel_var, true_and]

theorem fel_pred₂ (c : Lex) (s t : Tm) :
    (pred₂ c s t).fel S.model h ↔ s.fel S.model h ∧ t.fel S.model h := by
  show (∀ i, (![Term.var Var.w, s, t] i).fel S.model h) ↔ _
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff,
    Term.fel, true_and, and_true]

/-- `w ∈ τ` at the world `w₀`. -/
theorem sat_elem (hw : h .w = world w₀) (t : Tm) :
    (Formula.atom (.log .elem) ![.var .w, t]).sat S.model h ↔ t.mem S.model h (Sum.inl w₀) := by
  show (∃ a, h .w = {a} ∧ t.mem S.model h a) ↔ _
  rw [hw]
  simp only [world, Set.singleton_eq_singleton_iff, exists_eq_left']

theorem sat_sg (t : Tm) :
    (Formula.atom (.log .sg) ![t]).sat S.model h ↔ ∃ a, {b | t.mem S.model h b} = {a} := Iff.rfl

theorem fel_sgPronoun (y : Var) (φ : Fm) :
    (sgPronoun y φ).fel S.model h ↔
      (Term.sigma y φ).fel S.model h ∧
        (Formula.atom (.log .sg) ![Term.sigma y φ]).sat S.model h := by
  show (Term.sigma y φ).fel S.model h ∧ (∀ i, (![Term.sigma y φ] i).fel S.model h) ∧ _ ↔ _
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero]
  exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, a, c⟩⟩

/-- Membership in a summation over `w` whose body holds only at worlds. -/
theorem mem_sigmaW {φ : Fm}
    (hφ : ∀ (h : Var → Set (Atom W E)) d, closeOver (φ.locals.filter (· ≠ Var.w))
      (Function.update h .w d) (φ.sat S.model ·) → ∃ w', d = world w') (a : Atom W E) :
    (Term.sigma .w φ).mem S.model h a ↔ ∃ w', a = Sum.inl w' ∧
      closeOver (φ.locals.filter (· ≠ Var.w)) (Function.update h .w (world w'))
        (φ.sat S.model ·) := by
  constructor
  · rintro ⟨d, hd, ha⟩
    obtain ⟨w', rfl⟩ := hφ h d hd
    exact ⟨w', ha, hd⟩
  · rintro ⟨w', rfl, hd⟩
    exact ⟨world w', hd, rfl⟩

/-! ### Paycheck pronouns and negation: an indefinite related to an external variable -/

/-- `c₁_w([y]) ∧ c₂_w(x, y)`: an indefinite `[y]` of kind `c₁` standing in the relation `c₂`
to the external variable `x` — `D ≡ DIORAMA([d]) ∧ MADE(x, d)` (112), `O ≡ CAR([c]) ∧
OWNS(x, c)` (137). -/
def indefOwned (c₁ c₂ : Lex) (y : Var) : Fm :=
  .conj (pred₁ c₁ (.bvar y)) (pred₂ c₂ (.var .x) (.var y))

variable (c₁ c₂ : Lex) {y : Var}

theorem locals_indefOwned : (indefOwned c₁ c₂ y).locals = [y] := rfl

theorem sat_indefOwned :
    (indefOwned c₁ c₂ y).sat S.model h ↔
      distr (S.rel₁ c₁) (h .w) (h y) ∧ distr₂ (S.rel₂ c₂) (h .w) (h .x) (h y) := Iff.rfl

theorem fel_indefOwned : (indefOwned c₁ c₂ y).fel S.model h :=
  Formula.fel_of_presupFree _ _ _ (of_decide_eq_true rfl)

/-- The summation over the indefinite takes its value from the external variable: the
paycheck pronoun `ΣdD` denotes the dioramas made by whatever `x` is (112). -/
theorem mem_sigma_indefOwned (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀}) (hyw : y ≠ .w)
    (hyx : y ≠ .x) (a : Atom W E) :
    (Term.sigma y (indefOwned c₁ c₂ y)).mem S.model h a ↔
      ∃ e, a = Sum.inr e ∧ S.rel₁ c₁ w₀ e ∧ S.rel₂ c₂ w₀ x₀ e := by
  simp only [Term.mem, locals_indefOwned, List.filter_cons, List.filter_nil, decide_eq_true_eq,
    ne_eq, not_true_eq_false, reduceIte, closeOver, sat_indefOwned, Function.update_self,
    Function.update_of_ne hyw.symm, Function.update_of_ne hyx.symm, hw, hx]
  constructor
  · rintro ⟨d, ⟨⟨w', hw', -, hall⟩, ⟨w'', hw'', -, -, hall₂⟩⟩, ha⟩
    obtain rfl := world_inj.1 hw'
    obtain rfl := world_inj.1 hw''
    obtain ⟨e, rfl, he⟩ := hall a ha
    obtain ⟨e₁, e₂, h₁, h₂, he₂⟩ := hall₂ _ rfl _ ha
    cases Sum.inr.inj h₁
    cases Sum.inr.inj h₂
    exact ⟨e, rfl, he, he₂⟩
  · rintro ⟨e, rfl, h₁, h₂⟩
    exact ⟨{Sum.inr e}, ⟨⟨w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩,
      ⟨w₀, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, fun a ha b hb => ⟨x₀, e, ha, hb, h₂⟩⟩⟩, rfl⟩

/-- The summation over worlds of the indefinite's description: the worlds where `x` has
such a thing. -/
theorem mem_sigmaW_indefOwned (hx : h .x = {Sum.inr x₀}) (hyw : y ≠ .w) (hyx : y ≠ .x)
    (a : Atom W E) :
    (Term.sigma .w (indefOwned c₁ c₂ y)).mem S.model h a ↔
      ∃ w' e, a = Sum.inl w' ∧ S.rel₁ c₁ w' e ∧ S.rel₂ c₂ w' x₀ e := by
  simp only [Term.mem, locals_indefOwned, List.filter_cons, decide_eq_true_eq, if_pos hyw,
    List.filter_nil, closeOver, sat_indefOwned, Function.update_self,
    Function.update_of_ne hyw.symm, Function.update_of_ne hyx.symm,
    Function.update_of_ne (show Var.x ≠ Var.w by decide), hx]
  constructor
  · rintro ⟨d, ⟨X, ⟨w', rfl, ⟨b, hb⟩, hall⟩, ⟨w'', hw'', -, -, hall₂⟩⟩, ha⟩
    obtain rfl := world_inj.1 hw''
    obtain ⟨e, rfl, he⟩ := hall b hb
    obtain ⟨e₁, e₂, h₁, h₂, he₂⟩ := hall₂ _ rfl _ hb
    cases Sum.inr.inj h₁
    cases Sum.inr.inj h₂
    exact ⟨w', e, ha, he, he₂⟩
  · rintro ⟨w', e, rfl, h₁, h₂⟩
    exact ⟨world w', ⟨{Sum.inr e}, ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩,
      ⟨w', rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, fun a ha b hb => ⟨x₀, e, ha, hb, h₂⟩⟩⟩, rfl⟩

theorem fel_sigmaW_indefOwned : (Term.sigma .w (indefOwned c₁ c₂ y)).fel S.model h :=
  Term.fel_sigma_of_forall _ _ fun _ => fel_indefOwned S _ c₁ c₂

theorem fel_sgPronoun_indefOwned_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀})
    (hyw : y ≠ .w) (hyx : y ≠ .x) :
    (sgPronoun y (indefOwned c₁ c₂ y)).fel S.model h ↔
      ∃! e, S.rel₁ c₁ w₀ e ∧ S.rel₂ c₂ w₀ x₀ e := by
  rw [fel_sgPronoun, sat_sg]
  simp only [Term.fel_sigma_of_forall _ _ fun _ => fel_indefOwned S _ c₁ c₂, true_and,
    mem_sigma_indefOwned S h c₁ c₂ hw hx hyw hyx, exists_eq_singleton_iff]

/-- `O ≡ CAR_w([c]) ∧ OWNS_w(x, c)` (137). -/
def ownCar : Fm := indefOwned .car .owns .c

/-- `NOT^O`: `w ∉ ΣwO` (136)–(137), "he doesn't own a car". -/
def notOwn : Fm := .neg (.atom (.log .elem) ![.var .w, .sigma .w (.label .O)])

/-- (139): "He doesn't own a car. #It is in the shop." -/
def shop139 : Fm :=
  .conj (.conj notOwn (pred₁ .inShop (sgPronoun .c (.label .O)))) (.labelDef .O ownCar)

/-- (138b): "It's not like he doesn't own a car. It is just in the shop." -/
def shop138 : Fm :=
  .conj (.conj (.neg (.atom (.log .elem) ![.var .w, .sigma .w notOwn]))
      (pred₁ .inShop (sgPronoun .c (.label .O))))
    (.labelDef .O ownCar)

theorem expandSelf_shop139 :
    shop139.expandSelf =
      .conj (.conj (.neg (.atom (.log .elem) ![.var .w, .sigma .w ownCar]))
          (pred₁ .inShop (sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := by
  rw [Formula.expandSelf, show shop139.defs = [(.O, ownCar)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, shop139, notOwn, sgPronoun, pred₁,
    ownCar, indefOwned, pred₂, Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map,
    reduceIte]

theorem expandSelf_shop138 :
    shop138.expandSelf =
      .conj (.conj (.neg (.atom (.log .elem) ![.var .w,
            .sigma .w (.neg (.atom (.log .elem) ![.var .w, .sigma .w ownCar]))]))
          (pred₁ .inShop (sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := by
  rw [Formula.expandSelf, show shop138.defs = [(.O, ownCar)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, shop138, notOwn, sgPronoun, pred₁,
    ownCar, indefOwned, pred₂, Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map,
    reduceIte]

/-- (139) is felicitous at `w₀` iff he owns a car there — iff its first sentence is false. -/
theorem fel_shop139_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀}) :
    shop139.expandSelf.fel S.model h ↔ ∃ c, S.rel₁ .car w₀ c ∧ S.rel₂ .owns w₀ x₀ c := by
  rw [expandSelf_shop139]
  show ((∀ i, (![Term.var Var.w, Term.sigma .w ownCar] i).fel S.model h) ∧
      (¬(Formula.atom (.log .elem) ![.var .w, .sigma .w ownCar]).sat S.model h →
        (pred₁ .inShop (sgPronoun .c ownCar)).fel S.model h)) ∧ (_ → True) ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Term.fel_var, ownCar,
    fel_sigmaW_indefOwned, sat_elem S h hw,
    mem_sigmaW_indefOwned S h _ _ hx (show Var.c ≠ Var.w by decide) (show Var.c ≠ Var.x by decide),
    Sum.inl.injEq, exists_and_left, exists_eq_left', fel_pred₁,
    fel_sgPronoun_indefOwned_iff S h _ _ hw hx (show Var.c ≠ Var.w by decide)
      (show Var.c ≠ Var.x by decide),
    implies_true, true_and, and_true]
  exact ⟨fun H => not_not.1 fun hn => hn (H hn).exists, fun H hn => absurd H hn⟩

/-- The double negation of (138b) sums `w` over all pluralities, of which every non-world
fails `w ∈ ΣwO`; so `w ∉ Σw(w ∉ ΣwO)` is false at any world once the model has a second
atom. -/
theorem not_sat_shop138 (hw : h .w = world w₀) (a₁ : Atom W E) (ha : a₁ ≠ Sum.inl w₀) :
    ¬ shop138.expandSelf.sat S.model h := by
  rw [expandSelf_shop138]
  rintro ⟨⟨hneg, -⟩, -⟩
  refine hneg ((sat_elem S h hw _).2 ⟨{Sum.inl w₀, a₁}, ?_, Set.mem_insert _ _⟩)
  rintro ⟨a, hd, -⟩
  have hd' : ({Sum.inl w₀, a₁} : Set (Atom W E)) = {a} := hd
  exact ha ((Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert_of_mem _ (Set.mem_singleton a₁))).trans
    (Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert _ _)).symm)

/-! ### Negation and disjunction -/

/-- `X ≡ SG(b) ∧ BATHROOM_w([b]) ∧ HERE_w(b)` (143). -/
def bathroomX : Fm :=
  .conj (.atom (.log .sg) ![.var .b]) (.conj (pred₁ .bathroom (.bvar .b)) (pred₁ .here (.var .b)))

/-- (143): "Either there is no bathroom here or it's in a funny place",
`(w ∉ ΣwX ∨ FUNNY-PLACE_w(ΣbX | SG(ΣbX))) ∧ X ≡ …`. -/
def bathroom143 : Fm :=
  .conj (.disj (.neg (.atom (.log .elem) ![.var .w, .sigma .w (.label .X)]))
      (pred₁ .funnyPlace (sgPronoun .b (.label .X))))
    (.labelDef .X bathroomX)

theorem locals_bathroomX : bathroomX.locals = [.b] := rfl

theorem sat_bathroomX :
    bathroomX.sat S.model h ↔
      (∃ a, h .b = {a}) ∧ distr (S.rel₁ .bathroom) (h .w) (h .b) ∧
        distr (S.rel₁ .here) (h .w) (h .b) := Iff.rfl

theorem fel_bathroomX : bathroomX.fel S.model h := Formula.fel_of_presupFree _ _ _ (by decide)

theorem sat_bathroomX_iff (hw : h .w = world w₀) (d : Set (Atom W E)) :
    bathroomX.sat S.model (Function.update h .b d) ↔
      ∃ e, d = {Sum.inr e} ∧ S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e := by
  rw [sat_bathroomX, Function.update_self, Function.update_of_ne (show Var.w ≠ Var.b by decide),
    hw]
  constructor
  · rintro ⟨⟨a, rfl⟩, ⟨w', hw', -, h₁⟩, ⟨w'', hw'', -, h₂⟩⟩
    obtain rfl := world_inj.1 hw'
    obtain rfl := world_inj.1 hw''
    obtain ⟨e, rfl, he⟩ := h₁ a rfl
    obtain ⟨e', he', he''⟩ := h₂ _ rfl
    cases Sum.inr.inj he'
    exact ⟨e, rfl, he, he''⟩
  · rintro ⟨e, rfl, h₁, h₂⟩
    exact ⟨⟨_, rfl⟩, ⟨w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩,
      ⟨w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₂⟩⟩⟩

theorem mem_sigmaB_bathroomX (hw : h .w = world w₀) (a : Atom W E) :
    (Term.sigma .b bathroomX).mem S.model h a ↔
      ∃ e, a = Sum.inr e ∧ S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e := by
  simp only [Term.mem, locals_bathroomX, List.filter_cons, List.filter_nil, decide_eq_true_eq,
    ne_eq, not_true_eq_false, reduceIte, closeOver, sat_bathroomX_iff S h hw]
  constructor
  · rintro ⟨d, ⟨e, rfl, he⟩, ha⟩
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨_, ⟨e, rfl, he⟩, rfl⟩

theorem mem_sigmaW_bathroomX (a : Atom W E) :
    (Term.sigma .w bathroomX).mem S.model h a ↔
      ∃ w' e, a = Sum.inl w' ∧ S.rel₁ .bathroom w' e ∧ S.rel₁ .here w' e := by
  simp only [Term.mem, locals_bathroomX, List.filter_cons, List.filter_nil, decide_eq_true_eq,
    ne_eq, reduceCtorEq, not_false_eq_true, reduceIte, closeOver, sat_bathroomX,
    Function.update_self, Function.update_of_ne (show Var.w ≠ Var.b by decide)]
  constructor
  · rintro ⟨d, ⟨X, ⟨a', rfl⟩, ⟨w', rfl, -, h₁⟩, ⟨w'', hw'', -, h₂⟩⟩, ha⟩
    obtain rfl := world_inj.1 hw''
    obtain ⟨e, rfl, he⟩ := h₁ a' rfl
    obtain ⟨e', he', he''⟩ := h₂ _ rfl
    cases Sum.inr.inj he'
    exact ⟨w', e, ha, he, he''⟩
  · rintro ⟨w', e, rfl, h₁, h₂⟩
    exact ⟨world w', ⟨{Sum.inr e}, ⟨_, rfl⟩, ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩,
      ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₂⟩⟩⟩, rfl⟩

theorem expandSelf_bathroom143 :
    bathroom143.expandSelf =
      .conj (.disj (.neg (.atom (.log .elem) ![.var .w, .sigma .w bathroomX]))
          (pred₁ .funnyPlace (sgPronoun .b bathroomX)))
        (.labelDef .X bathroomX) := by
  rw [Formula.expandSelf, show bathroom143.defs = [(.X, bathroomX)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, bathroom143, Formula.disj,
    sgPronoun, pred₁, bathroomX, Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map,
    reduceIte]

/-- (145): the bathroom disjunction is felicitous at `w₀` iff, if there is a bathroom here,
there is exactly one. -/
theorem fel_bathroom143_iff (hw : h .w = world w₀) :
    bathroom143.expandSelf.fel S.model h ↔
      ((∃ e, S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e) →
        ∃! e, S.rel₁ .bathroom w₀ e ∧ S.rel₁ .here w₀ e) := by
  rw [expandSelf_bathroom143]
  show ((Formula.neg _).disj _).fel S.model h ∧ (_ → True) ↔ _
  rw [Formula.fel_disj, fel_pred₁, fel_sgPronoun, sat_sg]
  show ((∀ i, (![Term.var Var.w, Term.sigma .w bathroomX] i).fel S.model h) ∧
      (¬¬(Formula.atom (.log .elem) ![.var .w, .sigma .w bathroomX]).sat S.model h → _)) ∧ _ ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Term.fel_var,
    Term.fel_sigma_of_forall _ _ (fel_bathroomX S), not_not, sat_elem S h hw,
    mem_sigmaW_bathroomX, Sum.inl.injEq, exists_and_left, exists_eq_left',
    mem_sigmaB_bathroomX S h hw, exists_eq_singleton_iff, implies_true, true_and, and_true]

/-! ### Modal subordination -/

/-- `β_w = Σu acc(w, u)`: the modal base. -/
def base : Tm := .sigma .u (.atom (.log .acc) ![.var .w, .var .u])

/-- `W ≡ WOLF_w([x]) ∧ ENTERS_w(x)` (133a). -/
def wolfW : Fm := .conj (pred₁ .wolf (.bvar .x)) (pred₁ .enters (.var .x))

/-- `E ≡ W ∧ TIM_w([t]) ∧ EATS_w(x, t)` (133b). -/
def wolfE : Fm :=
  .conj (.label .W) (.conj (pred₁ .tim (.bvar .t)) (pred₂ .eats (.var .x) (.var .t)))

/-- (133): "A wolf might enter. It would eat Tasty Tim first.", `MIGHT(β_w, ΣwW) ∧
MUST(β_w, ΣwW, ΣwE)` with the second modal's restriction the first's nuclear scope. -/
def wolfDiscourse : Fm :=
  .conj (.conj (.atom (.log .some) ![base, .sigma .w (.label .W)])
      (.atom (.log .must) ![base, .sigma .w (.label .W), .sigma .w (.label .E)]))
    (.conj (.labelDef .W wolfW) (.labelDef .E wolfE))

/-- `E` with `W` expanded. -/
def wolfE' : Fm := .conj wolfW (.conj (pred₁ .tim (.bvar .t)) (pred₂ .eats (.var .x) (.var .t)))

theorem expandSelf_wolfDiscourse :
    wolfDiscourse.expandSelf =
      .conj (.conj (.atom (.log .some) ![base, .sigma .w wolfW])
          (.atom (.log .must) ![base, .sigma .w wolfW, .sigma .w wolfE']))
        (.conj (.labelDef .W wolfW) (.labelDef .E wolfE')) := by
  rw [Formula.expandSelf, show wolfDiscourse.defs = [(.W, wolfW), (.E, wolfE)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, wolfDiscourse, wolfW, wolfE, wolfE',
    base, pred₁, pred₂, Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map,
    reduceCtorEq, reduceIte]

theorem mem_base (a : Atom W E) :
    base.mem S.model h a ↔ ∃ w u, h .w = world w ∧ a = Sum.inl u ∧ S.acc w u := by
  simp only [base, Term.mem, show (Formula.atom (.log .acc) ![Term.var Var.w, Term.var Var.u]
      : Fm).locals.filter (· ≠ Var.u) = [] from rfl, closeOver]
  show (∃ d, (∃ w u, Function.update h .u d .w = world w ∧ Function.update h .u d .u = world u ∧
    S.acc w u) ∧ a ∈ d) ↔ _
  simp only [Function.update_self, Function.update_of_ne (show Var.w ≠ Var.u by decide)]
  constructor
  · rintro ⟨d, ⟨w, u, hw, rfl, hacc⟩, ha⟩
    exact ⟨w, u, hw, ha, hacc⟩
  · rintro ⟨w, u, hw, rfl, hacc⟩
    exact ⟨world u, ⟨w, u, hw, rfl, hacc⟩, rfl⟩

theorem locals_wolfW : wolfW.locals = [.x] := rfl

theorem locals_wolfE' : wolfE'.locals = [.x, .t] := rfl

theorem sat_wolfW :
    wolfW.sat S.model h ↔
      distr (S.rel₁ .wolf) (h .w) (h .x) ∧ distr (S.rel₁ .enters) (h .w) (h .x) :=
  Iff.rfl

theorem sat_wolfE' :
    wolfE'.sat S.model h ↔
      (distr (S.rel₁ .wolf) (h .w) (h .x) ∧ distr (S.rel₁ .enters) (h .w) (h .x)) ∧
        distr (S.rel₁ .tim) (h .w) (h .t) ∧ distr₂ (S.rel₂ .eats) (h .w) (h .x) (h .t) := Iff.rfl

theorem mem_sigmaW_wolfW (a : Atom W E) :
    (Term.sigma .w wolfW).mem S.model h a ↔
      ∃ w' e, a = Sum.inl w' ∧ S.rel₁ .wolf w' e ∧ S.rel₁ .enters w' e := by
  simp only [Term.mem, locals_wolfW, List.filter_cons, List.filter_nil, decide_eq_true_eq, ne_eq,
    reduceCtorEq, not_false_eq_true, reduceIte, closeOver, sat_wolfW, Function.update_self,
    Function.update_of_ne (show Var.w ≠ Var.x by decide)]
  constructor
  · rintro ⟨d, ⟨X, ⟨w', rfl, ⟨b, hb⟩, h₁⟩, ⟨w'', hw'', -, h₂⟩⟩, ha⟩
    obtain rfl := world_inj.1 hw''
    obtain ⟨e, rfl, he⟩ := h₁ b hb
    obtain ⟨e', he', he''⟩ := h₂ _ hb
    cases Sum.inr.inj he'
    exact ⟨w', e, ha, he, he''⟩
  · rintro ⟨w', e, rfl, h₁, h₂⟩
    exact ⟨world w', ⟨{Sum.inr e}, ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩,
      ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₂⟩⟩⟩, rfl⟩

theorem mem_sigmaW_wolfE' (a : Atom W E) :
    (Term.sigma .w wolfE').mem S.model h a ↔
      ∃ w' e t, a = Sum.inl w' ∧ (S.rel₁ .wolf w' e ∧ S.rel₁ .enters w' e) ∧
        S.rel₁ .tim w' t ∧ S.rel₂ .eats w' e t := by
  simp only [Term.mem, locals_wolfE', List.filter_cons, List.filter_nil, decide_eq_true_eq, ne_eq,
    reduceCtorEq, not_false_eq_true, reduceIte, closeOver, sat_wolfE', Function.update_self,
    Function.update_of_ne (show Var.w ≠ Var.x by decide),
    Function.update_of_ne (show Var.w ≠ Var.t by decide),
    Function.update_of_ne (show Var.x ≠ Var.t by decide)]
  constructor
  · rintro ⟨d, ⟨X, T, ⟨⟨w', rfl, ⟨b, hb⟩, h₁⟩, ⟨w₁, hw₁, -, h₂⟩⟩, ⟨w₂, hw₂, ⟨b', hb'⟩, h₃⟩,
      ⟨w₃, hw₃, -, -, h₄⟩⟩, ha⟩
    obtain rfl := world_inj.1 hw₁
    obtain rfl := world_inj.1 hw₂
    obtain rfl := world_inj.1 hw₃
    obtain ⟨e, rfl, he⟩ := h₁ b hb
    obtain ⟨e', he', he''⟩ := h₂ _ hb
    cases Sum.inr.inj he'
    obtain ⟨t, rfl, ht⟩ := h₃ b' hb'
    obtain ⟨e₁, t₁, h₁', h₂', het⟩ := h₄ _ hb _ hb'
    cases Sum.inr.inj h₁'
    cases Sum.inr.inj h₂'
    exact ⟨w', e, t, ha, ⟨he, he''⟩, ht, het⟩
  · rintro ⟨w', e, t, rfl, ⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨world w', ⟨{Sum.inr e}, {Sum.inr t},
      ⟨⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₁⟩⟩, ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, h₂⟩⟩⟩,
      ⟨w', rfl, ⟨_, rfl⟩, fun a ha => ⟨t, ha, h₃⟩⟩,
      ⟨w', rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, fun a ha b hb => ⟨e, t, ha, hb, h₄⟩⟩⟩, rfl⟩

/-- (133) at `w₀`: some accessible world has a wolf entering, and in every accessible
world where a wolf enters, a wolf that enters eats Tim. -/
theorem sat_wolfDiscourse_iff (hw : h .w = world w₀) :
    wolfDiscourse.expandSelf.sat S.model h ↔
      (∃ u e, S.acc w₀ u ∧ S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) ∧
        ∀ u, S.acc w₀ u → (∃ e, S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) →
          ∃ e t, (S.rel₁ .wolf u e ∧ S.rel₁ .enters u e) ∧ S.rel₁ .tim u t ∧
            S.rel₂ .eats u e t := by
  rw [expandSelf_wolfDiscourse]
  show (({a | base.mem S.model h a} ∩ {a | (Term.sigma .w wolfW).mem S.model h a}).Nonempty ∧
      {a | base.mem S.model h a} ∩ {a | (Term.sigma .w wolfW).mem S.model h a} ⊆
        {a | (Term.sigma .w wolfE').mem S.model h a}) ∧ (True ∧ True) ↔ _
  simp only [Set.Nonempty, Set.subset_def, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_base,
    mem_sigmaW_wolfW, mem_sigmaW_wolfE', hw, world_inj, and_true]
  constructor
  · rintro ⟨⟨_, ⟨_, u, rfl, rfl, hacc⟩, w', e, ⟨⟩, he⟩, H⟩
    refine ⟨⟨u, e, hacc, he⟩, fun u hu ⟨e, he⟩ => ?_⟩
    obtain ⟨w', e', t, ⟨⟩, het⟩ := H _ ⟨⟨_, u, rfl, rfl, hu⟩, u, e, rfl, he⟩
    exact ⟨e', t, het⟩
  · rintro ⟨⟨u, e, hacc, he⟩, H⟩
    refine ⟨⟨_, ⟨_, u, rfl, rfl, hacc⟩, u, e, rfl, he⟩, ?_⟩
    rintro _ ⟨⟨_, u, rfl, rfl, hu⟩, w', e, ⟨⟩, he⟩
    obtain ⟨e', t, het⟩ := H u hu ⟨e, he⟩
    exact ⟨u, e', t, rfl, het⟩

/-! ### Summation pronouns -/

/-- (102)–(103): "Most dogs bark. They are loud.", `LOUD(ΣdB) ∧ MOST(ΣdD, ΣdB)` with
`D ≡ DOG([d])`, `B ≡ (D ∧ BARKS(d))`. -/
def theyLoud : Fm :=
  .conj (.conj (.atom (.log .most) ![.sigma .d (.label .D), .sigma .d (.label .B)])
      (pred₁ .loud (.sigma .d (.label .B))))
    (.conj (.labelDef .D (pred₁ .dog (.bvar .d)))
      (.labelDef .B (.conj (.label .D) (pred₁ .barks (.var .d)))))

/-- (104): the pronoun denotes the sum of the barking dogs. -/
theorem expandSelf_theyLoud :
    theyLoud.expandSelf =
      .conj (.conj (.atom (.log .most) ![.sigma .d (pred₁ .dog (.bvar .d)),
            .sigma .d (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d)))])
          (pred₁ .loud (.sigma .d (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d))))))
        (.conj (.labelDef .D (pred₁ .dog (.bvar .d)))
          (.labelDef .B (.conj (pred₁ .dog (.bvar .d)) (pred₁ .barks (.var .d))))) := by
  rw [Formula.expandSelf, show theyLoud.defs = [(.D, pred₁ .dog (.bvar .d)),
    (.B, .conj (.label .D) (pred₁ .barks (.var .d)))] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, theyLoud, pred₁, Formula.substLabel,
    Term.substLabel, vecCons_map, vecEmpty_map, reduceCtorEq, reduceIte]

/-! ### Presupposition under quantification -/

/-- `K ≡ MONARCH-OF_w([k], m)`; `ΣkK | SG(ΣkK)` is "its monarch". -/
def monarchK : Fm := pred₂ .monarchOf (.bvar .k) (.var .m)

/-- `X ∧ CHERISH_w(m, ΣkK | SG(ΣkK))`: the nuclear scope of "cherishes its monarch" over the
restriction `X`, the pronoun's presupposition to be satisfied by `X`. -/
def cherishBody (Z : Lab) : Fm :=
  .conj (.label Z) (pred₂ .cherish (.var .m) (sgPronoun .k (.label .K)))

/-- `R ≡ SG(m) ∧ MONARCHY_w([m])`, with the singular restricted variable's `SG` as in (143). -/
def monarchyR : Fm := .conj (.atom (.log .sg) ![.var .m]) (pred₁ .monarchy (.bvar .m))

/-- (146a): "Every monarchy cherishes its monarch", `EVERY(ΣmR, ΣmS)` with `S ≡ R ∧
CHERISH(m, ΣkK | SG(ΣkK))`. -/
def everyMonarchy : Fm :=
  .conj (.atom (.log .every) ![.sigma .m (.label .R), .sigma .m (.label .S)])
    (.conj (.labelDef .R monarchyR) (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody .R))))

/-- `C ≡ SG(m) ∧ COUNTRY_w([m])`. -/
def countryC : Fm := .conj (.atom (.log .sg) ![.var .m]) (pred₁ .country (.bvar .m))

/-- `M ≡ C ∧ MONARCHY_w(m)`: the reference set of "every European country was a monarchy". -/
def monarchyM : Fm := .conj (.label .C) (pred₁ .monarchy (.var .m))

/-- (150a): "Every European country was a monarchy. Most of them cherished their monarchs.",
the subordinate quantifier's restriction the first sentence's reference-set label `M`. -/
def discourse150a : Fm :=
  .conj (.conj (.atom (.log .every) ![.sigma .m (.label .C), .sigma .m (.label .M)])
      (.atom (.log .most) ![.sigma .m (.label .M), .sigma .m (.label .S)]))
    (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM)
      (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody .M)))))

/-- The nuclear scope with the restriction and the pronoun's label expanded. -/
def cherishBody' (ρ : Fm) : Fm :=
  .conj ρ (pred₂ .cherish (.var .m) (sgPronoun .k monarchK))

/-- `M` with `C` expanded. -/
def monarchyM' : Fm := .conj countryC (pred₁ .monarchy (.var .m))

theorem expandSelf_everyMonarchy :
    everyMonarchy.expandSelf =
      .conj (.atom (.log .every) ![.sigma .m monarchyR, .sigma .m (cherishBody' monarchyR)])
        (.conj (.labelDef .R monarchyR)
          (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody' monarchyR)))) := by
  rw [Formula.expandSelf, show everyMonarchy.defs =
    [(.R, monarchyR), (.K, monarchK), (.S, cherishBody .R)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, everyMonarchy, cherishBody,
    cherishBody', monarchyR, monarchK, sgPronoun, pred₁, pred₂, Formula.substLabel,
    Term.substLabel, vecCons_map, vecEmpty_map, reduceCtorEq, reduceIte]

theorem expandSelf_discourse150a :
    discourse150a.expandSelf =
      .conj (.conj (.atom (.log .every) ![.sigma .m countryC, .sigma .m monarchyM'])
          (.atom (.log .most) ![.sigma .m monarchyM', .sigma .m (cherishBody' monarchyM')]))
        (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM')
          (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody' monarchyM'))))) := by
  rw [Formula.expandSelf, show discourse150a.defs =
    [(.C, countryC), (.M, monarchyM), (.K, monarchK), (.S, cherishBody .M)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, discourse150a, cherishBody,
    cherishBody', countryC, monarchyM, monarchyM', monarchK, sgPronoun, pred₁, pred₂,
    Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map, reduceCtorEq, reduceIte]

theorem sat_monarchK :
    monarchK.sat S.model h ↔ distr₂ (S.rel₂ .monarchOf) (h .w) (h .k) (h .m) := Iff.rfl

theorem fel_monarchK : monarchK.fel S.model h := Formula.fel_of_presupFree _ _ _ (by decide)

/-- "Its monarch" at a singular `m₀`: the monarchs of `m₀`. -/
theorem mem_sigmaK_monarchK {m₀ : E} (hw : h .w = world w₀) (hm : h .m = {Sum.inr m₀})
    (a : Atom W E) :
    (Term.sigma .k monarchK).mem S.model h a ↔ ∃ e, a = Sum.inr e ∧ S.rel₂ .monarchOf w₀ e m₀ := by
  simp only [Term.mem, show monarchK.locals.filter (· ≠ Var.k) = [] from rfl, closeOver,
    sat_monarchK, Function.update_self, Function.update_of_ne (show Var.w ≠ Var.k by decide),
    Function.update_of_ne (show Var.m ≠ Var.k by decide), hw, hm]
  constructor
  · rintro ⟨d, ⟨w', hw', -, -, hall⟩, ha⟩
    obtain rfl := world_inj.1 hw'
    obtain ⟨e, e', h₁, h₂, he⟩ := hall a ha _ rfl
    cases Sum.inr.inj h₂
    exact ⟨e, h₁, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨{Sum.inr e}, ⟨w₀, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, fun a ha b hb => ⟨e, m₀, ha, hb, he⟩⟩, rfl⟩

theorem fel_sgPronoun_monarchK_iff {m₀ : E} (hw : h .w = world w₀) (hm : h .m = {Sum.inr m₀}) :
    (sgPronoun .k monarchK).fel S.model h ↔ ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  rw [fel_sgPronoun, sat_sg]
  simp only [Term.fel_sigma_of_forall _ _ (fel_monarchK S), true_and,
    mem_sigmaK_monarchK S h hw hm, exists_eq_singleton_iff]

/-- Felicity of the nuclear-scope summation over a restriction `ρ` true exactly of the
singular `m` satisfying `Q`: the pronoun's presupposition, for each of them. -/
theorem fel_sigmaM_cherishBody'_iff {ρ : Fm} {Q : E → Prop} (hw : h .w = world w₀)
    (hl : ρ.locals.filter (· ≠ Var.m) = []) (hρf : ∀ g, ρ.fel S.model g)
    (hρ : ∀ d, ρ.sat S.model (Function.update h .m d) ↔ ∃ m₀, d = {Sum.inr m₀} ∧ Q m₀) :
    (Term.sigma .m (cherishBody' ρ)).fel S.model h ↔
      ∀ m₀, Q m₀ → ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  simp only [Term.fel, cherishBody', Formula.locals,
    show (pred₂ .cherish (.var .m) (sgPronoun .k monarchK)).locals = [] from rfl, List.append_nil,
    hl, forallOver, Formula.fel_conj, hρf, true_and, hρ, fel_pred₂]
  constructor
  · intro H m₀ hm
    exact (fel_sgPronoun_monarchK_iff S (Function.update h .m {Sum.inr m₀})
      (by rw [Function.update_of_ne (show Var.w ≠ Var.m by decide), hw])
      (Function.update_self ..)).1 (H _ ⟨m₀, rfl, hm⟩)
  · rintro H d ⟨m₀, rfl, hm⟩
    exact (fel_sgPronoun_monarchK_iff S (Function.update h .m {Sum.inr m₀})
      (by rw [Function.update_of_ne (show Var.w ≠ Var.m by decide), hw])
      (Function.update_self ..)).2 (H m₀ hm)

theorem fel_monarchyR : monarchyR.fel S.model h := Formula.fel_of_presupFree _ _ _ (by decide)

theorem sat_monarchyR_iff (hw : h .w = world w₀) (d : Set (Atom W E)) :
    monarchyR.sat S.model (Function.update h .m d) ↔
      ∃ m₀, d = {Sum.inr m₀} ∧ S.rel₁ .monarchy w₀ m₀ := by
  show (∃ a, d = {a}) ∧ distr (S.rel₁ .monarchy) (Function.update h .m d .w) d ↔ _
  rw [Function.update_of_ne (show Var.w ≠ Var.m by decide), hw]
  constructor
  · rintro ⟨⟨a, rfl⟩, w', hw', -, hall⟩
    obtain rfl := world_inj.1 hw'
    obtain ⟨e, rfl, he⟩ := hall a rfl
    exact ⟨e, rfl, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨⟨_, rfl⟩, w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, he⟩⟩

/-- (146a) is felicitous at `w₀` iff every monarchy there has exactly one monarch: the
restriction satisfies the presupposition of the nuclear scope pointwise. -/
theorem fel_everyMonarchy_iff (hw : h .w = world w₀) :
    everyMonarchy.expandSelf.fel S.model h ↔
      ∀ m₀, S.rel₁ .monarchy w₀ m₀ → ∃! e, S.rel₂ .monarchOf w₀ e m₀ := by
  rw [expandSelf_everyMonarchy]
  show (∀ i, (![Term.sigma .m monarchyR, Term.sigma .m (cherishBody' monarchyR)] i).fel S.model h) ∧
    _ ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Formula.fel_conj,
    Formula.fel_labelDef, Formula.sat_labelDef, Term.fel_sigma_of_forall _ _ (fel_monarchyR S),
    implies_true, and_true, true_and,
    fel_sigmaM_cherishBody'_iff S h hw rfl (fel_monarchyR S) (sat_monarchyR_iff S h hw)]

theorem fel_countryC : countryC.fel S.model h := Formula.fel_of_presupFree _ _ _ (by decide)

theorem fel_monarchyM' : monarchyM'.fel S.model h := Formula.fel_of_presupFree _ _ _ (by decide)

theorem sat_countryC_iff (hw : h .w = world w₀) (d : Set (Atom W E)) :
    countryC.sat S.model (Function.update h .m d) ↔
      ∃ m₀, d = {Sum.inr m₀} ∧ S.rel₁ .country w₀ m₀ := by
  show (∃ a, d = {a}) ∧ distr (S.rel₁ .country) (Function.update h .m d .w) d ↔ _
  rw [Function.update_of_ne (show Var.w ≠ Var.m by decide), hw]
  constructor
  · rintro ⟨⟨a, rfl⟩, w', hw', -, hall⟩
    obtain rfl := world_inj.1 hw'
    obtain ⟨e, rfl, he⟩ := hall a rfl
    exact ⟨e, rfl, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨⟨_, rfl⟩, w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, he⟩⟩

theorem sat_monarchyM'_iff (hw : h .w = world w₀) (d : Set (Atom W E)) :
    monarchyM'.sat S.model (Function.update h .m d) ↔
      ∃ m₀, d = {Sum.inr m₀} ∧ S.rel₁ .country w₀ m₀ ∧ S.rel₁ .monarchy w₀ m₀ := by
  show countryC.sat S.model (Function.update h .m d) ∧
    distr (S.rel₁ .monarchy) (Function.update h .m d .w) d ↔ _
  rw [sat_countryC_iff S h hw, Function.update_of_ne (show Var.w ≠ Var.m by decide), hw]
  constructor
  · rintro ⟨⟨e, rfl, he⟩, w', hw', -, hall⟩
    obtain rfl := world_inj.1 hw'
    obtain ⟨e', he', he''⟩ := hall _ rfl
    cases Sum.inr.inj he'
    exact ⟨e, rfl, he, he''⟩
  · rintro ⟨e, rfl, he, he'⟩
    exact ⟨⟨e, rfl, he⟩, w₀, rfl, ⟨_, rfl⟩, fun a ha => ⟨e, ha, he'⟩⟩

theorem mem_sigmaM_countryC (hw : h .w = world w₀) (a : Atom W E) :
    (Term.sigma .m countryC).mem S.model h a ↔ ∃ e, a = Sum.inr e ∧ S.rel₁ .country w₀ e := by
  simp only [Term.mem, show countryC.locals.filter (· ≠ Var.m) = [] from rfl, closeOver,
    sat_countryC_iff S h hw]
  constructor
  · rintro ⟨d, ⟨e, rfl, he⟩, ha⟩
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨_, ⟨e, rfl, he⟩, rfl⟩

theorem mem_sigmaM_monarchyM' (hw : h .w = world w₀) (a : Atom W E) :
    (Term.sigma .m monarchyM').mem S.model h a ↔
      ∃ e, a = Sum.inr e ∧ S.rel₁ .country w₀ e ∧ S.rel₁ .monarchy w₀ e := by
  simp only [Term.mem, show monarchyM'.locals.filter (· ≠ Var.m) = [] from rfl, closeOver,
    sat_monarchyM'_iff S h hw]
  constructor
  · rintro ⟨d, ⟨e, rfl, he⟩, ha⟩
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨_, ⟨e, rfl, he⟩, rfl⟩

/-- (150a) is felicitous at `w₀` iff, granted its first sentence, every country that is a
monarchy has exactly one monarch: the label incorporated into the subordinate quantifier's
restriction satisfies the presupposition of its nuclear scope. -/
theorem fel_discourse150a_iff (hw : h .w = world w₀) :
    discourse150a.expandSelf.fel S.model h ↔
      ((∀ e, S.rel₁ .country w₀ e → S.rel₁ .monarchy w₀ e) →
        ∀ m₀, S.rel₁ .country w₀ m₀ ∧ S.rel₁ .monarchy w₀ m₀ →
          ∃! e, S.rel₂ .monarchOf w₀ e m₀) := by
  rw [expandSelf_discourse150a]
  show ((∀ i, (![Term.sigma .m countryC, Term.sigma .m monarchyM'] i).fel S.model h) ∧
      ({a | (Term.sigma .m countryC).mem S.model h a} ⊆
          {a | (Term.sigma .m monarchyM').mem S.model h a} →
        ∀ i, (![Term.sigma .m monarchyM', Term.sigma .m (cherishBody' monarchyM')] i).fel
          S.model h)) ∧ _ ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Formula.fel_conj,
    Formula.fel_labelDef, Formula.sat_labelDef, Term.fel_sigma_of_forall _ _ (fel_countryC S),
    Term.fel_sigma_of_forall _ _ (fel_monarchyM' S), implies_true, and_true, true_and,
    Set.subset_def, Set.mem_ofPred_eq, mem_sigmaM_countryC S h hw,
    mem_sigmaM_monarchyM' S h hw,
    fel_sigmaM_cherishBody'_iff S h hw rfl (fel_monarchyM' S) (sat_monarchyM'_iff S h hw)]
  constructor
  · exact fun H hc => H fun a ⟨e, he, hc'⟩ => ⟨e, he, hc', hc e hc'⟩
  · intro H hc e he
    refine H (fun e' hc' => ?_) e he
    obtain ⟨e'', he'', -, hm⟩ := hc _ ⟨e', rfl, hc'⟩
    cases Sum.inr.inj he''
    exact hm

end AbneyKeshet2025
