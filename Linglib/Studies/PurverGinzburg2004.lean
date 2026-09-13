import Linglib.Studies.BarwiseCooper1981
import Linglib.Data.Examples.PurverGinzburg2004

/-!
# Purver and Ginzburg (2004): Clarifying Noun Phrase Semantics

This file formalizes [purver-ginzburg-2004]'s use of reprise questions as probes of noun phrase
denotations. Under the Reprise Content Hypothesis a nominal fragment reprise queries a part of
the standard semantic content of the fragment (weak version) or exactly that content (strong
version), and in [ginzburg-cooper-2004]'s grammar what a reprise can query is a member of the
sign's contextual parameters. The paper's semantic representations are therefore signs with a
content and the parameters abstracted to C-PARAMS or stored for existential closure, built by
the Definiteness Principle (74) and (75) (`Sign.word`, `Sign.phrase`, `Sign.Definiteness`).
On the paper's account a quantified noun phrase denotes its witness set, a definite abstracts
that set and an indefinite stores it, and the readings a reprise makes available are the
abstracted parameters: the content itself for definites (`strong_np`), never for indefinites
(`indefinite_no_referent`), and the daughters' parameters for both (`daughters_available`).
The generalized-quantifier alternative (66) makes the same parameters available
(`gq_cparams`) but never its content (`not_strong_gq`), so it holds only the weak hypothesis.
The corpus readings of (25) to (90) are the rows, and every reading the paper judges possible is
available and every reading it marks impossible is not (`rows_predicted`).

The truth conditions follow [barwise-cooper-1981]: a monotone increasing quantifier holds of a
predicate exactly when a witness set is contained in it, which is (24), and the plain witness
representation fails for a monotone decreasing quantifier, since the empty set witnesses it
(`witness_subset_of_empty`); the representation as a pair of a reference set and its
complement (91) is exact for every quantifier living on its restriction (`pair_apply_iff`).

## Implementation notes

The semantic objects a sign can contribute are reified as kinds (`Kind`), since the argument
turns on which kind of object a reprise queries, not on its value; a content is the list of
its components, so that the pair representation (93) can have both members abstracted. The
corpus examples carry their noun phrase type as a feature and the paper's paraphrase readings
with the paper's judgments; marginal readings make no claim. Quantifier scope, anaphora, the
STORE and QUANTS mechanism of §5.3 and §5.4, and the corpus counts of Tables 2 to 6 are not
formalized.

## References

* [purver-ginzburg-2004]
* [ginzburg-cooper-2004]
* [barwise-cooper-1981]
-/

namespace PurverGinzburg2004

open Data.Examples Examples Quantification

/-! ### Signs and the Definiteness Principle (§2.1, §4.5) -/

/-- The kinds of semantic object a nominal sign can contribute or abstract: an individual or
witness set, a property, a determiner relation, a function to witness sets and its situational
argument, a generalized quantifier, and the complement set of a monotone decreasing phrase. -/
inductive Kind
  | individual
  | property
  | relation
  | function
  | situation
  | quantifier
  | complement
  deriving DecidableEq, Repr

/-- A nominal sign: the components of its content, the parameters abstracted to C-PARAMS, and
the parameters stored for existential closure. -/
structure Sign where
  content : List Kind
  cparams : List Kind
  store : List Kind
  deriving DecidableEq, Repr

/-- The Definiteness Principle for a word (74): the content is abstracted to C-PARAMS unless it
is stored. -/
def Sign.word (k : Kind) (definite : Bool) : Sign :=
  if definite then ⟨[k], [k], []⟩ else ⟨[k], [], [k]⟩

/-- The Definiteness Principle for a phrase (75): C-PARAMS is the union of the daughters' with
the content of the mother unless that is stored, and STORE is the union of the daughters' with
the stored content. -/
def Sign.phrase (k : Kind) (definite : Bool) (dtrs : List Sign) : Sign :=
  ⟨[k], (if definite then [k] else []) ++ dtrs.flatMap (·.cparams),
    (if definite then [] else [k]) ++ dtrs.flatMap (·.store)⟩

/-- The content of a sign is a member of C-PARAMS or of STORE. -/
def Sign.Definiteness (s : Sign) : Prop := ∀ k ∈ s.content, k ∈ s.cparams ∨ k ∈ s.store

instance (s : Sign) : Decidable s.Definiteness := by unfold Sign.Definiteness; infer_instance

theorem Sign.word_definiteness (k : Kind) (definite : Bool) :
    (Sign.word k definite).Definiteness := by
  cases definite <;> simp [Sign.word, Sign.Definiteness]

theorem Sign.phrase_definiteness (k : Kind) (definite : Bool) (dtrs : List Sign) :
    (Sign.phrase k definite dtrs).Definiteness := by
  cases definite <;> simp [Sign.phrase, Sign.Definiteness]

/-- The strong Reprise Content Hypothesis for a sign: a reprise, which queries a member of
C-PARAMS, can query the whole content. -/
def Sign.Strong (s : Sign) : Prop := ∀ k ∈ s.content, k ∈ s.cparams

instance (s : Sign) : Decidable s.Strong := by unfold Sign.Strong; infer_instance

/-- A common noun (28): its content is a property, abstracted to C-PARAMS. -/
def cn : Sign := Sign.word .property true

/-- A determiner: its content is a relation between sets, abstracted to C-PARAMS. -/
def det : Sign := Sign.word .relation true

/-- A quantified noun phrase (72), (75): its content is the witness set the determiner relation
picks out of the noun's property, abstracted when definite and stored when indefinite. -/
def np (definite : Bool) : Sign := Sign.phrase .individual definite [det, cn]

/-- An attributive definite (48): the content is a function applied to a situation, and the
function and its argument are the abstracted parameters. -/
def attributive : Sign :=
  ⟨[.individual], [.function, .situation] ++ det.cparams ++ cn.cparams, []⟩

/-- The generalized-quantifier alternative (66): the content is a quantifier, and the abstracted
parameters are its witness set, when definite, and the daughters' contents. -/
def gq (definite : Bool) : Sign :=
  ⟨[.quantifier], (if definite then [.individual] else []) ++ det.cparams ++ cn.cparams, []⟩

/-- A monotone decreasing phrase as a pair of reference and complement set, (92) when
existentially quantified and (93) when referential. -/
def pair (referential : Bool) : Sign :=
  ⟨[.individual, .complement], (if referential then [.individual, .complement] else []) ++
    det.cparams ++ cn.cparams, if referential then [] else [.individual, .complement]⟩

/-- Common nouns hold the strong hypothesis (§3.3). -/
theorem strong_cn : cn.Strong := by decide

/-- Definite noun phrases hold the strong hypothesis (§4.4.2). -/
theorem strong_np : (np true).Strong := by decide

/-- The witness set of an indefinite is stored, not abstracted, so no reprise of an indefinite
queries a referent (§4.2). -/
theorem indefinite_no_referent : Kind.individual ∉ (np false).cparams := by decide

/-- The parameters of the daughters are inherited (73): the sub-constituent readings. -/
theorem daughters_available (definite : Bool) :
    det.cparams ⊆ (np definite).cparams ∧ cn.cparams ⊆ (np definite).cparams := by
  cases definite <;> decide

/-- The generalized-quantifier alternative makes exactly the same parameters available. -/
theorem gq_cparams (definite : Bool) : (gq definite).cparams = (np definite).cparams := by
  cases definite <;> decide

/-- But it never lets a reprise query its content: it holds only the weak hypothesis. -/
theorem not_strong_gq (definite : Bool) : ¬ (gq definite).Strong := by
  cases definite <;> decide

/-- The functional representation of attributive definites holds only the weak hypothesis
(§4.1.3). -/
theorem not_strong_attributive : ¬ attributive.Strong := by decide

/-- The referential pair (93) holds the strong hypothesis. -/
theorem strong_pair : (pair true).Strong := by decide

/-! ### The corpus readings -/

/-- The sign of a row's noun phrase type. -/
def sign? : String → Option Sign
  | "cn" | "bareSingular" => some cn
  | "demonstrative" | "pronoun" | "definite" | "specificIndefinite" | "universal" =>
    some (np true)
  | "indefinite" | "negative" | "wh" => some (np false)
  | "attributiveDefinite" => some attributive
  | "determiner" => some det
  | "monotoneDecreasing" => some (pair false)
  | "monotoneDecreasingReferential" => some (pair true)
  | _ => none

/-- The kind of object a paraphrase reading queries. -/
def kind? : String → Option Kind
  | "referent" => some .individual
  | "predicate" => some .property
  | "determiner" => some .relation
  | "functional" => some .function
  | "domain" => some .situation
  | "complement" => some .complement
  | _ => none

/-- A paraphrase reading is predicted by a sign: if the paper judges it possible it queries an
abstracted parameter, and if the paper marks it impossible it does not. -/
def ReadingPredicted (s : Sign) (p : String × Judgment) : Prop :=
  match kind? p.1 with
  | some k => (p.2 = .acceptable → k ∈ s.cparams) ∧ (p.2 = .unacceptable → k ∉ s.cparams)
  | none => False

instance (s : Sign) (p : String × Judgment) : Decidable (ReadingPredicted s p) := by
  unfold ReadingPredicted; split <;> infer_instance

/-- A row is predicted: every paraphrase reading is predicted by the sign of its noun phrase
type. -/
def Predicted (r : LinguisticExample) : Prop :=
  match (r.feature? "np").bind sign? with
  | some s => ∀ p ∈ r.readings, ReadingPredicted s p
  | none => False

instance (r : LinguisticExample) : Decidable (Predicted r) := by
  unfold Predicted; split <;> infer_instance

/-- (25) to (90): the readings the paper finds and the ones it excludes. -/
theorem rows_predicted : ∀ r ∈ Examples.all, Predicted r := by decide

/-! ### Witness sets and truth conditions (§2.2.3, §4.4, §5.5) -/

variable {α : Type*} {Q : Quantifier α} {A X : α → Prop}

/-- The plain witness representation (85) is vacuous for a quantifier that the empty set
witnesses, such as *few* or *no*: every predicate contains a witness set. -/
theorem witness_subset_of_empty (hQ : Q (λ _ => False)) (X : α → Prop) :
    ∃ w, BarwiseCooper1981.Witness Q A w ∧ ∀ x, w x → X x :=
  ⟨λ _ => False, ⟨λ _ h => h.elim, hQ⟩, λ _ h => h.elim⟩

/-- So the equivalence (24) fails for every such quantifier that fails of some predicate. -/
theorem not_witness_iff_of_empty (hQ : Q (λ _ => False)) (hX : ¬ Q X) :
    ¬ ∀ X, Q X ↔ ∃ w, BarwiseCooper1981.Witness Q A w ∧ ∀ x, w x → X x :=
  λ h => hX ((h X).2 (witness_subset_of_empty hQ X))

/-- The pair representation (91): a quantifier living on `A` holds of `X` exactly when some
witness set is contained in `X` and its complement in `A` is disjoint from `X`. This is exact
for every quantifier, monotone or not. -/
theorem pair_apply_iff (h : LivesOn Q A) :
    Q X ↔ ∃ R, BarwiseCooper1981.Witness Q A R ∧ (∀ x, R x → X x) ∧
      ∀ x, A x → ¬ R x → ¬ X x := by
  constructor
  · intro hX
    exact ⟨λ x => A x ∧ X x, ⟨λ _ hx => hx.1, (h X).1 hX⟩, λ _ hx => hx.2,
      λ x hA hR hX' => hR ⟨hA, hX'⟩⟩
  · rintro ⟨R, ⟨hRA, hQR⟩, hRX, hC⟩
    refine (h X).2 ?_
    have : R = λ x => A x ∧ X x := by
      funext x
      exact propext ⟨λ hx => ⟨hRA x hx, hRX x hx⟩, λ hx => by_contra λ hR => hC x hx.1 hR hx.2⟩
    exact this ▸ hQR

end PurverGinzburg2004
