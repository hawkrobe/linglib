import Linglib.Fragments.Greek.StandardModern.Complementizers

/-!
# Roussou 2010: Selecting complementizers
[roussou-2010]

Modern Greek complementizers in their dual capacity of being selected
and of selecting. *oti*, *pu*, and *an* are nominal elements merging
OUTSIDE the embedded clause (under N, as the matrix verb's internal
argument), distinguished by the propositional quantification they
contribute: *pu* is definite — it binds a single proposition and
locates it to a reference point, whence factivity ([christidis-1986]);
*oti* is a plain indefinite ranging over a set of propositions; *an*
is a polarity indefinite requiring a binder. *na* instead merges
INSIDE the lower C domain as a deictic/locative nominal that re-opens
the EPP position, so a na-clause denotes a predicate rather than a
proposition — whence control mediation (*kséro* + *na* 'know how',
ex. 25) and the impossibility of *oti/an/pu* over a na-complement.

Selection is thus not one-to-one (ex. 1–3): the same predicate takes
different clause types under different conditions — *kséro* takes
*an* only under matrix negation/question, epistemic *pistévo* takes
*na* only with present-tense matrix inflection (ex. 23), and focus
licenses otherwise unselected *pu* (ex. 22). Factivity with *oti* is
verb-derived, weak, and deniable (ex. 15–16, 19), so *pu* → factive
holds only one way.

## Main declarations

- `PropQuant`, `MergeSite`, `CProfile`, `profile` — the nominal
  typology of the four clause-typers (§3–4)
- `factive_iff_definite` — the fragment's lexical `factive` flag
  coincides with definite propositional quantification
- `CTP`, `CTP.licensesAn` — *an* as polarity item: bound locally by a
  rogative or negation-incorporating predicate, non-locally by a
  matrix operator, and never under a True/False predicate
  ([adger-quer-2001], ex. 7)
- `na_reopens_epp` — the merge-site split deriving the propositional
  vs predicate complement divide
-/

namespace Roussou2010

open Greek.StandardModern.Complementizers

/-! ### The nominal typology (§3–4) -/

/-- Propositional quantification contributed by an outside-merging
complementizer: definite (binds a single proposition, locating it to a
reference point) vs indefinite (ranges over a set of propositions). -/
inductive PropQuant where
  | definite
  | indefinite
  deriving DecidableEq, Repr

/-- Merge site of a clause-typing element: outside the embedded clause
(under N, as the matrix verb's internal argument — *oti*, *pu*, *an*)
or inside its lower C domain (*na*, ex. 28). -/
inductive MergeSite where
  | outside
  | inside
  deriving DecidableEq, Repr

/-- The lexical specification §4 attributes to a clause-typer: merge
site, propositional quantification (`none` for inside-mergers, which
bind no propositional variable), and polarity sensitivity. -/
structure CProfile where
  site : MergeSite
  quant : Option PropQuant
  polar : Bool := false
  deriving DecidableEq, Repr

/-- The MG assignment (§3.1, §4): *oti* indefinite, *an* polar
indefinite, *pu* definite — all outside — and *na* inside with no
propositional quantification. -/
def profile (c : Complementizer) : Option CProfile :=
  if c = oti then some { site := .outside, quant := some .indefinite }
  else if c = an then
    some { site := .outside, quant := some .indefinite, polar := true }
  else if c = pu then some { site := .outside, quant := some .definite }
  else if c = na then some { site := .inside, quant := none }
  else none

/-- Definiteness is what the fragment's lexical `factive` flag records
([christidis-1986]: *pu* as the definite article of the propositional
domain). One way only: the factive doxastics (*kséro*, *katalavéno*)
take indefinite *oti* (ex. 19), with weak, deniable, verb-derived
factivity (ex. 15). -/
theorem factive_iff_definite :
    ∀ c ∈ [oti, pu, an, na],
      (c.factive = some true ↔ (profile c).bind (·.quant) = some .definite) := by
  decide

/-! ### The polarity complementizer *an* (§2) -/

/-- The lexical properties of a clause-taking predicate that §2's
licensing generalization turns on: an inherent interrogative operator
(*anarotjéme* 'wonder', ex. 1b, 10), incorporated negation
(*amfivállo* 'doubt', *ksexnó* 'forget', ex. 14), or True/False-hood —
the subject's commitment to the truth or falsity of the complement
([adger-quer-2001]; *ipothéto* 'assume', *ipostirízo* 'claim',
ex. 7). -/
structure CTP where
  rogative : Bool := false
  incorpNeg : Bool := false
  tf : Bool := false
  deriving DecidableEq, Repr

/-- §2's generalization: *an*, a polarity indefinite, is bound either
locally by the predicate's own operator (rogative or incorporated
negation) or non-locally by a matrix propositional operator
(negation/question, ex. 11) — unless the predicate is True/False,
whose commitment leaves no open set of propositions to bind. -/
def CTP.licensesAn (p : CTP) (matrixOp : Bool) : Prop :=
  ¬p.tf ∧ (p.rogative ∨ p.incorpNeg ∨ matrixOp)

instance (p : CTP) (matrixOp : Bool) : Decidable (p.licensesAn matrixOp) := by
  unfold CTP.licensesAn; infer_instance

/-- *kséro* 'know': no operator of its own (ex. 1a: *oti*/**an*). -/
def kseroCTP : CTP := {}

/-- *anarotjéme* 'wonder': inherently interrogative (ex. 1b). -/
def anarotjemeCTP : CTP := { rogative := true }

/-- *amfivállo* 'doubt': incorporated negation (ex. 14). -/
def amfivaloCTP : CTP := { incorpNeg := true }

/-- *ipothéto* 'assume': True/False predicate (ex. 7). -/
def ipothetoCTP : CTP := { tf := true }

/-- Local licensing (ex. 1b, 10, 14): rogatives and
negation-incorporators take *an* with no matrix operator present. -/
theorem an_licensed_locally :
    anarotjemeCTP.licensesAn false ∧ amfivaloCTP.licensesAn false := by
  decide

/-- The unselected embedded question (ex. 2b, 11, 34): plain *kséro*
licenses *an* only under a matrix operator. -/
theorem an_unselected_needs_operator :
    ¬ kseroCTP.licensesAn false ∧ kseroCTP.licensesAn true := by
  decide

/-- True/False predicates never license *an* (ex. 7b): the commitment
they express is incompatible with the unbound propositional set,
matrix operator or not. -/
theorem tf_never_licenses_an :
    ∀ matrixOp, ¬ ipothetoCTP.licensesAn matrixOp := by
  decide

/-! ### *na* merges inside (§3.2, §4) -/

/-- The variable a clause makes available to its embedder: a closed
proposition, or — once *na* has re-opened the EPP position — a
predicate (§4; *na* as a deictic/locative nominal satisfying the EPP
word-internally, ex. 27–29). -/
inductive ClauseVar where
  | propositional
  | predicate
  deriving DecidableEq, Repr

/-- The variable provided by a clause headed by the given element:
inside-mergers re-open the proposition; outside-mergers leave it
closed. -/
def providedVar (c : Complementizer) : ClauseVar :=
  if (profile c).map (·.site) = some .inside then .predicate
  else .propositional

/-- The merge-site split cashed out (p. 597): the three outside
mergers each require a propositional variable (their `quant`), while a
na-clause supplies a predicate — deriving *[oti/an/pu [na …]] in
complement position. Relative *pu* + *na* (ex. 31) escapes because
relative *pu* binds an individual variable instead; control follows
the same split, *na* mediating the binding of the re-opened subject
position by a matrix argument under restructuring predicates
(ex. 25–26). -/
theorem na_reopens_epp :
    providedVar na = .predicate ∧
    ∀ c ∈ [oti, pu, an], ((profile c).bind (·.quant)).isSome := by
  decide

end Roussou2010
