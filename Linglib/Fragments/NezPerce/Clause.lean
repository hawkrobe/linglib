import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Data.UD.Basic

/-!
# Nez Perce clausal embedding

Nez Perce (Sahaptian, ISO 639-3 `nez`) embeds a finite clause under an attitude predicate in
two shapes. Under the emotive predicates *lilooy* 'be happy', *’etqew* 'be sad', *cicwaay* 'be
surprised', *’eey’s* 'be joyful', *q’eese’* 'be bothered' and *tim’neeneki* 'be worried', and
under *timiipni* 'remember', the clause opens with the relative pronoun *yox̂* and the
complementizer *ke*, the edge of a relative clause, and these predicates take no noun-phrase
object. Under *neki* 'think', *hi* 'say, tell' and *cuukwe* 'know' the clause has the shape of a
matrix clause, and *hi* takes an accusative addressee. Consultants endorse the complement of the
first class and of *cuukwe* under negation, in questions and in conditional antecedents, and not
the complement of *neki*. The relative pronoun inflects for case and number.

Forms follow Deal's orthography. The data are Deal's: the judgments on each shape are the rows
of `Data/Examples/Deal2026.json`, and the relative-embedding analysis is
`Studies/Deal2026.lean`.

## References

* [deal-2026]
* [deal-2016a]
* [noonan-2007]
-/

namespace NezPerce

/-! ### Clause-typers -/

/-- The complementizer *ke*, which heads relative clauses and the relative embeddings. -/
def ke : Complementizer where
  morphs := [.free "ke"]
  coding := some .indicative

/-! ### Predicates -/

/-- A Nez Perce complement-taking predicate is a verb entry with its [noonan-2007] class. -/
structure Verb extends _root_.Verb where
  predicateClass : Complement.PredicateClass
  deriving Repr

/-- *lilooy* 'be happy' ((27a), (28a), (33)). -/
def liloy : Verb where
  form := "lilooy"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  attitude := some (.preferential (.degreeComparison .positive))
  factivity := some .emotive

/-- *’etqew* 'be sad' (27b). -/
def etqew : Verb where
  form := "’etqew"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .emotive

/-- *cicwaay* 'be surprised' ((27c), (28b)). -/
def cicwaay : Verb where
  form := "cicwaay"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  factivity := some .emotive

/-- *’eey’s* 'be joyful', which takes no noun-phrase object ((27e), (41)). -/
def eeys : Verb where
  form := "’eey’s"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  attitude := some (.preferential (.degreeComparison .positive))
  factivity := some .emotive

/-- *q’eese’* 'be bothered, unhappy' (27e). -/
def qeese : Verb where
  form := "q’eese’"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .emotive

/-- *tim’neeneki* 'be worried', whose complement projects under negation ((27e), (34)). -/
def timneneki : Verb where
  form := "tim’neeneki"
  frames := [Frame.finiteClause]
  predicateClass := .commentative
  attitude := some (.preferential .uncertaintyBased)
  factivity := some .emotive

/-- *timiipni* 'remember', a cognitive factive with the relative edge (27d). -/
def timiipni : Verb where
  form := "timiipni"
  frames := [Frame.finiteClause]
  predicateClass := .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *neki* 'think', whose complement does not project ((35), (36), (48)). -/
def neki : Verb where
  form := "neki"
  frames := [Frame.finiteClause]
  predicateClass := .propAttitude
  attitude := some (.doxastic .nonVeridical)

/-- *hi* 'say, tell', with an accusative addressee before the clause ((47), (65b)). -/
def hi : Verb where
  form := "hi"
  frames := [[.nominal, .clausal (coding := some .indicative) (force := some .declarative)]]
  predicateClass := .utterance
  speechActVerb := true

/-- *cuukwe* 'know', whose complement projects from a conditional antecedent ((66), (68)). -/
def cuukwe : Verb where
  form := "cuukwe"
  frames := [Frame.finiteClause]
  predicateClass := .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb :=
  [liloy, etqew, cicwaay, eeys, qeese, timneneki, timiipni, neki, hi, cuukwe]

/-! ### Relative-pronoun paradigm

The *yox̂/ko* paradigm from [deal-2016a], reproduced at [deal-2026] (22).
Cells are indexed by `Core.UD.Case` (Nom/Erg/Acc) × `Core.UD.Number`. -/

/-- A relative-pronoun cell from [deal-2026] (22). -/
structure RelativePronoun where
  case : UD.Case
  number : UD.Number
  forms : List String  -- multiple if idiolectal variation
  deriving Repr

def rp_nom_sg : RelativePronoun := ⟨.Nom, .Sing, ["yox̂"]⟩
def rp_nom_pl : RelativePronoun := ⟨.Nom, .Plur, ["yox̂me"]⟩
def rp_erg_sg : RelativePronoun := ⟨.Erg, .Sing, ["konim"]⟩
def rp_erg_pl : RelativePronoun := ⟨.Erg, .Plur, ["konmam"]⟩
def rp_acc_sg : RelativePronoun := ⟨.Acc, .Sing, ["konya"]⟩
def rp_acc_pl : RelativePronoun := ⟨.Acc, .Plur, ["konmana", "yox̂mene"]⟩

/-- The full paradigm: three cases × two numbers, six cells. -/
def relativePronounParadigm : List RelativePronoun :=
  [rp_nom_sg, rp_nom_pl, rp_erg_sg, rp_erg_pl, rp_acc_sg, rp_acc_pl]

end NezPerce
