import Linglib.Features.Complementation

/-!
# Ndebele Clausal Embedding Inventory

[pietraszko-2019]

Northern Ndebele (Bantu S44, Zimbabwe; ISO 639-3 `nde`) inventory of
complement-taking predicates. The clause-typer is *ukuthi* — augment
*u-* (the exponent of D) over the class-15 complementizer root *kuthi*,
etymologically a nominalization of *thi* 'say' ((8)) — and it wraps
indicative and subjunctive complements alike in every syntactic context
[pietraszko-2019] tests (verb complement, clausal subject, preposition
object, demoted passive subject, adnominal). The augment drops exactly
where nominal augments drop (negation + in situ, (11)–(12)); the D
layer itself is obligatory. Since the paper establishes no
predicate-conditioned variation in the clause-typer, the observables
here are the complement's mood coding (lexically conditioned, their
fn. 3) and the clausal argument's syntactic role. No factivity data:
the paper runs no projection tests, and the *the fact that*
paraphrases in its translations are an English artifact it flags
itself (at (20)).
-/

namespace Ndebele.Clause

/-! ### Language-level constants -/

/-- The clause-typer: augment + class-15 complementizer root. -/
def clauseTyperForm : String := "ukuthi"

/-- Noun class of the clause-typer (Bantu class number): class 15, per
    the augment's agreement ((10)), the object marker *ku-* ((7b)), and
    clausal-subject agreement ((22)). Halpert's Zulu counterpart is
    glossed class 17. -/
def clauseTyperClass : Nat := 15

/-! ### Predicate schema -/

/-- Syntactic role of the predicate's attested clausal argument. -/
inductive ClausalRole where
  /-- Complement/object of the verb. -/
  | complement
  /-- Object of an independent preposition (*nga* 'about', (20b)). -/
  | prepositionObject
  /-- Demoted passive subject with oblique *yi-* ((14)). -/
  | obliquePassiveSubject
  /-- Clausal subject ((22)). -/
  | subject
  deriving DecidableEq, Repr

/-- An Ndebele complement-taking predicate.

    - `ctpClass`: [noonan-2007] category; `none` where the attested
      frame gives no clear assignment.
    - `coding`: mood of the *ukuthi*-complement — indicative vs
      subjunctive, lexically conditioned ([pietraszko-2019] fn. 3:
      indicative clauses allow only *ukuthi*; *ukuze*, *sengathi* are
      lexically selected and subjunctive-only).
    - `clausalRole`: where the clause sits. -/
structure NdebeleEmbedder where
  form : String
  gloss : String
  ctpClass : Option CTPClass
  coding : Option Complement.Coding
  clausalRole : ClausalRole
  deriving DecidableEq, Repr

/-! ### Predicates -/

/-- *cabanga* 'think'. Indicative *ukuthi*-complement; the augment-drop
    paradigm predicate ((4), (12a–c)). -/
def cabanga : NdebeleEmbedder where
  form := "cabanga"; gloss := "think"
  ctpClass := some .propAttitude
  coding := some .indicative
  clausalRole := .complement

/-- *funa* 'want'. Subjunctive *ukuthi*-complement ((7b)); also plain
    class-15 nominal objects ((7a)). -/
def funa : NdebeleEmbedder where
  form := "funa"; gloss := "want"
  ctpClass := some .desiderative
  coding := some .subjunctive
  clausalRole := .complement

/-- *zwa* 'hear'. Both attested examples are hearsay reports
    ((18), (26a)), not immediate perception. -/
def zwa : NdebeleEmbedder where
  form := "zwa"; gloss := "hear"
  ctpClass := some .perception
  coding := some .indicative
  clausalRole := .complement

/-- *khuluma nga* 'talk about': the clause is the object of the
    preposition *nga*, with no extra nominal structure —
    `nga [DP u-kuthi …]`, coalescing to *ngokuthi* ((20b)). -/
def khulumaNga : NdebeleEmbedder where
  form := "khuluma nga"; gloss := "talk about"
  ctpClass := some .utterance
  coding := some .indicative
  clausalRole := .prepositionObject

/-- *danisa* 'worry (caus.)', attested only passivized: the clause is a
    demoted subject with the augment-replacing oblique *yi-*
    (*yikuthi*, (14)). -/
def danisa : NdebeleEmbedder where
  form := "danisa"; gloss := "worry"
  ctpClass := none
  coding := some .indicative
  clausalRole := .obliquePassiveSubject

/-- *bala* 'write', passive impersonal: the *ukuthi*-clause is a
    subject controlling class-15 agreement ((22)). -/
def bala : NdebeleEmbedder where
  form := "bala"; gloss := "write"
  ctpClass := none
  coding := some .indicative
  clausalRole := .subject

/-! ### Inventories -/

/-- The predicates with quotable clausal-argument data in
    [pietraszko-2019]. -/
def allEmbedders : List NdebeleEmbedder :=
  [cabanga, funa, zwa, khulumaNga, danisa, bala]

/-- Drift sentry: *funa* is the only subjunctive-taker in the sample
    ([pietraszko-2019] fn. 3's lexical conditioning). -/
theorem subjunctive_takers :
    allEmbedders.filter (·.coding == some .subjunctive) = [funa] := by
  decide

/-- Drift sentry: the verb-complement frame is attested for exactly
    *cabanga*, *funa*, *zwa*. -/
theorem complement_takers :
    allEmbedders.filter (·.clausalRole == .complement) =
      [cabanga, funa, zwa] := by decide

end Ndebele.Clause
