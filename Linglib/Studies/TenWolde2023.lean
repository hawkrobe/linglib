import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.UpperLower.Basic
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Studies.Traugott2010

/-!
# ten Wolde (2023): The English Binominal Noun Phrase: A Cognitive-Functional Approach

This file formalizes ten Wolde's account of the English *of*-binominal as a grammaticalization
path from the prototypical N+PP (*the beast of the field*) through the head-classifier (*a cake
of rye*) and the evaluative binominal noun phrase (*that idiot of a doctor*) to the evaluative
modifier (*a hell of a time*) and the binominal intensifier (*a hell of a good time*) (`Stage`).
Each diagnostic that separates the constructions holds over an interval of the path
(`Diagnostic.span`), so a property of the last stage is never lost once gained
(`isUpperSet_span_of_top_mem`), and the diagnostics together tell every two stages apart
(`profile_injective`).

The first nouns of the three case studies are attested at every stage below the ones they have
reached, and every inanimate first noun develops the pseudo-partitive (*a cake of soap*), which
lies off the path. In the constructional network the metaphorical links are the covering relation
of the path (`metaphorical_iff_covBy`), and the step onto the evaluative stages is a
subjectification in Traugott's sense.

## Implementation notes

* The book was not available to this formalization. The path is the one the publisher's
  description gives and the case-study nouns are those of the table of contents; the span of each
  diagnostic, the attestations of the corpus nouns and the polysemy links are unverified.
* A diagnostic is the set of stages at which it holds, and an interval because the book's claim
  is the stage at which the property is gained or lost.
* A noun records the pseudo-partitive separately from its stages, since that construction is a
  side branch and not a stage of the path.

## TODO

* The corpus noun *bitch* has no head-classifier attestation here, so its stages are not a lower
  set; check the corpus chapter before extending `isLowerSet_stages_of_mem_caseStudies` to
  `Noun.all`.

## References

* [ten-wolde-2023]
* [traugott-2010]
-/

namespace TenWolde2023

/-! ### The path -/

/-- The constructions on the grammaticalization path, from the most lexical to the most
grammaticalized. -/
inductive Stage where
  /-- The first noun denotes a referent and the prepositional phrase ascribes a property to it,
  as in *the beast of the field*. -/
  | nPP
  /-- The second noun classifies the type or material of the first, as in *a cake of rye*. -/
  | headClassifier
  /-- The first noun ascribes an evaluative property to the referent of the second, as in *that
  idiot of a doctor*. -/
  | evaluative
  /-- The chunk [N₁ *of a*] is a modifier evaluating the second noun, as in *a hell of a time*. -/
  | evaluativeModifier
  /-- The chunk [N₁ *of a*] intensifies a following adjective or quantifier, as in *a hell of
  a good time*. -/
  | binominalIntensifier
  deriving DecidableEq, Fintype, Repr

/-- The stages are ordered as they are listed. -/
instance : LinearOrder Stage := LinearOrder.lift' Stage.ctorIdx (by decide)

instance : BoundedOrder Stage where
  top := .binominalIntensifier
  le_top := by decide
  bot := .nPP
  bot_le := by decide

/-- The path, from the first stage to the last. -/
def Stage.path : List Stage :=
  [nPP, headClassifier, evaluative, evaluativeModifier, binominalIntensifier]

/-- Each stage of the path is the immediate successor of the one before it. -/
theorem Stage.path_isChain : Stage.path.IsChain (· ⋖ ·) := by decide

/-! ### Diagnostics -/

/-- The properties that separate the constructions. -/
inductive Diagnostic where
  /-- The first noun is the semantic head. -/
  | n₁Head
  /-- The first noun denotes an entity. -/
  | n₁Referential
  /-- The first noun expresses the speaker's evaluation. -/
  | n₁Evaluative
  /-- *of* is a linking element without prepositional meaning. -/
  | ofLinker
  /-- The first noun can be plural. -/
  | n₁Plural
  /-- The second determiner marks number. -/
  | det₂Number
  /-- The first noun takes descriptive premodifiers, as in *a total idiot of a doctor*. -/
  | n₁Premodification
  /-- The two nouns agree in number without exception. -/
  | strictAgreement
  /-- The two nouns agree in number at least as a rule. -/
  | agreement
  /-- *of* cannot be dropped or fused, as it is in *helluva*. -/
  | ofObligatory
  /-- [N₁ *of a*] is a constituent. -/
  | chunk
  /-- *of* can be paraphrased by the copula, as in *the doctor is an idiot*. -/
  | copulaParaphrase
  /-- The second noun must be a count or collective noun. -/
  | n₂CountOnly
  deriving DecidableEq, Fintype, Repr

open Stage in
/-- The stages at which a diagnostic holds. -/
def Diagnostic.span : Diagnostic → Set Stage
  | .n₁Head | .n₁Referential => Set.Iic headClassifier
  | .n₁Evaluative => Set.Ici evaluative
  | .ofLinker => Set.Ici headClassifier
  | .n₁Plural | .det₂Number | .n₁Premodification | .strictAgreement => Set.Iic evaluative
  | .agreement | .ofObligatory => Set.Iic evaluativeModifier
  | .chunk => Set.Ici evaluativeModifier
  | .copulaParaphrase => Set.Icc evaluative evaluative
  | .n₂CountOnly => Set.Icc evaluative evaluativeModifier

instance (d : Diagnostic) : DecidablePred (· ∈ d.span) := fun _ ↦ by
  cases d <;> unfold Diagnostic.span <;> infer_instance

/-- Every diagnostic holds over a contiguous span of the path. -/
theorem ordConnected_span (d : Diagnostic) : d.span.OrdConnected := by
  cases d <;> unfold Diagnostic.span <;> infer_instance

/-- A property of the most grammaticalized stage, once gained along the path, is never lost. -/
theorem isUpperSet_span_of_top_mem {d : Diagnostic} (h : ⊤ ∈ d.span) : IsUpperSet d.span :=
  fun _ _ hab ha ↦ (ordConnected_span d).out ha h ⟨hab, le_top⟩

/-- A property of the most lexical stage, once lost along the path, is never regained. -/
theorem isLowerSet_span_of_bot_mem {d : Diagnostic} (h : ⊥ ∈ d.span) : IsLowerSet d.span :=
  fun _ _ hba ha ↦ (ordConnected_span d).out h ha ⟨bot_le, hba⟩

/-- The copula paraphrase is transient, arising with the evaluative binominal and lost at the
next stage. -/
theorem copulaParaphrase_span : Diagnostic.copulaParaphrase.span = {.evaluative} :=
  Set.Icc_self _

/-- The restriction of the second noun to count nouns is transient, arising with the evaluative
binominal and lifted again at the intensifier. -/
theorem n₂CountOnly_not_upper_not_lower :
    ¬ IsUpperSet Diagnostic.n₂CountOnly.span ∧ ¬ IsLowerSet Diagnostic.n₂CountOnly.span :=
  ⟨fun h ↦ absurd (h (b := .binominalIntensifier) (by decide)
      (show Stage.evaluativeModifier ∈ _ by decide)) (by decide),
    fun h ↦ absurd (h (b := .nPP) (by decide) (show Stage.evaluative ∈ _ by decide)) (by decide)⟩

/-- The head switches to the second noun exactly where the first noun becomes evaluative. -/
theorem n₁Head_span_compl : Diagnostic.n₁Head.spanᶜ = Diagnostic.n₁Evaluative.span := by
  ext s; cases s <;> decide

/-- The chunk [N₁ *of a*] forms exactly where the first noun stops inflecting. -/
theorem n₁Plural_span_compl : Diagnostic.n₁Plural.spanᶜ = Diagnostic.chunk.span := by
  ext s; cases s <;> decide

/-- The diagnostics that hold at a stage. -/
def Stage.profile (s : Stage) : Finset Diagnostic := {d | s ∈ d.span}

/-- The diagnostics tell every two stages apart. -/
theorem profile_injective : Function.Injective Stage.profile := by decide

/-! ### First nouns -/

/-- The semantic classes of first nouns. -/
inductive SemanticClass where
  /-- Inanimate concrete nouns such as *cake*, *nub*, *breeze* and *husk*. -/
  | inanimate
  /-- Animate nouns such as *beast*, *snake* and *whale*. -/
  | animate
  /-- Abstract nouns, among them mythical beings and expletives, such as *hell* and *bitch*. -/
  | abstract
  deriving DecidableEq, Repr

/-- A first noun with the constructions it is attested in. -/
structure Noun where
  semanticClass : SemanticClass
  /-- The stages of the path the noun is attested at. -/
  stages : Finset Stage
  /-- Whether the noun has pseudo-partitive uses, as in *a cake of soap*. -/
  pseudoPartitive : Bool
  /-- The form fused with *of a* in the intensifier, if there is one. -/
  fused : Option String := none
  deriving DecidableEq

namespace Noun

/-- The case-study noun *hell* is attested at every stage and fuses to *helluva*. -/
def hell : Noun := ⟨.abstract, Finset.univ, true, some "helluva"⟩

/-- The case-study noun *beast* is attested at every stage and has no pseudo-partitive uses. -/
def beast : Noun := ⟨.animate, Finset.univ, false, none⟩

/-- The case-study noun *cake* is attested up to the evaluative binominal. -/
def cake : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *whale* is attested at every stage and fuses to *whaleuva*. -/
def whale : Noun := ⟨.animate, Finset.univ, false, some "whaleuva"⟩

/-- The noun *bitch* has no head-classifier uses. -/
def bitch : Noun :=
  ⟨.abstract, {.nPP, .evaluative, .evaluativeModifier, .binominalIntensifier}, false, none⟩

/-- The noun *nub* is attested up to the evaluative binominal. -/
def nub : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *breeze* is attested up to the evaluative binominal. -/
def breeze : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *husk* is attested up to the evaluative binominal. -/
def husk : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *snake* is animate and yet has pseudo-partitive uses. -/
def snake : Noun := ⟨.animate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The nouns of the three case studies. -/
def caseStudies : List Noun := [cake, beast, hell]

/-- The nouns of the case studies and of the corpus study. -/
def all : List Noun := caseStudies ++ [whale, bitch, nub, breeze, husk, snake]

end Noun

/-- A case-study noun attested at a stage is attested at every earlier stage. -/
theorem isLowerSet_stages_of_mem_caseStudies :
    ∀ n ∈ Noun.caseStudies, IsLowerSet (n.stages : Set Stage) := by
  simp only [IsLowerSet, Finset.mem_coe]; decide

/-- Every inanimate first noun develops pseudo-partitive uses. -/
theorem pseudoPartitive_of_inanimate :
    ∀ n ∈ Noun.all, n.semanticClass = .inanimate → n.pseudoPartitive := by decide

/-- The animate and abstract nouns with pseudo-partitive uses are *snake* and *hell*. -/
theorem pseudoPartitive_iff :
    ∀ n ∈ Noun.all, n.pseudoPartitive ↔
      n.semanticClass = .inanimate ∨ n = .snake ∨ n = .hell := by decide

/-- A first noun fuses with *of a* only if it reaches the intensifier. -/
theorem binominalIntensifier_mem_of_fused :
    ∀ n ∈ Noun.all, n.fused.isSome → .binominalIntensifier ∈ n.stages := by decide

/-! ### The constructional network -/

open ConstructionGrammar

/-- The form of the construction at each stage; the optional *a* of the modifier and the
intensifier is left out. -/
def Stage.construction : Stage → Construction Unit
  | .nPP => ⟨"N+PP",
      [{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
       { filler := .fixed "of" }, { filler := .open_ .DET }, { filler := .open_ .NOUN }], (), false⟩
  | .headClassifier => ⟨"Head-Classifier",
      [{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
       { filler := .fixed "of" }, { filler := .open_ .NOUN }], (), false⟩
  | .evaluative => ⟨"Evaluative BNP",
      [{ filler := .open_ .DET }, { filler := .open_ .NOUN }, { filler := .fixed "of" },
       { filler := .fixed "a" }, { filler := .open_ .NOUN, isHead := true }], (), false⟩
  | .evaluativeModifier => ⟨"Evaluative Modifier",
      [{ filler := .open_ .DET }, { filler := .open_ .NOUN }, { filler := .fixed "of" },
       { filler := .open_ .NOUN, isHead := true }], (), false⟩
  | .binominalIntensifier => ⟨"Binominal Intensifier",
      [{ filler := .open_ .NOUN }, { filler := .fixed "of" }, { filler := .open_ .ADJ },
       { filler := .open_ .NOUN, isHead := true }], (), false⟩

/-- The simple noun phrase, whose classifying and evaluative premodifiers share their function
with the binominals. -/
def simpleNP : Construction Unit :=
  ⟨"Simple NP", [{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true }], (), false⟩

/-- The adjective phrase, whose intensifiers share their function with the binominal
intensifier. -/
def adjectivePhrase : Construction Unit :=
  ⟨"AP", [{ filler := .open_ .ADV }, { filler := .open_ .ADJ, isHead := true }], (), false⟩

/-- A link between two constructions of the network. -/
private def link (parent child : Construction Unit) (type : LinkType) (shared : String) :
    InheritanceLink :=
  { parent := parent.name, child := child.name, mode := .normal, linkType := some type,
    sharedProperties := [shared] }

open Stage in
/-- The network of the *of*-binominals: metaphorical links along the path, and polysemy links
from each stage to the phrase whose modifier shares its function (*a beast of a boy* and *a
beastly boy*, *a hell of a good time* and *a hella good time*). -/
def network : Constructicon Unit where
  constructions := Stage.path.map Stage.construction ++ [simpleNP, adjectivePhrase]
  links :=
    [ link nPP.construction headClassifier.construction .metaphorical "N₁ heads"
    , link headClassifier.construction evaluative.construction .metaphorical "N₁ characterizes N₂"
    , link evaluative.construction evaluativeModifier.construction .metaphorical "N₁ evaluates"
    , link evaluativeModifier.construction binominalIntensifier.construction .metaphorical
        "[N₁ of a] is a chunk"
    , link headClassifier.construction simpleNP .polysemy "classifying modifier"
    , link evaluative.construction simpleNP .polysemy "evaluative modifier"
    , link evaluativeModifier.construction simpleNP .polysemy "speaker evaluation"
    , link binominalIntensifier.construction adjectivePhrase .polysemy "intensifier" ]

/-- Every link of the network joins two of its constructions. -/
theorem network_wellFormed : network.WellFormed := by decide

/-- The metaphorical links are the covering relation of the path, so each stage is a metaphorical
extension of the one before it and of no other. -/
theorem metaphorical_iff_covBy (s t : Stage) :
    (∃ l ∈ network.links, l.linkType = some .metaphorical ∧
      l.parent = s.construction.name ∧ l.child = t.construction.name) ↔ s ⋖ t := by
  revert s t; decide

/-- The head of the form precedes *of* exactly at the stages where the first noun is the semantic
head. -/
theorem head_before_of_iff (s : Stage) :
    ((s.construction.form.takeWhile (·.filler ≠ .fixed "of")).any (·.isHead)) ↔
      s ∈ Diagnostic.n₁Head.span := by
  revert s; decide

/-! ### Subjectification -/

/-- The coded level of the first noun's meaning at a stage is nonsubjective while the noun
ascribes an objective property and subjective once it expresses the speaker's evaluation. -/
def Stage.level (s : Stage) : Traugott2010.SubjectivityLevel :=
  if s ∈ Diagnostic.n₁Evaluative.span then .subjective else .nonSubjective

/-- The path follows [traugott-2010]'s cline, with one subjectification at the evaluative
binominal and bleaching within the subjective level after it. -/
theorem path_unidirectional :
    Traugott2010.Unidirectional (Stage.path.map Stage.level) := by
  decide

end TenWolde2023
