import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.UpperLower.Basic
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Studies.Traugott2010

/-!
# ten Wolde (2023): The English Binominal Noun Phrase: A Cognitive-Functional Approach

This file formalizes ten Wolde's account of the English *of*-binominal as a grammaticalization
path from the prototypical N+PP (*the hell of his own invention*) through the head-classifier
(*a hell of loneliness*) and the evaluative binominal noun phrase (*a hell of a hotel*) to the
evaluative modifier (*a hell of a man*) and the binominal intensifier (*a hell of a large sum*)
(`Stage`). The features of the book's two overview tables hold over intervals of the path, with
one exception (`ordConnected_span_iff`): the second determiner is lost in the head-classifier and
reappears in the evaluative binominal, which the book explains by inheritance from the N+PP. A
feature that holds over an interval is never lost once gained if it holds at the last stage
(`isUpperSet_span_of_top_mem`), and the features together tell every two stages apart
(`profile_injective`).

Every first noun of the case studies and of the corpus study is attested at all stages below the
ones it has reached (`isLowerSet_stages`). In the constructional network the metaphorical links
are the covering relation of the path (`metaphorical_iff_covBy`), and the step onto the
evaluative stages is a subjectification in Traugott's sense.

## Implementation notes

* The spans of the diagnostics are read off the feature rows of Tables 3.2 and 4.2, the path off
  Figure 6.1, the semantic classes off Table 2.1, the attestations off Figures 5.1 and 5.2 and
  the summary of chapter 6, and the links off the network figures of chapter 8.
* A diagnostic is the set of stages at which it holds. The second determiner of the N+PP is an
  open determiner slot, which is counted here as marking number.
* A noun records the pseudo-partitive separately from its stages. Figure 6.1 draws that
  construction as an optional detour between the head-classifier and the evaluative binominal,
  not as a stage of the path.

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
  as in *the hell of his own invention*. -/
  | nPP
  /-- The second noun classifies the type or material of the first, as in *a hell of loneliness*. -/
  | headClassifier
  /-- The first noun ascribes an evaluative property to the referent of the second, as in *a hell
  of a hotel*. -/
  | evaluative
  /-- The chunk [N₁ *of a*] is a modifier evaluating the second noun, as in *a hell of a man*. -/
  | evaluativeModifier
  /-- The chunk [N₁ *of a*] intensifies a following adjective or quantifier, as in *a hell of
  a large sum*. -/
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

/-- The features that separate the constructions in the book's overview tables. -/
inductive Diagnostic where
  /-- *of* has prepositional meaning, such as 'out of', 'with' or 'from'. -/
  | ofMeaningful
  /-- *of* can be left out or fused, where elsewhere it is mandatory. -/
  | ofOmissible
  /-- The first determiner can be absent. -/
  | det₁Omissible
  /-- There is a second determiner. -/
  | det₂
  /-- The second determiner marks number. -/
  | det₂Number
  /-- The first noun is the semantic, syntactic and discourse head. -/
  | n₁Head
  /-- The second noun is the syntactic head, beyond being the semantic and discourse head. -/
  | n₂SyntacticHead
  /-- The first noun ascribes an evaluative property to the second or evaluates its referent. -/
  | n₁Evaluative
  /-- [N₁ *of a*] functions as a unit, a modifier or an intensifier. -/
  | chunk
  /-- The first determiner is selected by the first noun and does not scope over the whole. -/
  | det₁ScopeN₁
  /-- The *of*-phrase can be moved and coordinated. -/
  | ofPhraseMoves
  /-- The first noun can be plural. -/
  | n₁Plural
  /-- The first noun is modified without restriction to a limited set of modifiers. -/
  | n₁FullModification
  /-- The first noun can be modified at all. -/
  | n₁Modification
  /-- The two nouns agree in number without exception. -/
  | strictAgreement
  /-- The two nouns agree in number at least as a rule. -/
  | agreement
  /-- The second noun must be a count or collective noun. -/
  | n₂CountOnly
  deriving DecidableEq, Fintype, Repr

open Stage in
/-- The stages at which a diagnostic holds. -/
def Diagnostic.span : Diagnostic → Set Stage
  | .ofMeaningful | .ofPhraseMoves => Set.Iic nPP
  | .n₁Head | .det₁ScopeN₁ => Set.Iic headClassifier
  | .n₁Plural | .n₁FullModification => Set.Iic evaluative
  | .n₁Modification => Set.Iic evaluativeModifier
  | .n₁Evaluative => Set.Ici evaluative
  | .det₁Omissible | .n₂SyntacticHead | .chunk => Set.Ici evaluativeModifier
  | .ofOmissible => Set.Ici binominalIntensifier
  | .strictAgreement => Set.Icc evaluative evaluative
  | .agreement | .n₂CountOnly => Set.Icc evaluative evaluativeModifier
  | .det₂ => {nPP} ∪ Set.Ici evaluative
  | .det₂Number => {nPP, evaluative}

instance (d : Diagnostic) : DecidablePred (· ∈ d.span) := fun _ ↦ by
  cases d <;> unfold Diagnostic.span <;> infer_instance

/-- Every diagnostic but those of the second determiner holds over a contiguous span of the path.
The head-classifier has no second determiner, while the N+PP before it and the evaluative
binominal after it do. -/
theorem ordConnected_span_iff (d : Diagnostic) :
    d.span.OrdConnected ↔ d ≠ .det₂ ∧ d ≠ .det₂Number := by
  have gap {s : Set Stage} (h₁ : Stage.nPP ∈ s) (h₂ : Stage.evaluative ∈ s)
      (h₃ : Stage.headClassifier ∉ s) : ¬ s.OrdConnected :=
    fun h ↦ h₃ (h.out h₁ h₂ ⟨by decide, by decide⟩)
  cases d
  case det₂ => exact iff_of_false (gap (by decide) (by decide) (by decide)) (by decide)
  case det₂Number => exact iff_of_false (gap (by decide) (by decide) (by decide)) (by decide)
  all_goals exact iff_of_true (by unfold Diagnostic.span; infer_instance) (by decide)

/-- A feature of the most grammaticalized stage that holds over a contiguous span is never lost
once gained. -/
theorem isUpperSet_span_of_top_mem {d : Diagnostic} (hd : d.span.OrdConnected)
    (h : ⊤ ∈ d.span) : IsUpperSet d.span :=
  fun _ _ hab ha ↦ hd.out ha h ⟨hab, le_top⟩

/-- A feature of the most lexical stage that holds over a contiguous span is never regained once
lost. -/
theorem isLowerSet_span_of_bot_mem {d : Diagnostic} (hd : d.span.OrdConnected)
    (h : ⊥ ∈ d.span) : IsLowerSet d.span :=
  fun _ _ hba ha ↦ hd.out h ha ⟨bot_le, hba⟩

/-- Number agreement between the nouns is transient, arising with the evaluative binominal and
already weakened at the next stage. -/
theorem strictAgreement_span : Diagnostic.strictAgreement.span = {.evaluative} :=
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
  /-- Whether the noun has pseudo-partitive uses, as in *a hell of microwaves*. -/
  pseudoPartitive : Bool
  /-- The orthographically reduced form of [N₁ *of a*], if there is one. -/
  fused : Option String := none
  deriving DecidableEq

namespace Noun

/-- The case-study noun *hell* is attested at every stage and fuses to *helluva*. -/
def hell : Noun := ⟨.abstract, Finset.univ, true, some "helluva"⟩

/-- The case-study noun *beast* is attested at every stage and has no pseudo-partitive uses. -/
def beast : Noun := ⟨.animate, Finset.univ, false, none⟩

/-- The case-study noun *cake* is attested up to the evaluative modifier. -/
def cake : Noun :=
  ⟨.inanimate, {.nPP, .headClassifier, .evaluative, .evaluativeModifier}, true, none⟩

/-- The noun *whale* is attested at every stage and fuses to *whaleuva*. -/
def whale : Noun := ⟨.animate, Finset.univ, false, some "whaleuva"⟩

/-- The noun *bitch* is attested at every stage, at the intensifier by a single token. -/
def bitch : Noun := ⟨.abstract, Finset.univ, false, none⟩

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

/-- A first noun attested at a stage is attested at every earlier stage. -/
theorem isLowerSet_stages : ∀ n ∈ Noun.all, IsLowerSet (n.stages : Set Stage) := by
  simp only [IsLowerSet, Finset.mem_coe]; decide

/-- Every inanimate first noun develops pseudo-partitive uses. -/
theorem pseudoPartitive_of_inanimate :
    ∀ n ∈ Noun.all, n.semanticClass = .inanimate → n.pseudoPartitive := by decide

/-- The animate and abstract nouns with pseudo-partitive uses are *snake* and *hell*. -/
theorem pseudoPartitive_iff :
    ∀ n ∈ Noun.all, n.pseudoPartitive ↔
      n.semanticClass = .inanimate ∨ n = .snake ∨ n = .hell := by decide

/-- A first noun has a reduced form only if it reaches a stage at which [N₁ *of a*] is a unit. -/
theorem exists_mem_chunk_of_fused :
    ∀ n ∈ Noun.all, n.fused.isSome → ∃ s ∈ n.stages, s ∈ Diagnostic.chunk.span := by decide

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
      [{ filler := .open_ .DET }, { filler := .open_ .NOUN }, { filler := .fixed "of" },
       { filler := .open_ .ADJ }, { filler := .open_ .NOUN, isHead := true }], (), false⟩

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
from each stage to the phrase whose modifier shares its function (*a book of poetry* and *a
poetry book*, *her round moon of a face* and *her moon-like face*). -/
def network : Constructicon Unit where
  constructions := Stage.path.map Stage.construction ++ [simpleNP, adjectivePhrase]
  links :=
    [ link nPP.construction headClassifier.construction .metaphorical "N₁ heads"
    , link headClassifier.construction evaluative.construction .metaphorical
        "descriptive content of N₁"
    , link evaluative.construction evaluativeModifier.construction .metaphorical "N₁ evaluates"
    , link evaluativeModifier.construction binominalIntensifier.construction .metaphorical
        "[N₁ of a] is a chunk"
    , link headClassifier.construction simpleNP .polysemy "classifying modifier"
    , link evaluative.construction simpleNP .polysemy "N₁ denotes an attribute"
    , link evaluativeModifier.construction simpleNP .polysemy "evaluative premodifier"
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
