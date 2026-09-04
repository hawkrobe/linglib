import Linglib.Syntax.Minimalist.Linearization.Chain

/-!
# Citko and Gračanin-Yuksek (2025): Economy in PF reduction

[citko-gracanin-yuksek-2025] argue that economy chooses between the two mechanisms of PF
reduction, multidominance and ellipsis: among the derivations that yield the same string and the
same interpretation and violate no independent principle, the one with the fewest lexical
resources and operations wins. A coordinated wh-question (*What and when should you teach?*)
keeps each wh-phrase in its own conjunct, the conjuncts sharing their heads but not their
phrases. Building two clauses and eliding one costs more lexical items and an ellipsis; sharing
the whole C′ is cheaper still, but sends both wh-phrases through one vP edge, which the ban on
multiple wh-fronting excludes in English. A coordinated sluice (*I forgot what and when*) does
share the C′: both conjuncts must be reduced, so an ellipsis is unavoidable, and one [E] on the
shared C elides the shared TP once, at the price of a vP edge with two wh-specifiers. The ban on
multiple wh-fronting is therefore restated at PF as an asterisk on a phase edge with several
wh-specifiers, parameterised by edge: the elided vP edge is harmless, and multiple sluicing
divides speakers by whether the surviving CP edge counts.

Pronunciation Economy bans ellipsis with no effect on pronunciation. It excludes the sluice with
the coordinated-question shape, where one shared [E] complementizer has two TP complements and
the second deletion silences nothing new, and it forces the nonpaired sluice to carry two
complementizers, only one bearing [E]. In right node raising the same economy prefers sharing
the pivot to building it twice and, when the verbs match, sharing the verb phrase to eliding it.

Each candidate is a planar object of `Linearization/Chain.lean`: a token at two positions is
shared, a moved wh-phrase leaves indexed traces at the vP edge and its base position, and the
coordinator is left out, so a string is its conjuncts' words. The predictions decide: the
pronounced strings, the unbound traces that carry the paired reading, the asterisks, and the
costs the winners beat.

## References

* [B. Citko and M. Gračanin-Yuksek, *Economy in PF reduction* (2025)][citko-gracanin-yuksek-2025]
* [J. Merchant, *The Syntax of Silence* (2001)][merchant-2001]
* [Z. Belk, A. Neeleman and J. Philip, *What divides, and what unites, right-node raising*
  (2023)][belk-neeleman-philip-2023]
-/

namespace CitkoGracaninYuksek2025

open Minimalist RoseTree RoseTree.Pathed
open Syntax.Question (MWFParameter)

/-! ### The lexicon -/

/-- A token: a category, its selection, its form, and the wh and [E] features. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false)
    (ellipsis : Bool := false) : LIToken :=
  ⟨LexicalItem.simple cat sel phon wh ellipsis, id⟩

def what := tok 1 .D (phon := "what") (wh := true)
def when := tok 2 .P (phon := "when") (wh := true)
def who := tok 3 .D (phon := "who") (wh := true)
def you := tok 4 .D (phon := "you")
def T := tok 5 .T [.v]
def v := tok 6 .v [.V]
def teach := tok 7 .V [.D] "teach"
def should := tok 8 .C [.T] "should"
def will := tok 9 .C [.T] "will"
/-- The null complementizer, and a second one. -/
def c := tok 10 .C [.T]
def c' := tok 11 .C [.T]
/-- The null complementizer bearing [E], and a second one. -/
def cE := tok 12 .C [.T] (ellipsis := true)
def cE' := tok 13 .C [.T] (ellipsis := true)
/-- The tokens a second, separately built clause draws. -/
def you' := tok 14 .D (phon := "you")
def T' := tok 15 .T [.v]
def v' := tok 16 .v [.V]
def teach' := tok 17 .V [.D] "teach"
/-- The auxiliary in T. -/
def shouldT := tok 18 .T [.v] "should"
def it := tok 19 .D (phon := "it")
def saw := tok 20 .V [.D] "saw"

/-! ### The candidate objects -/

/-- `[CP wh [C′ c [TP subj [T′ T [vP wh [v′ v VP]]]]]]`: the wh-phrase moved through the edge of
vP. -/
def clause (wh c subj T v : LIToken) (VP : RoseTree ChainLabel) : RoseTree ChainLabel :=
  nodeC (leafC wh) (nodeC (leafC c)
    (nodeC (leafC subj) (nodeC (leafC T) (nodeC (traceC wh) (nodeC (leafC v) VP)))))

/-- Non-bulk sharing under the complementizers `c₁` and `c₂`: each wh-phrase in its own
conjunct, the subject, T, v and verb shared ((10b), (14), (16b), (38d), (45b), (46b)). -/
def nonBulk (c₁ c₂ : LIToken) : RoseTree ChainLabel :=
  nodeC (clause what c₁ you T v (nodeC (leafC teach) (traceC what)))
    (clause when c₂ you T v (nodeC (leafC teach) (traceC when)))

/-- Bulk sharing: one C′ under both wh-phrases, both of which moved through its vP edge ((12b),
(20b)). -/
def bulk (c : LIToken) : RoseTree ChainLabel :=
  let c' := nodeC (leafC c) (nodeC (leafC you) (nodeC (leafC T) (nodeC (traceC what)
    (nodeC (traceC when)
      (nodeC (leafC v) (nodeC (nodeC (leafC teach) (traceC what)) (traceC when)))))))
  nodeC (nodeC (leafC what) c') (nodeC (leafC when) c')

/-- Footnote 21's alternative to `bulk`: a shared TP under two complementizers. -/
def bulkTP (c₁ c₂ : LIToken) : RoseTree ChainLabel :=
  let tp := nodeC (leafC you) (nodeC (leafC T) (nodeC (traceC what)
    (nodeC (traceC when)
      (nodeC (leafC v) (nodeC (nodeC (leafC teach) (traceC what)) (traceC when))))))
  nodeC (nodeC (leafC what) (nodeC (leafC c₁) tp)) (nodeC (leafC when) (nodeC (leafC c₂) tp))

/-- Two clauses from separate tokens, the first elided under its [E] complementizer with its
auxiliary in T, as the Sluicing-COMP generalization requires of a sluice: the ellipsis analysis
of the coordinated wh-question (11b). -/
def cwhEllipsis : RoseTree ChainLabel :=
  nodeC (nodeC (leafC what) (nodeC (leafC cE) (nodeC (leafC you) (nodeC (leafC shouldT)
      (nodeC (traceC what) (nodeC (leafC v) (nodeC (leafC teach) (traceC what))))))))
    (clause when should you' T' v' (nodeC (leafC teach') (traceC when)))

/-- Two clauses from separate tokens, both elided, the second's object the pronoun of vehicle
change: the double-ellipsis analysis of the coordinated sluice (19b). -/
def csEllipsis : RoseTree ChainLabel :=
  nodeC (clause what cE you T v (nodeC (leafC teach) (traceC what)))
    (clause when cE' you' T' v' (nodeC (nodeC (leafC teach') (leafC it)) (traceC when)))

/-- A multiple question, both wh-phrases fronted through the vP edge: (28b), and the multiple
sluice (29b) under an [E] complementizer. -/
def multipleQuestion (c : LIToken) : RoseTree ChainLabel :=
  nodeC (leafC who) (nodeC (leafC what) (nodeC (leafC c) (nodeC (traceC who) (nodeC (leafC T)
    (nodeC (traceC who)
      (nodeC (traceC what) (nodeC (leafC v) (nodeC (leafC saw) (traceC what)))))))))

/-- The coordinated wh-question (10b), its complementizer shared. -/
abbrev cwh := nonBulk should should
/-- Its bulk-sharing rival (12b). -/
abbrev cwhBulk := bulk should
/-- Its rival with a null complementizer in the first conjunct (14). -/
abbrev cwhNullC := nonBulk c should
/-- Footnote 15: the null complementizer in the second conjunct instead. -/
abbrev cwhNullCSecond := nonBulk should c
/-- The embedded coordinated wh-question (15a) with its null complementizer shared, and with two
(15b). -/
abbrev cwhEmbedded := nonBulk c c
abbrev cwhEmbeddedTwoC := nonBulk c c'
/-- Two pronounced complementizers (16b). -/
abbrev cwhTwoAux := nonBulk should will
/-- The coordinated sluice (20b), (26b), (38b). -/
abbrev cs := bulk cE
/-- Its rival with two [E] complementizers over a shared TP (footnote 21). -/
abbrev csTwoC := bulkTP cE cE'
/-- The coordinated sluice with the shape of the coordinated wh-question, one shared [E]
complementizer over two TPs ((38d), (45c)). -/
abbrev csSharedC := nonBulk cE cE
/-- Two [E] complementizers (45b). -/
abbrev csnrTwoE := nonBulk cE cE'
/-- The nonpaired coordinated sluice (46b): two complementizers, one bearing [E]. -/
abbrev csnr := nonBulk cE c

/-- The paired reading: the second conjunct holds an unbound trace of the first conjunct's
wh-phrase, the copy that vehicle change reads as an E-type pronoun (footnote 20). -/
def Paired (t : RoseTree ChainLabel) : Prop :=
  ∃ x ∈ unboundTraces t, x.2 = what ∧ x.1.head? = some 1

instance : DecidablePred Paired := λ _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ### The multiple-wh-fronting parameter (27) by language -/

/-- English variety A: the asterisk lands on both phase edges, so multiple sluicing crashes. -/
def englishA : MWFParameter := .nonFrontsBothEdges
/-- English variety B: the asterisk lands on the vP edge only, so multiple sluicing converges. -/
def englishB : MWFParameter := .nonFrontsVPOnly
/-- German and Greek: no multiple wh-fronting (30), multiple sluicing (31). -/
def german : MWFParameter := .nonFrontsVPOnly
def greek : MWFParameter := .nonFrontsVPOnly
def bulgarian : MWFParameter := .fronts
def romanian : MWFParameter := .fronts

/-! ### Coordinated wh-questions (§3.1) -/

theorem cwh_pf : pfPhon cwh = ["what", "when", "should", "you", "teach"] := by decide
theorem cwhEllipsis_pf : pfPhon cwhEllipsis = pfPhon cwh := by decide
theorem cwhBulk_pf : pfPhon cwhBulk = pfPhon cwh := by decide
theorem cwhNullC_pf : pfPhon cwhNullC = pfPhon cwh := by decide
/-- Footnote 15: a pronounced complementizer in the first conjunct only precedes the second
wh-phrase. -/
theorem cwhNullCSecond_pf : pfPhon cwhNullCSecond = ["what", "should", "when", "you", "teach"] := by
  decide
theorem cwhTwoAux_pf : pfPhon cwhTwoAux = ["what", "should", "when", "will", "you", "teach"] := by
  decide

/-- Each wh-phrase is interpreted in its own conjunct. -/
theorem cwh_nonpaired : unboundTraces cwh = [] := by decide
/-- The shared C′ carries a copy of each wh-phrase into the other conjunct. -/
theorem cwhBulk_paired : Paired cwhBulk := by decide

theorem cwh_beats_ellipsis : strictlyMoreEconomical (planarCost cwh) (planarCost cwhEllipsis) := by
  decide
theorem cwhBulk_beats_cwh : strictlyMoreEconomical (planarCost cwhBulk) (planarCost cwh) := by
  decide
/-- The null complementizer of (14) adds structure and nothing to pronunciation. -/
theorem cwh_beats_nullC : strictlyMoreEconomical (planarCost cwh) (planarCost cwhNullC) := by decide
theorem cwhEmbedded_beats_twoC :
    strictlyMoreEconomical (planarCost cwhEmbedded) (planarCost cwhEmbeddedTwoC) := by decide

/-- The shared C′ sends both wh-phrases through one vP edge, asterisked in English and
pronounced. -/
theorem cwhBulk_crashes : ¬ Converges cwhBulk englishA ∧ ¬ Converges cwhBulk englishB := by decide
/-- Footnote 14: in a multiple-wh-fronting language the same object converges. -/
theorem cwhBulk_converges_romanian : Converges cwhBulk romanian := by decide
theorem cwh_converges : Converges cwh englishA ∧ Converges cwh englishB := by decide

/-! ### Coordinated sluices (§3.2) -/

theorem cs_pf : pfPhon cs = ["what", "when"] := by decide
theorem csEllipsis_pf : pfPhon csEllipsis = pfPhon cs := by decide
theorem cs_paired : Paired cs := by decide
theorem cs_beats_ellipsis : strictlyMoreEconomical (planarCost cs) (planarCost csEllipsis) := by
  decide
theorem cs_beats_twoC : strictlyMoreEconomical (planarCost cs) (planarCost csTwoC) := by decide

/-- The shared vP edge hosts two wh-specifiers: the asterisk of (26b). -/
theorem cs_asterisked :
    ∃ p ∈ vertices cs, IsAsterisked cs englishA p ∧ IsAsterisked cs englishB p := by decide
/-- Elided, the asterisked edge never reaches PF. -/
theorem cs_converges : Converges cs englishA ∧ Converges cs englishB := by decide

/-- A multiple question crashes in English and converges in Bulgarian. -/
theorem multipleQuestion_crashes :
    ¬ Converges (multipleQuestion c) englishA ∧ ¬ Converges (multipleQuestion c) englishB := by
  decide
theorem multipleQuestion_converges_bulgarian : Converges (multipleQuestion c) bulgarian := by decide
/-- Multiple sluicing elides the vP edge but not the CP edge: variety B, German and Greek
converge, variety A does not. -/
theorem multipleSluicing :
    Converges (multipleQuestion cE) englishB ∧ Converges (multipleQuestion cE) german ∧
      Converges (multipleQuestion cE) greek ∧ ¬ Converges (multipleQuestion cE) englishA := by
  decide

/-! ### Pronunciation Economy (§5, §6.1) -/

/-- One shared [E] complementizer over two TPs: the second deletion silences nothing new. -/
theorem csSharedC_vacuous : ¬ PronunciationEconomy csSharedC := by decide
theorem csSharedC_pf : pfPhon csSharedC = pfPhon cs := by decide
theorem csSharedC_nonpaired : ¬ Paired csSharedC := by decide
theorem cs_economy : PronunciationEconomy cs ∧ PronunciationEconomy csEllipsis := by decide

theorem csnr_pf : pfPhon csnr = pfPhon cs := by decide
theorem csnr_economy : PronunciationEconomy csnr ∧ ¬ Paired csnr := by decide
/-- Two [E] complementizers over shared material elide it twice. -/
theorem csnrTwoE_vacuous : ¬ PronunciationEconomy csnrTwoE := by decide
theorem csnr_beats_twoE : strictlyMoreEconomical (planarCost csnr) (planarCost csnrTwoE) := by
  decide
/-- The nonpaired sluice is the cheapest nonpaired object respecting Pronunciation Economy: the
shared [E] complementizer of (45c) draws one token fewer but elides vacuously. -/
theorem csnr_optimal : ∀ t ∈ [csSharedC, csnrTwoE],
    strictlyMoreEconomical (planarCost csnr) (planarCost t) ∨ ¬ PronunciationEconomy t := by decide
/-- Footnote 30: the verb, shared, occurs in the second conjunct outside the elided TP and is
silenced all the same, so the object cannot surface as a coordinated wh-question. -/
theorem csnr_silences_shared :
    (∃ p ∈ occurrences csnr teach, ∀ K ∈ elidedDomains csnr, ¬ K <+: p) ∧
      IsSilenced csnr teach := by decide

/-! ### Right node raising (§6.2) -/

def alice := tok 21 .D (phon := "Alice")
def iris := tok 22 .D (phon := "Iris")
def must := tok 23 .T [.V] "must"
/-- `must` bearing [E]. -/
def mustE := tok 24 .T [.V] "must" (ellipsis := true)
def oughtToBe := tok 25 .T [.V] "ought to be"
def shouldRNR := tok 26 .T [.V] "should"
def work := tok 27 .V [.P] "work"
def working := tok 28 .V [.P] "working"
def on := tok 29 .P [.N] "on"
def different := tok 30 .A (phon := "different")
def topics := tok 31 .N (phon := "topics")
def on' := tok 32 .P [.N] "on"
def different' := tok 33 .A (phon := "different")
def topics' := tok 34 .N (phon := "topics")

/-- The pivot, `on different topics`. -/
def pivot : RoseTree ChainLabel := nodeC (leafC on) (nodeC (leafC different) (leafC topics))

/-- `[TP subj [T′ T VP]]`. -/
def tp (subj T : LIToken) (VP : RoseTree ChainLabel) : RoseTree ChainLabel :=
  nodeC (leafC subj) (nodeC (leafC T) VP)

/-- (53b), after the pruning of [belk-neeleman-philip-2023] that removes the shared pivot from
the first conjunct: the first verb phrase, the bare verb, elided under [E] on `must`. -/
def rnrMixed : RoseTree ChainLabel :=
  nodeC (tp alice mustE (leafC work)) (tp iris oughtToBe (nodeC (leafC working) pivot))
/-- (54): the first verb phrase built with its own pivot and elided. -/
def rnrElided : RoseTree ChainLabel :=
  nodeC
    (tp alice mustE
      (nodeC (leafC work) (nodeC (leafC on') (nodeC (leafC different') (leafC topics')))))
    (tp iris oughtToBe (nodeC (leafC working) pivot))
/-- (55b): with matching verbs, the verb phrase shared. -/
def rnrShared : RoseTree ChainLabel :=
  let VP := nodeC (leafC work) pivot
  nodeC (tp alice must VP) (tp iris shouldRNR VP)
/-- The rival of (55b) with the shape of (53b). -/
def rnrMatchedMixed : RoseTree ChainLabel :=
  nodeC (tp alice mustE (leafC work)) (tp iris shouldRNR (nodeC (leafC working) pivot))

theorem rnrMixed_pf : pfPhon rnrMixed =
    ["Alice", "must", "Iris", "ought to be", "working", "on", "different", "topics"] := by decide
theorem rnrElided_pf : pfPhon rnrElided = pfPhon rnrMixed := by decide
theorem rnrMixed_beats_elided :
    strictlyMoreEconomical (planarCost rnrMixed) (planarCost rnrElided) := by decide

theorem rnrShared_pf : pfPhon rnrShared =
    ["Alice", "must", "Iris", "should", "work", "on", "different", "topics"] := by decide
theorem rnrShared_isShared : IsShared rnrShared work := by decide
/-- With matching verbs, ellipsis is no longer an option. -/
theorem rnrShared_beats_mixed :
    strictlyMoreEconomical (planarCost rnrShared) (planarCost rnrMatchedMixed) := by decide

end CitkoGracaninYuksek2025
