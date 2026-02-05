/-
# Exclusive Particles: *just* vs *only*

Empirical data on the discourse particle *just* and its contrast with *only*,
following Deo & Thomas (2025). *Just* has at least 7 distinct interpretive
"flavors" that emerge from context, but only the complement-exclusion and
rank-order uses are shared with *only*.

## Core observations (Deo & Thomas 2025: §2.8)

1. **No commonly shared CQ**: *just* does not require the CQ to be shared
   between interlocutors (unlike standard analyses of *only*)
2. **Non-standard alternatives**: *just*'s alternatives are not reducible to
   Roothian focus alternatives (e.g., granularity levels, causal explanations)
3. **Mirativity**: across all uses, *just* conveys deviation from expectations

## The unified analysis

*Just* signals that the speaker is addressing the **widest answerable construal**
of an underspecified question (UQ). The 7 flavors arise from how the widest
construal is determined:

- (37a) Widest construal exists and is answerable → complement-exclusion, rank-order,
  precisifying, emphatic
- (37b) Wider construals exist but fail Quality → unexplanatory, minimal sufficiency
- (37c) Wider construals exist but fail Relevance → unelaboratory

## References

- Deo, A. & Thomas, W. (2025). Addressing the widest answerable question:
  English "just" as a domain widening strategy.
- Coppock, E. & Beaver, D. (2014). Principles of the exclusive muddle.
- Beaver, D. & Clark, B. (2008). Sense and Sensitivity.
- Wiegand, M. (2018). Exclusive morphemes.
- Beltrama, A. (2021). Just perfect, These people are amazing.
- Warstadt, A. (2020). On the role of discourse particles.
- Thomas, W. & Deo, A. (2020). Approximative uses of just.
-/

namespace Phenomena.Focus.Exclusives

-- ============================================================================
-- Flavors of *just*
-- ============================================================================

/-- The 7 interpretive flavors of *just* (Deo & Thomas 2025: §2). -/
inductive JustFlavor where
  | complementExclusion  -- "She just went to Spain and Portugal" → nowhere else
  | rankOrder            -- "She is just an intern" → nothing higher on scale
  | emphatic             -- "The food was just amazing!" → exceeds expectations
  | precisifyingEquality -- "The tank is just full" → exactly (= paraphrase)
  | precisifyingProximity -- "Fafen is just older than Siri" → barely (≈ slightly)
  | minimalSufficiency   -- "Just a 3.5 GPA is sufficient" → nothing less needed
  | unexplanatory        -- "The lamp just broke" → no identifiable cause
  | unelaboratory        -- "Fido is just a dog" → no further elaboration needed
  | counterexpectational -- "She just ate the communion wafer!" → norm violation
  deriving Repr, DecidableEq, BEq

/-- Why the widest answerable construal is optimal at context.
    Corresponds to Deo & Thomas (2025: (37a-c)). -/
inductive ContextType where
  | answerable  -- (37a): widest construal is answerable (Quality + Relevance)
  | qualityFail -- (37b): wider construals fail Quality (speaker lacks evidence)
  | relevanceFail -- (37c): wider construals fail Relevance (not discourse-relevant)
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Data structures
-- ============================================================================

/-- Datum for a *just* example with flavor classification. -/
structure JustDatum where
  sentence : String
  flavor : JustFlavor
  /-- Can *only* be felicitously substituted? -/
  onlyOk : Bool
  /-- Which context type from (37) -/
  contextType : ContextType
  /-- The relevant QUD / underspecified question -/
  qud : String := ""
  /-- The inference triggered -/
  inference : String := ""
  deriving Repr

-- ============================================================================
-- §2.1 Complement exclusion (shared with *only*)
-- ============================================================================

def complementExclusion_vacation : JustDatum :=
  { sentence := "She just/only went to Spain and Portugal"
  , flavor := .complementExclusion
  , onlyOk := true
  , contextType := .answerable
  , qud := "Where did Mary go for her vacation this year?"
  , inference := "Mary did not go to any country other than Spain and Portugal" }

-- ============================================================================
-- §2.1 Rank order (shared with *only*)
-- ============================================================================

def rankOrder_intern : JustDatum :=
  { sentence := "She is only/just an intern"
  , flavor := .rankOrder
  , onlyOk := true
  , contextType := .answerable
  , qud := "What is Mary's job at the hospital?"
  , inference := "Mary is nothing more senior than an intern" }

-- ============================================================================
-- §2.2 Emphatic (*just* only, NOT *only*)
-- ============================================================================

def emphatic_amazing : JustDatum :=
  { sentence := "The food was just/#only amazing!"
  , flavor := .emphatic
  , onlyOk := false
  , contextType := .answerable
  , qud := "How good was the food?"
  , inference := "The degree of goodness exceeds contextual expectations" }

def emphatic_enormous : JustDatum :=
  { sentence := "The Empire State Building is just/#only gigantic!"
  , flavor := .emphatic
  , onlyOk := false
  , contextType := .answerable
  , qud := "How big is the Empire State Building?"
  , inference := "The size exceeds what the speaker expected to be relevant" }

-- ============================================================================
-- §2.3 Precisifying (*just* only, NOT *only*)
-- ============================================================================

def precisifying_eq_full : JustDatum :=
  { sentence := "The tank is just/#only full"
  , flavor := .precisifyingEquality
  , onlyOk := false
  , contextType := .answerable
  , qud := "How full is the tank?"
  , inference := "The tank is full at the highest level of precision (= exactly full)" }

def precisifying_prox_older : JustDatum :=
  { sentence := "Fafen is just/#only older than Siri"
  , flavor := .precisifyingProximity
  , onlyOk := false
  , contextType := .answerable
  , qud := "How much older than Siri is Fafen?"
  , inference := "Fafen is older by the smallest relevant amount (≈ barely/slightly)" }

def precisifying_temporal : JustDatum :=
  { sentence := "My sister just/#only got here"
  , flavor := .precisifyingProximity
  , onlyOk := false
  , contextType := .answerable
  , qud := "When did your sister get here?"
  , inference := "The arrival was at the finest temporal granularity (= just now)" }

-- ============================================================================
-- §2.4 Minimal sufficiency (*just* only, NOT *only*)
-- ============================================================================

def minSuff_cat : JustDatum :=
  { sentence := "Just/#only one cat will make Patrick happy"
  , flavor := .minimalSufficiency
  , onlyOk := false
  , contextType := .answerable
  , qud := "What is sufficient for Patrick to be happy?"
  , inference := "One cat is causally sufficient; nothing less is needed" }

def minSuff_gpa : JustDatum :=
  { sentence := "Just/#only a 3.5 GPA is sufficient for Jason to stay in the program"
  , flavor := .minimalSufficiency
  , onlyOk := false
  , contextType := .answerable
  , qud := "What GPA is sufficient to stay in the program?"
  , inference := "3.5 is the minimum sufficient GPA; nothing less works" }

-- ============================================================================
-- §2.5 Unexplanatory (*just* only, NOT *only*)
-- ============================================================================

def unexplanatory_lamp : JustDatum :=
  { sentence := "I was sitting there and the lamp just/#only broke!"
  , flavor := .unexplanatory
  , onlyOk := false
  , contextType := .qualityFail
  , qud := "Why is the lamp broken?"
  , inference := "The speaker can identify no explanation for the lamp's breaking" }

def unexplanatory_mangoes : JustDatum :=
  { sentence := "I just/#only had extra mangoes"
  , flavor := .unexplanatory
  , onlyOk := false
  , contextType := .qualityFail
  , qud := "Why did you make mango-mousse cake?"
  , inference := "There is no stronger explanation than having extra mangoes" }

-- ============================================================================
-- §2.6 Unelaboratory (*just* only, NOT *only*)
-- ============================================================================

def unelaboratory_dog : JustDatum :=
  { sentence := "Fido is just/#only a dog"
  , flavor := .unelaboratory
  , onlyOk := false
  , contextType := .relevanceFail
  , qud := "What kind of dog is Fido?"
  , inference := "No further elaboration is needed or relevant" }

def unelaboratory_proton : JustDatum :=
  { sentence := "A proton is just/#only a hydrogen atom without an electron"
  , flavor := .unelaboratory
  , onlyOk := false
  , contextType := .relevanceFail
  , qud := "What is a proton?"
  , inference := "No more elaboration is needed to define a proton" }

def unelaboratory_mad : JustDatum :=
  { sentence := "I am just/#only mad"
  , flavor := .unelaboratory
  , onlyOk := false
  , contextType := .relevanceFail
  , qud := "Why are you mad?"
  , inference := "The speaker is not mad at anyone in particular" }

-- ============================================================================
-- §2.7 Counterexpectational (*just* only, NOT *only*)
-- ============================================================================

def counterexp_texting : JustDatum :=
  { sentence := "He started seeing an ex-girlfriend and just/#only stopped texting me"
  , flavor := .counterexpectational
  , onlyOk := false
  , contextType := .answerable
  , qud := "What happened to your relationship?"
  , inference := "The subject referent failed to adhere to norms" }

def counterexp_wafer : JustDatum :=
  { sentence := "The priest gave Charlotte her communion wafer and she just/#only ate it!"
  , flavor := .counterexpectational
  , onlyOk := false
  , contextType := .answerable
  , qud := "What happened at the church?"
  , inference := "Charlotte behaved in a way inconsistent with Catholic norms" }

-- ============================================================================
-- Collected data
-- ============================================================================

/-- All *just* examples from the paper. -/
def allJustData : List JustDatum :=
  [ complementExclusion_vacation, rankOrder_intern
  , emphatic_amazing, emphatic_enormous
  , precisifying_eq_full, precisifying_prox_older, precisifying_temporal
  , minSuff_cat, minSuff_gpa
  , unexplanatory_lamp, unexplanatory_mangoes
  , unelaboratory_dog, unelaboratory_proton, unelaboratory_mad
  , counterexp_texting, counterexp_wafer ]

-- ============================================================================
-- Key empirical generalizations
-- ============================================================================

/-- *Only* can substitute for *just* only in complement-exclusion and rank-order uses. -/
theorem only_substitutes_iff_exclusive :
    complementExclusion_vacation.onlyOk = true ∧
    rankOrder_intern.onlyOk = true ∧
    emphatic_amazing.onlyOk = false ∧
    precisifying_eq_full.onlyOk = false ∧
    minSuff_cat.onlyOk = false ∧
    unexplanatory_lamp.onlyOk = false ∧
    unelaboratory_dog.onlyOk = false ∧
    counterexp_texting.onlyOk = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unexplanatory uses arise when wider construals fail Quality. -/
theorem unexplanatory_is_quality_fail :
    unexplanatory_lamp.contextType = .qualityFail ∧
    unexplanatory_mangoes.contextType = .qualityFail := ⟨rfl, rfl⟩

/-- Unelaboratory uses arise when wider construals fail Relevance. -/
theorem unelaboratory_is_relevance_fail :
    unelaboratory_dog.contextType = .relevanceFail ∧
    unelaboratory_proton.contextType = .relevanceFail := ⟨rfl, rfl⟩

/-- The complement-exclusion, rank-order, emphatic, precisifying, and
    counterexpectational uses all arise when the widest construal IS answerable. -/
theorem standard_uses_are_answerable :
    complementExclusion_vacation.contextType = .answerable ∧
    rankOrder_intern.contextType = .answerable ∧
    emphatic_amazing.contextType = .answerable ∧
    precisifying_eq_full.contextType = .answerable ∧
    counterexp_texting.contextType = .answerable := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Emphatic *just* requires extreme adjectives (Morzycki 2012).
    With non-extreme adjectives, *just* gets complement-exclusion instead.

    "The food was just amazing" → emphatic (amazing is extreme)
    "The soup was just tasty" → complement-exclusion (tasty is NOT extreme)
    i.e. "The soup was no more than tasty" -/
structure EmphatiConstraint where
  sentence : String
  adjIsExtreme : Bool
  reading : JustFlavor
  deriving Repr

def emphatic_extreme : EmphatiConstraint :=
  { sentence := "The food was just amazing"
  , adjIsExtreme := true
  , reading := .emphatic }

def nonextreme_gets_exclusion : EmphatiConstraint :=
  { sentence := "The soup was just tasty"
  , adjIsExtreme := false
  , reading := .complementExclusion }

/-- Extreme adjectives never combine with imprecision markers.
    This is why emphatic *just* ≠ precisifying *just*. -/
structure ImprecisionTest where
  sentence : String
  felicitous : Bool
  deriving Repr

def extreme_no_roughly : ImprecisionTest :=
  { sentence := "#Roughly speaking, this soup is amazing"
  , felicitous := false }

def maxstd_roughly_ok : ImprecisionTest :=
  { sentence := "Roughly speaking, this tank is full"
  , felicitous := true }

/-- Emphatic reading blocked when endpoint is objective. -/
def no_emphatic_objective_closed : ImprecisionTest :=
  { sentence := "#The door is just [closed]F!"
  , felicitous := false }

def no_emphatic_objective_full : ImprecisionTest :=
  { sentence := "#The tank is just [full]F!"
  , felicitous := false }

end Phenomena.Focus.Exclusives
