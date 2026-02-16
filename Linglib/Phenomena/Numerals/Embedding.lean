/-!
# Numeral Embedding Test Cases

Theory-neutral empirical test cases for bare numerals in embedding environments
(negation, modals, attitudes, conditionals, DE contexts). These environments are
where lower-bound and bilateral numeral theories diverge most sharply.

## Key Diagnostic Environments

1. **Negation**: "John doesn't have three children" — LB predicts <3, BL predicts ≠3
2. **Modals**: "You must read three books" — □(≥3) vs □(=3)
3. **"Exactly" redundancy**: informative under LB, redundant under BL
4. **Conditionals**: "If you have three children..." — ≥3 vs =3 as trigger condition
5. **Existential scope**: embedded EXH blocked under existential quantifier

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1–44.
- Bylinina, L. & Nouwen, R. (2020). Numeral semantics. *Language and Linguistics
  Compass* 14(8).
- Nouwen, R. (2006). Remarks on the Polar Orientation of Almost.
- Coppock, E. & Beaver, D. (2014). Principles of the Exclusive Muddle.
- Solt, S. & Waldon, B. (2019). Numerals under negation. *Glossa* 4(1).
- Musolino, J. (2004). The semantics and acquisition of number words.
- Kaufmann, M. (2012). Interpreting Imperatives. Springer.
- Gajewski, J. (2007). Neg-raising and polarity.
- Meier, C. (2003). The meaning of too, enough, and so...that.
- Kiparsky, P. & Kiparsky, C. (1970). Fact.
-/

namespace Phenomena.Numerals.Embedding

-- ============================================================================
-- Types
-- ============================================================================

/-- Type of embedding environment for numeral test cases. -/
inductive EmbeddingType where
  | negation
  | modal_possibility
  | modal_necessity
  | attitude
  | conditional
  | restrictor
  | question
  | existential_scope
  | exactly_modification
  | collective
  | focus_only
  | factive
  | imperative
  | neg_raising
  | approximator
  | degree
  | convexity_test
  | acquisition
  deriving Repr, DecidableEq, BEq

/-- A theory-neutral test case for a numeral in an embedding environment.

Each datum records the sentence, what reading each theory predicts,
and (when clear) which reading speakers prefer. -/
structure NumeralEmbeddingDatum where
  sentence : String
  embedding : EmbeddingType
  numeral : Nat
  lowerBoundReading : String
  bilateralReading : String
  preferredReading : Option String
  source : String
  deriving Repr, BEq

-- ============================================================================
-- Negation
-- ============================================================================

/-- "John doesn't have three children" — the classic divergence case.
LB: has fewer than 3. BL: doesn't have exactly 3 (could have more). -/
def neg_plain : NumeralEmbeddingDatum where
  sentence := "John doesn't have three children"
  embedding := .negation
  numeral := 3
  lowerBoundReading := "John has fewer than three children"
  bilateralReading := "John doesn't have exactly three children (could have more or fewer)"
  preferredReading := some "fewer than three"
  source := "Horn 1972; Kennedy 2015 §5"

/-- Sentential negation — same divergence, more formal register. -/
def neg_sentential : NumeralEmbeddingDatum where
  sentence := "It is not the case that John has three children"
  embedding := .negation
  numeral := 3
  lowerBoundReading := "John has fewer than three children"
  bilateralReading := "John doesn't have exactly three children"
  preferredReading := some "fewer than three"
  source := "Kennedy 2015 §5"

/-- Metalinguistic negation — supports only ≠3, not <3.
"He doesn't have THREE children — he has four" is felicitous. -/
def neg_metalinguistic : NumeralEmbeddingDatum where
  sentence := "John doesn't have THREE children — he has four"
  embedding := .negation
  numeral := 3
  lowerBoundReading := "Infelicitous under LB (four > three, so 'has three' is true under LB)"
  bilateralReading := "Felicitous: he doesn't have exactly three, he has four"
  preferredReading := some "not exactly three (has four)"
  source := "Horn 1972; Kennedy 2015 §5"

-- ============================================================================
-- Modals
-- ============================================================================

/-- "You are allowed to eat two biscuits" — modal possibility.
Key interaction: EXH scope relative to modal. -/
def modal_possibility_biscuit : NumeralEmbeddingDatum where
  sentence := "You are allowed to eat two biscuits"
  embedding := .modal_possibility
  numeral := 2
  lowerBoundReading := "There is a permitted world where you eat ≥2 biscuits"
  bilateralReading := "There is a permitted world where you eat exactly 2 biscuits"
  preferredReading := some "permitted to eat exactly 2 (not more)"
  source := "Bylinina & Nouwen 2020 (35)–(36)"

/-- "You must read three books" — modal necessity.
Necessity quantifies universally over accessible worlds. -/
def modal_necessity_books : NumeralEmbeddingDatum where
  sentence := "You must read three books"
  embedding := .modal_necessity
  numeral := 3
  lowerBoundReading := "In all obligation worlds, you read ≥3 books"
  bilateralReading := "In all obligation worlds, you read exactly 3 books"
  preferredReading := some "at least three required"
  source := "Bylinina & Nouwen 2020; Kennedy 2015"

-- ============================================================================
-- "Exactly" Modification
-- ============================================================================

/-- "John has exactly three children" — redundancy test.
Informative under LB (restricts ≥3 to =3), redundant under BL (=3 already). -/
def exactly_children : NumeralEmbeddingDatum where
  sentence := "John has exactly three children"
  embedding := .exactly_modification
  numeral := 3
  lowerBoundReading := "Informative: strengthens ≥3 to =3"
  bilateralReading := "Redundant: =3 is already the bare meaning"
  preferredReading := none
  source := "Kennedy 2015 §5.2"

-- ============================================================================
-- Attitude Verbs
-- ============================================================================

/-- "John believes there are three solutions" — attitude embedding. -/
def attitude_believe : NumeralEmbeddingDatum where
  sentence := "John believes there are three solutions"
  embedding := .attitude
  numeral := 3
  lowerBoundReading := "John's belief worlds all have ≥3 solutions"
  bilateralReading := "John's belief worlds all have exactly 3 solutions"
  preferredReading := some "believes exactly three"
  source := "Bylinina & Nouwen 2020 §5"

-- ============================================================================
-- Conditionals / DE Contexts
-- ============================================================================

/-- "If you have three children, you qualify for the tax credit" —
numeral in conditional antecedent (downward-entailing context). -/
def conditional_qualify : NumeralEmbeddingDatum where
  sentence := "If you have three children, you qualify for the tax credit"
  embedding := .conditional
  numeral := 3
  lowerBoundReading := "Having ≥3 children qualifies you (4 children → qualifies)"
  bilateralReading := "Having exactly 3 children qualifies you (4 children → doesn't qualify)"
  preferredReading := some "at least three qualifies"
  source := "Kennedy 2015 §5"

/-- "Every student who read three books passed" —
numeral in restrictor of universal (downward-entailing). -/
def restrictor_universal : NumeralEmbeddingDatum where
  sentence := "Every student who read three books passed"
  embedding := .restrictor
  numeral := 3
  lowerBoundReading := "Every student who read ≥3 books passed (includes 4-book readers)"
  bilateralReading := "Every student who read exactly 3 books passed (excludes 4-book readers)"
  preferredReading := some "at least three"
  source := "Kennedy 2015 §5"

-- ============================================================================
-- Questions
-- ============================================================================

/-- "Did John read three books?" — numeral in polar question. -/
def question_books : NumeralEmbeddingDatum where
  sentence := "Did John read three books?"
  embedding := .question
  numeral := 3
  lowerBoundReading := "Did John read ≥3 books? (yes if he read 4)"
  bilateralReading := "Did John read exactly 3 books? (no if he read 4)"
  preferredReading := none
  source := "Bylinina & Nouwen 2020 §5"

-- ============================================================================
-- Existential Scope
-- ============================================================================

/-- "Some students answered three questions correctly" —
numeral embedded under existential (Bylinina & Nouwen 2020 (38)–(39)).
Embedded EXH is blocked in this environment under LB. -/
def existential_some : NumeralEmbeddingDatum where
  sentence := "Some students answered three questions correctly"
  embedding := .existential_scope
  numeral := 3
  lowerBoundReading := "Some students answered ≥3 correctly (embedded EXH blocked)"
  bilateralReading := "Some students answered exactly 3 correctly"
  preferredReading := some "at least three"
  source := "Bylinina & Nouwen 2020 (38)–(39)"

-- ============================================================================
-- Collective Predicates
-- ============================================================================

/-- "Twelve dots surround the square" — collective predicate.
Collective reading requires the group to be exactly 12. -/
def collective_dots : NumeralEmbeddingDatum where
  sentence := "Twelve dots surround the square"
  embedding := .collective
  numeral := 12
  lowerBoundReading := "≥12 dots surround the square (14 dots → true)"
  bilateralReading := "Exactly 12 dots surround the square (14 dots → false)"
  preferredReading := some "exactly twelve"
  source := "Bylinina & Nouwen 2020 §3"

-- ============================================================================
-- "Almost" / Approximators (Nouwen 2006)
-- ============================================================================

/-- "Almost three students passed" — the polar orientation diagnostic.
Under LB, "almost ≥3" admits only values below 3 (polar blocks ≥3).
Under BL, "almost =3" admits values above AND below (2 or 4).
Empirically, "almost three" means ~2, favoring LB for the polar component. -/
def almost_passed : NumeralEmbeddingDatum where
  sentence := "Almost three students passed"
  embedding := .approximator
  numeral := 3
  lowerBoundReading := "Close to ≥3 but not ≥3: approximately 2 passed (below only)"
  bilateralReading := "Close to =3 but not =3: approximately 2 or 4 passed (above or below)"
  preferredReading := some "approximately 2 (below only)"
  source := "Nouwen 2006; Penka 2006; Sadock 1981"

-- ============================================================================
-- "Only" + Focus (Coppock & Beaver 2014)
-- ============================================================================

/-- "Only three students passed" — focus particle + numeral.
Under LB, "only" is truth-conditionally informative (adds upper bound ≥3 → =3).
Under BL, "only" is truth-conditionally redundant (=3 already exact) but
contributes an evaluative scalar presupposition ("3 is low"). -/
def only_passed : NumeralEmbeddingDatum where
  sentence := "Only three students passed"
  embedding := .focus_only
  numeral := 3
  lowerBoundReading := "Informative: only(≥3) = ≥3 ∧ ¬(≥4) = exactly 3"
  bilateralReading := "Redundant: only(=3) = =3 (no stronger alternative to exclude)"
  preferredReading := none
  source := "Fox 2007; Coppock & Beaver 2014"

-- ============================================================================
-- Factive Presupposition (Kiparsky & Kiparsky 1970)
-- ============================================================================

/-- "I'm surprised that three students passed" — emotive factive.
The numeral is under a factive presupposition trigger:
LB presupposes ≥3 passed, BL presupposes =3 passed.
If 5 passed, LB presupposition is satisfied but BL is violated. -/
def factive_surprised : NumeralEmbeddingDatum where
  sentence := "I'm surprised that three students passed"
  embedding := .factive
  numeral := 3
  lowerBoundReading := "Presupposes ≥3 passed; surprise about ≥3 (5 passing consistent)"
  bilateralReading := "Presupposes =3 passed; surprise about =3 (5 passing violates presup)"
  preferredReading := some "presupposes exactly three"
  source := "Kiparsky & Kiparsky 1970; Karttunen 1971"

-- ============================================================================
-- Imperatives (Kaufmann 2012)
-- ============================================================================

/-- "Read three books!" — imperative compliance condition.
Does reading 5 books comply with the command?
Under LB: yes (5 ≥ 3). Under BL: no (5 ≠ 3). -/
def imperative_read : NumeralEmbeddingDatum where
  sentence := "Read three books!"
  embedding := .imperative
  numeral := 3
  lowerBoundReading := "Reading ≥3 satisfies the imperative (reading 5 → compliant)"
  bilateralReading := "Reading =3 satisfies the imperative (reading 5 → non-compliant)"
  preferredReading := some "reading 5 satisfies it (at least 3)"
  source := "Kaufmann 2012"

-- ============================================================================
-- Neg-Raising "doubt" (Gajewski 2007)
-- ============================================================================

/-- "I doubt that three students passed" — neg-raising verb.
"Doubt" ≈ "believe not" (neg-raising).
Under LB: think ¬(≥3) = think <3 passed.
Under BL: think ¬(=3) = think ≠3 (could think 5 passed). -/
def doubt_passed : NumeralEmbeddingDatum where
  sentence := "I doubt that three students passed"
  embedding := .neg_raising
  numeral := 3
  lowerBoundReading := "Speaker thinks <3 passed (5 passing incompatible with doubting)"
  bilateralReading := "Speaker thinks ≠3 passed (5 passing compatible with doubting)"
  preferredReading := some "thinks fewer than three"
  source := "Gajewski 2007; Horn 1978"

-- ============================================================================
-- QUD-Convexity (Solt & Waldon 2019)
-- ============================================================================

/-- "She doesn't have 40 sheep" — QUD-convexity diagnostic.
Infelicitous in neutral "how many?" context (Solt & Waldon 2019).
Under LB: ¬(≥40) = {0..39}, a convex set → predicts felicitous (wrong).
Under BL: ¬(=40) = {0..39, 41, 42, ...}, non-convex → predicts infelicitous (correct). -/
def convexity_sheep : NumeralEmbeddingDatum where
  sentence := "She doesn't have 40 sheep"
  embedding := .convexity_test
  numeral := 40
  lowerBoundReading := "¬(≥40) = <40: convex set, predicts felicitous (wrong)"
  bilateralReading := "¬(=40) = ≠40: non-convex set (gap at 40), predicts infelicitous (correct)"
  preferredReading := some "infelicitous in neutral context"
  source := "Solt & Waldon 2019"

-- ============================================================================
-- Acquisition (Musolino 2004)
-- ============================================================================

/-- "Two of the horses jumped over the fence" — child interpretation.
When 3 horses jumped, 5-year-olds reject "two horses jumped."
Under LB: 3 ≥ 2, so should be accepted (children don't compute SI).
Under BL: 3 ≠ 2, so should be rejected (exact reading is semantic).
Children reject → supports BL. -/
def acquisition_horses : NumeralEmbeddingDatum where
  sentence := "Two of the horses jumped over the fence"
  embedding := .acquisition
  numeral := 2
  lowerBoundReading := "3 ≥ 2 → should be accepted (but children reject)"
  bilateralReading := "3 ≠ 2 → should be rejected (children reject, as predicted)"
  preferredReading := some "children reject (supports bilateral)"
  source := "Musolino 2004; Papafragou & Musolino 2003"

-- ============================================================================
-- Degree "too" / "enough" (Meier 2003)
-- ============================================================================

/-- "Three students is too many" — degree construction monotonicity.
Under LB: ≥3 is too many → 4 is also too many (upward monotone).
Under BL: =3 is too many → 4 being too many is NOT entailed. -/
def degree_too_many : NumeralEmbeddingDatum where
  sentence := "Three students is too many"
  embedding := .degree
  numeral := 3
  lowerBoundReading := "≥3 is too many; entails 4 is also too many (monotonic)"
  bilateralReading := "=3 is too many; 4 being too many not entailed (non-monotonic)"
  preferredReading := some "4 is also too many (monotonic)"
  source := "Meier 2003"

-- ============================================================================
-- Data Collection
-- ============================================================================

/-- All embedding test cases. -/
def allData : List NumeralEmbeddingDatum :=
  [ neg_plain, neg_sentential, neg_metalinguistic
  , modal_possibility_biscuit, modal_necessity_books
  , exactly_children
  , attitude_believe
  , conditional_qualify, restrictor_universal
  , question_books
  , existential_some
  , collective_dots
  , almost_passed
  , only_passed
  , factive_surprised
  , imperative_read
  , doubt_passed
  , convexity_sheep
  , acquisition_horses
  , degree_too_many ]

/-- 20 test cases covering 18 embedding types. -/
theorem data_count : allData.length = 20 := by native_decide

-- ============================================================================
-- Generalizations
-- ============================================================================

/-- A generalization about numeral behavior across embedding environments. -/
structure EmbeddingGeneralization where
  name : String
  description : String
  deriving Repr, BEq

/-- Key cross-cutting generalizations from the literature. -/
def generalizations : List EmbeddingGeneralization :=
  [ { name := "Negation is the classic divergence point"
    , description := "Under negation, LB predicts <n while BL predicts ≠n. Metalinguistic negation ('not THREE — four') supports only the BL reading." }
  , { name := "\"Exactly\" redundancy test"
    , description := "\"Exactly n\" is informative under LB (strengthens ≥n to =n) but redundant under BL (=n is already the bare meaning). Kennedy (2015 §5.2) argues this favors BL." }
  , { name := "Modal scope interaction"
    , description := "EXH-over-modal and EXH-under-modal give different readings under LB. EXH(◇(≥n)) ≠ ◇(EXH(≥n)). Under BL, EXH is vacuous so scope doesn't matter for bare numerals." }
  , { name := "DE contexts reverse entailment direction"
    , description := "In isolation, BL entails LB (=n → ≥n). Under negation and other DE operators, this reverses: ¬(≥n) → ¬(=n) but not vice versa." }
  , { name := "Collective predicates favor bilateral"
    , description := "Collective predicates like 'surround' require the group to be exactly n, not at-least-n. This favors the BL reading without pragmatic enrichment." }
  , { name := "\"Almost\" polar orientation favors lower-bound"
    , description := "\"Almost n\" admits only values below n, not above. Under LB, the polar component ¬(≥n) restricts to <n (below only). Under BL, ¬(=n) admits both above and below. The empirical asymmetry (below only) favors LB (Nouwen 2006)." }
  , { name := "QUD-convexity constrains negated numerals"
    , description := "Under BL, ¬(=n) denotes a non-convex set (gap at n), predicting infelicity in neutral 'how many?' contexts. Under LB, ¬(≥n) = <n is convex, incorrectly predicting felicity (Solt & Waldon 2019)." }
  , { name := "Acquisition data supports bilateral"
    , description := "Children reject 'two horses jumped' when three jumped (Musolino 2004). Since children are poor at computing scalar implicatures, this supports BL (exact reading is semantic) over LB (exact reading requires pragmatic strengthening)." } ]

end Phenomena.Numerals.Embedding
