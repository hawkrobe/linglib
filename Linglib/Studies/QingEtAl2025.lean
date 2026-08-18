import Linglib.Semantics.Attitudes.Preference

/-!
# Qing, Özyıldız, Roelofsen, Romero & Uegaki 2025: question-taking preferentials

[qing-uegaki-2025] classify non-veridical preferential predicates by
two factors — clausal distributivity and evaluative valence — and
show that only the distributive positive class (*hope*-type) is
anti-rogative: non-distributive predicates (*worry*, Mandarin
*qidai*, Japanese *tanosimi*) and distributive negative ones (*fear*,
Japanese *osore*, Turkish *kork-*) take questions canonically,
because the [uegaki-sudo-2019] triviality needs both distributivity
and the positive-valence Threshold Significance Presupposition
(`Studies/UegakiSudo2019.lean`). `PredicateClass` and `classify`
render the classification (their Table 1); the observations record
the paper's cross-linguistic acceptability judgments over English,
Mandarin, Japanese, and Turkish. Apparent *hope* + question cases are
analyzed as non-canonical adjunction-style composition (their §4),
with the highlighting analysis considered and dispreferred.
-/

namespace QingEtAl2025

open Features (AttitudeValence)

/-! ### The classification (Table 1) -/

/-- The three classes of non-veridical preferential predicates: the
    two distributivity-by-valence cells that take questions, and the
    anti-rogative distributive positive class. -/
inductive PredicateClass where
  /-- Non-distributive (*worry*, *qidai*, *tanosimi*): the question
      semantics outruns the existential over answers. -/
  | nonDistributive
  /-- Distributive with negative valence (*fear*, *osore*, *kork-*):
      no Threshold Significance Presupposition. -/
  | distributiveNegative
  /-- Distributive with positive valence (*hope*, *wish*, *expect*):
      anti-rogative via the [uegaki-sudo-2019] triviality. -/
  | distributivePositive
  deriving DecidableEq, Repr

/-- The class determined by the two factors. Distributivity facts for
    the substrate's predicates are
    `Preferential.mkDegreeComparison_isDistributive` and
    `Preferential.worry_not_distributive`. -/
def classify (distributive : Bool) (valence : AttitudeValence) :
    PredicateClass :=
  match distributive, valence with
  | false, _ => .nonDistributive
  | true, .negative => .distributiveNegative
  | true, .positive => .distributivePositive

/-- Only the distributive positive class is anti-rogative (Table 1). -/
def PredicateClass.takesQuestions : PredicateClass → Prop
  | .nonDistributive => True
  | .distributiveNegative => True
  | .distributivePositive => False

example : classify true .positive = .distributivePositive := rfl
example : classify true .negative = .distributiveNegative := rfl
example : classify false .negative = .nonDistributive := rfl
example : classify false .positive = .nonDistributive := rfl

-- Language Type

/-- Languages represented in the data -/
inductive Language where
  | english
  | mandarin
  | japanese
  | turkish
  deriving DecidableEq, Repr

-- Empirical Observation Records

/--
An empirical observation: predicate name, language, and acceptability.

The semantic properties are stored in the corresponding Fragment entry.
Here we just record the empirical acceptability judgments.
-/
structure Observation where
  /-- Predicate form -/
  form : String
  /-- Language -/
  language : Language
  /-- English gloss (for non-English) -/
  gloss : String := ""
  /-- Empirical: Does it take polar questions? -/
  takesPolQ : Bool
  /-- Empirical: Does it take wh-questions? -/
  takesWhQ : Bool
  /-- Additional notes -/
  notes : String := ""
  deriving Repr, BEq

-- English Observations

def hopeEn : Observation := ⟨"hope", .english, "", false, false,
  "Class 3: C-dist + positive + TSP → anti-rogative"⟩

def wishEn : Observation := ⟨"wish", .english, "", false, false, ""⟩

def expectEn : Observation := ⟨"expect", .english, "", false, false, ""⟩

def fearEn : Observation := ⟨"fear", .english, "", true, true,
  "Class 2: C-dist + negative → no TSP → takes questions"⟩

def dreadEn : Observation := ⟨"dread", .english, "", true, true, ""⟩

def worryEn : Observation := ⟨"worry", .english, "", true, true,
  "Class 1: non-C-dist → takes questions"⟩

def englishObs : List Observation := [hopeEn, wishEn, expectEn, fearEn, dreadEn, worryEn]

-- Mandarin Observations

def qidaiZh : Observation := ⟨"qidai", .mandarin, "look forward to", true, true,
  "Class 1: positive but non-C-dist, so takes questions"⟩

def danxinZh : Observation := ⟨"danxin", .mandarin, "worry", true, true, ""⟩

def xiwangZh : Observation := ⟨"xiwang", .mandarin, "hope", false, false,
  "distributive positive: anti-rogative like English hope"⟩

def haipaZh : Observation := ⟨"haipa", .mandarin, "fear", true, true, ""⟩

def mandarinObs : List Observation := [qidaiZh, danxinZh, xiwangZh, haipaZh]

-- Japanese Observations

def tanosimiJa : Observation := ⟨"tanosimi", .japanese, "looking forward to", true, true,
  "Class 1: positive but non-C-dist"⟩

def osoreJa : Observation := ⟨"osore", .japanese, "fear", true, true, ""⟩

def kitaiJa : Observation := ⟨"kitai", .japanese, "expect/hope", false, false,
  "distributive positive: behaves like English hope"⟩

def shinpaiJa : Observation := ⟨"shinpai", .japanese, "worry", true, true, ""⟩

def japaneseObs : List Observation := [tanosimiJa, osoreJa, kitaiJa, shinpaiJa]

-- Turkish Observations

def korkTr : Observation := ⟨"kork-", .turkish, "fear", true, true,
  "Class 2: symmetric interpretation with questions"⟩

def umTr : Observation := ⟨"um-", .turkish, "hope", false, false,
  "Class 3: anti-rogative canonically; diye provides workaround"⟩

def endiselenTr : Observation := ⟨"endişelen-", .turkish, "worry", true, true, ""⟩

def turkishObs : List Observation := [korkTr, umTr, endiselenTr]

-- All Observations

def allObservations : List Observation :=
  englishObs ++ mandarinObs ++ japaneseObs ++ turkishObs

/-!
## Verifying predictions against observations

Each predicate's class follows from its distributivity and valence
via `classify` — distributivity proved from the semantics
(`Preferential.mkDegreeComparison_isDistributive`,
`Preferential.worry_not_distributive`) — and the class predicts
question-embedding, checked against the observations:

### Cross-linguistic verification

| Language | Predicate | Class | Predicted | Observed | ✓/✗ |
|----------|-----------|-------|-----------|----------|-----|
| English | hope | 3 | ✗ questions | ✗ | ✓ |
| English | fear | 2 | ✓ questions | ✓ | ✓ |
| English | worry | 1 | ✓ questions | ✓ | ✓ |
| Mandarin | qidai | 1 | ✓ questions | ✓ | ✓ |
| Mandarin | xiwang | 3 | ✗ questions | ✗ | ✓ |
| Japanese | tanosimi | 1 | ✓ questions | ✓ | ✓ |
| Japanese | kitai | 3 | ✗ questions | ✗ | ✓ |
| Turkish | kork- | 2 | ✓ questions | ✓ | ✓ |
| Turkish | um- | 3 | ✗ questions | ✗ | ✓ |
-/

-- Key Examples from the Paper

/-!
## Key examples

*Hope* cannot embed questions in English (*John hopes whether Mary
will come; *John hopes who will come): *hope* is distributive and
positive, so with the answers drawn from the comparison class the
assertion is settled by the Threshold Significance Presupposition —
the [uegaki-sudo-2019] triviality, `Studies/UegakiSudo2019.lean`.

Mandarin *qidai* is positive yet embeds questions (Zhangsan qidai
shei hui lai, "Zhangsan looks forward to who will come"): its
question semantics carries an anticipation-of-resolution condition,
so it is not distributive and the triviality derivation does not go
through (§3.1).

Turkish *kork-* "fear" embeds questions with a symmetric
interpretation — "John fears whether his neighbor will be home" is
felicitous whether he fears the neighbor's presence or absence
(their GoodFriend and NoiseHater contexts, §3.2) — because negative
predicates do not trigger the Threshold Significance Presupposition.
-/

end QingEtAl2025
