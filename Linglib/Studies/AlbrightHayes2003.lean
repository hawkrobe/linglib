import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Positivity
import Linglib.Data.Examples.AlbrightHayes2003
import Linglib.Fragments.English.Phonology

/-!
# Rules vs. analogy in English past tenses

[albright-hayes-2003] learn the English past tense as a set of stochastic rules. Every
stem–past pair is a word-specific rule, and minimal generalization over two rules with the same
change keeps the segments they share outward from the change site, reduces the first pair that
differ to the class of their shared features, and frees whatever lies beyond
([albright-hayes-2002] gives the full procedure). Each rule is scored by its reliability in the
lexicon, hits over scope, discounted for small scope by a lower confidence limit
([mikheev-1997]); the most reliable rules, the islands of reliability, exist for the regular
change as well as for irregular ones ([albright-2002] for Italian), and a candidate past takes
the score of its best rule. Two wug experiments ([berko-1958]) on 58 stems that the model chose
to cross islands for the regular and for an irregular past find island effects of the same size
for both, which the single default rule of the dual mechanism model ([pinker-prince-1988],
[prasada-pinker-1993]) cannot produce; the irregular effects replicate [bybee-moder-1983]. A
generalized context model ([nosofsky-1990], with [broe-1993]'s segment similarity) run on the
same lexicon misses the regular islands, follows single similar verbs, and misplaces the regular
allomorphs, because its similarity is variegated where a rule's is structured: the allomorph
depends on the final segment alone.

## Implementation notes

Minimal generalization is `mg` on the substrate's rewrite contexts, in which a leading word
boundary is the anchored word-specific rule and its absence the free variable. The paper's own
steps (6) and footnote 4, the island (8), and the regular allomorphy of (7b) are computed on
the English fragment's segments, whose meet is the featural term. Reliability is `Stats`; the
statistics reported in Tables 1 and 4 and the ratings and production probabilities of Appendix
A are rows. Vowel changes, which generalize on both sides of the change, the confidence-limit
discount, and the analogical model itself are not modelled.

## References

* [albright-hayes-2003]
* [albright-hayes-2002]
* [albright-2002]
* [berko-1958]
* [pinker-prince-1988]
* [prasada-pinker-1993]
* [bybee-moder-1983]
* [mikheev-1997]
* [nosofsky-1990]
* [broe-1993]
-/

namespace AlbrightHayes2003

open Data.Examples Phonology Subregular.LocalRewrite English.Phonology

deriving instance DecidableEq for ContextElem

/-! ### Minimal generalization -/

/-- The structural description of a past-tense rule: the stem-final material before the change
site, read left to right, a leading word boundary anchoring it to a whole stem and its absence
standing for the free variable. -/
abbrev Context := List ContextElem

/-- The word-specific rule of a stem ((3)). -/
def wordSpecific (stem : List Segment) : Context := .wordBoundary :: stem.map .seg

/-- The stem meets the description. -/
def Matches (c : Context) (stem : List Segment) : Prop := matchLeftContext c stem = true

instance (c : Context) (stem : List Segment) : Decidable (Matches c stem) :=
  inferInstanceAs (Decidable (_ = true))

/-- Generalization from the change site outward ((5)): shared segments are kept, the first pair
that differ become the class of their shared features, and everything beyond them is freed. -/
def mgRev : List ContextElem → List ContextElem → List ContextElem
  | .seg a :: as, .seg b :: bs => if a = b then .seg a :: mgRev as bs else [.seg (a ⊓ b)]
  | .wordBoundary :: _, .wordBoundary :: _ => [.wordBoundary]
  | _, _ => []

/-- The minimal generalization of two descriptions. -/
def mg (c₁ c₂ : Context) : Context := (mgRev c₁.reverse c₂.reverse).reverse

/-- The rule learned from a list of stems: each stem's word-specific rule generalized in
turn. -/
def learned : List (List Segment) → Context
  | [] => []
  | s :: ss => ss.foldl (λ c w => mg c (wordSpecific w)) (wordSpecific s)

variable {c c₁ c₂ : Context} {stem : List Segment}

private theorem matchRightContext_map_seg (l : List Segment) :
    matchRightContext (l.map .seg ++ [.wordBoundary]) l = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [matchRightContext, ih]

/-- A stem meets its own word-specific rule. -/
theorem matches_wordSpecific : Matches (wordSpecific stem) stem := by
  simp only [Matches, wordSpecific, matchLeftContext, List.reverse_cons, ← List.map_reverse]
  exact matchRightContext_map_seg _

/-- A description one segment long is met by exactly the segments it subsumes. -/
theorem matches_single_iff (k x : Segment) : Matches [.seg k] [x] ↔ k ≤ x := by
  simp [Matches, matchLeftContext, matchRightContext]

private theorem mgRev_comm (r₁ r₂ : List ContextElem) : mgRev r₁ r₂ = mgRev r₂ r₁ := by
  induction r₁ generalizing r₂ with
  | nil => cases r₂ with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  | cons a as ih => cases r₂ with
    | nil => cases a <;> rfl
    | cons b bs =>
      cases a <;> cases b <;> simp only [mgRev]
      split
      · subst_vars; simp [ih]
      · rename_i h; rw [if_neg (Ne.symm h), inf_comm]

/-- Minimal generalization is symmetric. -/
theorem mg_comm : mg c₁ c₂ = mg c₂ c₁ := by simp [mg, mgRev_comm]

private theorem matchRightContext_mgRev {r₁ r₂ : List ContextElem} {l : List Segment}
    (h : matchRightContext r₁ l = true) : matchRightContext (mgRev r₁ r₂) l = true := by
  induction r₁ generalizing r₂ l with
  | nil => cases r₂ with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  | cons a as ih => cases r₂ with
    | nil => cases a <;> rfl
    | cons b bs => cases a with
      | seg a => cases b with
        | seg b =>
          cases l with
          | nil => simp [matchRightContext] at h
          | cons s ss =>
            simp only [matchRightContext, Bool.and_eq_true, decide_eq_true_eq] at h
            simp only [mgRev]
            split
            · simp [matchRightContext, h.1, ih h.2]
            · simp [matchRightContext, inf_le_left.trans h.1]
        | wordBoundary => rfl
      | wordBoundary => cases b with
        | seg _ => rfl
        | wordBoundary =>
          cases l with
          | nil => rfl
          | cons s ss => simp [matchRightContext] at h

/-- The generalized rule covers everything either rule covered: generalization only widens. -/
theorem matches_mg_left (h : Matches c₁ stem) : Matches (mg c₁ c₂) stem := by
  simp only [Matches, matchLeftContext, mg, List.reverse_reverse] at h ⊢
  exact matchRightContext_mgRev h

theorem matches_mg_right (h : Matches c₂ stem) : Matches (mg c₁ c₂) stem :=
  mg_comm ▸ matches_mg_left h

/-- A description one segment long reads the final segment alone: the structured similarity a
rule is confined to. -/
theorem matches_rtake_one (h : c.length ≤ 1) : Matches c stem ↔ Matches c (stem.rtake 1) := by
  simp only [Matches, matchLeftContext_rtake_of_le c h]

/-! ### Reliability -/

/-- The stems of a lexicon meeting a description: the rule's scope. -/
def scopeOf {C : Type*} (c : Context) (lex : List (List Segment × C)) : List (List Segment × C) :=
  lex.filter (matchLeftContext c ·.1)

/-- A rule's performance in a lexicon: the forms meeting its description and, among them,
those whose past shows its change. -/
structure Stats where
  scope : ℕ
  hits : ℕ
  deriving DecidableEq

/-- The statistics of a change in a described context over a lexicon. -/
def Stats.ofLexicon {C : Type*} [DecidableEq C] (ch : C) (c : Context)
    (lex : List (List Segment × C)) : Stats :=
  ⟨(scopeOf c lex).length, ((scopeOf c lex).filter (·.2 = ch)).length⟩

section
variable {C : Type*} [DecidableEq C] (ch : C) (lex : List (List Segment × C))

theorem hits_le_scope : (Stats.ofLexicon ch c lex).hits ≤ (Stats.ofLexicon ch c lex).scope :=
  List.length_filter_le _ _

/-- Generalization never loses a form. -/
theorem scope_mono : (Stats.ofLexicon ch c₁ lex).scope ≤ (Stats.ofLexicon ch (mg c₁ c₂) lex).scope :=
  (List.monotone_filter_right lex λ _ h => matches_mg_left h).length_le
end

/-- Raw confidence: hits over scope. -/
def Stats.rawConfidence (s : Stats) : ℚ := s.hits / s.scope

/-- `r` is less reliable than `s`, the ratios cross-multiplied. -/
def LessReliable (r s : Stats) : Prop := r.hits * s.scope < s.hits * r.scope

instance (r s : Stats) : Decidable (LessReliable r s) := inferInstanceAs (Decidable (_ < _))

theorem lessReliable_iff {r s : Stats} (hr : 0 < r.scope) (hs : 0 < s.scope) :
    LessReliable r s ↔ r.rawConfidence < s.rawConfidence := by
  simp only [LessReliable, Stats.rawConfidence]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- The general suffixation rule (7a) over the learning set. -/
def general : Stats := ⟨4253, 4034⟩

/-- An island of reliability: a rule the change works better in than the general rule ((8)). -/
def IsIsland (s : Stats) : Prop := LessReliable general s

instance (s : Stats) : Decidable (IsIsland s) := inferInstanceAs (Decidable (LessReliable _ _))

/-! ### The paper's steps on the English fragment -/

def vote : List Segment := [v, o, t]
def need : List Segment := [n, tenseI, d]
def rub : List Segment := [r, wedge, b]
def sag : List Segment := [s, æ, g]
def plan : List Segment := [p, l, æ, n]
def love : List Segment := [l, wedge, v]
def flow : List Segment := [f, l, o]
def jump : List Segment := [dezh, wedge, m, p]
def miss : List Segment := [m, laxI, s]
def wish : List Segment := [w, laxI, esh]
def laugh : List Segment := [l, æ, f]

/-- The fragment's consonants. -/
def consonants : List Segment := [p, t, k, b, d, g, m, n, ŋ, f, v, θ, s, esh, dezh, l, r, w]

/-- (6): *vote* and *need* differ first in their final segments, so the learned `-əd` rule keeps
what [t] and [d] share, a class no other consonant meets. -/
theorem learned_vote_need : ∀ x ∈ consonants, Matches (learned [vote, need]) [x] ↔ x = t ∨ x = d := by
  decide

/-- Footnote 4: whatever [b], [g] and [n] share, [d] has, so the `-d` rule learned from *rub*,
*sag* and *plan* reaches *need*, and only the phonology keeps *needd* out. -/
theorem learned_rub_sag_plan : Matches (learned [rub, sag, plan]) need := by decide

/-- (7b): once the data include a voiced continuant and a vowel-final stem, the `-d` rule keeps
[+voice] alone and is met by every voiced consonant. -/
theorem learned_voiced : ∀ x ∈ consonants,
    Matches (learned [rub, sag, plan, love, flow]) [x] ↔ x.HasValue .voice true := by
  decide

/-- (7b): the `-t` rule learned from *jump*, *miss* and *laugh* is met by every voiceless
consonant. -/
theorem learned_voiceless : ∀ x ∈ consonants,
    Matches (learned [jump, miss, laugh]) [x] ↔ x.HasValue .voice false := by
  decide

/-- The island (8): `-t` after a voiceless fricative. -/
def voicelessFricative : Context :=
  [.seg (Segment.ofSpecs [(.sonorant, false), (.continuant, true), (.voice, false)])]

/-- (8) is met by the four voiceless fricatives and nothing else. -/
theorem voicelessFricative_iff : ∀ x ∈ consonants,
    Matches voicelessFricative [x] ↔ x ∈ [f, θ, s, esh] := by
  decide

/-- The rule learned from *miss*, *wish* and *laugh* lies inside the island (8): further
fricative-final forms widen it to the island. -/
theorem learned_le_voicelessFricative (x : Segment)
    (h : Matches (learned [miss, wish, laugh]) [x]) : Matches voicelessFricative [x] := by
  have e : learned [miss, wish, laugh] = [.seg (s ⊓ esh ⊓ f)] := by decide
  rw [e, matches_single_iff] at h
  exact (matches_single_iff _ _).2 (le_trans (by decide) h)

/-! ### Appendix A -/

/-- Table 3's cells: whether the stem occupies an island for the regular past and for some
irregular past. -/
structure IORCategory where
  iorForRegular : Bool
  iorForIrregular : Bool
  deriving DecidableEq

def IORCategory.ofString : String → Option IORCategory
  | "both" => some ⟨true, true⟩
  | "regOnly" => some ⟨true, false⟩
  | "irregOnly" => some ⟨false, true⟩
  | "neither" => some ⟨false, false⟩
  | _ => none

/-- A printed decimal read as the integer of its digits: ratings in hundredths, production
probabilities in thousandths. -/
def digits (s : String) : ℕ :=
  s.toList.foldl (λ n c => if c.isDigit then 10 * n + (c.toNat - '0'.toNat) else n) 0

/-- A row's numeric feature. -/
def value (key : String) (r : LinguisticExample) : ℕ := digits ((r.feature? key).getD "0")

/-- A row's reported rule statistics (Tables 1 and 4). -/
def statsOf (r : LinguisticExample) : Option Stats :=
  (r.nat? "ruleScope").bind λ s => (r.nat? "ruleHits").map (⟨s, ·⟩)

/-- Table 4: the twelve regular islands all outscore the general rule. -/
theorem table4_islands :
    ∀ r ∈ Examples.all, (r.feature? "island").isSome → ∀ s ∈ statsOf r, IsIsland s := by
  decide +kernel

/-- Table 1: *gleed*'s pasts by raw confidence, *gleed* below *gled* below *gleeded*. -/
theorem gleed_ranking :
    ∀ s₁ ∈ statsOf Examples.a1_25_gleed, ∀ s₂ ∈ statsOf Examples.a1_25_gled,
      ∀ s₃ ∈ statsOf Examples.a1_25_gleeded, LessReliable s₁ s₂ ∧ LessReliable s₂ s₃ := by
  decide

/-- The Appendix A rows of one past type in the cells satisfying `p` (the Peripheral stems of
Table A2 have no cell). -/
def rows (regular : Bool) (p : IORCategory → Bool) : List LinguisticExample :=
  Examples.all.filter λ r =>
    r.feature? "pastType" = some (if regular then "regular" else "irregular") ∧
      ((r.feature? "cell").bind IORCategory.ofString).any p

/-- The sum of a numeric feature over rows. -/
def total (key : String) (rs : List LinguisticExample) : ℕ := (rs.map (value key)).sum

/-- The mean of `key` over `A` exceeds its mean over `B`, cross-multiplied. -/
def MeanGT (key : String) (A B : List LinguisticExample) : Prop :=
  total key A * B.length > total key B * A.length

instance (key : String) (A B : List LinguisticExample) : Decidable (MeanGT key A B) :=
  inferInstanceAs (Decidable (_ > _))

/-- Islands of reliability for regulars (Fig. 2): novel regular pasts are rated higher, and
volunteered more often, when the stem occupies an island for the regular change. -/
theorem regulars_ior :
    MeanGT "adjustedRating" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) ∧
      MeanGT "production" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by
  decide

/-- Islands of reliability for irregulars, likewise. -/
theorem irregulars_ior :
    MeanGT "adjustedRating" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) ∧
      MeanGT "production" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) := by
  decide

/-- The single-default-rule prediction, that novel regular ratings do not vary with the stem's
cell, fails on the Core data: the regulars-only and irregulars-only cells differ. -/
theorem regulars_not_cell_invariant :
    total "adjustedRating" (rows true (· = ⟨true, false⟩)) *
        (rows true (· = ⟨false, true⟩)).length ≠
      total "adjustedRating" (rows true (· = ⟨false, true⟩)) *
        (rows true (· = ⟨true, false⟩)).length := by
  decide

/-- Trade-off (Figs. 3–4): a past is rated higher when its rival is not in an island, for
regulars and irregulars alike. -/
theorem tradeoff :
    MeanGT "adjustedRating" (rows true (· = ⟨true, false⟩)) (rows true (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows true (· = ⟨false, false⟩)) (rows true (· = ⟨false, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, true⟩)) (rows false (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, false⟩))
        (rows false (· = ⟨true, false⟩)) := by
  decide

/-- The rule-based model's predicted regular ratings are higher in the regular islands: the
stimuli were chosen by the model. -/
theorem ruleBased_islands :
    MeanGT "ruleBased" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by decide

/-- Table 4: on the twelve regular pasts in the best islands the analogical model, unable to
locate structured similarity, scores below both the participants and the rule-based model. -/
theorem analogical_misses_islands :
    ∀ r ∈ Examples.all, (r.feature? "island").isSome →
      value "analogical" r < value "adjustedRating" r ∧
        value "analogical" r < value "ruleBased" r := by
  decide +kernel

/-- The pseudo-*burnt* irregulars of (15). -/
def burnt : List LinguisticExample := Examples.all.filter (·.feature? "set" = some "burnt")

/-- The rule-based model's one systematic error: it underrates the *burnt*-class forms, which
the analogical model overrates. -/
theorem burnt_underestimated :
    total "ruleBased" burnt < total "adjustedRating" burnt ∧
      total "adjustedRating" burnt < total "analogical" burnt := by
  decide

/-- Participants preferred regular pasts overall. -/
theorem regulars_preferred :
    MeanGT "rating" (Examples.all.filter λ r => r.feature? "pastType" = some "regular")
      (Examples.all.filter λ r => r.feature? "pastType" = some "irregular") := by
  decide

end AlbrightHayes2003
