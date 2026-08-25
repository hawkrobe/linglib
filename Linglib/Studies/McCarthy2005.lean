import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Studies.Benua1997

/-!
# [mccarthy-2005] — Optimal Paradigms

Optimal Paradigms evaluates entire inflectional paradigms as candidates: markedness and
input–output faithfulness are summed over the members, and the stem of every member stands
in a correspondence relation ℛ_OP with the stem of every other, with no distinguished base —
the symmetric counterpart of the base priority of [benua-1997], which OP leaves to
derivational morphology. Faithfulness on ℛ_OP resists alternation within the paradigm, and
three consequences follow from the architecture alone: overapplication only, attraction to
the unmarked, and majority rules.

`Paradigm` carries the shared input and the members, each with its inflectional cell,
surface stem and input–stem correspondence; `Paradigm.corr` is the correspondence diagram
whose ℛ_OP relations are read off the members' input correspondences — stem positions
realising the same input position correspond, as do epenthetic positions at the same site —
so the relation is symmetric and base-free by construction.
`markedness`, `ioFaith` and `opFaith` sum a constraint over the members or the ordered
member pairs. The Classical Arabic sections rerun the tableaux for the right edge of the verb
stem (/faʕaːl/, /faʕl/), for the left edge (/fʕaːl/, /stafʕal/, /ftaʕal/) and for the
Moroccan majority-rules paradigm of /kətb/; the Hebrew section reruns the jussive paradigms
of [benua-1997] under OP, where epenthesis underapplies only because overapplication is
blocked by the ban on a schwa in a two-sided open syllable. Locators are those of the
ROA-485 (2001) version.
-/

namespace McCarthy2005

open Constraints OptimalityTheory

variable {α ι : Type*}

/-! ### Paradigms as candidates -/

/-- The roles of a candidate paradigm: the shared input stem and the stem of each member. -/
inductive Role
  | input
  | member (i : ℕ)
  deriving DecidableEq, Repr

/-- A paradigm member: its inflectional cell, its surface stem, and the correspondence from
the input to the stem. -/
structure Member (α ι : Type*) where
  cell : ι
  stem : List α
  io : List (ℕ × ℕ)

/-- A candidate paradigm (2a): the inflected forms of one input stem. -/
structure Paradigm (α ι : Type*) where
  input : List α
  members : List (Member α ι)

/-- The stem of the `i`th member, empty beyond the paradigm. -/
def Paradigm.stem (P : Paradigm α ι) (i : ℕ) : List α :=
  ((P.members[i]?).map Member.stem).getD []

/-- The input correspondence of the `i`th member, empty beyond the paradigm. -/
def Paradigm.io (P : Paradigm α ι) (i : ℕ) : List (ℕ × ℕ) :=
  ((P.members[i]?).map Member.io).getD []

/-- The positions of two stems that realise the same input position. -/
def compose (l₁ l₂ : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l₁.flatMap λ (r, p) => l₂.filterMap λ (r', q) => if r = r' then some (p, q) else none

/-- The positions of a stem of length `n` without an input correspondent. -/
def epenthetic (l : List (ℕ × ℕ)) (n : ℕ) : List ℕ :=
  (List.range n).filter λ p => ∀ rp ∈ l, rp.2 ≠ p

/-- The site of a stem position: the last input position realised at or before it. -/
def site (l : List (ℕ × ℕ)) (p : ℕ) : Option ℕ :=
  ((l.filter λ rp => rp.2 ≤ p).map Prod.fst).max?

/-- ℛ_OP between two stems of lengths `n₁`, `n₂` with input correspondences `l₁`, `l₂`: the
positions realising the same input position, and the epenthetic positions at the same site. -/
def opPairs (l₁ l₂ : List (ℕ × ℕ)) (n₁ n₂ : ℕ) : List (ℕ × ℕ) :=
  compose l₁ l₂ ++ (epenthetic l₁ n₁).flatMap λ p =>
    (epenthetic l₂ n₂).filterMap λ q => if site l₁ p = site l₂ q then some (p, q) else none

/-- The correspondence diagram of a candidate (2c): each member's input–stem relation, and
between the stems of distinct members the relation ℛ_OP of `opPairs`. -/
def Paradigm.corr (P : Paradigm α ι) : Correspondence Role α :=
  .ofPairs (λ | .input => P.input | .member i => P.stem i)
    λ | .input, .member i => P.io i
      | .member i, .member j =>
        if i = j then [] else opPairs (P.io i) (P.io j) (P.stem i).length (P.stem j).length
      | _, _ => []

/-- A markedness constraint on the word of each cell, summed over the members (2b). -/
def markedness (m : ι → List α → ℕ) : Constraint (Paradigm α ι) :=
  λ P => (P.members.map λ x => m x.cell x.stem).sum

/-- An input–output faithfulness constraint summed over the members (2b). -/
def ioFaith (f : Correspondence Role α → Role → Role → ℕ) : Constraint (Paradigm α ι) :=
  λ P => ((List.range P.members.length).map λ i => f P.corr .input (.member i)).sum

/-- An OP faithfulness constraint (2d): a correspondence constraint summed over the ordered
pairs of distinct members. -/
def opFaith (f : Correspondence Role α → Role → Role → ℕ) : Constraint (Paradigm α ι) :=
  λ P => ((List.range P.members.length).flatMap λ i => (List.range P.members.length).map λ j =>
    if i = j then 0 else f P.corr (.member i) (.member j)).sum

/-- The tableau of the labelled candidate paradigms under a ranking. -/
def tableau {L : Type*} [DecidableEq L] (cand : L → Paradigm α ι) (labels : List L)
    (ranking : List (Constraint (Paradigm α ι))) (h : labels ≠ [] := by decide) :=
  Tableau.ofRanking labels (ranking.map (Constraint.comap cand)) h

/-- The candidate paradigms of a tableau. -/
inductive Cand
  | a | b | c | d
  deriving DecidableEq, Repr

/-! ### German *Bund* (§2)

The paradigm ⟨bʊnt, bʊndə⟩ draws two OP-IDENT(voice) marks, one on each direction of
ℛ_OP, and ⟨bʊn, bʊndə⟩ one OP-MAX and one OP-DEP mark (fn. 3). -/

namespace German

inductive Seg
  | b | u | n | t | d | schwa
  deriving DecidableEq, Repr

/-- Voicing of the alternating obstruents. -/
def voice : Seg → Option Bool
  | .t => some false
  | .d => some true
  | _ => none

/-- The paradigm of /bund/ with final devoicing: ⟨bʊnt, bʊndə⟩. -/
def bund : Paradigm Seg (List Seg) :=
  ⟨[.b, .u, .n, .d], [⟨[], [.b, .u, .n, .t], Correspondence.diagonalPairs 4⟩,
    ⟨[.schwa], [.b, .u, .n, .d], Correspondence.diagonalPairs 4⟩]⟩

example : opFaith (Correspondence.identViolFeature voice) bund = 2 := by decide

/-- The paradigm ⟨bʊn, bʊndə⟩ of fn. 3. -/
def bun : Paradigm Seg (List Seg) :=
  ⟨[.b, .u, .n, .d], [⟨[], [.b, .u, .n], Correspondence.diagonalPairs 3⟩,
    ⟨[.schwa], [.b, .u, .n, .d], Correspondence.diagonalPairs 4⟩]⟩

example : opFaith Correspondence.maxViol bun = 1 ∧ opFaith Correspondence.depViol bun = 1 := by
  decide

end German

/-! ### Arabic syllables

The markedness constraints of §4 and §5.1 read syllable weight. A long vowel is a vowel
followed by its length mora `long`, a nuclear position of its own, so MAX-µ and MAX-V are
MAX restricted to the moras and to the vowels. -/

namespace Arabic

inductive Seg
  | f | ayn | l | s | t | j | k | b | n | a | i | u | schwa | long
  deriving DecidableEq, Repr

def IsVowel (x : Seg) : Prop := x ∈ [Seg.a, .i, .u, .schwa]

instance : DecidablePred IsVowel := λ x => inferInstanceAs (Decidable (x ∈ _))

/-- A nuclear position: a vowel or a length mora. -/
def IsNuclear (x : Seg) : Prop := IsVowel x ∨ x = .long

instance : DecidablePred IsNuclear := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A syllable by its nucleus (one or two vowel positions) and coda. -/
structure Syllable where
  nucleus : List Seg
  coda : List Seg
  deriving DecidableEq, Repr

/-- CV. -/
def Syllable.IsLight (σ : Syllable) : Prop := σ.nucleus.length + σ.coda.length = 1

/-- CVVC or CVCC. -/
def Syllable.IsSuperheavy (σ : Syllable) : Prop := 3 ≤ σ.nucleus.length + σ.coda.length

instance : DecidablePred Syllable.IsLight := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Syllable.IsSuperheavy := λ _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The maximal runs of vowels and of consonants. -/
def runs : List Seg → List (List Seg)
  | [] => []
  | x :: xs =>
    match runs xs with
    | (y :: ys) :: rest =>
      if IsNuclear x ↔ IsNuclear y then (x :: y :: ys) :: rest else [x] :: (y :: ys) :: rest
    | rs => [x] :: rs

/-- The syllables of alternating vowel and consonant runs from the first vowel: a medial
consonant run closes the preceding syllable but for its last consonant, the next onset. -/
def nuclei : List (List Seg) → List Syllable
  | [] => []
  | [v] => [⟨v, []⟩]
  | [v, c] => [⟨v, c⟩]
  | v :: c :: v' :: rest => ⟨v, c.dropLast⟩ :: nuclei (v' :: rest)

/-- The word-initial appendices and the syllables of a word: of the consonants before the
first vowel, the last is its onset and the rest are appendices. -/
def syllabify (w : List Seg) : ℕ × List Syllable :=
  match runs w with
  | [] => (0, [])
  | r :: rest =>
    if ∀ x ∈ r, IsNuclear x then (0, nuclei (r :: rest)) else (r.length - 1, nuclei rest)

/-- NO-LL: adjacent light syllables (fn. 17 counts overlapping pairs). -/
def noLL (w : List Seg) : ℕ :=
  let σs := (syllabify w).2
  ((σs.zip σs.tail).filter λ p => p.1.IsLight ∧ p.2.IsLight).length

/-- EXH(PrWd): word-initial appendices. -/
def exhPrWd (w : List Seg) : ℕ := (syllabify w).1

/-- Superheavy syllables, parsed with a moraic coda (\*µµµ]σ) or a syllable appendix
(\*APP-σ). -/
def superheavy (w : List Seg) : ℕ := ((syllabify w).2.filter (·.IsSuperheavy)).length

/-- An inflectional cell of the Classical Arabic verb or noun: its affixes, and whether a
superheavy coda is parsed as an appendix. -/
structure Cell where
  prefixes : List Seg := []
  suffixes : List Seg := []
  appendix : Bool := false
  deriving DecidableEq, Repr

/-- The word of a stem in a cell. -/
def Cell.word (c : Cell) (stem : List Seg) : List Seg := c.prefixes ++ stem ++ c.suffixes

/-! ### The Classical Arabic verb (§4)

Verb stems end in CVC] and may begin with [CCV; noun stems may end in CVːC] or CVCC] and
begin only with [CV. Verbs alone have C-initial suffixes and CV- prefixes, and OP
faithfulness carries the repairs they force through the paradigm, whereas the noun's
one-member paradigm leaves the markedness of each form to itself. -/

/-- \*µµµ]σ. -/
def starTrimoraic : Constraint (Paradigm Seg Cell) :=
  markedness λ c s => if c.appendix then 0 else superheavy (c.word s)

/-- \*APP-σ. -/
def starAppendix : Constraint (Paradigm Seg Cell) :=
  markedness λ c s => if c.appendix then superheavy (c.word s) else 0

def noLLParadigm : Constraint (Paradigm Seg Cell) := markedness λ c s => noLL (c.word s)

def exhParadigm : Constraint (Paradigm Seg Cell) := markedness λ c s => exhPrWd (c.word s)

def opDepV : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.depViolOn IsVowel)

/-- OP-MAX-µ, on the length moras. -/
def opMaxMora : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.maxViolOn (· = .long))

def ioDepV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.depViolOn IsVowel)

def ioMaxV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.maxViolOn IsVowel)

/-- IO-MAX-µ, on the length moras. -/
def ioMaxMora : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.maxViolOn (· = .long))

/-- The summary ranking (18): IO-MAX-V, OP-DEP-V, \*µµµ]σ, \*APP-σ, OP-MAX-µ >> NO-LL >>
EXH(PrWd) >> IO-DEP-V >> IO-MAX-µ. -/
def ranking : List (Constraint (Paradigm Seg Cell)) :=
  [ioMaxV, opDepV, starTrimoraic, starAppendix, opMaxMora, noLLParadigm, exhParadigm, ioDepV,
   ioMaxMora]

/-- The 3sg.m. perfective, suffix *-a*. -/
def perfective : Cell := { suffixes := [.a] }

/-- The 1sg perfective, suffix *-tu*. -/
def perfective1 : Cell := { suffixes := [.t, .u] }

/-- The 3sg.m. imperfective, *ja-* … *-u*. -/
def imperfective : Cell := { prefixes := [.j, .a], suffixes := [.u] }

/-- The nominative indefinite noun, suffix *-un*. -/
def nominative : Cell := { suffixes := [.u, .n] }

/-- The paradigms of /faʕaːl/ in (12): shortened throughout, long throughout with the
superheavy coda an appendix or moraic, or alternating. -/
def long : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, short, shortened⟩, ⟨perfective1, short, shortened⟩]⟩
  | .b => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 6⟩,
      ⟨{ perfective1 with appendix := true }, input, Correspondence.diagonalPairs 6⟩]⟩
  | .c => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 6⟩,
      ⟨perfective1, input, Correspondence.diagonalPairs 6⟩]⟩
  | .d => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 6⟩,
      ⟨perfective1, short, shortened⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .a, .long, .l]
  short : List Seg := [.f, .a, .ayn, .a, .l]
  /-- Closed-syllable shortening: one vowel position deleted. -/
  shortened : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 4)]

/-- (12): the long vowel of /faʕaːl/ is shortened throughout the paradigm, ⟨faʕala, faʕaltu⟩ —
overapplication of closed-syllable shortening, under OP-MAX-µ >> IO-MAX-µ. -/
theorem shortening_overapplies : (tableau long [.a, .b, .c, .d] ranking).optimal = {.a} := by
  decide

/-- The paradigms of /faʕl/ in (13): epenthesis throughout, the cluster kept throughout with
the superheavy coda an appendix or moraic, or alternating. -/
def cluster : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, epenthesized, epenthetic⟩,
      ⟨perfective1, epenthesized, epenthetic⟩]⟩
  | .b => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 4⟩,
      ⟨{ perfective1 with appendix := true }, input, Correspondence.diagonalPairs 4⟩]⟩
  | .c => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 4⟩,
      ⟨perfective1, input, Correspondence.diagonalPairs 4⟩]⟩
  | .d => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 4⟩,
      ⟨perfective1, epenthesized, epenthetic⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .l]
  epenthesized : List Seg := [.f, .a, .ayn, .i, .l]
  /-- A vowel epenthesized into the final cluster. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4)]

/-- (13): epenthesis into the final cluster of /faʕl/ carries through the paradigm,
⟨faʕila, faʕiltu⟩, under OP-DEP-V >> IO-DEP-V. -/
theorem epenthesis_overapplies : (tableau cluster [.a, .b, .c, .d] ranking).optimal = {.a} := by
  decide

/-- The noun /fʕaːl/ in (14): epenthesis or an initial appendix, in a one-member paradigm. -/
def noun : Cand → Paradigm Seg Cell
  | .a => ⟨input,
      [⟨nominative, [.f, .i, .ayn, .a, .long, .l], [(0, 0), (1, 2), (2, 3), (3, 4), (4, 5)]⟩]⟩
  | _ => ⟨input, [⟨nominative, input, Correspondence.diagonalPairs 5⟩]⟩
where
  input : List Seg := [.f, .ayn, .a, .long, .l]

/-- (14): a [CCV noun stem is broken up by epenthesis, EXH(PrWd) >> IO-DEP-V. -/
theorem noun_epenthesis : (tableau noun [.a, .b] ranking).optimal = {.a} := by decide

/-- The paradigms of the tenth conjugation /stafʕal/ in (19): the initial cluster kept
throughout, epenthesis throughout, or epenthesis in the unprefixed form only. -/
def tenth : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 7⟩,
      ⟨imperfective, [.s, .t, .a, .f, .ayn, .i, .l], Correspondence.diagonalPairs 7⟩]⟩
  | .b => ⟨input, [⟨perfective, [.s, .i, .t, .a, .f, .ayn, .a, .l], epenthetic⟩,
      ⟨imperfective, [.s, .i, .t, .a, .f, .ayn, .i, .l], epenthetic⟩]⟩
  | _ => ⟨input, [⟨perfective, [.s, .i, .t, .a, .f, .ayn, .a, .l], epenthetic⟩,
      ⟨imperfective, [.s, .t, .a, .f, .ayn, .i, .l], Correspondence.diagonalPairs 7⟩]⟩
where
  input : List Seg := [.s, .t, .a, .f, .ayn, .a, .l]
  /-- A vowel epenthesized into the initial cluster. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]

/-- (19): attraction to the unmarked — the prefixed *jastafʕilu*, which needs no epenthesis,
is the attractor, and *sωtafʕala* keeps its appendix: NO-LL blocks epenthesis in the prefixed
form and OP-DEP-V carries the blocking to the unprefixed one. -/
theorem attraction_to_the_unmarked :
    (tableau tenth [.a, .b, .c] ranking).optimal = {.a} := by decide

/-- The paradigms of the eighth conjugation /ftaʕal/ in (17): the cluster kept, or epenthesis
with syncope of the following vowel. -/
def eighth : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, input, Correspondence.diagonalPairs 6⟩,
      ⟨imperfective, [.f, .t, .a, .ayn, .i, .l], Correspondence.diagonalPairs 6⟩]⟩
  | _ => ⟨input, [⟨perfective, [.f, .i, .t, .ayn, .a, .l], syncopated⟩,
      ⟨imperfective, [.f, .i, .t, .ayn, .i, .l], syncopated⟩]⟩
where
  input : List Seg := [.f, .t, .a, .ayn, .a, .l]
  /-- Epenthesis into the initial cluster and syncope of the first stem vowel. -/
  syncopated : List (ℕ × ℕ) := [(0, 0), (1, 2), (3, 3), (4, 4), (5, 5)]

/-- (17): NO-LL is too low to force syncope, IO-MAX-V >> NO-LL. -/
theorem no_syncope : (tableau eighth [.a, .b] ranking).optimal = {.a} := by decide

/-! ### Moroccan Arabic majority rules (§5.1)

Schwa is banned from open syllables and appears only to break up triconsonantal clusters,
so the phonology fixes CCəC before C-initial and CəCC before V-initial suffixes; the
unaffixed verb joins the larger class, *ktəb*, whereas nouns — paradigms of one — follow
sonority. The prefixes of the imperfective play no part in the constraints and are
omitted from the cells. -/

/-- Schwa in an open syllable. -/
def schwaOpen (w : List Seg) : ℕ :=
  ((syllabify w).2.filter λ σ => σ.nucleus = [.schwa] ∧ σ.coda = []).length

/-- Triconsonantal clusters. -/
def ccc : List Seg → ℕ
  | x :: y :: z :: rest =>
    (if ¬IsVowel x ∧ ¬IsVowel y ∧ ¬IsVowel z then 1 else 0) + ccc (y :: z :: rest)
  | _ => 0

def IsSonorant (x : Seg) : Prop := x ∈ [Seg.l, .j, .n]

instance : DecidablePred IsSonorant := λ x => inferInstanceAs (Decidable (x ∈ _))

/-- The sonority constraints deciding nouns, as one constraint: CCəC wants a final sonorant,
CəCC a final obstruent. -/
def sonority : List Seg → ℕ
  | [_, _, .schwa, x] => if IsSonorant x then 0 else 1
  | [_, .schwa, _, x] => if IsSonorant x then 1 else 0
  | _ => 0

/-- The ranking of (23): the schwa phonotactics >> OP-MAX-V >> sonority >> IO-MAX-V, IO-DEP-V. -/
def moroccanRanking : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness λ suf s => schwaOpen (s ++ suf), markedness λ suf s => ccc (s ++ suf),
   opFaith (Correspondence.maxViolOn IsVowel), markedness λ _ s => sonority s,
   ioFaith (Correspondence.maxViolOn IsVowel), ioFaith (Correspondence.depViolOn IsVowel)]

/-- A CCəC member from /kətb/: the input schwa deleted, a schwa epenthesized. -/
def ccec (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [.k, .t, .schwa, .b], [(0, 0), (2, 1), (3, 3)]⟩

/-- A CəCC member from /kətb/. -/
def cecc (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [.k, .schwa, .t, .b], Correspondence.diagonalPairs 4⟩

/-- The suffixes of the fifteen members of (22): the unaffixed verb, four C-initial
suffixes, four prefixed forms, and six V-initial suffixes. -/
def cells : List (List Seg) :=
  [[], [.t], [.n, .a], [.t, .i], [.t, .u], [], [], [], [], [.u], [.schwa, .t], [.i], [.u], [.u],
   [.u]]

/-- The paradigms of /kətb/ in (23): the unaffixed verb CCəC or CəCC with the rest fixed by
the phonology, or levelled to CCəC or to CəCC throughout. -/
def kteb : Cand → Paradigm Seg (List Seg)
  | .a => ⟨input, (cells.take 9).map ccec ++ (cells.drop 9).map cecc⟩
  | .b => ⟨input, cecc [] :: ((cells.drop 1).take 8).map ccec ++ (cells.drop 9).map cecc⟩
  | .c => ⟨input, cells.map ccec⟩
  | .d => ⟨input, cells.map cecc⟩
where
  input : List Seg := [.k, .schwa, .t, .b]

/-- (23): majority rules — the unaffixed *ktəb* joins the nine CCəC members against the six
CəCC members, since OP-MAX-V is violated once in each direction by every CCəC–CəCC pair. -/
theorem majority_rules : (tableau kteb [.a, .b, .c, .d] moroccanRanking).optimal = {.a} := by
  decide +kernel

end Arabic

/-! ### Tiberian Hebrew jussives (§5.2)

The final cluster of the jussive *yišb* is not broken up by the epenthesis that nouns
undergo, the underapplication [benua-1997] derives from base priority. Under OP the
paradigm ⟨yišbē, yišb⟩ wins because its levelled rival ⟨yišəbē, yišeb⟩ puts a schwa in a
two-sided open syllable; into a rising-sonority cluster, SON-CON >> OP-MAX-V, epenthesis
applies, ⟨yiɣlē, yiɣel⟩. The segments and the markedness constraints are those of the
[benua-1997] study, whose winners the OP tableaux reproduce. -/

namespace Hebrew

open Benua1997.Hebrew (Seg sonCon complexCoda)

/-- A vowel in a two-sided open syllable, CV.CV.CV. -/
def twoSidedOpen : List Seg → ℕ
  | v₁ :: c₁ :: v₂ :: c₂ :: v₃ :: rest =>
    (if v₁ = .vowel ∧ c₁ ≠ .vowel ∧ v₂ = .vowel ∧ c₂ ≠ .vowel ∧ v₃ = .vowel then 1 else 0)
      + twoSidedOpen (c₁ :: v₂ :: c₂ :: v₃ :: rest)
  | _ => 0

/-- \*ə]σσ, SON-CON >> OP-MAX-V >> \*COMPLEX-CODA >> IO-DEP-V. -/
def ranking : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness λ suf s => twoSidedOpen (s ++ suf), markedness λ suf s => sonCon (s ++ suf),
   opFaith (Correspondence.maxViolOn (· = .vowel)), markedness λ suf s => complexCoda (s ++ suf),
   ioFaith (Correspondence.depViolOn (· = .vowel))]

/-- The paradigms of an imperfective and its jussive from a stem ending in the cluster
`x y`: the cluster throughout, epenthesis throughout, or epenthesis in the jussive alone. -/
def jussive (x y : Seg) : Cand → Paradigm Seg (List Seg)
  | .a => ⟨stem, [⟨[.vowel], stem, Correspondence.diagonalPairs 4⟩,
      ⟨[], stem, Correspondence.diagonalPairs 4⟩]⟩
  | .b => ⟨stem, [⟨[.vowel], epenthesized, epenthetic⟩, ⟨[], epenthesized, epenthetic⟩]⟩
  | _ => ⟨stem, [⟨[.vowel], stem, Correspondence.diagonalPairs 4⟩, ⟨[], epenthesized, epenthetic⟩]⟩
where
  stem : List Seg := [.glide, .vowel, x, y]
  epenthesized : List Seg := [.glide, .vowel, x, .vowel, y]
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4)]

/-- *yiš.bē ~ yišb* 'take captive': the cluster is kept throughout, overapplication of
epenthesis being blocked. -/
theorem captive :
    (tableau (jussive .sibilant .stop) [.a, .b, .c] ranking).optimal = {.a} := by decide

/-- *yiɣ.lē ~ yi.ɣel* 'uncover': into a rising-sonority cluster epenthesis applies in the
jussive alone, OP-MAX-V being dominated by SON-CON. -/
theorem uncover :
    (tableau (jussive .spirant .liquid) [.a, .b, .c] ranking).optimal = {.c} := by decide

/-- The OP winners carry the forms of the [benua-1997] winners, (87) and (92). -/
example :
    ((Benua1997.Hebrew.captive .d).form .base, (Benua1997.Hebrew.captive .d).form .derivative) =
      ((jussive .sibilant .stop .a).stem 0 ++ [.vowel], (jussive .sibilant .stop .a).stem 1) ∧
    ((Benua1997.Hebrew.uncover .b).form .base, (Benua1997.Hebrew.uncover .b).form .derivative) =
      ((jussive .spirant .liquid .c).stem 0 ++ [.vowel], (jussive .spirant .liquid .c).stem 1) :=
  ⟨rfl, rfl⟩

end Hebrew

end McCarthy2005

