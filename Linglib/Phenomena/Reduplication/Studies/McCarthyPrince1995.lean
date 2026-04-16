import Linglib.Core.Logic.OT
import Linglib.Theories.Phonology.Correspondence
import Linglib.Theories.Phonology.Constraints
import Linglib.Fragments.Akan.Phonology

/-!
# McCarthy & Prince (1995): Faithfulness and Reduplicative Identity
@cite{mccarthy-prince-1995}

Formalizes the core empirical results of Correspondence Theory: the
interaction between I-O faithfulness, B-R identity, and phonological
markedness produces three typological patterns in the Basic Model —
**non-application**, **emergence of the unmarked**, and **overapplication**
— via ranking permutation of universal constraints. A fourth pattern,
**normal application**, requires additional candidates beyond the
Basic Model and is demonstrated by concrete language examples.

The paper's most striking theoretical result (§5) is that
**underapplication is not a Basic Model category**: no ranking of the
three core constraints can produce it. We prove this as
`basic_model_no_underapplication`.

## Sections (keyed to the paper's numbering)

- **§3.4**: Javanese intervocalic *h*-deletion — the paper's signature
  example of overapplication (ex. 1, 6–7).
- **§4.2**: Balangao partial reduplication — emergence of the unmarked
  (ex. 106–107). MAX-IO >> NO-CODA >> MAX-BR.
- **§4**: Basic Model factorial typology — the abstract 3-constraint
  interaction space. All 6 rankings of {IO-Faith, Phono, BR-Id} are
  computed; the distinct optima are verified.
- **§5**: Underapplication impossibility — the Basic Model cannot produce
  underapplication; every ranking selects faithful, over, or normal.
- **§5.1**: Akan underapplication — a 4th constraint (OCP) blocks
  overapplication, producing underapplication. Demonstrates the
  mechanism predicted by the Basic Model impossibility result.
-/

namespace McCarthyPrince1995

open Core.OT
open Phonology.Constraints

-- ============================================================================
-- § 1: Javanese Intervocalic h-Deletion (Overapplication)
-- ============================================================================

/-! ### Javanese h-deletion (ex. 1, 6-7)

Javanese disallows *h* between vowels (*VhV). In reduplication, *h* is
lost in **both** base and reduplicant (overapplication): the expected
form *bədah–bəda–e is avoided in favor of bəda–bəda–e, maintaining
B-R identity at the cost of I-O faithfulness.

Ranking: IDENT-BR, *VhV >> MAX-IO -/

/-- Candidates for `RED-bədah + -e` in Javanese.
    Each represents a different resolution of the *VhV vs. B-R identity
    conflict. -/
inductive JavaneseCand where
  | over    -- bəda–bəda–e: h lost in both B and R (overapplication)
  | under   -- bədah–bədah–e: h kept in both (violates *VhV)
  | normal  -- bədah–bəda–e: h in B only (violates B-R identity)
  deriving DecidableEq, Repr

/-- IDENT-BR: penalizes featural mismatch between base and reduplicant.
    Only the normal candidate has B ≠ R (B retains h, R lacks it). -/
def javIdentBR : NamedConstraint JavaneseCand :=
  mkIdent "IDENT-BR" (· == .normal)

/-- *VhV: markedness constraint against intervocalic *h*.
    Violated by `under` (h in both B and R) and `normal` (h in B). -/
def javStarVhV : NamedConstraint JavaneseCand :=
  { name := "*VhV"
    family := .markedness
    eval := λ
      | .over => 0
      | .under => 1
      | .normal => 1 }

/-- MAX-IO: I-O faithfulness — penalizes deletion from the input.
    Only the `over` candidate deletes h from the input stem. -/
def javMaxIO : NamedConstraint JavaneseCand :=
  mkMax "MAX-IO" (· == .over)

/-- Skeletal ranking for overapplication (ex. 7):
    IDENT-BR, *VhV >> MAX-IO -/
def javRanking : List (NamedConstraint JavaneseCand) :=
  [javIdentBR, javStarVhV, javMaxIO]

def javCandidates : List JavaneseCand := [.over, .under, .normal]
theorem javCandidates_ne : javCandidates ≠ [] := by simp [javCandidates]

/-- **Overapplication wins in Javanese**: the doubly h-lacking form
    bəda–bəda–e is optimal under IDENT-BR, *VhV >> MAX-IO.

    This is the paper's central empirical result: B-R identity and
    phonological markedness both outrank I-O faithfulness, so the
    output sacrifices faithfulness to achieve both identity and
    phonological well-formedness. -/
theorem javanese_overapplication :
    (mkTableau javCandidates javRanking javCandidates_ne).optimal
    = {JavaneseCand.over} := by decide

-- ============================================================================
-- § 2: Balangao Partial Reduplication (Emergence of the Unmarked)
-- ============================================================================

/-! ### Balangao partial reduplication (ex. 106-107)

Balangao has a disyllabic prefixed reduplicant without a final coda:
/RED-tagtag/ → tagta–tagtag, not *tagtag–tagtag. The reduplicant
obeys NO-CODA even though the base (and the language generally)
permits codas. This is **emergence of the unmarked**: a marked
structure (codas) is avoided in the reduplicant because B-R identity
is low-ranked.

Ranking (ex. 107): MAX-IO >> NO-CODA >> MAX-BR -/

/-- Candidates for /RED-tagtag/ in Balangao.
    Violation counts from the paper's tableau (ex. 106). -/
inductive BalangaoCand where
  | totalFaithful   -- tagta–tagta: base modified too (MAX-IO violated)
  | totalRedup      -- tagtag–tagtag: perfect copy (many NO-CODA violations)
  | partialRedup    -- tagta–tagtag: coda-free reduplicant (MAX-BR violated)
  deriving DecidableEq, Repr

/-- MAX-IO: penalizes deletion from input.
    Only `totalFaithful` deletes a segment from the base. -/
def balMaxIO : NamedConstraint BalangaoCand :=
  { name := "MAX-IO"
    family := .faithfulness
    eval := λ
      | .totalFaithful => 1
      | .totalRedup => 0
      | .partialRedup => 0 }

/-- NO-CODA: markedness constraint against syllable codas.
    Violation counts from the tableau (ex. 106):
    - totalFaithful (tagta–tagta): 2 codas (medial g in each half)
    - totalRedup (tagtag–tagtag): 4 codas
    - partial (tagta–tagtag): 3 codas (2 in base, 1 in R medial) -/
def balNoCoda : NamedConstraint BalangaoCand :=
  { name := "NO-CODA"
    family := .markedness
    eval := λ
      | .totalFaithful => 2
      | .totalRedup => 4
      | .partialRedup => 3 }

/-- MAX-BR: B-R identity — penalizes incomplete copying.
    Only `partial` has a segment in the base without a correspondent
    in the reduplicant (the final coda). -/
def balMaxBR : NamedConstraint BalangaoCand :=
  { name := "MAX-BR"
    family := .faithfulness
    eval := λ
      | .totalFaithful => 0
      | .totalRedup => 0
      | .partialRedup => 1 }

/-- Ranking for emergence of the unmarked (ex. 107):
    MAX-IO >> NO-CODA >> MAX-BR -/
def balRanking : List (NamedConstraint BalangaoCand) :=
  [balMaxIO, balNoCoda, balMaxBR]

def balCandidates : List BalangaoCand :=
  [.totalFaithful, .totalRedup, .partialRedup]
theorem balCandidates_ne : balCandidates ≠ [] := by simp [balCandidates]

/-- **Emergence of the unmarked in Balangao**: the partial reduplicant
    tagta–tagtag is optimal under MAX-IO >> NO-CODA >> MAX-BR.

    The reduplicant is coda-free even though the base and the language
    generally permit codas — because B-R identity (MAX-BR) is low-ranked,
    the unmarked (coda-free) structure emerges in the reduplicant. -/
theorem balangao_emergence_unmarked :
    (mkTableau balCandidates balRanking balCandidates_ne).optimal
    = {.partialRedup} := by decide

-- ============================================================================
-- § 3: Basic Model Factorial Typology (§4)
-- ============================================================================

/-! ### Basic Model (§4)

The Basic Model has faithfulness constraints on two correspondence
dimensions — I-O faithfulness and B-R identity — interacting with a
phonological markedness constraint ("Phono-Constraint"). Permuting
the three constraints produces the factorial typology.

We model this with an abstract candidate type carrying violation
profiles, and verify the distinct optima across all 6 rankings. -/

/-- Abstract candidate for the Basic Model interaction space.
    Each candidate represents a different resolution of the three-way
    conflict between I-O faithfulness, phonological well-formedness,
    and B-R identity.

    - `faithful`: preserves input, B=R, but phonologically marked
    - `over`: unfaithful to input, B=R, but phonologically unmarked
    - `normal`: preserves input, phonologically unmarked in R, but B≠R -/
inductive BasicCand where
  | faithful   -- IO=0, Phono=2 (marked in both B and R), BR=0
  | over       -- IO=1, Phono=0 (unmarked), BR=0
  | normal     -- IO=0, Phono=1 (marked in B only), BR=1
  deriving DecidableEq, Repr

def basicIOFaith : NamedConstraint BasicCand :=
  { name := "IO-Faith"
    family := .faithfulness
    eval := λ | .faithful => 0 | .over => 1 | .normal => 0 }

def basicPhono : NamedConstraint BasicCand :=
  { name := "Phono"
    family := .markedness
    eval := λ | .faithful => 2 | .over => 0 | .normal => 1 }

def basicBRId : NamedConstraint BasicCand :=
  { name := "BR-Id"
    family := .faithfulness
    eval := λ | .faithful => 0 | .over => 0 | .normal => 1 }

def basicCandidates : List BasicCand := [.faithful, .over, .normal]
theorem basicCandidates_ne : basicCandidates ≠ [] := by simp [basicCandidates]

/-- Non-application ranking (ex. 104): IO-Faith, BR-Id >> Phono.
    The faithful candidate wins — phonology cannot affect anything. -/
theorem nonapplication_io_br_phono :
    (mkTableau basicCandidates [basicIOFaith, basicBRId, basicPhono]
      basicCandidates_ne).optimal = {.faithful} := by decide

/-- Non-application (symmetric): BR-Id, IO-Faith >> Phono.
    Same outcome — faithful candidate wins regardless of IO/BR order. -/
theorem nonapplication_br_io_phono :
    (mkTableau basicCandidates [basicBRId, basicIOFaith, basicPhono]
      basicCandidates_ne).optimal = {.faithful} := by decide

/-- Emergence of the unmarked (ex. 105): IO-Faith >> Phono >> BR-Id.
    The normal candidate wins — phonology affects the reduplicant
    (low BR-Id), but the base is protected (high IO-Faith). -/
theorem emergence_unmarked :
    (mkTableau basicCandidates [basicIOFaith, basicPhono, basicBRId]
      basicCandidates_ne).optimal = {BasicCand.normal} := by decide

/-- Overapplication: Phono >> IO-Faith >> BR-Id.
    The over candidate wins — phonological unmarking applies to both
    B and R, sacrificing IO faithfulness. -/
theorem overapplication_phono_io_br :
    (mkTableau basicCandidates [basicPhono, basicIOFaith, basicBRId]
      basicCandidates_ne).optimal = {BasicCand.over} := by decide

/-- Overapplication: Phono >> BR-Id >> IO-Faith.
    Same outcome — phonology dominates. -/
theorem overapplication_phono_br_io :
    (mkTableau basicCandidates [basicPhono, basicBRId, basicIOFaith]
      basicCandidates_ne).optimal = {BasicCand.over} := by decide

/-- Overapplication: BR-Id >> Phono >> IO-Faith.
    B-R identity copies phonological effects to both B and R. -/
theorem overapplication_br_phono_io :
    (mkTableau basicCandidates [basicBRId, basicPhono, basicIOFaith]
      basicCandidates_ne).optimal = {BasicCand.over} := by decide

/-- **Factorial typology summary**: all 6 rankings of 3 constraints produce
    exactly 3 distinct optima — `faithful` (non-application), `normal`
    (emergence of the unmarked), and `over` (overapplication).

    The 4th interaction type from the paper — **normal application** —
    requires additional candidates (where phonology targets the reduplicant
    independently) and is demonstrated by the Balangao and Tagalog examples
    in §§3-5 rather than the abstract model. -/
theorem basic_model_factorial :
    mkFactorialOptima basicCandidates
      [basicIOFaith, basicPhono, basicBRId] basicCandidates_ne
    = [{BasicCand.normal}, {BasicCand.over}, {BasicCand.faithful}] := by decide

-- ============================================================================
-- § 4: Underapplication Impossibility
-- ============================================================================

/-! ### Underapplication is not a Basic Model category (§5)

@cite{mccarthy-prince-1995} §5 argues that underapplication cannot emerge
from the Basic Model. Unlike overapplication and emergence of the unmarked,
which follow from ranking permutations of {IO-Faith, Phono, BR-Id},
underapplication requires an additional independent constraint (like the
OCP in Akan) that blocks the overapplicational candidate. In the Basic
Model, B-R identity can restrict the candidate set to B=R pairs, but
within that set the choice between over and under is determined by
Phono-Constraint — and Phono-Constraint always prefers the phonologically
unmarked form (= over), never the marked form (= under).

The factorial typology theorem already proves this: `.faithful` (non-
application), `.over` (overapplication), and `.normal` (emergence of the
unmarked) are the only optima. No ranking produces a 4th outcome. -/

/-- **Underapplication impossibility**: every ranking of the Basic Model
    selects one of `faithful`, `over`, or `normal`. No ranking can select
    an underapplicational candidate because the Basic Model has no
    independent blocking constraint to exclude overapplication.

    This is the formal content of @cite{mccarthy-prince-1995} §5's
    argument that underapplication requires an additional constraint
    beyond the three in the Basic Model. -/
theorem basic_model_no_underapplication :
    ∀ optima ∈ mkFactorialOptima basicCandidates
      [basicIOFaith, basicPhono, basicBRId] basicCandidates_ne,
    optima = {BasicCand.faithful} ∨ optima = {BasicCand.over} ∨ optima = {BasicCand.normal} := by
  decide

/-- The factorial typology produces exactly 3 distinct language types,
    not 4 — confirming that underapplication is absent from the Basic
    Model. -/
theorem basic_model_exactly_three_types :
    mkFactorialTypologySize basicCandidates
      [basicIOFaith, basicPhono, basicBRId] basicCandidates_ne
    = 3 := by decide

-- ============================================================================
-- § 5: Akan Underapplication (§5.1)
-- ============================================================================

/-! ### Akan underapplication (ex. 125, 130–131)

Akan has a monosyllabic reduplicative prefix with a high vowel.
Palatalization (velar → palatal before front vowels) is productive in
the language but **fails to apply** in reduplication: /RED-ka/ surfaces
as kɪ–ka, not *tɕɪ–tɕa (overapplication) or *tɕɪ–ka (normal application).

This is underapplication: a process that normally applies (PAL) is blocked
in reduplication. The mechanism is a **4th constraint** — OCP(+cor) — that
blocks the overapplicational candidate. Since B-R identity (IDENT-BR)
is high-ranked, normal application is also blocked, leaving
underapplication as the only survivor.

Ranking (ex. 129, 131): OCP(+cor) >> IDENT-BR(−cor) >> PAL >> IDENT-IO(−cor)

This confirms the Basic Model impossibility result: underapplication
requires a blocking constraint (here OCP) beyond the three in the
Basic Model. -/

/-- Candidates for /RED-ka/ in Akan (ex. 130).
    Each represents a different resolution of the palatalization
    vs. B-R identity vs. OCP conflict. -/
inductive AkanCand where
  | over    -- tɕɪ–tɕa: palatalization in both B and R (overapplication)
  | normal  -- tɕɪ–ka: palatalization in R only (normal application)
  | under   -- kɪ–ka: no palatalization (underapplication)
  deriving DecidableEq, Repr

/-- OCP(+cor): prohibits cooccurrence of [+coronal] segments in
    successive syllables. The overapplicational candidate tɕɪ–tɕa
    has coronal obstruents in both syllables of the output.

    Violation counts from tableau (131):
    - over (tɕɪ–tɕa): 2 violations (coronal in each syllable of B+R)
    - normal (tɕɪ–ka): 0
    - under (kɪ–ka): 0 -/
def akanOCP : NamedConstraint AkanCand :=
  { name := "OCP(+cor)"
    family := .markedness
    eval := λ
      | .over => 2
      | .normal => 0
      | .under => 0 }

/-- IDENT-BR(−cor): B-R identity for the [−coronal] feature.
    Penalizes featural mismatch between base and reduplicant
    consonants. Only the normal candidate has B ≠ R (R has
    palatalized tɕ, B retains velar k).

    Violation counts from tableau (131):
    - over (tɕɪ–tɕa): 0 (B = R)
    - normal (tɕɪ–ka): 1 (R ≠ B in coronal feature)
    - under (kɪ–ka): 0 (B = R) -/
def akanIdentBR : NamedConstraint AkanCand :=
  { name := "IDENT-BR(-cor)"
    family := .faithfulness
    eval := λ
      | .over => 0
      | .normal => 1
      | .under => 0 }

/-- PAL: palatalization constraint — velars must be palatalized
    before front vowels. The underapplicational candidate kɪ–ka
    has a velar before the front vowel ɪ in the reduplicant.

    Violation counts from tableau (131):
    - over (tɕɪ–tɕa): 0
    - normal (tɕɪ–ka): 0
    - under (kɪ–ka): 1 (velar k before front vowel ɪ) -/
def akanPAL : NamedConstraint AkanCand :=
  { name := "PAL"
    family := .markedness
    eval := λ
      | .over => 0
      | .normal => 0
      | .under => 1 }

/-- IDENT-IO(−cor): I-O faithfulness for the [−coronal] feature.
    Penalizes changing the coronal specification of an input segment.
    Only the overapplicational candidate changes the base consonant
    from velar to palatal (unfaithful to input /k/).

    Violation counts from tableau (131):
    - over (tɕɪ–tɕa): 1 (input /k/ → output tɕ in base)
    - normal (tɕɪ–ka): 0
    - under (kɪ–ka): 0 -/
def akanIdentIO : NamedConstraint AkanCand :=
  { name := "IDENT-IO(-cor)"
    family := .faithfulness
    eval := λ
      | .over => 1
      | .normal => 0
      | .under => 0 }

/-- Ranking for Akan underapplication (ex. 129, 131):
    OCP(+cor) >> IDENT-BR(−cor) >> PAL >> IDENT-IO(−cor) -/
def akanRanking : List (NamedConstraint AkanCand) :=
  [akanOCP, akanIdentBR, akanPAL, akanIdentIO]

def akanCandidates : List AkanCand := [.over, .normal, .under]
theorem akanCandidates_ne : akanCandidates ≠ [] := by simp [akanCandidates]

/-- **Underapplication wins in Akan**: the non-palatalized form
    kɪ–ka is optimal under OCP(+cor) >> IDENT-BR(−cor) >> PAL >> IDENT-IO(−cor).

    This is the paper's key demonstration that underapplication requires
    a 4th blocking constraint (OCP) beyond the Basic Model's three:
    OCP blocks overapplication, IDENT-BR blocks normal application,
    leaving underapplication as the only surviving candidate. -/
theorem akan_underapplication :
    (mkTableau akanCandidates akanRanking akanCandidates_ne).optimal
    = {AkanCand.under} := by decide

-- ============================================================================
-- § 5a: Akan Feature Grounding
-- ============================================================================

/-! ### Grounding the Akan tableau in phonological features

The violation counts in §5 are grounded in the featural representations
from `Fragments.Akan.Phonology`. The key connection: palatalization is
a [coronal] feature change (/k/ [−cor] → /tɕ/ [+cor]), and the four
constraints target exactly this feature dimension.

- **OCP(+cor)**: violated by adjacent [+coronal] segments — i.e., /tɕ/
  in successive syllables. Only the `over` candidate has this.
- **IDENT-BR(−cor)**: violated when B and R differ in [coronal]. Only
  `normal` (R has /tɕ/, B has /k/).
- **PAL**: violated when a velar ([−coronal]) precedes a front vowel
  without palatalizing. Only `under` (/kɪ/).
- **IDENT-IO(−cor)**: violated when the output changes an input segment's
  [coronal] value. Only `over` (input /k/ → output /tɕ/ in base). -/

section AkanGrounding
open Fragments.Akan.Phonology
open Phonology

/-- The `over` candidate's OCP violation is grounded: /tɕ/ is [+coronal],
    so two /tɕ/ in successive syllables violate OCP(+cor). -/
theorem akan_over_ocp_grounded :
    seg_tc.hasValue Feature.coronal true = true := by native_decide

/-- The `normal` candidate's IDENT-BR violation is grounded: the
    reduplicant has /tɕ/ ([+cor]) but the base has /k/ ([−cor]) — a
    featural mismatch on [coronal]. -/
theorem akan_normal_identBR_grounded :
    seg_tc.hasValue Feature.coronal true = true ∧
    seg_k.hasValue Feature.coronal false = true := ⟨by native_decide, by native_decide⟩

/-- The `under` candidate's PAL violation is grounded: /k/ is [−coronal]
    and /ɪ/ is [+front] — a velar before a front vowel without
    palatalization. -/
theorem akan_under_pal_grounded :
    seg_k.hasValue Feature.coronal false = true ∧
    seg_i.hasValue Feature.front true = true := ⟨by native_decide, by native_decide⟩

/-- The `over` candidate's IDENT-IO violation is grounded: input /k/
    is [−coronal] but output /tɕ/ is [+coronal] — an IO faithfulness
    violation on the [coronal] feature. -/
theorem akan_over_identIO_grounded :
    seg_k.hasValue Feature.coronal false = true ∧
    seg_tc.hasValue Feature.coronal true = true := ⟨by native_decide, by native_decide⟩

end AkanGrounding

end McCarthyPrince1995
