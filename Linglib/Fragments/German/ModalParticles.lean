import Linglib.Theories.Semantics.UseConditional.LTU
import Linglib.Theories.Semantics.Mood.SentenceMoodUCI
import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment

/-!
# German Modal Particles
@cite{gutzmann-2015}

Lexical entries for German modal particles (*Modalpartikeln*), analyzed
within the L_TU framework.

## Two Kinds of Modal Particle (@cite{gutzmann-2015}, §6.5)

Modal particles fall into two categories with distinct types and restriction
mechanisms:

### Functional Expletive UCIs (ja, denn, halt, doch)

Type: `⟨⟨s,t⟩, u⟩`. These take a proposition and return u-content. They are
[+functional], [−2-dimensional], [−resource-sensitive]. Their mood restriction
arises from **use-conditional conflict**: their independent u-content is
incompatible with certain sentence moods.

### UC-Modifiers (wohl)

Type: `⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩`. These take a UCI and return a modified UCI.
*wohl* modifies the epistemic mood operator EPIS. Its mood restriction is
**selectional**: imperatives lack EPIS, so *wohl* has no argument to modify
— a type mismatch, not a pragmatic conflict.

## Semantic Properties (derived from L_TU)

The special behavior of modal particles follows from their UCI type and
L_TU's composition rules, without any special syntactic assumptions:
- **Non-truth-conditionality**: identity in t-dim (functional expletive)
- **Scopelessness**: u-content is stored by UE, inaccessible to higher operators
- **Unfocusability**: focus operator and MP end up in different dimensions
- **Uncoordinatability**: no LER extends use-conditional coordination to 3D

## Mood Distribution (@cite{gutzmann-2015}, Table 6.1)

| Particle | Declarative | Interrogative | Imperative | Kind        | Restriction |
|----------|-------------|---------------|------------|-------------|-------------|
| ja       | ✓           | ✗             | ✗          | UCI         | conflict    |
| denn     | ✗           | ✓             | ✗          | UCI         | conflict    |
| wohl     | ✓           | ✓             | ✗          | UC-modifier | selectional |
| halt     | ✓           | ✗             | ✗          | UCI         | conflict    |
| doch     | ✓           | ✗             | ✓          | UCI         | conflict    |
-/

namespace Fragments.German.ModalParticles

open Core.Discourse (IllocutionaryMood)
open Semantics.UseConditional (UCIClass UCExprKind RestrictionKind functionalExpletive)
open Semantics.Mood.SentenceMoodUCI (GermanClauseType MoodStructure)


/-- A German modal particle lexical entry.

Follows the pattern of `QuestionParticles.QParticleEntry` with
per-sentence-type distribution booleans for direct per-datum
verification. -/
structure ModalParticleEntry where
  /-- Surface form -/
  form : String
  /-- Whether this is a UCI or a UC-modifier (@cite{gutzmann-2015}, §6.5) -/
  exprKind : UCExprKind
  /-- UCI classification (only meaningful when `exprKind = .uci`) -/
  uciClass : UCIClass
  /-- How mood restriction arises -/
  restrictionKind : RestrictionKind
  /-- Licensed in declarative sentences -/
  declOk : Bool
  /-- Licensed in interrogative sentences -/
  interrogOk : Bool
  /-- Licensed in imperative sentences -/
  imperOk : Bool
  /-- English gloss -/
  glossEnglish : String
  deriving DecidableEq, Repr

/-- Check whether a modal particle is licensed in a given sentence type. -/
def ModalParticleEntry.moodOk (mp : ModalParticleEntry) :
    IllocutionaryMood → Bool
  | .declarative => mp.declOk
  | .interrogative => mp.interrogOk
  | .imperative => mp.imperOk
  | _ => false

/-- Map a German clause type to the distribution field it tests. -/
def ModalParticleEntry.licensedInClause (mp : ModalParticleEntry) :
    GermanClauseType → Bool
  | .dassVL          => false  -- subordinate; MPs generally excluded
  | .v2Declarative   => mp.declOk
  | .v2Interrogative => mp.interrogOk
  | .vlInterrogative => mp.interrogOk
  | .imperative      => mp.imperOk


-- ════════════════════════════════════════════════════════════════
-- § 1. Lexical Entries
-- ════════════════════════════════════════════════════════════════

/-- *ja* — common-ground reminder particle.

Roughly: "as you may already know." Licensed only in declaratives;
excluded from interrogatives and imperatives. Its use condition
references the truth of its propositional argument, conflicting with
the epistemic uncertainty of interrogatives and the non-epistemic
nature of imperatives.

Restriction kind: use-conditional conflict. -/
def ja : ModalParticleEntry where
  form := "ja"
  exprKind := .uci
  uciClass := functionalExpletive
  restrictionKind := .ucConflict
  declOk := true
  interrogOk := false
  imperOk := false
  glossEnglish := "PART (common-ground reminder)"

/-- *denn* — question-prompting particle.

Signals the question is prompted by contextual evidence; the
interrogative counterpart of *ja*. Licensed only in interrogatives;
excluded from declaratives, imperatives, and dass-VL clauses.

Restriction kind: use-conditional conflict. -/
def denn : ModalParticleEntry where
  form := "denn"
  exprKind := .uci
  uciClass := functionalExpletive
  restrictionKind := .ucConflict
  declOk := false
  interrogOk := true
  imperOk := false
  glossEnglish := "PART (question-prompting)"

/-- *wohl* — epistemic hedging particle.

Modifies the epistemic mood operator EPIS, introducing a degree of
uncertainty. Licensed in declaratives and interrogatives (both of
which involve EPIS), but excluded from imperatives (which lack EPIS).

This is a **UC-modifier**, not a functional expletive UCI. Its type is
`⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩` — it takes a UCI (like DEONT composed with
EPIS) and modifies its epistemic component. The restriction is
**selectional**: imperatives lack EPIS, so *wohl* has no argument
to modify (type mismatch). -/
def wohl : ModalParticleEntry where
  form := "wohl"
  exprKind := .ucModifier
  uciClass := functionalExpletive  -- vestigial; exprKind takes precedence
  restrictionKind := .selectional
  declOk := true
  interrogOk := true
  imperOk := false
  glossEnglish := "PART (epistemic hedging)"

/-- *halt* — resignation/acceptance particle.

Roughly: "that's just the way it is." Licensed only in declaratives.

Restriction kind: use-conditional conflict. -/
def halt : ModalParticleEntry where
  form := "halt"
  exprKind := .uci
  uciClass := functionalExpletive
  restrictionKind := .ucConflict
  declOk := true
  interrogOk := false
  imperOk := false
  glossEnglish := "PART (resignation/acceptance)"

/-- *doch* — contradiction/insistence particle.

Signals conflict with an expected or salient counterstance. Uniquely
among common MPs, licensed in both declaratives and imperatives — its
use condition (contradiction of a salient proposition) is compatible
with both deontic-only and deontic/epistemic mood structures.

Restriction kind: use-conditional conflict. -/
def doch : ModalParticleEntry where
  form := "doch"
  exprKind := .uci
  uciClass := functionalExpletive
  restrictionKind := .ucConflict
  declOk := true
  interrogOk := false
  imperOk := true
  glossEnglish := "PART (contradiction/insistence)"

/-- All modal particle entries. -/
def allModalParticles : List ModalParticleEntry := [ja, denn, wohl, halt, doch]

/-- The functional expletive UCI entries (excluding UC-modifiers). -/
def uciParticles : List ModalParticleEntry := [ja, denn, halt, doch]


-- ════════════════════════════════════════════════════════════════
-- § 2. Per-Datum Verification
-- ════════════════════════════════════════════════════════════════

-- Mood distribution

theorem ja_decl_only : ja.declOk = true ∧ ja.interrogOk = false ∧ ja.imperOk = false :=
  ⟨rfl, rfl, rfl⟩

theorem denn_interrog_only : denn.declOk = false ∧ denn.interrogOk = true ∧ denn.imperOk = false :=
  ⟨rfl, rfl, rfl⟩

theorem wohl_decl_and_interrog : wohl.declOk = true ∧ wohl.interrogOk = true ∧ wohl.imperOk = false :=
  ⟨rfl, rfl, rfl⟩

theorem halt_decl_only : halt.declOk = true ∧ halt.interrogOk = false ∧ halt.imperOk = false :=
  ⟨rfl, rfl, rfl⟩

theorem doch_decl_and_imper : doch.declOk = true ∧ doch.interrogOk = false ∧ doch.imperOk = true :=
  ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 3. Structural Classification
-- ════════════════════════════════════════════════════════════════

/-- Every true UCI among these particles is a functional expletive. -/
theorem uci_mps_functional_expletive :
    ∀ mp ∈ uciParticles, mp.exprKind = .uci → mp.uciClass = functionalExpletive := by
  intro mp hm _
  simp [uciParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> rfl

/-- wohl is the only UC-modifier among these particles. -/
theorem wohl_unique_uc_modifier :
    ∀ mp ∈ allModalParticles, mp.exprKind = .ucModifier → mp.form = "wohl" := by
  intro mp hm hk
  simp [allModalParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp_all [ja, denn, wohl, halt, doch]

/-- Every UCI in this list has conflict-based restriction;
the UC-modifier has selectional restriction. -/
theorem restriction_tracks_kind :
    ∀ mp ∈ allModalParticles,
      (mp.exprKind = .uci → mp.restrictionKind = .ucConflict) ∧
      (mp.exprKind = .ucModifier → mp.restrictionKind = .selectional) := by
  intro mp hm
  simp [allModalParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- *doch* is the only common MP licensed in imperatives. -/
theorem doch_unique_imperative :
    ∀ mp ∈ allModalParticles, mp.imperOk = true → mp.form = "doch" := by
  intro mp hm hi
  simp [allModalParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp_all [ja, denn, wohl, halt, doch]

/-- No MP is licensed in all three sentence types. -/
theorem no_mp_universal :
    ∀ mp ∈ allModalParticles, ¬(mp.declOk = true ∧ mp.interrogOk = true ∧ mp.imperOk = true) := by
  intro mp hm ⟨hd, hi, him⟩
  simp [allModalParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp_all [ja, denn, wohl, halt, doch]


-- ════════════════════════════════════════════════════════════════
-- § 4. Derived Licensing from Mood Structure
-- ════════════════════════════════════════════════════════════════

/-- wohl's licensing across ALL German clause types is exactly determined
by the presence of EPIS in the clause type's mood structure.

This is the formal content of the selectional restriction analysis:
wohl modifies EPIS, so it is licensed iff EPIS is present. -/
theorem wohl_iff_epis :
    ∀ ct : GermanClauseType,
      wohl.licensedInClause ct = ct.moodStructure.hasEpistemic := by
  intro ct; cases ct <;> rfl

/-- Every MP is excluded from dass-VL clauses (subordinate, no matrix mood). -/
theorem all_excluded_from_dassVL :
    ∀ mp ∈ allModalParticles, mp.licensedInClause .dassVL = false := by
  intro mp hm
  simp [allModalParticles] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- *ja* and *denn* are in complementary distribution: for every clause
type, at most one of them is licensed. -/
theorem ja_denn_complementary :
    ∀ ct : GermanClauseType,
      ¬(ja.licensedInClause ct = true ∧ denn.licensedInClause ct = true) := by
  intro ct ⟨hj, hd⟩; cases ct <;> simp_all [ModalParticleEntry.licensedInClause, ja, denn]

end Fragments.German.ModalParticles
