import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Noun.Basic

/-!
# Russian Noun Gender
[wade-2020] [corbett-1991] [kramer-2020] [kramer-2015] [corbett-1998]

Russian has three surface genders: masculine, feminine, neuter. Gender
is partly determined by the referent's biological sex (semantic core)
and partly by morphological declension class.

## Theory-neutral data layer

Each entry is a `GenderedNoun` over the three controller genders, with a
declension class besides:

- `gender : Value` — the agreement-trigger fact (verified against
  [wade-2020]).
- `isNaturalGender : Bool` — whether the gender comes from the
  referent's biological sex.
- `declClass : Option DeclClass` — Russian-specific morphological
  classification ([wade-2020]). Optional because semantic-core
  nouns get their gender from the referent, not morphology.

These fields suffice to project entries to [kramer-2015] Ch. 7's
5-n DM analysis (projection in `Studies/Kramer2020.lean`); they also
support [corbett-1991]'s controller-target classification directly.

## Hybrid nouns

*vrač* 'doctor' triggers feminine agreement on some targets (verb,
predicate adjective) when the referent is female, while retaining
masculine morphology ([wade-2020], e.g. "Врач обязана..." with
fem.-agreeing predicate; [corbett-1991]). The Fragment encodes
*vrač*'s morphological gender (masculine, derived from Class I); the
hybrid agreement datum is `Kramer2020.hybridTargets`.

## Per-entry verification

Entries explicitly named in [kramer-2015]: *otec*, *put'*, *vrač*.
All others are extrapolations from Kramer's framework, anchored on
[wade-2020]'s declension and gender treatment + [corbett-1991]'s
canonical 5-language sample. *kost'* (Class III feminine) verified at
Wade ≈ noun-declension tables; *put'* (Class III masculine, sole
exception) verified at Wade §6397; *znamja* (-мя neuter) is the textbook
Class III neuter group.
-/

namespace Russian.Gender

-- ============================================================================
-- § 1: Genders and Declension Classes ([wade-2020])
-- ============================================================================

/-- Russian's three controller genders — the carrier of its
    `Gender.System` ([corbett-1991]; [kramer-2015] ch. 7). -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine
  | .neut => .neuter

instance : HasGender Value := ⟨λ g => genderOf g.toLabel⟩

/-- Russian declension classes. Gender correlates with class but neither
    fully determines the other ([corbett-1991];
    [kramer-2020] §2.3.2). -/
inductive DeclClass where
  | I    -- e.g. zakon 'law' (typically masculine)
  | II   -- e.g. škola 'school' (typically feminine)
  | III  -- e.g. kost' 'bone' (typically feminine; exceptions: put', znamja)
  | IV   -- remaining patterns (typically neuter)
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Russian Noun (theory-neutral schema)
-- ============================================================================

/-- A Russian noun: its gender, whether that gender comes from the
    referent's sex, and its declension class. No commitment to any
    specific theoretical framework — Kramer's DM categorizing head and
    Corbett's controller-target classification are projections in
    `Studies/`. For *vrač* 'doctor' (hybrid) the morphological gender is
    encoded; the hybrid female-referent agreement is the datum
    `Kramer2020.hybridTargets`. -/
structure Noun extends GenderedNoun Value where
  /-- Optional declension class. Semantic-core nouns may omit since
      their gender is determined by the referent. -/
  declClass : Option DeclClass := none
  deriving DecidableEq, Repr

instance : HasGender Noun := ⟨λ n => genderOf n.gender⟩

-- ============================================================================
-- § 3: Semantic Core ([kramer-2020] ex. 17)
-- ============================================================================

def otec : Noun := { form := "otec", gloss := "father", gender := .masc, isNaturalGender := true }
def mat' : Noun := { form := "mat'", gloss := "mother", gender := .fem, isNaturalGender := true }
def brat : Noun := { form := "brat", gloss := "brother", gender := .masc, isNaturalGender := true }
def sestra : Noun :=
  { form := "sestra", gloss := "sister", gender := .fem, isNaturalGender := true }
def byk : Noun := { form := "byk", gloss := "bull", gender := .masc, isNaturalGender := true }
def korova : Noun := { form := "korova", gloss := "cow", gender := .fem, isNaturalGender := true }
/-- *djadja* 'uncle': declension II like most feminines, masculine by sex ([wade-2020];
    [corbett-1991]). -/
def djadja : Noun :=
  { form := "djadja", gloss := "uncle", gender := .masc, isNaturalGender := true
  , declClass := some .II }

-- ============================================================================
-- § 4: Remainder — Declension-Class Correlation ([kramer-2020] ex. 18)
-- ============================================================================

def zakon : Noun := { form := "zakon", gloss := "law", gender := .masc, declClass := some .I }
def škola : Noun := { form := "škola", gloss := "school", gender := .fem, declClass := some .II }
def kost' : Noun := { form := "kost'", gloss := "bone", gender := .fem, declClass := some .III }
def vino : Noun := { form := "vino", gloss := "wine", gender := .neut, declClass := some .IV }

-- ============================================================================
-- § 5: Class III Exceptions ([kramer-2020] ex. 19)
-- ============================================================================

/-- *znamja* 'banner': Class III but neuter, not feminine (the -мя
    neuter group; [corbett-1991]; [kramer-2020] ex. 19a). -/
def znamja : Noun :=
  { form := "znamja", gloss := "banner", gender := .neut, declClass := some .III }

/-- *put'* 'way': the only masculine noun in Class III
    ([wade-2020] §6397: "путь is qualified by masculine adjectives";
    [corbett-1991]; [kramer-2020] ex. 19b). -/
def put' : Noun := { form := "put'", gloss := "way", gender := .masc, declClass := some .III }

-- ============================================================================
-- § 6: Hybrid Noun ([kramer-2020] ex. 15–16)
-- ============================================================================

/-- *vrač* 'doctor': morphologically masculine (Class I), but triggers
    feminine agreement on some targets when the referent is female
    (verified at [wade-2020] "Врач обязана…" with feminine-agreeing
    predicate). The Fragment encodes morphological gender; the hybrid
    behavior is the datum `Kramer2020.hybridTargets`. -/
def vrač : Noun := { form := "vrač", gloss := "doctor", gender := .masc, declClass := some .I }

-- ============================================================================
-- § 7: Inventory
-- ============================================================================

def semanticCoreNouns : List Noun :=
  [otec, mat', brat, sestra, byk, korova, djadja]

def remainderNouns : List Noun :=
  [zakon, škola, kost', vino, znamja, put']

def allNouns : List Noun :=
  semanticCoreNouns ++ remainderNouns ++ [vrač]

-- ============================================================================
-- § 8: Cross-class observation
-- ============================================================================

/-- Declension class does not determine gender: *znamja* and *kost'*
    share Class III but differ in surface gender (the Class III
    counter-correlation [corbett-1991] highlights). -/
theorem declClass_ne_gender :
    znamja.declClass = kost'.declClass ∧ znamja.gender ≠ kost'.gender := ⟨rfl, by decide⟩

-- ============================================================================
-- § 9: Gender System (`Gender.System` instantiation)
-- ============================================================================

/-- Past-tense verbal concord exponents: *-∅* / *-a* / *-o*
    ([wade-2020]). Evidence type for `Gender.Faithful`. -/
inductive PastConcord where
  | zero
  | a
  | o
  deriving DecidableEq, Repr

/-- Per-gender past-tense concord. -/
def Value.pastConcord : Value → PastConcord
  | .masc => .zero
  | .fem  => .a
  | .neut => .o

/-- The nominative endings of a hard-stem adjective such as *novyj* 'new': *-yj*, *-aja*,
*-oe* by gender in the singular, *-ye* for all three in the plural ([wade-2020];
[corbett-1998]). -/
inductive AdjEnding where
  | yj
  | aja
  | oe
  | ye
  deriving DecidableEq, Repr, Fintype

/-- The nominative ending by gender and number. -/
def Value.adjEnding : Value → Bool → AdjEnding
  | .masc, false => .yj
  | .fem, false => .aja
  | .neut, false => .oe
  | _, true => .ye

/-- The singular ending alone distinguishes the three genders. -/
theorem faithful_adjEnding : Function.Injective (Value.adjEnding · false) := by decide

/-- The Russian gender system over its own carrier: full comparative
    labelling; neuter is the morphosyntactic default (the all-others
    nouns like *vino* of [corbett-1991]'s declension rule surface neuter,
    at `Kramer2020.declensionGender`). -/
def system : Gender.System Value where
  label := λ g => some g.toLabel
  default := .neut

/-- The assigned system: every noun gets its controller gender. For the
    hybrid *vrač* this is the morphological masculine; the
    female-referent agreement alternation is the datum
    `Kramer2020.hybridTargets`. -/
def assigned : Gender.System.Assigned Noun Value := { system with assign := (·.gender) }

/-- The carrier is faithful to the past-tense concord evidence:
    *-∅* / *-a* / *-o* distinguishes all three genders on a single
    target. [corbett-1991]'s genders-are-agreement-classes criterion. -/
theorem faithful_pastConcord : Function.Injective Value.pastConcord := by decide

/-- [kramer-2015]'s (7ii) / [dahl-2000]'s generalization instantiated:
    the natural-gender nouns form a semantic core, their gender being the
    referent-sex classification. The hybrid *vrač* and the
    declension-class remainder are outside the core. -/
theorem assigned_semanticCore :
    assigned.SemanticCore {n | n.isNaturalGender = true} (·.gender) :=
  ⟨⟨mat', rfl⟩, λ _ _ _ _ h => h⟩

end Russian.Gender
