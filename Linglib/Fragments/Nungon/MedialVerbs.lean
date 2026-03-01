import Linglib.Core.Lexical.UD

/-!
# Nungon Medial Verb Morphology @cite{sarvasy-2017}
@cite{sarvasy-2015} @cite{sarvasy-aikhenvald-2025}

Medial verb morphology in Nungon (Trans-New Guinea, Finisterre-Huon family;
Morobe Province, Papua New Guinea). Nungon has the most extensively described
clause chaining system in the recent literature.

## Key properties

Nungon medial verbs are maximally reduced: they carry no tense, no aspect,
and no independent mood marking. The single final verb in each chain supplies
tense and mood for the entire chain. The only morphology on a medial verb is:
1. The verb stem
2. A switch-reference suffix encoding subject continuity (SS vs. DS) and
   temporal relation (sequential vs. simultaneous)

## Switch-reference

The SR system is four-way, crossing two binary dimensions:
- **Subject continuity**: same subject (SS) vs. different subject (DS)
- **Temporal relation**: sequential (SEQ) vs. simultaneous (SIM)

SS forms are invariant (no person/number indexing). DS forms obligatorily
index the person and number of the medial clause's subject argument — the
participant whose identity *differs* from the following clause's subject.

## DS person/number paradigm (Sarvasy 2025: Table 2)

| Person | Singular | Dual | Plural |
|--------|----------|------|--------|
| 1 | -wa-ya | -ra-ya | -na-ya |
| 2 | -i-ya | -uny-a | -u-ya |
| 3 | -un-a | -uny-a | -u-ya |

Note: 2du and 3du are syncretic (-uny-a); 2pl and 3pl are syncretic (-u-ya).

-/

namespace Fragments.Nungon.MedialVerbs

-- ============================================================================
-- § SR suffix types
-- ============================================================================

/-- Switch-reference category combining subject continuity and temporal relation.
    Nungon has a four-way system: SS-SEQ, SS-SIM, DS-SEQ, DS-SIM. -/
inductive SRCategory where
  | ssSEQ  -- same subject, sequential events
  | ssSIM  -- same subject, simultaneous events
  | dsSEQ  -- different subject, sequential events
  | dsSIM  -- different subject, simultaneous events
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether this SR category indicates same subject. -/
def SRCategory.isSS : SRCategory → Bool
  | .ssSEQ | .ssSIM => true
  | .dsSEQ | .dsSIM => false

/-- Whether this SR category indicates sequential temporal relation. -/
def SRCategory.isSequential : SRCategory → Bool
  | .ssSEQ | .dsSEQ => true
  | .ssSIM | .dsSIM => false

-- ============================================================================
-- § DS person/number paradigm (Sarvasy 2025: Table 2)
-- ============================================================================

/-- Person/number combination for DS medial verb agreement. -/
structure PersonNumber where
  person : UD.Person
  number : UD.Number
  deriving DecidableEq, Repr, BEq

/-- A DS suffix entry: form + person/number it indexes. -/
structure DSSuffix where
  form : String
  personNumber : PersonNumber
  deriving Repr, BEq

/-- 1sg DS suffix. -/
def ds1sg : DSSuffix := { form := "-wa-ya", personNumber := ⟨.first, .Sing⟩ }
/-- 2sg DS suffix. -/
def ds2sg : DSSuffix := { form := "-i-ya", personNumber := ⟨.second, .Sing⟩ }
/-- 3sg DS suffix. -/
def ds3sg : DSSuffix := { form := "-un-a", personNumber := ⟨.third, .Sing⟩ }
/-- 1du DS suffix. -/
def ds1du : DSSuffix := { form := "-ra-ya", personNumber := ⟨.first, .Dual⟩ }
/-- 2du DS suffix (syncretic with 3du). -/
def ds2du : DSSuffix := { form := "-uny-a", personNumber := ⟨.second, .Dual⟩ }
/-- 3du DS suffix (syncretic with 2du). -/
def ds3du : DSSuffix := { form := "-uny-a", personNumber := ⟨.third, .Dual⟩ }
/-- 1pl DS suffix. -/
def ds1pl : DSSuffix := { form := "-na-ya", personNumber := ⟨.first, .Plur⟩ }
/-- 2pl DS suffix (syncretic with 3pl). -/
def ds2pl : DSSuffix := { form := "-u-ya", personNumber := ⟨.second, .Plur⟩ }
/-- 3pl DS suffix (syncretic with 2pl). -/
def ds3pl : DSSuffix := { form := "-u-ya", personNumber := ⟨.third, .Plur⟩ }

/-- Full DS paradigm. -/
def dsParadigm : List DSSuffix :=
  [ds1sg, ds2sg, ds3sg, ds1du, ds2du, ds3du, ds1pl, ds2pl, ds3pl]

-- ============================================================================
-- § SS suffixes
-- ============================================================================

/-- SS suffixes are invariant (no person/number indexing). -/
structure SSSuffix where
  form : String
  category : SRCategory
  deriving Repr, BEq

/-- SS sequential suffix. -/
def ssSEQ : SSSuffix := { form := "-se", category := .ssSEQ }

/-- SS simultaneous suffix. -/
def ssSIM : SSSuffix := { form := "-ma", category := .ssSIM }

/-- All SS suffixes. -/
def ssSuffixes : List SSSuffix := [ssSEQ, ssSIM]

-- ============================================================================
-- § Verification theorems
-- ============================================================================

/-- 9 cells in the DS paradigm (3 persons x 3 numbers). -/
theorem ds_paradigm_size : dsParadigm.length = 9 := rfl

/-- 2 SS suffixes (sequential and simultaneous). -/
theorem ss_suffix_count : ssSuffixes.length = 2 := rfl

/-- 2du and 3du are syncretic (same form). -/
theorem du_syncretism : ds2du.form = ds3du.form := rfl

/-- 2pl and 3pl are syncretic (same form). -/
theorem pl_syncretism : ds2pl.form = ds3pl.form := rfl

/-- SS-SEQ is same-subject. -/
theorem ssSEQ_is_ss : SRCategory.ssSEQ.isSS = true := rfl

/-- DS-SEQ is different-subject. -/
theorem dsSEQ_is_ds : SRCategory.dsSEQ.isSS = false := rfl

/-- SS-SEQ is sequential. -/
theorem ssSEQ_is_seq : SRCategory.ssSEQ.isSequential = true := rfl

/-- SS-SIM is not sequential (it's simultaneous). -/
theorem ssSIM_not_seq : SRCategory.ssSIM.isSequential = false := rfl

end Fragments.Nungon.MedialVerbs
