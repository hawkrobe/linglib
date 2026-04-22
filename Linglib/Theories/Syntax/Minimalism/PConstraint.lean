import Linglib.Core.Prominence
import Linglib.Theories.Syntax.Minimalism.PersonGeometry

/-!
# The P-Constraint: Person Hierarchy Effects via Point-of-View
@cite{pancheva-zubizarreta-2018}

@cite{pancheva-zubizarreta-2018} (P&Z) attribute PCC effects to the encoding
of point-of-view centers within a phase defined by an argument-introducing
verbal head (Appl). Their P-Constraint has four parametric components:

1. **Domain of application**: the interpretable person feature is present on
   all Appl heads (default), or only on those whose phase contains a
   [+author]-marked DP (restricted).
2. **P-Prominence**: an *n*-valued D at the phase edge must enter an Agree
   relation with the interpretable person feature. *n* is [+PROXIMATE]
   (default), restricted to [+PARTICIPANT] or [+AUTHOR].
3. **P-Uniqueness**: at most one DP in α can agree with the interpretable
   person feature (default: active).
4. **P-Primacy**: if P-Uniqueness is active and multiple DPs can agree,
   the [+AUTHOR] DP takes priority (default: inactive).

## Contextual Proximate Marking

SAPs are inherently [+PROXIMATE]. 3P arguments are [-PROXIMATE] by default
but can be contextually marked [+PROXIMATE] when co-occurring with another
3P in the same Appl domain. This contextual mechanism applies ONLY to the
[+PROXIMATE] prominence setting — [+PARTICIPANT] and [+AUTHOR] are inherent
features with no contextual variant.

## PCC Typology

| Variety       | P-Prominence  | P-Uniqueness | P-Primacy | Domain     | Licit |
|---------------|---------------|-------------|-----------|------------|-------|
| Strong        | +proximate    | active      | inactive  | all (dflt) | 3     |
| Ultra-strong  | +proximate    | active      | active    | all        | 5     |
| Weak          | +proximate    | inactive    | (n/a)     | all        | 7     |
| Super-strong  | +participant  | active      | inactive  | all        | 2     |
| Me-first      | +author       | active      | inactive  | restricted | 6     |

-/

namespace Minimalism.PConstraint

open Core.Prominence (PersonLevel)
open Minimalism (DecomposedPerson decomposePerson)

-- ============================================================================
-- § 1: Proximacy
-- ============================================================================

/-- Whether a DP is inherently [+PROXIMATE]. SAPs are inherently
    [+PROXIMATE]; 3P is not (requires contextual marking). -/
def isInherentlyProximate (p : PersonLevel) : Bool :=
  (decomposePerson p).hasProximate

-- ============================================================================
-- § 2: P-Prominence Settings
-- ============================================================================

/-- P-Prominence settings: what feature value the interpretable person
    feature on Appl requires for Agree.

    Correspond to logophoric roles (Sells 1987):
    - `.proximate` → pivot (default, least restrictive)
    - `.participant` → self (attitude holder)
    - `.author` → source (most restrictive) -/
inductive PProminence where
  | proximate    -- default: [+PROXIMATE]
  | participant  -- restricted: [+PARTICIPANT]
  | author       -- most restricted: [+AUTHOR]
  deriving DecidableEq, Repr

/-- Does a DP inherently satisfy the P-Prominence condition? -/
def satisfiesProminence (setting : PProminence) (p : PersonLevel) : Bool :=
  let dp := decomposePerson p
  match setting with
  | .proximate   => dp.hasProximate
  | .participant => dp.hasParticipant
  | .author      => dp.hasAuthor

-- ============================================================================
-- § 3: PCC Grammar — Full Parametric System
-- ============================================================================

/-- A PCC grammar is parameterized by four settings of the P-Constraint. -/
structure PCCGrammar where
  /-- P-Prominence: what person feature the IO must satisfy.
      Default: `proximate`. -/
  prominence : PProminence := .proximate
  /-- P-Uniqueness: at most one DP can agree with the interpretable
      person feature. Default: `true` (active). -/
  uniqueness : Bool := true
  /-- P-Primacy: when both DPs satisfy P-Prominence, the [+author]
      DP takes priority as IO. Conditional on P-Uniqueness.
      Default: `false` (inactive). -/
  primacy : Bool := false
  /-- Domain: whether the interpretable person feature is present on
      ALL Appl heads (false = default) or only when a [+author] DP
      is present (true = restricted). -/
  restrictedDomain : Bool := false
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: Grammar Instances
-- ============================================================================

/-- **Strong PCC**: all defaults. DO must be 3P. -/
def strongGrammar : PCCGrammar := ⟨.proximate, true, false, false⟩

/-- **Ultra-strong PCC**: P-Primacy active. Allows ⟨1,2⟩ but not ⟨2,1⟩. -/
def ultraStrongGrammar : PCCGrammar := ⟨.proximate, true, true, false⟩

/-- **Weak PCC**: P-Uniqueness inactive. Allows SAP co-occurrence. -/
def weakGrammar : PCCGrammar := ⟨.proximate, false, false, false⟩

/-- **Super-strong PCC**: [+participant] prominence. IO must be SAP. -/
def superStrongGrammar : PCCGrammar := ⟨.participant, true, false, false⟩

/-- **Me-first PCC**: [+author] prominence, restricted domain. -/
def meFirstGrammar : PCCGrammar := ⟨.author, true, false, true⟩

/-- **PG1** (predicted): [+participant] + P-Primacy. -/
def pg1Grammar : PCCGrammar := ⟨.participant, true, true, false⟩

/-- **PG2** (predicted): [+participant], no P-Uniqueness. -/
def pg2Grammar : PCCGrammar := ⟨.participant, false, false, false⟩

/-- **PG3** (predicted): [+author], unrestricted domain. -/
def pg3Grammar : PCCGrammar := ⟨.author, true, false, false⟩

-- ============================================================================
-- § 5: PCC Evaluation
-- ============================================================================

/-- Is a ditransitive clitic combination licit under a given PCC grammar?

    `ioPerson` and `doPerson` are the **interpretable** person values.

    The logic:
    1. **Domain**: if restricted and no [+author] DP present, P-Constraint
       does not apply.
    2. **P-Prominence**: IO must satisfy the prominence condition. For
       [+proximate], a 3P IO can satisfy contextually when paired with
       another 3P (contextual proximate marking). For [+participant] and
       [+author], satisfaction is inherent only.
    3. **P-Uniqueness**: if active, at most one DP may inherently satisfy
       the prominence condition. Contextually-marked 3P IOs don't
       trigger this (the DO in ⟨3,3⟩ stays [-proximate]).
    4. **P-Primacy**: when P-Uniqueness is violated, if the IO is
       [+author], it takes priority and the violation is rescued. -/
def pccLicit (g : PCCGrammar) (ioPerson doPerson : PersonLevel) : Bool :=
  let ioDp := decomposePerson ioPerson
  let doDp := decomposePerson doPerson
  -- Step 1: Domain restriction
  if g.restrictedDomain && !ioDp.hasAuthor && !doDp.hasAuthor then true
  else
    let ioInherently := satisfiesProminence g.prominence ioPerson
    -- Contextual proximate marking: a 3P IO can satisfy [+proximate]
    -- when the DO is also 3P. This mechanism applies ONLY to [+proximate].
    let ioContextually := g.prominence == .proximate &&
                          !ioInherently &&
                          !(satisfiesProminence g.prominence doPerson)
    let ioSatisfies := ioInherently || ioContextually
    -- Step 2: P-Prominence — IO must satisfy
    if !ioSatisfies then false
    else if g.uniqueness then
      -- Step 3: P-Uniqueness — does DO also inherently satisfy?
      -- (Contextually-marked 3P DO doesn't count — only IO gets
      -- the contextual marking in ⟨3,3⟩.)
      let doInherently := satisfiesProminence g.prominence doPerson
      if doInherently then
        -- Violation — check P-Primacy rescue
        if g.primacy then ioDp.hasAuthor
        else false
      else true
    else true

-- ============================================================================
-- § 6: Verification — Strong PCC
-- ============================================================================

theorem strong_1_3 : pccLicit strongGrammar .first .third = true := rfl
theorem strong_2_3 : pccLicit strongGrammar .second .third = true := rfl
theorem strong_3_3 : pccLicit strongGrammar .third .third = true := rfl
theorem strong_3_1 : pccLicit strongGrammar .third .first = false := rfl
theorem strong_3_2 : pccLicit strongGrammar .third .second = false := rfl
theorem strong_1_2 : pccLicit strongGrammar .first .second = false := rfl
theorem strong_2_1 : pccLicit strongGrammar .second .first = false := rfl
theorem strong_1_1 : pccLicit strongGrammar .first .first = false := rfl
theorem strong_2_2 : pccLicit strongGrammar .second .second = false := rfl

-- ============================================================================
-- § 7: Verification — Ultra-strong PCC
-- ============================================================================

theorem ultra_1_3 : pccLicit ultraStrongGrammar .first .third = true := rfl
theorem ultra_2_3 : pccLicit ultraStrongGrammar .second .third = true := rfl
theorem ultra_3_3 : pccLicit ultraStrongGrammar .third .third = true := rfl
/-- Ultra-strong allows ⟨1,2⟩: P-Primacy rescues (1P is [+author]). -/
theorem ultra_1_2 : pccLicit ultraStrongGrammar .first .second = true := rfl
theorem ultra_1_1 : pccLicit ultraStrongGrammar .first .first = true := rfl
/-- Ultra-strong bans ⟨2,1⟩: 2P IO lacks [+author], no P-Primacy rescue. -/
theorem ultra_2_1 : pccLicit ultraStrongGrammar .second .first = false := rfl
theorem ultra_3_1 : pccLicit ultraStrongGrammar .third .first = false := rfl
theorem ultra_3_2 : pccLicit ultraStrongGrammar .third .second = false := rfl
theorem ultra_2_2 : pccLicit ultraStrongGrammar .second .second = false := rfl

-- ============================================================================
-- § 8: Verification — Weak PCC
-- ============================================================================

theorem weak_1_3 : pccLicit weakGrammar .first .third = true := rfl
theorem weak_2_3 : pccLicit weakGrammar .second .third = true := rfl
theorem weak_3_3 : pccLicit weakGrammar .third .third = true := rfl
theorem weak_1_2 : pccLicit weakGrammar .first .second = true := rfl
theorem weak_2_1 : pccLicit weakGrammar .second .first = true := rfl
theorem weak_1_1 : pccLicit weakGrammar .first .first = true := rfl
theorem weak_2_2 : pccLicit weakGrammar .second .second = true := rfl
theorem weak_3_1 : pccLicit weakGrammar .third .first = false := rfl
theorem weak_3_2 : pccLicit weakGrammar .third .second = false := rfl

-- ============================================================================
-- § 9: Verification — Super-strong PCC
-- ============================================================================

theorem super_1_3 : pccLicit superStrongGrammar .first .third = true := rfl
theorem super_2_3 : pccLicit superStrongGrammar .second .third = true := rfl
/-- Super-strong bans ⟨3,3⟩: 3P IO is not [+participant]. -/
theorem super_3_3 : pccLicit superStrongGrammar .third .third = false := rfl
theorem super_3_1 : pccLicit superStrongGrammar .third .first = false := rfl
theorem super_3_2 : pccLicit superStrongGrammar .third .second = false := rfl
theorem super_1_2 : pccLicit superStrongGrammar .first .second = false := rfl
theorem super_2_1 : pccLicit superStrongGrammar .second .first = false := rfl

-- ============================================================================
-- § 10: Verification — Me-first PCC
-- ============================================================================

theorem mefirst_1_2 : pccLicit meFirstGrammar .first .second = true := rfl
theorem mefirst_1_3 : pccLicit meFirstGrammar .first .third = true := rfl
theorem mefirst_2_3 : pccLicit meFirstGrammar .second .third = true := rfl
theorem mefirst_3_2 : pccLicit meFirstGrammar .third .second = true := rfl
theorem mefirst_3_3 : pccLicit meFirstGrammar .third .third = true := rfl
theorem mefirst_2_2 : pccLicit meFirstGrammar .second .second = true := rfl
theorem mefirst_3_1 : pccLicit meFirstGrammar .third .first = false := rfl
theorem mefirst_2_1 : pccLicit meFirstGrammar .second .first = false := rfl

-- ============================================================================
-- § 11: Entailment Relations
-- ============================================================================

/-- Strong PCC entails Weak PCC: anything licit under strong is licit
    under weak. (Strong is strictly more restrictive.) -/
theorem strong_entails_weak (io do_ : PersonLevel) :
    pccLicit strongGrammar io do_ = true → pccLicit weakGrammar io do_ = true := by
  cases io <;> cases do_ <;> decide

/-- Strong PCC entails Ultra-strong PCC: anything licit under strong
    is licit under ultra-strong. (Ultra-strong adds P-Primacy, which
    only rescues — never bans — so it is less restrictive.) -/
theorem strong_entails_ultra (io do_ : PersonLevel) :
    pccLicit strongGrammar io do_ = true → pccLicit ultraStrongGrammar io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 12: Markedness — Parameter Departures from Default
-- ============================================================================

/-- Count licit combinations (out of 9 = 3×3). -/
def licitCount (g : PCCGrammar) : Nat :=
  let ps : List PersonLevel := [.first, .second, .third]
  (ps.flatMap (λ io => ps.filter (λ do_ => pccLicit g io do_))).length

/-- Count parameter departures from the default (strong PCC). -/
def parameterDepartures (g : PCCGrammar) : Nat :=
  (if g.prominence != .proximate then 1 else 0) +
  (if !g.uniqueness then 1 else 0) +
  (if g.primacy then 1 else 0) +
  (if g.restrictedDomain then 1 else 0)

/-- Strong PCC is the default (0 departures). -/
theorem strong_is_default : parameterDepartures strongGrammar = 0 := rfl

/-- Ultra-strong and weak each have 1 departure. -/
theorem ultra_one_departure : parameterDepartures ultraStrongGrammar = 1 := rfl
theorem weak_one_departure : parameterDepartures weakGrammar = 1 := rfl

/-- Me-first has 2 departures (prominence + domain). -/
theorem mefirst_two_departures : parameterDepartures meFirstGrammar = 2 := rfl

-- ============================================================================
-- § 13: Polite Pronouns
-- ============================================================================

/-- A polite pronoun with interpretable 2nd person is inherently
    [+PROXIMATE], triggering PCC effects in DO position. -/
theorem proximate_from_interpretable_2nd :
    isInherentlyProximate .second = true := rfl

/-- PCC effect with polite pronoun in DO, 3rd person IO (Weak PCC). -/
theorem polite_do_triggers_weak_pcc :
    pccLicit weakGrammar .third .second = false := rfl

/-- Morphosyntactic accounts evaluate agreement person (3rd) → licit. -/
theorem agreement_person_wrongly_predicts_licit :
    pccLicit weakGrammar .third .third = true := rfl

-- ============================================================================
-- § 14: Impossible Grammar — Me-first + *<3,3>
-- ============================================================================

/-- Me-first grammar cannot exhibit *<3,3> effects: the domain
    restriction exempts ⟨3,3⟩ combinations entirely. -/
theorem mefirst_allows_3_3 : pccLicit meFirstGrammar .third .third = true := rfl

end Minimalism.PConstraint
