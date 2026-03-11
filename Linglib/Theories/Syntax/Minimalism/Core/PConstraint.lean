import Linglib.Core.Prominence
import Linglib.Theories.Syntax.Minimalism.Core.PersonGeometry

/-!
# The P-Constraint: Person Hierarchy Effects via Point-of-View
@cite{pancheva-zubizarreta-2018}

@cite{pancheva-zubizarreta-2018} (P&Z) attribute PCC effects to the encoding
of point-of-view centers within a phase defined by an argument-introducing
verbal head (Appl). Their P-Constraint has four parametric components:

1. **Domain of application**: the interpretable person feature is present on
   all heads of a certain functional category (default).
2. **P-Prominence**: an *n*-valued D at the phase edge must enter an Agree
   relation with the interpretable person feature. *n* is [+PROXIMATE]
   (default), restricted to [+PARTICIPANT] or [+AUTHOR].
3. **P-Uniqueness**: at most one DP in α can agree with the interpretable
   person feature.
4. **P-Primacy**: if multiple DPs can agree, the [+AUTHOR] DP takes priority.

The [+PROXIMATE] feature sits in an implicational hierarchy:
  [+AUTHOR] ⊂ [+PARTICIPANT] ⊂ [+PROXIMATE]

First and second person arguments are inherently [+PROXIMATE]. Third person
arguments can be [+PROXIMATE] only when they co-occur with another third
person argument in the same domain.

## PCC Derivation

**Strong PCC**: P-Uniqueness is active ((36c)). In 3>3, the IO can be
[+PROXIMATE]; in 3>1 and 3>2, P-Uniqueness is violated because both
arguments are [+PROXIMATE]. In 1>2 and 2>1, same problem — banned.

**Weak PCC**: P-Uniqueness is NOT active. 1>2 and 2>1 are permitted (multiple
[+PROXIMATE] arguments allowed). But 3>1 and 3>2 are still banned because
P-Prominence requires the IO to be [+PROXIMATE] and the SAP DO prevents
this.

## Polite Pronouns

LEI bears [+PROXIMATE] by virtue of having interpretable 2nd person
features. In DO position with a 3rd person IO, LEI triggers a PCC effect
because the IO cannot be [+PROXIMATE] (it's non-participant, and the
domain already has a [+PROXIMATE] argument).

-/

namespace Minimalism.PConstraint

open Core.Prominence (PersonLevel)
open Minimalism (DecomposedPerson decomposePerson)

-- ============================================================================
-- § 1: Proximacy
-- ============================================================================

/-- The [+PROXIMATE] feature: whether a DP is a potential point-of-view
    center. First and second person are inherently [+PROXIMATE]; third
    person can be [+PROXIMATE] only in certain configurations.

    The hierarchy: [+AUTHOR] ⊂ [+PARTICIPANT] ⊂ [+PROXIMATE] -/
def isInherentlyProximate (p : PersonLevel) : Bool :=
  (decomposePerson p).hasParticipant

/-- P-Prominence settings: what feature the probe on the phase head
    requires for the Agree relation. -/
inductive PProminence where
  | proximate    -- default: [+PROXIMATE]
  | participant  -- restricted: [+PARTICIPANT]
  | author       -- most restricted: [+AUTHOR]
  deriving DecidableEq, BEq, Repr

/-- Does a DP satisfy the P-Prominence condition? -/
def satisfiesProminence (setting : PProminence) (p : PersonLevel) : Bool :=
  let dp := decomposePerson p
  match setting with
  | .proximate   => dp.hasParticipant  -- inherently [+PROXIMATE] SAPs
  | .participant => dp.hasParticipant
  | .author      => dp.hasAuthor

-- ============================================================================
-- § 2: PCC Grammar Types
-- ============================================================================

/-- A PCC grammar is parameterized by whether P-Uniqueness is active. -/
structure PCCGrammar where
  /-- P-Prominence setting -/
  prominence : PProminence := .proximate
  /-- Whether P-Uniqueness is active (Strong PCC) or not (Weak PCC) -/
  uniqueness : Bool
  deriving DecidableEq, BEq, Repr

/-- Weak PCC grammar: P-Uniqueness is NOT active. -/
def weakGrammar : PCCGrammar := ⟨.proximate, false⟩

/-- Strong PCC grammar: P-Uniqueness IS active. -/
def strongGrammar : PCCGrammar := ⟨.proximate, true⟩

-- ============================================================================
-- § 3: PCC Evaluation
-- ============================================================================

/-- Is a ditransitive clitic combination licit under a given PCC grammar?

    `ioPerson` and `doPerson` are the **interpretable** person values.

    The derivation:
    - Both IO and DO are checked for [+PROXIMATE]
    - If P-Uniqueness is active: at most one can be [+PROXIMATE]
    - If P-Uniqueness is not active (Weak PCC): multiple [+PROXIMATE] OK,
      but a 3rd person IO still cannot be [+PROXIMATE] if the DO is a SAP

    This is a simplified but faithful encoding of P&Z's constraint. -/
def pccLicit (g : PCCGrammar) (ioPerson doPerson : PersonLevel) : Bool :=
  let ioProx := satisfiesProminence g.prominence ioPerson
  let doProx := satisfiesProminence g.prominence doPerson
  -- Base constraint (always active): a non-proximate IO cannot co-occur
  -- with a proximate DO. A 3rd person IO can only be [+PROXIMATE] when
  -- it co-occurs with another 3rd person argument; if the DO is SAP
  -- (inherently [+PROXIMATE]), the 3rd person IO cannot achieve
  -- [+PROXIMATE] status → banned.
  let baseOK := !((!ioProx) && doProx)
  if g.uniqueness then
    -- Strong PCC adds P-Uniqueness: at most one [+PROXIMATE] argument.
    -- This additionally bans 1>2 and 2>1.
    baseOK && !(ioProx && doProx)
  else
    baseOK

-- ============================================================================
-- § 4: Verification — Weak PCC
-- ============================================================================

theorem weak_3_3 : pccLicit weakGrammar .third .third = true := rfl
theorem weak_2_3 : pccLicit weakGrammar .second .third = true := rfl
theorem weak_1_3 : pccLicit weakGrammar .first .third = true := rfl
theorem weak_3_2 : pccLicit weakGrammar .third .second = false := rfl
theorem weak_3_1 : pccLicit weakGrammar .third .first = false := rfl
theorem weak_1_2 : pccLicit weakGrammar .first .second = true := rfl
theorem weak_2_1 : pccLicit weakGrammar .second .first = true := rfl

-- ============================================================================
-- § 5: Verification — Strong PCC
-- ============================================================================

theorem strong_3_3 : pccLicit strongGrammar .third .third = true := rfl
theorem strong_2_3 : pccLicit strongGrammar .second .third = true := rfl
theorem strong_1_3 : pccLicit strongGrammar .first .third = true := rfl
theorem strong_3_2 : pccLicit strongGrammar .third .second = false := rfl
theorem strong_3_1 : pccLicit strongGrammar .third .first = false := rfl
/-- Strong PCC bans 1>2 and 2>1 (unlike Weak PCC). -/
theorem strong_1_2 : pccLicit strongGrammar .first .second = false := rfl
theorem strong_2_1 : pccLicit strongGrammar .second .first = false := rfl

/-- Strong PCC entails Weak PCC. -/
theorem strong_entails_weak (io do_ : PersonLevel) :
    pccLicit strongGrammar io do_ = true → pccLicit weakGrammar io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 6: Polite Pronouns and the P-Constraint
-- ============================================================================

/-- A polite pronoun with interpretable 2nd person is inherently
    [+PROXIMATE], triggering PCC effects in DO position. -/
theorem proximate_from_interpretable_2nd :
    isInherentlyProximate .second = true := rfl

/-- PCC effect with polite pronoun in DO, 3rd person IO (Weak PCC).
    The polite pronoun's interpretable 2nd person makes it [+PROXIMATE],
    and the 3rd person IO is NOT [+PROXIMATE], yielding the same
    configuration as 3>2. -/
theorem polite_do_triggers_weak_pcc :
    pccLicit weakGrammar .third .second = false := rfl

/-- Morphosyntactic accounts would evaluate using agreement person (3rd),
    yielding a 3>3 configuration — predicted licit. -/
theorem agreement_person_wrongly_predicts_licit :
    pccLicit weakGrammar .third .third = true := rfl

end Minimalism.PConstraint
