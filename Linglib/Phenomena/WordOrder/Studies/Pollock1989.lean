import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.VerbMovement
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# Pollock's Verb Movement Diagnostics
@cite{pollock-1989}

Connects the Minimalist verb movement parameter
(`Theories/Syntax/Minimalism/Formal/HeadMovement/VerbMovement.lean`) to the
theory-neutral verb movement and do-support data in SubjectAuxInversion.lean.

## Structure

**§1 Pollock diagnostics**: Each of Pollock's 12 examples is paired
with the theory's prediction via `verbPrecedesDiagnostic`. French examples
(V raises) are grammatical when V precedes the diagnostic; English examples
(V in situ) are ungrammatical in the same configuration.

**§2 Do-support**: Each do-support datum is paired with
`needsDoSupport`. Lexical verb contexts that need do-support are grammatical
when do-support is used and ungrammatical without it.

**§3 Convergence**: All four diagnostics agree for any parameter setting.

**§4 Anticorrelation**: Do-support and verb raising are complementary.

-/

namespace Phenomena.WordOrder.Studies.Pollock1989

open Phenomena.WordOrder.SubjectAuxInversion
open Minimalism

-- ============================================================================
-- § 1  Pollock Diagnostic Bridge Theorems
-- ============================================================================

/-! Each theorem pairs the datum's acceptability judgment with the verb
movement theory's prediction. French examples have `french` (= `.raises`),
English lexical verb examples have `englishLexical` (= `.inSitu`). -/

/-- ex_p01 "Aime-t-il Marie?" — French lexical V inverts (V raises to C via T) -/
theorem bridge_ex_p01 :
    ex_p01.acceptability == .grammatical ∧
    ex_p01.language == "French" ∧
    verbPrecedesDiagnostic french .inversion = true := ⟨rfl, rfl, rfl⟩

/-- ex_p02 "*Likes he Mary?" — English lexical V cannot invert (V in situ) -/
theorem bridge_ex_p02 :
    ex_p02.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .inversion = false := ⟨rfl, rfl⟩

/-- ex_p03 "Jean embrasse souvent Marie" — French V raises past adverb -/
theorem bridge_ex_p03 :
    ex_p03.acceptability == .grammatical ∧
    ex_p03.language == "French" ∧
    verbPrecedesDiagnostic french .adverb = true := ⟨rfl, rfl, rfl⟩

/-- ex_p04 "*John kisses often Mary" — English V cannot raise past adverb -/
theorem bridge_ex_p04 :
    ex_p04.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .adverb = false := ⟨rfl, rfl⟩

/-- ex_p06 "*Jean souvent embrasse Marie" — French adverb cannot precede V
    (V must raise, so Adv > V order is ungrammatical) -/
theorem bridge_ex_p06 :
    ex_p06.acceptability == .ungrammatical ∧
    ex_p06.language == "French" ∧
    verbPrecedesDiagnostic french .adverb = true := ⟨rfl, rfl, rfl⟩

/-- ex_p07 "Jean n'aime pas Marie" — French V raises past negation -/
theorem bridge_ex_p07 :
    ex_p07.acceptability == .grammatical ∧
    ex_p07.language == "French" ∧
    verbPrecedesDiagnostic french .negation = true := ⟨rfl, rfl, rfl⟩

/-- ex_p08 "*John likes not Mary" — English V cannot raise past negation -/
theorem bridge_ex_p08 :
    ex_p08.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .negation = false := ⟨rfl, rfl⟩

/-- ex_p09 "Mes amis aiment tous Marie" — French V raises past FQ -/
theorem bridge_ex_p09 :
    ex_p09.acceptability == .grammatical ∧
    ex_p09.language == "French" ∧
    verbPrecedesDiagnostic french .floatingQ = true := ⟨rfl, rfl, rfl⟩

/-- ex_p10 "*My friends love all Mary" — English V cannot raise past FQ -/
theorem bridge_ex_p10 :
    ex_p10.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .floatingQ = false := ⟨rfl, rfl⟩

/-- ex_p11 "John has often eaten pizza" — English auxiliary raises past adverb,
    patterning with French lexical verbs -/
theorem bridge_ex_p11 :
    ex_p11.acceptability == .grammatical ∧
    verbPrecedesDiagnostic englishAux .adverb = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2  Do-Support Bridge Theorems
-- ============================================================================

/-! Each do-support datum is paired with `needsDoSupport`. Grammatical
do-support examples confirm that English lexical verbs need it; ungrammatical
examples confirm that auxiliaries do not. -/

/-- ex27 "Where does Sue eat fish?" — do-support in question (lexical verb needs it) -/
theorem bridge_ex27 :
    ex27.acceptability == .grammatical ∧
    needsDoSupport englishLexical .question = true := ⟨rfl, rfl⟩

/-- ex28 "*Eats John pizza?" — lexical verb cannot invert directly -/
theorem bridge_ex28 :
    ex28.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .inversion = false := ⟨rfl, rfl⟩

/-- ex29 "What did Mary buy?" — do-support in wh-question -/
theorem bridge_ex29 :
    ex29.acceptability == .grammatical ∧
    needsDoSupport englishLexical .question = true := ⟨rfl, rfl⟩

/-- ex30 "Where is Sue eating fish?" — auxiliary inverts directly (raises) -/
theorem bridge_ex30 :
    ex30.acceptability == .grammatical ∧
    needsDoSupport englishAux .question = false := ⟨rfl, rfl⟩

/-- ex31 "*Where does Sue be eating fish?" — do-support with auxiliary is ungrammatical -/
theorem bridge_ex31 :
    ex31.acceptability == .ungrammatical ∧
    needsDoSupport englishAux .question = false := ⟨rfl, rfl⟩

/-- ex32 "Sue does not eat fish" — do-support in negation (lexical verb) -/
theorem bridge_ex32 :
    ex32.acceptability == .grammatical ∧
    needsDoSupport englishLexical .negation = true := ⟨rfl, rfl⟩

/-- ex33 "*Sue not eats fish" — lexical verb cannot raise past negation -/
theorem bridge_ex33 :
    ex33.acceptability == .ungrammatical ∧
    verbPrecedesDiagnostic englishLexical .negation = false := ⟨rfl, rfl⟩

/-- ex34 "Sue is not eating fish" — auxiliary raises past negation directly -/
theorem bridge_ex34 :
    ex34.acceptability == .grammatical ∧
    needsDoSupport englishAux .negation = false := ⟨rfl, rfl⟩

/-- ex35 "*Sue does not be eating fish" — do-support with auxiliary blocked -/
theorem bridge_ex35 :
    ex35.acceptability == .ungrammatical ∧
    needsDoSupport englishAux .negation = false := ⟨rfl, rfl⟩

/-- ex36 "She likes him, doesn't she?" — tag question with do-support -/
theorem bridge_ex36 :
    ex36.acceptability == .grammatical ∧
    needsDoSupport englishLexical .tagQuestion = true := ⟨rfl, rfl⟩

/-- ex37 "*She likes him, likesn't she?" — tag without do-support blocked -/
theorem bridge_ex37 :
    ex37.acceptability == .ungrammatical ∧
    needsDoSupport englishLexical .tagQuestion = true := ⟨rfl, rfl⟩

/-- ex38 "She runs faster than he does" — VP ellipsis with do-support -/
theorem bridge_ex38 :
    ex38.acceptability == .grammatical ∧
    needsDoSupport englishLexical .vpEllipsis = true := ⟨rfl, rfl⟩

/-- ex39 "Sue DOES eat fish" — verum focus with do-support (lexical verb) -/
theorem bridge_ex39 :
    ex39.acceptability == .grammatical ∧
    needsDoSupport englishLexical .verumFocus = true := ⟨rfl, rfl⟩

/-- ex40 "She IS eating fish" — verum focus, auxiliary raises directly -/
theorem bridge_ex40 :
    ex40.acceptability == .grammatical ∧
    needsDoSupport englishAux .verumFocus = false := ⟨rfl, rfl⟩

/-- ex41 "*She DOES be eating fish" — do-support with auxiliary blocked in verum -/
theorem bridge_ex41 :
    ex41.acceptability == .ungrammatical ∧
    needsDoSupport englishAux .verumFocus = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3  Diagnostic Convergence
-- ============================================================================

/-! All four diagnostics agree for any parameter setting. This is the core
of Pollock's argument: the four tests are not independent observations but
consequences of a single parameter (V-raises vs. V-in-situ). -/

/-- For any parameter setting, all four diagnostics give the same answer. -/
theorem all_diagnostics_converge (p : VMovementParam) (d₁ d₂ : VDiagnostic) :
    verbPrecedesDiagnostic p d₁ = verbPrecedesDiagnostic p d₂ :=
  diagnostics_converge p d₁ d₂

-- ============================================================================
-- § 4  Do-Support / V-Raising Anticorrelation
-- ============================================================================

/-! Do-support and verb raising are complementary: a parameter setting that
raises V never needs do-support, and a setting that keeps V in situ always
needs it. This follows from the theory: do-support exists *because* V
cannot raise. -/

/-- Do-support is needed iff V does not raise past negation. -/
theorem doSupport_iff_no_raising (p : VMovementParam) (ctx : TenseSupportContext) :
    needsDoSupport p ctx = !verbPrecedesDiagnostic p .negation :=
  doSupport_anticorrelates_raising p ctx

end Phenomena.WordOrder.Studies.Pollock1989
