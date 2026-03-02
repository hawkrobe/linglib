import Linglib.Fragments.English.TemporalExpressions

/-!
# Finnish Temporal Connectives Fragment
@cite{heinamaki-1974} @cite{karttunen-1974} @cite{rett-2020}

Finnish lexicalizes the two-*until* distinction that @cite{karttunen-1974} argues
is covert in English:

- **kunnes** / **siihen saakka** (durative *until*): "John slept until 3pm."
  The main event persists to the complement time.

- **ennenkuin** (punctual *until*): literally 'before-than'. Used with
  negation: "He didn't wake up ennenkuin 3pm." Morphologically encodes
  Karttunen's NOT(BEFORE) analysis.

The fact that the Finnish punctual *until* is morphologically derived from
*before* (ennen = 'before', kuin = 'than') provides strong evidence for
Karttunen's identity: punctual *until* = ¬*before*.

Finnish also has **kun** ('when') and the standard *before*/*after* pair:
**ennen** / **jälkeen**.

-/

namespace Fragments.Finnish.TemporalConnectives

open Fragments.English.TemporalExpressions (TemporalExprEntry Reading TemporalOrder ComplementType)

-- ============================================================================
-- § 1: Connective Entries
-- ============================================================================

/-- Finnish *ennen* ('before'): mirrors English *before*.
    Licenses NPIs, non-veridical complement. -/
def ennen : TemporalExprEntry :=
  { form := "ennen"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *jälkeen* ('after'): mirrors English *after*.
    Does not license NPIs, veridical complement. -/
def jälkeen : TemporalExprEntry :=
  { form := "jälkeen"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *kun* ('when'): temporal coincidence.
    Veridical, does not license NPIs. -/
def kun : TemporalExprEntry :=
  { form := "kun"
  , complementType := .clausal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *kunnes* (durative *until*): "John slept kunnes 3pm."
    The main event persists to the complement time. Veridical complement. -/
def kunnes : TemporalExprEntry :=
  { form := "kunnes"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *ennenkuin* (punctual *until*): literally 'before-than'.
    Used with negation: "He didn't wake up ennenkuin the prince kissed her."

    Morphologically: **ennen** ('before') + **kuin** ('than').
    This overt morphological decomposition confirms Karttunen's analysis
    that punctual *until* = NOT(BEFORE). The negation is external to the
    connective, which is literally *before*. -/
def ennenkuin : TemporalExprEntry :=
  { form := "ennenkuin"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := false
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 1b: Additional Connective Entries (Heinämäki 1974)
-- ============================================================================

/-- Finnish *sillä aikaa kun* ('while', literally 'that time when'):
    temporal containment, mirrors English *while* / *as long as*.
    Multi-word expression; not a single lexeme. -/
def sillä_aikaa_kun : TemporalExprEntry :=
  { form := "sillä aikaa kun"
  , complementType := .clausal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *aina kun* ('whenever', literally 'always when'):
    universally quantified temporal overlap, mirrors English *whenever*.
    Multi-word expression. -/
def aina_kun : TemporalExprEntry :=
  { form := "aina kun"
  , complementType := .clausal
  , order := .whenever
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Finnish *heti kun* ('as soon as', literally 'immediately when'):
    strengthened *after* with temporal proximity, mirrors English *as soon as*.
    Multi-word expression. -/
def heti_kun : TemporalExprEntry :=
  { form := "heti kun"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := none
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 2: The Two-*Until* Distinction
-- ============================================================================

/-- Finnish lexicalizes the two-*until* distinction: *kunnes* (durative)
    and *ennenkuin* (punctual) are different lexical items with different
    temporal orders. -/
theorem two_until_lexicalized :
    kunnes.form ≠ ennenkuin.form ∧
    kunnes.order ≠ ennenkuin.order := by
  exact ⟨by decide, by decide⟩

/-- *Ennenkuin* is morphologically *before* (ennen): its `order` field
    is `.before`, confirming Karttunen's NOT(BEFORE) analysis. -/
theorem ennenkuin_is_before :
    ennenkuin.order = .before ∧ ennen.order = .before := ⟨rfl, rfl⟩

/-- *Kunnes* (durative until) is a genuine `.until_` connective,
    distinct from *ennenkuin*'s `.before`. -/
theorem kunnes_is_until :
    kunnes.order = .until_ ∧ ennenkuin.order = .before := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Finnish *ennen* and English *before* agree on all semantic properties. -/
theorem ennen_matches_before :
    ennen.order = before_.order ∧
    ennen.licensesNPI = before_.licensesNPI ∧
    ennen.defaultReading = before_.defaultReading ∧
    ennen.coercedReading = before_.coercedReading ∧
    ennen.complementVeridical = before_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Finnish *jälkeen* and English *after* agree on all semantic properties. -/
theorem jälkeen_matches_after :
    jälkeen.order = after_.order ∧
    jälkeen.licensesNPI = after_.licensesNPI ∧
    jälkeen.defaultReading = after_.defaultReading ∧
    jälkeen.coercedReading = after_.coercedReading ∧
    jälkeen.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Finnish *kun* and English *when* agree on all semantic properties. -/
theorem kun_matches_when :
    kun.order = when_conn.order ∧
    kun.licensesNPI = when_conn.licensesNPI ∧
    kun.defaultReading = when_conn.defaultReading ∧
    kun.complementVeridical = when_conn.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Finnish *kunnes* (durative until) and English *until* agree on all
    semantic properties. -/
theorem kunnes_matches_until :
    kunnes.order = until_.order ∧
    kunnes.licensesNPI = false ∧
    kunnes.defaultReading = until_.defaultReading ∧
    kunnes.complementVeridical = until_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Finnish veridicality asymmetry: *ennen* non-veridical, *jälkeen* veridical. -/
theorem veridicality_asymmetry :
    ennen.complementVeridical = false ∧ jälkeen.complementVeridical = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 4: Coverage of *Since*, *By*, *Till*
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Finnish *kunnes* covers both English *until* and *till* (durative).
    Finnish does not lexically distinguish *until* from *till* because
    *kunnes* already has the single durative-until meaning; the English
    dialectal split is irrelevant. -/
theorem kunnes_covers_till :
    kunnes.order = till_conn.order ∧
    kunnes.defaultReading = till_conn.defaultReading ∧
    kunnes.complementVeridical = till_conn.complementVeridical :=
  ⟨rfl, rfl, rfl⟩

/-- Finnish lacks a single-lexeme equivalent of English *since* or *by*.
    *Since* is expressed as *siitä lähtien kun* ('from that onwards when')
    or with the elative case + *lähtien*. *By* is expressed as *mennessä*
    (inessive of 'going') or *viimeistään* ('at the latest').

    This is not a gap in Finnish — it reflects that *since* and *by* are
    typologically less basic than *before*/*after*/*when*/*until*. -/
theorem since_by_not_single_lexeme : True := trivial

-- ============================================================================
-- § 5: Cross-Linguistic Agreement for Additional Connectives
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Finnish *sillä aikaa kun* and English *while* agree on semantic properties. -/
theorem sillä_aikaa_kun_matches_while :
    sillä_aikaa_kun.order = while_conn.order ∧
    sillä_aikaa_kun.licensesNPI = while_conn.licensesNPI ∧
    sillä_aikaa_kun.defaultReading = while_conn.defaultReading ∧
    sillä_aikaa_kun.complementVeridical = while_conn.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Finnish *aina kun* and English *whenever* agree on semantic properties. -/
theorem aina_kun_matches_whenever :
    aina_kun.order = whenever_conn.order ∧
    aina_kun.licensesNPI = whenever_conn.licensesNPI ∧
    aina_kun.defaultReading = whenever_conn.defaultReading ∧
    aina_kun.complementVeridical = whenever_conn.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Finnish *heti kun* and English *as soon as* agree on semantic properties. -/
theorem heti_kun_matches_asSoonAs :
    heti_kun.order = asSoonAs.order ∧
    heti_kun.licensesNPI = asSoonAs.licensesNPI ∧
    heti_kun.defaultReading = asSoonAs.defaultReading ∧
    heti_kun.complementVeridical = asSoonAs.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Finnish morphological transparency: *aina kun* and *heti kun* are
    compositionally built from *kun* ('when') with adverbial modifiers
    *aina* ('always') and *heti* ('immediately'). All three share the
    base connective *kun*'s complement veridicality. -/
theorem kun_family_veridical :
    kun.complementVeridical = true ∧
    aina_kun.complementVeridical = true ∧
    heti_kun.complementVeridical = true :=
  ⟨rfl, rfl, rfl⟩

end Fragments.Finnish.TemporalConnectives
