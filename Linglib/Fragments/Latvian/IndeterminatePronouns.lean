/-!
# Latvian Indeterminate Pronoun Paradigm
@cite{haspelmath-1997} @cite{kratzer-shimoyama-2002}

Latvian exhibits a morphologically transparent indeterminate system with
three productive prefixes that mark operator association (p. 277 of
@cite{haspelmath-1997}, cited in §1 of @cite{kratzer-shimoyama-2002}):

- **kaut-** series: existential (∃)
- **ne-** series: negative polarity (direct negation scope)
- **jeb-** series: free choice / indirect negation / comparatives

Each prefix attaches to the same set of wh-interrogative bases
(*kas* 'who/what', *kur* 'where', *kad* 'when', *ka* 'how', *kads/kurs* 'which'),
making Latvian a **selective** system in the sense of
@cite{kratzer-shimoyama-2002}: the morphological prefix determines the
operator, unlike Japanese where a single base (*dare*) combines with
different particles.

Diacritics omitted following @cite{kratzer-shimoyama-2002}.
-/

set_option autoImplicit false

namespace Fragments.Latvian.IndeterminatePronouns

/-- A row in a cross-linguistic indeterminate paradigm table.
    Each row represents one semantic domain (person, thing, place, ...)
    with forms for the interrogative and each operator-series. -/
structure IndeterminateSeriesEntry where
  domain : String
  interrogative : String
  existential : String       -- kaut-series
  negPolarity : String       -- ne-series (direct negation scope)
  freeChoice : String        -- jeb-series (indirect neg/comparatives/FC)
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- Latvian Indeterminate Paradigm (Haspelmath 1997, p. 277)
-- ============================================================================

def person : IndeterminateSeriesEntry where
  domain := "person"; interrogative := "kas"
  existential := "kaut kas, kads"; negPolarity := "ne-viens"; freeChoice := "jeb-kads"

def thing : IndeterminateSeriesEntry where
  domain := "thing"; interrogative := "kas"
  existential := "kaut kas"; negPolarity := "ne-kas"; freeChoice := "jeb-kas"

def place : IndeterminateSeriesEntry where
  domain := "place"; interrogative := "kur"
  existential := "kaut kur"; negPolarity := "ne-kur"; freeChoice := "jeb-kur"

def time : IndeterminateSeriesEntry where
  domain := "time"; interrogative := "kad"
  existential := "kaut kad"; negPolarity := "ne-kad"; freeChoice := "jeb-kad"

def manner : IndeterminateSeriesEntry where
  domain := "manner"; interrogative := "ka"
  existential := "kaut ka"; negPolarity := "ne-ka"; freeChoice := "jeb-ka"

def determiner : IndeterminateSeriesEntry where
  domain := "determiner"; interrogative := "kads, kurs"
  existential := "kaut kads"; negPolarity := "ne-kads"; freeChoice := "jeb-kads, jeb-kurs"

/-- The full 6-row Latvian paradigm. -/
def paradigm : List IndeterminateSeriesEntry :=
  [person, thing, place, time, manner, determiner]

theorem paradigm_size : paradigm.length = 6 := rfl

/-- Each ne-series form uses the common prefix "ne-". -/
theorem negpol_prefix :
    paradigm.all (fun e => e.negPolarity.startsWith "ne-") = true := by
  native_decide

/-- Each jeb-series form uses the common prefix "jeb-". -/
theorem fc_prefix :
    paradigm.all (fun e => e.freeChoice.startsWith "jeb-") = true := by
  native_decide

/-- Each kaut-series form uses the common prefix "kaut ". -/
theorem exist_prefix :
    paradigm.all (fun e => e.existential.startsWith "kaut ") = true := by
  native_decide

end Fragments.Latvian.IndeterminatePronouns
