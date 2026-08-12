import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Deterministic screening core for tail-index SIS

This file formalizes the deterministic content of Lemma 8 and the selection
step in Theorems 6--7 of the accompanying mathematical proof. Probability and
extreme-value estimates enter only through the uniform score-error hypothesis.
-/

namespace TailSIS

variable {ι : Type*} [DecidableEq ι]

/-- Every selected score is no larger than every unselected score. This is the
only property of a deterministic `d`-smallest selection used below; it also
allows ties fixed by any deterministic rule. -/
def IsLowestSelection (score : ι → ℝ) (selected : Finset ι) : Prop :=
  ∀ i ∈ selected, ∀ j ∉ selected, score i ≤ score j

/-- A uniform error smaller than half the population gap strictly separates
all active estimated scores from all inactive estimated scores. -/
theorem score_separation
    (active : Finset ι) (population estimated : ι → ℝ)
    (baseline gap : ℝ) (_hgap : 0 < gap)
    (hactive : ∀ i ∈ active, population i ≤ baseline - gap)
    (hinactive : ∀ j ∉ active, population j = baseline)
    (herror : ∀ k, |estimated k - population k| < gap / 2) :
    ∀ i ∈ active, ∀ j ∉ active, estimated i < estimated j := by
  intro i hi j hj
  have hei := herror i
  have hej := herror j
  rw [abs_lt] at hei hej
  have hpi := hactive i hi
  have hpj := hinactive j hj
  linarith

/-- Strict active/inactive score separation and selection of at least as many
indices as there are active variables imply sure screening. -/
theorem sure_screening_of_separation
    (active selected : Finset ι) (score : ι → ℝ)
    (hsep : ∀ i ∈ active, ∀ j ∉ active, score i < score j)
    (hlow : IsLowestSelection score selected)
    (hcard : active.card ≤ selected.card) :
    active ⊆ selected := by
  by_contra hnot
  simp only [Finset.not_subset] at hnot
  obtain ⟨a, haA, haS⟩ := hnot
  have hselected_active : selected ⊆ active := by
    intro x hxS
    by_contra hxA
    have hxA' : x ∉ active := by simpa using hxA
    have horder : score x ≤ score a := hlow x hxS a haS
    have hstrict : score a < score x := hsep a haA x hxA'
    exact (not_lt_of_ge horder) hstrict
  have heq : selected = active :=
    Finset.eq_of_subset_of_card_le hselected_active hcard
  exact haS (heq.symm ▸ haA)

/-- With exactly `|active|` selected indices, sure screening strengthens to
exact recovery. -/
theorem exact_recovery_of_separation
    (active selected : Finset ι) (score : ι → ℝ)
    (hsep : ∀ i ∈ active, ∀ j ∉ active, score i < score j)
    (hlow : IsLowestSelection score selected)
    (hcard : selected.card = active.card) :
    selected = active := by
  have hscreen : active ⊆ selected :=
    sure_screening_of_separation active selected score hsep hlow (by omega)
  exact (Finset.eq_of_subset_of_card_le hscreen (by omega)).symm

/-- End-to-end deterministic SIS implication from a uniform score bound. -/
theorem uniform_error_implies_sure_screening
    (active selected : Finset ι) (population estimated : ι → ℝ)
    (baseline gap : ℝ) (hgap : 0 < gap)
    (hactive : ∀ i ∈ active, population i ≤ baseline - gap)
    (hinactive : ∀ j ∉ active, population j = baseline)
    (herror : ∀ k, |estimated k - population k| < gap / 2)
    (hlow : IsLowestSelection estimated selected)
    (hcard : active.card ≤ selected.card) :
    active ⊆ selected :=
  sure_screening_of_separation active selected estimated
    (score_separation active population estimated baseline gap hgap hactive hinactive herror)
    hlow hcard

/-- End-to-end exact-recovery implication when the selected size is correct. -/
theorem uniform_error_implies_exact_recovery
    (active selected : Finset ι) (population estimated : ι → ℝ)
    (baseline gap : ℝ) (hgap : 0 < gap)
    (hactive : ∀ i ∈ active, population i ≤ baseline - gap)
    (hinactive : ∀ j ∉ active, population j = baseline)
    (herror : ∀ k, |estimated k - population k| < gap / 2)
    (hlow : IsLowestSelection estimated selected)
    (hcard : selected.card = active.card) :
    selected = active :=
  exact_recovery_of_separation active selected estimated
    (score_separation active population estimated baseline gap hgap hactive hinactive herror)
    hlow hcard

end TailSIS
