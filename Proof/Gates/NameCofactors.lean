import Proof.Gates.FiniteAverages

/-! A single minimizing Boolean cofactor is selected globally for each name.
    Repeated occurrences share that choice. -/

set_option autoImplicit false

namespace NearCubicGates.NameCofactors

open NearCubicGates.FiniteAverages

variable {Name Address Input : Type*} [Fintype Address] [Nonempty Address]
  [Fintype Input]

noncomputable def fiber (name : Address → Name) (n : Name) : Finset Address := by
  classical
  exact Finset.univ.filter fun a => name a = n

noncomputable def chosenAddress (name : Address → Name) (err : Address → ℝ)
    (n : Name) : Address := by
  classical
  exact if h : (fiber name n).Nonempty then
    Classical.choose ((fiber name n).exists_min_image err h)
  else Classical.choice (inferInstance : Nonempty Address)

theorem chosenAddress_minimum (name : Address → Name) (err : Address → ℝ)
    (a : Address) :
    name (chosenAddress name err (name a)) = name a ∧
      err (chosenAddress name err (name a)) ≤ err a := by
  classical
  have ha : a ∈ fiber name (name a) := by simp [fiber]
  have hn : (fiber name (name a)).Nonempty := ⟨a, ha⟩
  have h := Classical.choose_spec ((fiber name (name a)).exists_min_image err hn)
  simp only [chosenAddress, dif_pos hn]
  exact ⟨(Finset.mem_filter.mp h.1).2, h.2 a ha⟩

noncomputable def addressError (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (a : Address) : ℝ :=
  error (honest (name a)) (candidate a)

noncomputable def selected (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (n : Name) : Input → Bool :=
  candidate (chosenAddress name (addressError name honest candidate) n)

theorem selected_error_le (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (a : Address) :
    error (honest (name a)) (selected name honest candidate (name a)) ≤
      error (honest (name a)) (candidate a) := by
  obtain ⟨hn, hmin⟩ := chosenAddress_minimum name
    (addressError name honest candidate) a
  simpa only [addressError, hn, selected] using hmin

noncomputable def prescribedSelected (prescribed : Name → Bool)
    (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (n : Name) : Input → Bool :=
  if prescribed n then honest n else selected name honest candidate n

theorem prescribedSelected_exact (prescribed : Name → Bool)
    (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (n : Name) (hn : prescribed n = true) :
    prescribedSelected prescribed name honest candidate n = honest n := by
  simp [prescribedSelected, hn]

theorem prescribedSelected_auxiliary (prescribed : Name → Bool)
    (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (n : Name) (hn : prescribed n = false) :
    prescribedSelected prescribed name honest candidate n = selected name honest candidate n := by
  simp [prescribedSelected, hn]

theorem prescribedSelected_error_le [Nonempty Input] (prescribed : Name → Bool)
    (name : Address → Name) (honest : Name → Input → Bool)
    (candidate : Address → Input → Bool) (a : Address) :
    error (honest (name a)) (prescribedSelected prescribed name honest candidate (name a)) ≤
      error (honest (name a)) (candidate a) := by
  cases h : prescribed (name a)
  · simpa [prescribedSelected, h] using selected_error_le name honest candidate a
  · simp only [prescribedSelected, h, ↓reduceIte, error_self]
    exact error_nonneg _ _

end NearCubicGates.NameCofactors
