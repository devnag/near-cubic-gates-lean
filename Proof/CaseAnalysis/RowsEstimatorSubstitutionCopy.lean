import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset

/-! One logical polynomial copy either restores the accumulator or appends
to the live output. Its cost is independent of padding and output prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCopy
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (reset : Bool) (i : Fin 5) : Bool:=decide (i=0) || (reset && decide (i=2))
noncomputable def machine (reset : Bool):=MaskedReset.machine CloseoutRowsRawPolynomialAdd.machine (selected reset)
def outputCap (reset : Bool) (C : ℕ):=if reset then C else 0
def pads (reset : Bool) (C : ℕ) (i : Fin 5):=if i=2 then outputCap reset C else C
def heads (pos : ℕ) : Fin 6 → ℕ:=![0,0,pos,0,0,0]
def data (reset : Bool) (C : ℕ) (p : List (List ℕ)) (out : List Bool) : Fin 6 → List Bool:=
  ![ZeroPadding.pad C (ExtIncidence.stream p),List.replicate C false,ZeroPadding.pad (outputCap reset C) out,
    List.replicate C false,List.replicate C false,List.replicate C false]
def budget (p : List (List ℕ)):=2*CloseoutRowsRawPolynomialAdd.budget p []+2

theorem run (reset : Bool) (C : ℕ) (p : List (List ℕ)) (out : List Bool)
    (ho : reset=true → out=[]) (hb : CloseoutRowsRawPolynomialAdd.budget p [] ≤ C) :
    Step (machine reset) (budget p) (heads out.length) (data reset C p out)
      (heads (if reset then 0 else (out++ExtIncidence.stream p).length))
      (data reset C p (out++ExtIncidence.stream p)) := by
  have hC : 1 ≤ C := by unfold CloseoutRowsRawPolynomialAdd.budget at hb;omega
  have raw:=CloseoutRowsRawPolynomialAdd.add_run C p [] out hC
  simp only [List.append_nil] at raw
  have padded:=raw.pad (pads reset C)
  have masked:=padded.mask (cap:=C) (selected reset) (by
    intro i hi
    have hs : i=0 ∨ (reset=true ∧ i=2):=by simpa [selected] using hi
    rcases hs with rfl | ⟨hs,rfl⟩
    · rfl
    · rw [ho hs];rfl) hb
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i
  all_goals simp [heads,data,pads,selected,CloseoutRowsRawPolynomialAdd.heads,
    CloseoutRowsRawPolynomialAdd.data,CloseoutRowsRawPolynomialAdd.body,ExtIncidence.stream,
    Fin.addCases,SubstitutionErase.false_pad C C (by omega),
    show ZeroPadding.pad C [false]=List.replicate C false from SubstitutionErase.false_pad 1 C hC]

theorem budget_bound (p : List (List ℕ)) : budget p ≤ 64*((ExtIncidence.stream p).length+3)+2 := by
  have h:=CloseoutRowsRawPolynomialAdd.budget_bound p []
  simp only [CloseoutRowsRawProductBudget.inputLength,ExtIncidence.stream,List.flatMap_nil,
    List.nil_append,List.length_singleton] at h
  unfold budget
  simp only [ExtIncidence.stream]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCopy
