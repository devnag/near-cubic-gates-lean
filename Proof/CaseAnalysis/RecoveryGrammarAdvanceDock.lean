import Proof.CaseAnalysis.RecoveryGrammarReloadBank

/-! Dock the physical row advance into the unchanged 112-tape grammar
bank. The graph and reference stack keep their actual append cursors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit
open RecoveryBoundedGrammarCold
open private install_eq from Proof.Amplification.RecoveryRowLookupCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots : Fin 37→Fin 112:=Fin.addCases (m:=33) (n:=4) (motive:=fun _=>Fin 112)
  (fun j=>j.natAdd 79) ![73,78,76,77]

theorem outer_injective : Function.Injective outerSlots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=33) (n:=4) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=33) (n:=4) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [outerSlots,Fin.addCases_left] at he
    apply Fin.ext
    have hv:=congrArg Fin.val he
    change 79+a.val=79+b.val at hv
    change a.val=b.val
    omega
  · intro he
    simp only [outerSlots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg Fin.val he
    fin_cases b <;> simp at hv <;> omega
  · intro he
    simp only [outerSlots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg Fin.val he
    fin_cases a <;> simp at hv <;> omega
  · intro he
    fin_cases a <;> fin_cases b <;> first | rfl | contradiction

noncomputable def focused:=RecoveryFocus.machine outerSlots machine

theorem projection (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) (j : Fin 37) :
    data fields node B P out stack packet source cold (outerSlots j)=bank B cold j := by
  refine Fin.addCases (m:=33) (n:=4) (fun k=>?_) (fun k=>?_) j
  · simp only [outerSlots,bank,data,Fin.addCases_left,Fin.addCases_right]
  · fin_cases k
    · exact data73 fields node B P out stack packet source cold
    · change ZeroPadding.pad 0 (List.replicate B false)=List.replicate B false
      exact ZeroPadding.pad_zero _
    · exact data76 fields node B P out stack packet source cold
    · exact data77 fields node B P out stack packet source cold

theorem projection_heads (out stack : List Bool) (j : Fin 37) : heads out stack (outerSlots j)=0 := by
  refine Fin.addCases (m:=33) (n:=4) (fun k=>?_) (fun k=>?_) j
  · simp only [outerSlots,heads,Fin.addCases_left,Fin.addCases_right]
  · fin_cases k <;> rfl

theorem install_bank (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold next : Fin 33→List Bool) :
    install outerSlots (data fields node B P out stack packet source cold) (bank B next)=
      data fields node B P out stack packet source next := by
  apply install_eq outerSlots outer_injective
  · intro j
    exact (projection fields node B P out stack packet source next j).symm
  · intro i
    refine Fin.addCases (m:=79) (n:=33) (fun j=>?_) (fun j=>?_) i
    · intro hi
      simp only [data,Fin.addCases_left]
    · intro hi
      exact False.elim (hi (j.castAdd 4) (by simp only [outerSlots,Fin.addCases_left]))

theorem focused_run {W C D L S B P : ℕ} (room : Room W C D L S B P)
    (q bound row : ℕ) (extra : Fin 12→List Bool)
    (fields : Fin 78→List Bool) (node : ℕ) (out stack packet source : List Bool)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (hindex : (row+1)*rowWidth q bound+6+OuterPCPRecovery.boundedCircuitFieldLimit q bound≤W)
    (hrow : row+1≤W) :
    ∃ r,runFrom focused (budget B)
      (entry focused fields node B P out stack packet source (metadata q bound row C B extra))=some r ∧
      r.steps≤budget B ∧ r.final.heads=heads out stack ∧
      r.final.tapes=data fields node B P out stack packet source (metadata q bound (row+1) C B extra) := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(ready room q bound row extra width hindex hrow).focus_at outerSlots outer_injective
    (heads out stack) (data fields node B P out stack packet source (metadata q bound row C B extra))
    (projection fields node B P out stack packet source _) (projection_heads out stack)
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,install_bank]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
