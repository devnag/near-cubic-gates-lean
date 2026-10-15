import Proof.Hierarchy.CompetitorSelectedTableLayout

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedTable
open LocalBitMultitape RecoveryRootRound CompetitorCountMask MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem request_input_cases (r : Request) (Q : ℕ) (xs : List (Bool × ℕ)) (i : Fin 91) :
    CompetitorSelectedRequestCount.input r Q xs i=
      if i.val=0 then MatrixScoreBatch.physicalInput r else if i.val=61 then List.replicate Q true
      else if i.val=78 then mask xs else if i.val=79 then CompetitorCountFold.raw Q (counts xs) else [] := by
  fin_cases i <;> rfl

theorem extend_slot (p : Program) (r : Request) (Q : ℕ) (xs : List (Bool × ℕ))
    (data : Fin (CompetitorCountTable.tapes p) → List Bool)
    (h0 : data (source p)=MatrixScoreBatch.physicalInput r)
    (hq : data (CompetitorCountTable.slot p 36)=List.replicate Q true)
    (hc : data (CompetitorCountTable.slot p 141)=CompetitorCountFold.raw Q (counts xs))
    (i : Fin 91) : extend p xs data (slot p i)=CompetitorSelectedRequestCount.input r Q xs i := by
  by_cases hzero : i.val=0
  · have hi : i=0 := Fin.ext hzero
    subst i
    exact h0
  by_cases hwidth : i.val=61
  · have hi : i=61 := Fin.ext hwidth
    subst i
    simpa [request_input_cases,slot,extend,old] using hq
  by_cases hcount : i.val=79
  · have hi : i=79 := Fin.ext hcount
    subst i
    simpa [request_input_cases,slot,extend,old] using hc
  by_cases hmask : i.val=78
  · have hi : i=78 := Fin.ext hmask
    subst i
    simp [request_input_cases,slot,extend,fresh,extra]
  have hfresh : (⟨i.val+1,by omega⟩ : Fin 92)≠0 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=0 at hv
    omega
  rw [request_input_cases]
  simp only [slot,hzero,hwidth,hcount,hmask,↓reduceIte,extend,fresh,Fin.addCases_right,extra,hfresh]

end NearCubicWires.RepairOrdinary.CompetitorSelectedTable
