import Proof.Circuits.DecompositionSchemaRun

/-! Ordinary cold carrier for the already executed complete serializer. -/
namespace NearCubicWires.RepairOrdinary.DecompositionGlobal
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sparse_extend {m n : ℕ} (hm : 0 < m) (source : List Bool)
    (data : Fin m → List Bool) (hdata : ∀ i,data i=if i.val=0 then source else []) :
    ∀ i,Fin.addCases (m:=m) (n:=n) data (fun _ => []) i=
      if i.val=0 then source else [] := by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    exact hdata j
  · have hn : ¬ m+j.val=0 := by omega
    simp only [Fin.addCases_right,Fin.val_natAdd,hn,ite_false]

theorem input_sparse (D : ℕ) (payload : List Bool) :
    ∀ i,input D payload i=if i.val=0 then frame payload else [] := by
  apply sparse_extend (by unfold DecompositionColdPrepare.tapes; omega)
  apply sparse_extend (by unfold PCPSerializerCapacity.tapes; omega)
  apply sparse_extend (by decide : 0 < 5)
  intro i
  fin_cases i <;> rfl

noncomputable def program (D C : ℕ) : Program where
  tapeCount := tapes D
  stateCount := _
  twoTapes := by unfold tapes; omega
  machine := machine D C
  outputTape := outputSlot D
  outputFresh := by
    change (DecompositionColdPrepare.tapes D+393)≠0
    omega

theorem input_eq (D C : ℕ) (payload : List Bool) :
    (program D C).inputTapes payload=input D payload := by
  funext i
  exact (input_sparse D payload i).symm

end NearCubicWires.RepairOrdinary.DecompositionGlobal
