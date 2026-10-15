import Proof.Amplification.RecoveryRowStructureRetained

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def leafAmbient (x : Children) (core : Fin 46→List Bool) : Fin 68→List Bool :=
  Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) core x.base.right)
      (fun _=>List.replicate x.copyCapacity false))
    (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)
noncomputable def rowLeafMachine := onBase (onCore RecoveryRowLeaf.machine)

theorem leaf_embed {s : Nat} (p : Machine 46 s) (x : Children) (fuel : Nat)
    (base : ExecutionReceipt 46 s) (hr : run p fuel x.base.left=some base) (hh : ∀ i,base.final.heads i=0) :
    ∃ r,runFrom (onBase (onCore p)) fuel (x.cfg p.start)=some r ∧
      r.final.heads=x.heads ∧ r.final.tapes=leafAmbient x base.final.tapes ∧ r.steps=base.steps := by
  let middle := TapeEmbedding.receipt x.base.rightHeads x.base.right base
  have hm := TapeEmbedding.run_embed p x.base.rightHeads x.base.right fuel _ base hr
  let copy := fun _ : Fin 1=>List.replicate x.copyCapacity false
  let upper := TapeEmbedding.receipt (fun _ : Fin 1=>0) copy middle
  have hu := TapeEmbedding.run_embed (TapeEmbedding.machine 5 p) (fun _ : Fin 1=>0) copy fuel _ middle hm
  let bank := RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity
  let result := TapeEmbedding.receipt (fun _ : Fin 16=>0) bank upper
  have h := TapeEmbedding.run_embed (TapeEmbedding.machine 1 (TapeEmbedding.machine 5 p))
    (fun _ : Fin 16=>0) bank fuel _ upper hu
  refine ⟨result,h,?_,rfl,rfl⟩
  funext i
  refine Fin.addCases (m:=52) (n:=16) (motive:=fun i=>result.final.heads i=x.heads i) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=51) (n:=1) (motive:=fun j=>result.final.heads (j.castAdd 16)=x.heads (j.castAdd 16)) ?_ ?_ j
    · intro k
      refine Fin.addCases (m:=46) (n:=5) (motive:=fun k=>result.final.heads ((k.castAdd 1).castAdd 16)=
        x.heads ((k.castAdd 1).castAdd 16)) ?_ ?_ k
      · intro l
        simpa only [result,upper,middle,TapeEmbedding.receipt,TapeEmbedding.config,Children.heads,cfg,Data.cfg,
          Fin.addCases_left] using hh l
      · intro l
        simp only [result,upper,middle,TapeEmbedding.receipt,TapeEmbedding.config,Children.heads,cfg,Data.cfg,
          Fin.addCases_left,Fin.addCases_right]
    · intro k
      simp only [result,upper,TapeEmbedding.receipt,TapeEmbedding.config,Children.heads,cfg,
        Fin.addCases_left,Fin.addCases_right]
  · intro j
    simp only [result,TapeEmbedding.receipt,TapeEmbedding.config,Children.heads,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
