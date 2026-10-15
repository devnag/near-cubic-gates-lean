import Proof.CaseAnalysis.FinalTailCompose
import Proof.CaseAnalysis.WitnessBoundedFamilySupportLayout

/-! The actual length-gate exit supplies the cold bank and its empty rewind log.
This projection is shared by admitted and rejected continuations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdGateInput
open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CloseoutFinal ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem input
    (m : Nat)
    (e : Nat)
    (W : Nat)
    (input : List Bool)
    (bits : List Bool) :
    let P := 301+e
    let total := (HeaderDock.tapes m+2+(301+e+96+W))
    let coldSlots : Fin (HeaderDock.tapes m+1+1) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    ∀ j,C10TailCompose.entryOf flag input bits (coldSlots j)=(Fin.addCases (m:=HeaderDock.tapes m+1) (n:=1) (motive:=fun _ => List Bool) (SupportDock.lift (HeaderDock.input m (CompetitorWitnessBounded.input input bits)) []) (fun _ : Fin 1 => [])) j :=
  by
    have inputShape : ∀ j : Fin (HeaderDock.tapes m+1+1),(Fin.addCases (m:=HeaderDock.tapes m+1) (n:=1) (motive:=fun _ => List Bool) (SupportDock.lift (HeaderDock.input m (CompetitorWitnessBounded.input input bits)) []) (fun _ : Fin 1 => [])) j=if j.val=0 then frame input else if j.val=1 then frame bits else [] := by
      intro j
      refine Fin.addCases (m:=HeaderDock.tapes m+1) (n:=1) ?_ ?_ j
      · intro j
        rw [Fin.addCases_left]
        refine Fin.addCases (m:=HeaderDock.tapes m) (n:=1) ?_ ?_ j
        · intro j
          rw [SupportDock.lift,Fin.addCases_left]
          refine Fin.addCases (m:=150) (n:=m+1) ?_ ?_ j
          · intro j
            simp only [HeaderDock.input,Fin.addCases_left,Fin.val_castAdd]
            exact CompetitorWitnessBounded.input_eq input bits j
          · intro j
            simp only [HeaderDock.input,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
            rw [if_neg (by omega),if_neg (by omega)]
        · intro j
          simp only [SupportDock.lift,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
          rw [if_neg (by dsimp [HeaderDock.tapes];omega),if_neg (by dsimp [HeaderDock.tapes];omega)]
      · intro j
        simp only [Fin.addCases_right,Fin.val_natAdd]
        rw [if_neg (by dsimp [HeaderDock.tapes];omega),if_neg (by dsimp [HeaderDock.tapes];omega)]
    dsimp only
    let P := 301+e
    let total := (HeaderDock.tapes m+2+(301+e+96+W))
    let coldSlots : Fin (HeaderDock.tapes m+1+1) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    change ∀ j,C10TailCompose.entryOf flag input bits (coldSlots j)=(Fin.addCases (m:=HeaderDock.tapes m+1) (n:=1) (motive:=fun _ => List Bool) (SupportDock.lift (HeaderDock.input m (CompetitorWitnessBounded.input input bits)) []) (fun _ : Fin 1 => [])) j
    intro j
    rw [inputShape]
    have hflag : coldSlots j ≠ flag := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [coldSlots,flag] at hv
      split_ifs at hv <;> (try dsimp [P] at *) <;> omega
    have h0 : (coldSlots j).val=0 ↔ j.val=0 := by
      dsimp only [coldSlots]
      split_ifs <;> dsimp [P] at * <;> omega
    have h1 : (coldSlots j).val=1 ↔ j.val=1 := by
      dsimp only [coldSlots]
      split_ifs <;> dsimp [P] at * <;> omega
    simp only [C10TailCompose.entryOf,hflag,if_false,h0,h1]

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdGateInput
