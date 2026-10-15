import Proof.CaseAnalysis.RecoverySuppliersLayout

/-! The supplier entry has only the retained raw hierarchy request and W.
The original count worker receives its exact cold input with all heads zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem count_input_lookup (k : ℕ) (word : List Bool) (i : Fin (base source k)) :
    RecoveryBoundedColdHierarchyDock.Count.input source k (fun _=>[]) word i=
      if i.val=158 then word else []:=by
  change Fin.addCases (RecoveryBoundedColdHierarchyDock.input source k (fun _=>[]) word)
    (fun _ : Fin 1=>[]) i=if i.val=158 then word else []
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd]
    change Fin.addCases (fun _ : Fin 158=>[]) (SourceHandoff.sourceTapes word) j=
      if j.val=158 then word else []
    refine Fin.addCases (fun a=>?_) (fun a=>?_) j
    · have ha:=a.isLt
      simp only [Fin.addCases_left,Fin.val_castAdd,if_neg (show a.val≠158 by omega)]
    · simp only [Fin.addCases_right,Fin.val_natAdd,SourceHandoff.sourceTapes]
      by_cases ha : a.val=0
      · simp only [ha,if_pos,Nat.add_zero]
      · simp only [if_neg ha,if_neg (show 158+a.val≠158 by omega)]
  · have hb : 158<RecoveryBoundedColdHierarchyDock.tapes source k:=by
      dsimp only [RecoveryBoundedColdHierarchyDock.tapes,HierarchyStreams.tapes]
      omega
    simp only [Fin.addCases_right,Fin.val_natAdd,if_neg (show
      RecoveryBoundedColdHierarchyDock.tapes source k+j.val≠158 by omega)]

theorem count_heads (k : ℕ) (i : Fin (base source k)) :
    RecoveryBoundedColdHierarchyDock.Count.heads source k (fun _=>0) i=0:=by
  change Fin.addCases (RecoveryBoundedColdHierarchyDock.heads source k (fun _=>0))
    (fun _ : Fin 1=>0) i=0
  refine Fin.addCases (fun j=>?_) (fun j=>Fin.addCases_right j) i
  rw [Fin.addCases_left]
  change Fin.addCases (fun _ : Fin 158=>0) (fun _=>0) j=0
  exact Fin.addCases (fun a=>Fin.addCases_left a) (fun a=>Fin.addCases_right a) j

theorem count_input (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin (base source k)) :
    input source k d word W (countSlots source k d i)=
      RecoveryBoundedColdHierarchyDock.Count.input source k (fun _=>[]) word i:=by
  have hi:=i.isLt
  simp only [input,countSlots,Fin.val_castAdd,count_input_lookup,if_neg (show i.val≠base source k by omega)]

theorem input_old (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin 158) :
    input source k d word W (old source k d i)=[]:=by
  have hi:=i.isLt
  have hb:=base_large source k
  simp only [input,old,if_neg (show i.val≠158 by omega),if_neg (show i.val≠base source k by omega)]

theorem input_w (k d : ℕ) (word : List Bool) (W : ℕ) :
    input source k d word W (wPort source k d)=List.replicate W true:=by
  have hb:=base_large source k
  simp only [input,wPort,if_neg (show base source k≠158 by omega),if_pos]

theorem input_fresh (k d : ℕ) (word : List Bool) (W : ℕ) (i : Fin (tapes source k d))
    (hi : base source k < i.val) : input source k d word W i=[]:=by
  have hb:=base_large source k
  simp only [input,if_neg (show i.val≠158 by omega),if_neg (show i.val≠base source k by omega)]

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
