import Proof.SourceAssembly.SourceThresholdTopQuery

/- The three logical outputs fit the ORIGINAL quadratic C reserve, even
though repeated native-index production spends cubic preprocessing time. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdBounds
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

theorem emitted_bound (q j : Nat) (bits : List Bool) (hj : j≤q) (hlen : bits.length=q) (i : Fin 2) :
    (SourceAssemblyThresholdGate.emitted q j bits i).length≤16*q+15 := by
  have hn:natBitLength j≤j+1:=Nat.add_le_add_right (Nat.log_le_self 2 j) 1
  have hq:natBitLength q≤q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  fin_cases i
  · change (frame (natWord q++weights bits++false::natWord j)).length≤16*q+15
    simp only [frame_length,List.length_append,List.length_cons,DecompositionSource.natWord_length,weights_length,hlen]
    omega
  · change (frame bits).length≤16*q+15
    rw [frame_length,hlen]
    omega

theorem outputs_linear (q n : Nat) (bits : List Bool) (hn : n≤q) (hlen : bits.length=q) (i : Fin 2) :
    (SourceAssemblyThresholdLoop.outputs q bits n i).length≤n*(16*q+15) := by
  induction n with
  | zero=>simp [SourceAssemblyThresholdLoop.outputs]
  | succ n ih=>
    rw [SourceAssemblyThresholdLoop.outputs_succ]
    have h:=emitted_bound q n bits (by omega) hlen i
    have hprev:=ih (by omega)
    simp only [List.length_append]
    nlinarith

theorem outputs_bound (q n : Nat) (bits : List Bool) (hn : n≤q) (hlen : bits.length=q) (i : Fin 2) :
    (SourceAssemblyThresholdLoop.outputs q bits n i).length≤Capacity.value q := by
  have h:=(outputs_linear q n bits hn hlen i).trans (Nat.mul_le_mul_right (16*q+15) hn)
  unfold Capacity.value
  nlinarith [Nat.zero_le (q*q)]

theorem top_bound (q n : Nat) (hn : n≤q) : (frame (SourceAssemblyThresholdTop.payload n)).length≤Capacity.value q := by
  have hl : ((List.range n).flatMap (fun j=>[Alternating.flag j,true,false,true])).length=4*n := by
    induction n with
    | zero=>rfl
    | succ n ih=>simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,
        List.length_append,List.length_cons,List.length_nil] at *;omega
  have hbit:natBitLength n≤n+1:=Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  simp only [frame_length,SourceAssemblyThresholdTop.payload,List.length_append,
    DecompositionSource.natWord_length,hl,bitWeight,List.length_cons,List.length_nil,Capacity.value]
  nlinarith [Nat.zero_le (q*q)]

end
end SourceAssemblyThresholdBounds
