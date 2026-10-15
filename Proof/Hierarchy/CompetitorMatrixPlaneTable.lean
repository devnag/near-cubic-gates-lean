import Proof.Hierarchy.CompetitorPlaneTableEntry
import Proof.MachineModel.OrdinaryMatrixScoreBatchTarget

/-! Literal corrected matrix output is the input of the executed P4 table
loop. The bridge preserves every original row-major cell, including zeros,
and derives native count/shift/prefix fits rather than requesting them. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMatrixPlaneTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorPlaneStream MatrixScoreBatch
open SourceInterfaces
open WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def count (r : Request) (negative : Bool) (bit : ℕ) (i : Fin (r.U*r.U)) : ℕ :=
  integerMatrixProduct (fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit)
    (booleanRight r) i.divNat i.modNat
def plane (r : Request) (bit : ℕ) : Plane (r.U*r.U) := ⟨bit,count r false bit,count r true bit⟩
def planes (r : Request) := (List.range r.p).map (plane r)

theorem count_fits (r : Request) (negative : Bool) (bit : ℕ) (i : Fin (r.U*r.U)) :
    count r negative bit i<2^natBitLength r.U := by
  have hi := RepairRepresentation.product_entry_le_inner
    (fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit) (booleanRight r) i.divNat i.modNat
  have hcap : r.Capacity≤r.U := by
    unfold Request.Capacity rectangularInnerDimension
    exact integerCeilRoot_le (by omega) (Nat.le_self_pow (by omega) r.U)
  exact (hi.trans hcap).trans_lt (show r.U<2^natBitLength r.U from Nat.lt_pow_succ_log_self (by decide) r.U)

theorem count_cells (r : Request) (negative : Bool) (bit : ℕ) :
    List.ofFn (count r negative bit)=rowMajorNatMatrix (integerMatrixProduct
      (fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit) (booleanRight r)) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  have hU : 0<r.U := by unfold Request.U; positivity
  have hd : (row.val*r.U+column.val)/r.U=row.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hU,Nat.div_eq_of_lt column.isLt,Nat.zero_add]
  have hm : (row.val*r.U+column.val)%r.U=column.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt column.isLt]
  simp [count,Fin.divNat,Fin.modNat,hd,hm]

theorem count_word (r : Request) (negative : Bool) (bit : ℕ) (state : State (r.U*r.U)) :
    countWords (natBitLength r.U) (cells (count r negative bit) state)=planeCounts r negative bit := by
  unfold countWords planeCounts encodedNatCellTape
  rw [← count_cells]
  simp only [cells,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact (RepairSource.VerifierDecoding.fixedBits_binary _ _).symm

theorem packet_word (r : Request) (bit : ℕ) :
    (plane r bit).word (natBitLength r.U)=packet r false bit++packet r true bit := by
  unfold Plane.word pairWord CompetitorPlanePacketPair.word
  simp only [plane]
  rw [count_word,count_word]
  rfl

theorem output_stream (r : Request) : stream (natBitLength r.U) (planes r)=output r := by
  simp only [stream,planes,List.flatMap_map,packet_word,output]

theorem valid_planes (r : Request) : ∀ a∈planes r,a.Valid (natBitLength r.U) r.p := by
  intro a ha
  obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp ha
  exact ⟨List.mem_range.mp hbit,count_fits r false bit,count_fits r true bit⟩

theorem native_table_run (r : Request) (pre suffix : List Bool) (ambient : Fin 34 → List Bool)
    (hcontext : TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
      (zero (r.U*r.U)) ambient)
    (hsource : ambient 32=pre++output r++suffix) :
    ∃ run out,runFrom CompetitorPlaneTableEntry.machine
      (CompetitorPlaneTableEntry.budget (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p)
      (CompetitorPlaneTableEntry.cfg CompetitorPlaneTableEntry.machine.start pre.length 0 ambient r.p)=some run ∧
      run.steps≤CompetitorPlaneTableEntry.budget (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p ∧
      run.final.heads=CompetitorPlaneTableEntry.heads (pre.length+(output r).length) 0 ∧
      run.final.tapes=CompetitorPlaneTableEntry.tapes out r.p ∧
      TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
        (evaluate (planes r) (zero (r.U*r.U))) out ∧
      out 32=pre++output r++suffix ∧
      Bounded (natBitLength r.U) r.p (2*r.p) (evaluate (planes r) (zero (r.U*r.U))) := by
  have hs : Bounded (natBitLength r.U) r.p 0 (zero (r.U*r.U)) := by intro i; simp [zero]
  have hlen : (planes r).length=r.p := by simp [planes]
  simpa only [output_stream,hlen] using
    CompetitorPlaneTableEntry.table_run (natBitLength r.U) r.p (planes r) (zero (r.U*r.U)) pre suffix ambient
      (by simp [planes]) (valid_planes r) hs hcontext (by rw [output_stream]; exact hsource)

end NearCubicWires.RepairOrdinary.CompetitorMatrixPlaneTable
