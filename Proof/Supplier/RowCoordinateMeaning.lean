import Proof.Supplier.RowCoordinateLoop
import Proof.Supplier.RowCachedEquationMeaning
import Proof.Supplier.EquationWidenLoop

/-! The actual coordinate stream is the weight-and-target encoding of the
power-radix stack. The canonical radix is related only by its conjunction. -/
namespace NearCubicWires.RepairOrdinary.RowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :=
  RowCachedCoordinateBounds.width gs*indices.length
def equation {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :=
  RowPowerBinLift.stack (RowCachedCoordinateBounds.width gs) (RowCachedEquation.equations gs indices)
def equationWord {n : ℕ} (p : ℕ) (e : LabelledEquation (Fin n)) :=
  EquationWidenLoop.stream p (List.ofFn e.weights++[e.target])

theorem field_weight {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) (j : Fin n) :
    field gs indices j.val=MatrixScoreBatch.signMagnitude (width gs indices) ((equation gs indices).weights j) := by
  simp only [field,dif_pos j.isLt.le,RowCoefficientStream.field,width,equation,
    RowCachedEquation.stack_weight]

theorem field_target {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) :
    field gs indices n=MatrixScoreBatch.signMagnitude (width gs indices) (equation gs indices).target := by
  simp only [field,dif_pos le_rfl,RowCoefficientStream.field,width,equation,
    RowCachedEquation.stack_target]

theorem word_add {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (j a b : ℕ) : word gs indices j (a+b)=word gs indices j a++word gs indices (j+a) b := by
  induction a generalizing j with
  | zero => simp [word]
  | succ a ih =>
    rw [Nat.succ_add,word,word,ih,List.append_assoc]
    rw [show j+1+a=j+(a+1) by omega]

theorem word_ofFn {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (j count : ℕ) : word gs indices j count=
      (List.ofFn (fun i : Fin count=>frame (field gs indices (j+i.val)))).flatten := by
  induction count generalizing j with
  | zero => simp [word]
  | succ count ih =>
    rw [word,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have h : (fun i : Fin count=>frame (field gs indices (j+1+i.val)))=
        (fun i : Fin count=>frame (field gs indices (j+(i.val+1)))) := by
      funext i
      rw [show j+1+i.val=j+(i.val+1) by omega]
    rw [h]

theorem word_equation {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :
    word gs indices 0 (n+1)=equationWord (width gs indices) (equation gs indices) := by
  rw [word_add,word_ofFn]
  simp only [Nat.zero_add,word,List.append_nil,field_target]
  simp only [equationWord,EquationWidenLoop.stream,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,field_weight]
  congr 1
  rw [List.flatMap]
  simp only [List.map_ofFn,Function.comp_def]

theorem equation_magnitude {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) :
    equationMagnitudeBound (equation gs indices)<2^(width gs indices) := by
  have h := RowPowerBinLift.stack_width (RowCachedCoordinateBounds.width gs)
    (RowCachedEquation.equations gs indices) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
      exact RowCachedEquation.cache_radix_safe gs i)
  simpa only [RowCachedEquation.equations,List.length_map,width,equation] using h

theorem equation_holds {n : ℕ} (gs : List (ExactThresholdGate n))
    (indices : List (Fin gs.length)) (input : Fin n→Bool) :
    (equation gs indices).Holds input ↔
      (canonicalEquationStack (RowCachedEquation.equations gs indices)).Holds input :=
  RowCachedEquation.same_conjunction gs indices input

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length))
    (tail out : List Bool) :
    ∃ r,runFrom machine (budget gs indices) (cfg gs indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs indices 3 (n+1) 1 tail
        (out++equationWord (width gs indices) (equation gs indices)) ∧
      r.steps ≤ budget gs indices := by
  simpa only [word_equation] using row_run gs indices tail out

end NearCubicWires.RepairOrdinary.RowCoordinateLoop
