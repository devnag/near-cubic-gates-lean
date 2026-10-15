import Proof.MachineModel.OrdinaryMatrixScoreLeftLoop
import Proof.MachineModel.OrdinaryMatrixScorePhi

namespace NearCubicWires.RepairOrdinary.MatrixScorePhiFields
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

/-- The 42 per-gate native fields with `φ`. -/
def fields (r : Request) (gate : Fin r.Gates) : Fin 42 → List Bool :=
  ![cutWord r.p (r.cuts.get gate),frame (binary r.width 0),[],[],[],[],List.replicate (r.S+1) true,
    [],[],[],[],[],[],[],[],List.replicate (C r) true,zeros (C r+1),UnaryTemplate.tape r.width,
    frame (binary (r.S+1) (2^r.S)),frame (binary (r.S+1) 0),[],[],frame (binary r.M 0),
    frame (binary r.M r.U),[],zeros (C r),[],MatrixScorePhi.columnsWord r.width r.cols,
    UnaryTemplate.tape r.U,frame (binary r.width 0),
    [],[],[],[],[],[],[],[],[],[],[],[]]

/-- Old slot `i` of today's 41-slot layout sits at `i` below 27 and at `i+1` from 27 on. -/
def oldSlot (i : Fin 41) : Fin 42 := if i.val<27 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩

/-- For Theorem 2.5's requests (`width = d`) the old slots hold today's fields. -/
theorem fields_old_slots (r : Request) (gate : Fin r.Gates) (hw : r.width=r.d) (i : Fin 41) :
    fields r gate (oldSlot i)=
      (![cutWord r.p (r.cuts.get gate),frame (binary r.d 0),[],[],[],[],List.replicate (r.S+1) true,
        [],[],[],[],[],[],[],[],List.replicate (C r) true,zeros (C r+1),UnaryTemplate.tape r.d,
        frame (binary (r.S+1) (2^r.S)),frame (binary (r.S+1) 0),[],[],frame (binary r.M 0),
        frame (binary r.M r.U),[],zeros (C r),[],UnaryTemplate.tape r.U,frame (binary r.d 0),
        [],[],[],[],[],[],[],[],[],[],[],[]] : Fin 41 → List Bool) i := by
  unfold fields
  rw [hw]
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.MatrixScorePhiFields
