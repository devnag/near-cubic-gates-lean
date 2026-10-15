import Proof.MachineModel.ClosureRadixCoordinate

/-! A.12's per-monomial degree, supplied by the actual mask bank. The
physical mask/cursor machines are unchanged. No degree bound on arbitrary
unrelated masks is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler

def P1Radix.effectiveDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] :=
  min (P1Radix.degree gs) gs.length

class P1MaskDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (rows : List (List Bool)) : Prop where
  bound : ∀ row∈rows, row.count true ≤ P1Radix.effectiveDegree gs

class P1BankDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (bank : List (List (List Bool))) : Prop where
  bound : ∀ rows∈bank, P1MaskDegree gs rows

namespace P1MaskDegree
variable {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]

instance empty : P1MaskDegree gs [] := ⟨by simp⟩

instance getD (bank : List (List (List Bool))) [P1BankDegree gs bank] (j : Nat) :
    P1MaskDegree gs (bank.getD j []) := by
  by_cases hj : j < bank.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact P1BankDegree.bound _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega : bank.length ≤ j)]
    infer_instance

theorem count_le (rows : List (List Bool)) [P1MaskDegree gs rows]
    (ds : List Nat) (hd : ∀ d∈ds,d < rows.length) :
    RowTupleMaskLoop.count rows ds ≤ P1Radix.effectiveDegree gs*ds.length := by
  induction ds with
  | nil => simp [RowTupleMaskLoop.count]
  | cons d ds ih =>
    have ht := ih (fun k hk => hd k (List.mem_cons_of_mem d hk))
    have hd' := hd d (by simp)
    have hb := P1MaskDegree.bound (gs := gs) rows[d] (List.getElem_mem hd')
    have he : RowTupleMaskLoop.mask rows d = rows[d] := by
      simp only [RowTupleMaskLoop.mask,List.getElem?_eq_getElem hd',Option.getD_some]
    simp only [RowTupleMaskLoop.count,List.map_cons,List.sum_cons,List.length_cons] at *
    rw [he]
    nlinarith

end P1MaskDegree

end NearCubicWires.RepairOrdinary
