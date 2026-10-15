import Proof.CaseAnalysis.RowsEstimatorParityGlyph

/-! Literal native bytes for parity gates use only signed zero/one and the actual staircase index. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open LocalBitMultitape RepairRepresentation SupplierPipeline CompilerSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bitWeight (b : Bool) : List Bool:=[false,true,false,b]
def weights (mask : List Bool):=mask.flatMap bitWeight
def bottomWord (mask : List Bool) (j : ℕ):=natWord mask.length++weights mask++false::natWord j
def identityMask {n : ℕ} (j : Fin n):=List.ofFn (fun i=>decide (i=j))

theorem bitWeight_exact (b : Bool) : bitWeight b=intWord (if b then 1 else 0) := by cases b <;> rfl

theorem weights_exact {n : ℕ} (b : Fin n→Bool) :
    weights (List.ofFn b)=(List.ofFn (fun i=>if b i then (1 : ℤ) else 0)).flatMap intWord := by
  simp only [weights,List.ofFn_eq_map,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  exact bitWeight_exact _

theorem positive_int (j : ℕ) : intWord (j : ℤ)=false::natWord j := by
  simp [intWord]

theorem identity_native {n : ℕ} (i : Fin n) :
    CloseoutRowsCircuitBottom.nativeWord (inputBitSupportedGate i)=bottomWord (identityMask i) 0 := by
  change natWord n++(List.ofFn (fun j=>if j=i then (1 : ℤ) else 0)).flatMap intWord++intWord 0=_
  rw [bottomWord,identityMask,List.length_ofFn,weights_exact]
  simp only [decide_eq_true_eq]
  rfl

theorem identity_support {n : ℕ} (i : Fin n) :
    CloseoutRowsGateSupport.gateMembers (inputBitSupportedGate i).support=identityMask i := by
  simp [CloseoutRowsGateSupport.gateMembers,inputBitSupportedGate,identityMask]

theorem staircase_native {n : ℕ} (support : Finset (Fin n)) (j : Fin support.card) :
    CloseoutRowsCircuitBottom.nativeWord (thresholdParityBottomGate support j)=
      bottomWord (CloseoutRowsGateSupport.gateMembers support) j.val := by
  change natWord n++(List.ofFn (fun i=>if i∈support then (1 : ℤ) else 0)).flatMap intWord++
    intWord ((j.val : ℤ)+1-1)=_
  rw [bottomWord,CloseoutRowsGateSupport.gateMembers,List.length_ofFn,weights_exact]
  simp only [decide_eq_true_eq,show (j.val : ℤ)+1-1=j.val by omega,positive_int]

theorem staircase_support {n : ℕ} (support : Finset (Fin n)) (j : Fin support.card) :
    CloseoutRowsGateSupport.gateMembers (thresholdParityBottomGate support j).support=
      CloseoutRowsGateSupport.gateMembers support := rfl

theorem weights_length (mask : List Bool) : (weights mask).length=4*mask.length := by
  induction mask with
  | nil=>rfl
  | cons b bs ih=>simp only [weights,List.flatMap_cons,List.length_append,bitWeight,List.length_cons,
      List.length_nil] at *;omega

theorem bottom_length (mask : List Bool) (j : ℕ) :
    (bottomWord mask j).length=2*natBitLength mask.length+4*mask.length+2*natBitLength j+3 := by
  simp only [bottomWord,List.length_append,List.length_cons,DecompositionSource.natWord_length,weights_length]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
