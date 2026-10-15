import Proof.Amplification.RecoveryRetainedAssignment

/-! The literal truth/OR step reads the actual sign, assignment value and
two physical validity bits. It rejects either invalid input in one transition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryLiteralTruth
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def value (sign bit : Bool) := if sign then bit else !bit
def accepted (tagValid tableValid : Bool) := tagValid && tableValid
def result (sign bit old tagValid tableValid : Bool) :=
  if accepted tagValid tableValid then old || value sign bit else false

def machine : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    ![none,none,some (result (bits 0) (bits 1) (bits 2) (bits 3) (bits 4)),
      some (accepted (bits 3) (bits 4)),none],fun _=>.stay⟩ else none

theorem truth_ready (sign bit old tagValid tableValid : Bool) :
    ReadyRun machine 1 ![[sign],[bit],[old],[tagValid],[tableValid]]
      ![[sign],[bit],[result sign bit old tagValid tableValid],[accepted tagValid tableValid],[tableValid]] := by
  let input := ![[sign],[bit],[old],[tagValid],[tableValid]]
  let output := ![[sign],[bit],[result sign bit old tagValid tableValid],[accepted tagValid tableValid],[tableValid]]
  let last : Configuration 5 2 := ⟨1,fun _=>0,output⟩
  have h : step machine (initialConfiguration machine input)=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

end NearCubicWires.RepairOrdinary.RecoveryLiteralTruth
