import Proof.PCP.PCPPRequestInput

/-! One call to the faithful PCPP constructor on the physically emitted
request, with an isolated blank source workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestSource
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : PointwisePCPPAlgorithm)
def program := Rewind.program a.constructor.program
def tapes := PCPPRequestInput.tapes+(program a).tapeCount
def slots (j : Fin (program a).tapeCount) : Fin (tapes a) :=
  if j.val=0 then PCPPRequestInput.outputSlot.castAdd (program a).tapeCount
  else j.natAdd PCPPRequestInput.tapes
theorem slots_injective : Function.Injective (slots a) := by
  intro i j he
  have hv := congrArg Fin.val he
  have ho : PCPPRequestInput.outputSlot.val < PCPPRequestInput.tapes := PCPPRequestInput.outputSlot.isLt
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega
def outputSlot := slots a (program a).outputTape
noncomputable def first := TapeEmbedding.machine (program a).tapeCount PCPPRequestInput.machine
noncomputable def second := RecoveryFocus.machine (slots a) (program a).machine
noncomputable def machine := Composition.machine (first a) (second a)
def input (request : PCPPRequest a.minimumArity) : Fin (tapes a) → List Bool :=
  Fin.addCases (m:=PCPPRequestInput.tapes) (n:=(program a).tapeCount)
    (PCPPRequestInput.input request.circuit) (fun _ => [])
def sourceBudget (request : PCPPRequest a.minimumArity) :=
  a.coefficient*(request.circuit.size+request.arity+1)^a.degree
def budget (request : PCPPRequest a.minimumArity) :=
  PCPPRequestInput.budget request.circuit+2*sourceBudget a request+3

end NearCubicWires.RepairOrdinary.PCPPRequestSource
