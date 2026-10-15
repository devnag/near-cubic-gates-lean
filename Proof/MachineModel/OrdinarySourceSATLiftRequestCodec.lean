import Proof.MachineModel.OrdinarySourceSATLift

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceInput (code : List Bool) (n : ℕ) := frame code++frame (List.replicate n true)
def value (code : List Bool) (C D n : ℕ) := boundInput (sourceInput code n) (C*(n+1)^D)
def header (code : List Bool) := Streaming.marks (Streaming.marks (frame code))
def separator : List Bool := [true,true,true,false,true,false]
def trailer : List Bool := [true,false,false]

theorem marks_unary (n : ℕ) : Streaming.marks (List.replicate n true)=List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Streaming.marks,List.replicate_succ,Nat.mul_succ,List.replicate_add] using congrArg (fun w => true::true::w) ih

theorem frame_marks (bits : List Bool) : frame bits=Streaming.marks bits++[false] := by
  simpa only [List.append_nil,RepairOrdinary.frame] using Streaming.frame_append bits []
theorem marks_cons (bit : Bool) (bits : List Bool) :
    Streaming.marks (bit::bits)=true::bit::Streaming.marks bits := by simp [Streaming.marks]
theorem marks_nil : Streaming.marks []=[] := rfl

theorem frame_value (code : List Bool) (C D n : ℕ) :
    frame (value code C D n)=header code++List.replicate (8*n) true++separator++
      List.replicate (4*(C*(n+1)^D)) true++trailer := by
  simp only [value,boundInput,sourceInput,header,frame_marks,Streaming.marks_append,
    marks_unary,marks_cons,marks_nil,separator,trailer,List.append_assoc]
  have h8 : 2*(2*(2*n))=8*n := by ring
  have h4 : 2*(2*(C*(n+1)^D))=4*(C*(n+1)^D) := by ring
  simp only [h8,h4,List.cons_append,List.nil_append]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
