import Proof.CaseAnalysis.CaseTwoHonestInput

/-! The original honest auxiliary algorithm is called on the physically
joined request and actual input. Its output is the SAME PCPP's auxiliary
assignment; both retained input frames survive the call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HonestCall
open LocalBitMultitape RepairRepresentation RecoveryRootRound SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (a : PointwisePCPPAlgorithm)
def program:=Rewind.program a.honest.program
def tapes:=7+(program a).tapeCount
def joinSlots (i : Fin 7) : Fin (tapes a):=i.castAdd (program a).tapeCount
def slots (j : Fin (program a).tapeCount) : Fin (tapes a):=
  if j.val=0 then joinSlots a 5 else j.natAdd 7
def outputSlot:=slots a (program a).outputTape
theorem join_injective : Function.Injective (joinSlots a):=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin (tapes a)=>x.val) he
theorem slots_injective : Function.Injective (slots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots,joinSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_natAdd,Fin.val_castAdd] at hv <;>omega
theorem slots_away (i : Fin 2) : ∀ j,slots a j≠joinSlots a (i.castAdd 5):=by
  intro j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  dsimp only [slots,joinSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_natAdd,Fin.val_castAdd] at hv <;>omega
def first:=RecoveryFocus.machine (joinSlots a) HonestInput.machine
def last:=RecoveryFocus.machine (slots a) (program a).machine
def machine:=Composition.machine (first a) (last a)
def input (request : PCPPRequest a.minimumArity) (u : BitInput request.arity) : Fin (tapes a)→List Bool:=
  Fin.addCases (m:=7) (n:=(program a).tapeCount)
    (HonestInput.input (pcppInput request) (List.ofFn u)) (fun _=>[])
def sourceBudget (request : PCPPRequest a.minimumArity):=
  a.coefficient*(request.circuit.size+request.arity+1)^a.degree
def budget (request : PCPPRequest a.minimumArity) (u : BitInput request.arity):=
  HonestInput.budget (pcppInput request) (List.ofFn u)+1+(2*sourceBudget a request+2)

theorem honest_run (request : PCPPRequest a.minimumArity) (u : BitInput request.arity) : ∃ out,
    ClockJoin.ReadyRun (machine a) (budget a request u) (input a request u) out ∧
      out (outputSlot a)=List.ofFn ((a.output request).honestAuxiliary u) ∧
      out (joinSlots a 0)=frame (pcppInput request) ∧ out (joinSlots a 1)=frame (List.ofFn u):=by
  obtain ⟨joined,hj,joinedWord,keepR,keepU⟩:=HonestInput.honest_input_run (pcppInput request) (List.ofFn u)
  have firstReady:=hj.focus (joinSlots a) (join_injective a) (input a request u)
    (by intro j;exact Fin.addCases_left j)
  let middle:=install (joinSlots a) (input a request u) joined
  obtain ⟨r,hr,rt,rh⟩:=a.honest.reset_realizes ⟨request,u⟩
  have ready : ClockJoin.ReadyRun (program a).machine (2*sourceBudget a request+2)
      ((program a).inputTapes (pcppInput request++List.ofFn u)) r.final.tapes:=
    ⟨r,hr,rfl,rh,runFrom_steps_le _ _ _ r hr⟩
  have docked:=ready.focus (slots a) (slots_injective a) middle (by
    intro j
    by_cases hj0 : j.val=0
    · simp only [slots,hj0,if_true,Program.inputTapes]
      exact (install_slot (joinSlots a) (join_injective a) _ joined 5).trans joinedWord
    · have away : ∀ i,joinSlots a i≠slots a j:=by
        intro i he
        have hv:=congrArg Fin.val he
        simp only [slots,hj0,if_false,joinSlots,Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      rw [show middle (slots a j)=input a request u (slots a j) from
        install_other (joinSlots a) _ joined _ away]
      simp only [input,slots,hj0,if_false,Fin.addCases_right,Program.inputTapes])
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ firstReady docked,?_,?_,?_⟩
  · exact (install_slot (slots a) (slots_injective a) _ _ _).trans rt
  · exact (install_other (slots a) middle (show Fin (program a).tapeCount→List Bool from r.final.tapes)
      (joinSlots a 0) (slots_away a 0)).trans
        ((install_slot (joinSlots a) (join_injective a) _ _ 0).trans keepR)
  · exact (install_other (slots a) middle (show Fin (program a).tapeCount→List Bool from r.final.tapes)
      (joinSlots a 1) (slots_away a 1)).trans
        ((install_slot (joinSlots a) (join_injective a) _ _ 1).trans keepU)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HonestCall
