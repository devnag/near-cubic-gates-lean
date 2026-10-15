import Proof.CaseAnalysis.CaseTwoSelected
import Proof.Amplification.RecoveryCaseOneBooleanOutput

/-! The selected Case2 singleton is framed by the existing Boolean worker.
Two fresh empty tapes supply its output and private rewind log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SelectedOutput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

def tapes (k D copies : ℕ):=Execution.tapes source a k D copies+2
def old (k D copies : ℕ) (i : Fin (Execution.tapes source a k D copies)) :
    Fin (tapes source a k D copies):=i.castAdd 2
def fresh (k D copies : ℕ) (i : Fin 2) : Fin (tapes source a k D copies):=
  i.natAdd (Execution.tapes source a k D copies)
def slots (k D copies : ℕ) : Fin 3→Fin (tapes source a k D copies):=
  ![old source a k D copies (Execution.outputSlot source a k D copies),
    fresh source a k D copies 0,fresh source a k D copies 1]
def input (k D copies : ℕ) (bank : Fin (Execution.tapes source a k D copies)→List Bool) :
    Fin (tapes source a k D copies)→List Bool:=Fin.addCases bank (fun _=>[])
def first (k D copies CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source a k D copies) (Execution.machine source a k D copies CH Cpad code)
def last (k D copies : ℕ):=
  RecoveryFocus.machine (slots source a k D copies) RecoveryCaseOneBooleanOutput.machine
def machine (k D copies CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (first source a k D copies CH Cpad code) (last source a k D copies)

theorem old_injective (k D copies : ℕ) : Function.Injective (old source a k D copies):=by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin (tapes source a k D copies)=>q.val) h)

theorem slots_injective (k D copies : ℕ) : Function.Injective (slots source a k D copies):=by
  have hb:=(Execution.outputSlot source a k D copies).isLt
  intro i j h
  fin_cases i <;>fin_cases j <;>try rfl
  all_goals
    have hv:=congrArg Fin.val h
    simp [slots,old,fresh] at hv <;>omega

theorem fresh_outside (k D copies : ℕ) (i : Fin 2) :
    ∀ j,old source a k D copies j≠fresh source a k D copies i:=by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  change j.val=Execution.tapes source a k D copies+i.val at hv
  omega

theorem old_outside (k D copies : ℕ) (i : Fin (Execution.tapes source a k D copies))
    (hi : i≠Execution.outputSlot source a k D copies) :
    ∀ j,slots source a k D copies j≠old source a k D copies i:=by
  intro j h
  fin_cases j
  · exact hi ((old_injective source a k D copies h).symm)
  · exact fresh_outside source a k D copies 0 i h.symm
  · exact fresh_outside source a k D copies 1 i h.symm

theorem original_port_outside (k D copies : ℕ) (i : Fin 3) :
    Execution.old source a k D copies (i.castAdd 137)≠Execution.outputSlot source a k D copies:=by
  intro h
  have hv:=congrArg Fin.val h
  have hi:=i.isLt
  change i.val=143 at hv
  omega

theorem run (k D copies CH Cpad fuel : ℕ) (code : List Bool)
    (bank raw : Fin (Execution.tapes source a k D copies)→List Bool) (bit : Bool)
    (actual : ClockJoin.ReadyRun (Execution.machine source a k D copies CH Cpad code) fuel bank raw)
    (value : raw (Execution.outputSlot source a k D copies)=[bit]) :
    ∃ out,ClockJoin.ReadyRun (machine source a k D copies CH Cpad code) (fuel+9)
      (input source a k D copies bank) out ∧
      out (fresh source a k D copies 0)=frame bit.toNat.bits ∧
      ∀ i,i≠Execution.outputSlot source a k D copies → out (old source a k D copies i)=raw i :=by
  let middle:=install (old source a k D copies) (input source a k D copies bank) raw
  have firstRun:=actual.focus (old source a k D copies) (old_injective source a k D copies)
    (input source a k D copies bank) (by intro i;simp only [input,old,Fin.addCases_left])
  obtain ⟨encoded,encodedRun,encodedValue⟩:=RecoveryCaseOneBooleanOutput.ready bit
  have blank (i : Fin 2) : middle (fresh source a k D copies i)=[]:=by
    rw [show middle=install (old source a k D copies) (input source a k D copies bank) raw from rfl,
      install_other _ _ _ _ (fresh_outside source a k D copies i)]
    simp only [input,fresh,Fin.addCases_right]
  have lastRun:=encodedRun.focus (slots source a k D copies) (slots_injective source a k D copies)
    middle (by
      intro i;fin_cases i
      · exact (install_slot (old source a k D copies) (old_injective source a k D copies)
          (input source a k D copies bank) raw (Execution.outputSlot source a k D copies)).trans value
      · exact blank 0
      · exact blank 1)
  have whole:=ClockJoin.join (first source a k D copies CH Cpad code) (last source a k D copies)
    fuel 8 _ _ _ firstRun lastRun
  rw [show fuel+1+8=fuel+9 from by omega] at whole
  refine ⟨install (slots source a k D copies) middle encoded,?_,?_,?_⟩
  · exact whole
  · exact (install_slot (slots source a k D copies) (slots_injective source a k D copies)
      middle encoded 1).trans encodedValue
  · intro i hi
    exact (install_other _ _ _ _ (old_outside source a k D copies i hi)).trans
      (install_slot (old source a k D copies) (old_injective source a k D copies)
        (input source a k D copies bank) raw i)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SelectedOutput
