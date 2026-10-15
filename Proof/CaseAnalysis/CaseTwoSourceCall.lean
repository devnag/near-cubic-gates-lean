import Proof.PCP.PCPPRequestSourceLayout
import Proof.Amplification.RecoveryRootRoundTapes
import Proof.Hierarchy.HierarchyBinaryPower

/-! Copy the exact request before its single faithful constructor call.
The untouched original frame is the honest caller's retained input; the
constructor owns only its paid copy and initially empty private workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCall
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : PointwisePCPPAlgorithm)
def program:=PCPPRequestSource.program a
def tapes:=4+(program a).tapeCount
def copySlots (i : Fin 4) : Fin (tapes a):=i.castAdd (program a).tapeCount
theorem copy_injective : Function.Injective (copySlots a):=by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (tapes a)=>x.val) h)
def slots (j : Fin (program a).tapeCount) : Fin (tapes a):=
  if j.val=0 then ⟨1,by have h:=(program a).twoTapes;dsimp [tapes];omega⟩ else j.natAdd 4
def outputSlot:=slots a (program a).outputTape
theorem slots_injective : Function.Injective (slots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega
noncomputable def first:=RecoveryFocus.machine (copySlots a) copyMachine
noncomputable def second:=RecoveryFocus.machine (slots a) (program a).machine
noncomputable def machine:=Composition.machine (first a) (second a)
def input (word : List Bool) : Fin (tapes a)→List Bool:=SourceHandoff.sourceTapes (frame word)
def copied (word : List Bool) : Fin (tapes a)→List Bool:=
  Fin.addCases (m:=4) (n:=(program a).tapeCount)
    ![frame word,frame word,List.replicate (2*word.length+1) false,List.replicate (4*word.length+3) false] (fun _=>[])
def budget (request : PCPPRequest a.minimumArity):=
  (8*(pcppInput request).length+8)+1+(2*PCPPRequestSource.sourceBudget a request+2)

theorem copy_ready (word : List Bool) : ClockJoin.ReadyRun (first a) (8*word.length+8)
    (input a word) (copied a word):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryRootRound.copy_ready word [] 0 0 (by simp)
  have ready : ClockJoin.ReadyRun copyMachine (8*word.length+8) ![frame word,[],[],[]]
      ![frame word,frame word,List.replicate (2*word.length+1) false,List.replicate (4*word.length+3) false]:=by
    simpa only [List.replicate_zero,Nat.zero_max] using (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩)
  have f:=ready.focus (copySlots a) (copy_injective a) (input a word)
    (by intro j;fin_cases j <;>rfl)
  have hout : install (copySlots a) (input a word)
      ![frame word,frame word,List.replicate (2*word.length+1) false,List.replicate (4*word.length+3) false]=copied a word:=by
    funext i
    refine Fin.addCases (m:=4) (n:=(program a).tapeCount) (fun j=>?_) (fun j=>?_) i
    · simpa only [copied,copySlots,Fin.addCases_left] using
        (install_slot (copySlots a) (copy_injective a) (input a word)
          ![frame word,frame word,List.replicate (2*word.length+1) false,List.replicate (4*word.length+3) false] j)
    · rw [install_other (copySlots a) _ _ (j.natAdd 4) (by
        intro k he
        have hv:=congrArg Fin.val he
        dsimp [copySlots] at hv
        omega)]
      simp [copied,input,SourceHandoff.sourceTapes]
  rw [hout] at f
  exact f

theorem source_run (request : PCPPRequest a.minimumArity) : ∃ out,
    ClockJoin.ReadyRun (machine a) (budget a request) (input a (pcppInput request)) out ∧
      out (outputSlot a)=pcppOutput request (a.output request) ∧
      out ⟨0,by dsimp [tapes];omega⟩=frame (pcppInput request):=by
  have copy:=copy_ready a (pcppInput request)
  obtain ⟨r,hr,ht,hh⟩:=a.constructor.reset_realizes request
  have ready : ClockJoin.ReadyRun (program a).machine (2*PCPPRequestSource.sourceBudget a request+2)
      ((program a).inputTapes (pcppInput request)) r.final.tapes:=
    ⟨r,hr,rfl,hh,runFrom_steps_le _ _ _ r hr⟩
  have focused:=ready.focus (slots a) (slots_injective a) (copied a (pcppInput request)) (by
    intro j
    by_cases hj : j.val=0
    · simp only [slots,hj,if_true,Program.inputTapes]
      rfl
    · simp only [slots,hj,if_false,copied,Fin.addCases_right,Program.inputTapes])
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ copy focused,?_,?_⟩
  · exact (install_slot (slots a) (slots_injective a) _ _ _).trans ht
  · rw [install_other (slots a) _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      dsimp only [slots] at hv
      split_ifs at hv
      all_goals simp only [Fin.val_natAdd] at hv
      all_goals omega)]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCall
