import Proof.CaseAnalysis.RowsRawMonomialReturn
import Proof.MachineModel.Runs

/-! Literal ports of raw polynomial multiplication. A left monomial is
read with its cursor returned; a right monomial is consumed once. Only the
three actual raw streams and one paid rewind log participate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductFields
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (leftPos rightPos : ℕ) (out : List Bool) : Fin 4→ℕ:=![leftPos,rightPos,out.length,0]
def data (C : ℕ) (left right out : List Bool) : Fin 4→List Bool:=
  ![left,right,out,List.replicate C false]
def mark (bit advance : Bool) : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some bit,none],
    ![.stay,if advance then .right else .stay,.right,.stay]⟩ else none

theorem mark_run (bit advance : Bool) (C lp rp : ℕ) (left right out : List Bool) :
    Step (mark bit advance) 1 (heads lp rp out) (data C left right out)
      (heads lp (rp+if advance then 1 else 0) (out++[bit])) (data C left right (out++[bit])) := by
  have step':step (mark bit advance) ⟨0,heads lp rp out,data C left right out⟩=
      some ⟨1,heads lp (rp+if advance then 1 else 0) (out++[bit]),data C left right (out++[bit])⟩:=by
    simp only [step,mark,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> cases advance <;> simp [applyAction,heads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,data,heads,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) step').run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

def leftSlots : Fin 3→Fin 4:=![0,2,3]
def rightSlots : Fin 2→Fin 4:=![1,2]
noncomputable def leftMachine:=RecoveryFocus.machine leftSlots CloseoutRowsRawMonomialReturn.machine
noncomputable def rightMachine:=RecoveryFocus.machine rightSlots CloseoutRowsRawMonomialCopy.machine

theorem left_run (C : ℕ) (m : List ℕ) (pre tail right out : List Bool) (rp : ℕ)
    (hc : (m.flatMap ExtIncidence.block).length+1≤C) :
    Step leftMachine (CloseoutRowsRawMonomialReturn.budget m)
      (heads pre.length rp out) (data C (pre++m.flatMap ExtIncidence.block++false::tail) right out)
      (heads pre.length rp (out++m.flatMap ExtIncidence.block))
      (data C (pre++m.flatMap ExtIncidence.block++false::tail) right (out++m.flatMap ExtIncidence.block)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawMonomialReturn.returned_run C m pre tail out hc
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock leftSlots (by decide)
    CloseoutRowsRawMonomialReturn.machine _ (heads pre.length rp out)
    (data C (pre++m.flatMap ExtIncidence.block++false::tail) right out) _
    (by intro i;fin_cases i <;> rfl) (by
      intro i;fin_cases i <;>
        simp [leftSlots,data,CloseoutRowsRawMonomialReturn.input,ZeroPadding.config,
          Rewind.Workspace.capacities,Rewind.recording,Rewind.config,Fin.addCases,ZeroPadding.pad,
          CloseoutRowsRawMonomialCopy.cfg]) raw hr
  have one:=keep 1 (by intro i;fin_cases i <;> decide)
  have hh:r.final.heads=heads pre.length rp (out++m.flatMap ExtIncidence.block):=by
    funext i;fin_cases i
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact one.1
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    · exact (h 2).trans (congrArg (fun H=>H 2) rh)
  have ht:r.final.tapes=data C (pre++m.flatMap ExtIncidence.block++false::tail) right
      (out++m.flatMap ExtIncidence.block):=by
    funext i;fin_cases i
    · exact (t 0).trans (congrArg (fun A=>A 0) rt)
    · exact one.2
    · exact (t 1).trans (congrArg (fun A=>A 1) rt)
    · exact (t 2).trans (congrArg (fun A=>A 2) rt)
  exact Step.of_run rr hh ht

theorem right_run (C : ℕ) (m : List ℕ) (pre tail left out : List Bool) (lp : ℕ) :
    Step rightMachine ((m.flatMap ExtIncidence.block).length+1)
      (heads lp pre.length out) (data C left (pre++m.flatMap ExtIncidence.block++false::tail) out)
      (heads lp (pre.length+(m.flatMap ExtIncidence.block).length+1) (out++m.flatMap ExtIncidence.block))
      (data C left (pre++m.flatMap ExtIncidence.block++false::tail) (out++m.flatMap ExtIncidence.block)) := by
  obtain ⟨raw,hr,rf,_⟩:=CloseoutRowsRawMonomialCopy.copy_run m pre tail out
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock rightSlots (by decide)
    CloseoutRowsRawMonomialCopy.machine _ (heads lp pre.length out)
    (data C left (pre++m.flatMap ExtIncidence.block++false::tail) out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  have zero:=keep 0 (by intro i;fin_cases i <;> decide)
  have three:=keep 3 (by intro i;fin_cases i <;> decide)
  have hh:r.final.heads=heads lp (pre.length+(m.flatMap ExtIncidence.block).length+1)
      (out++m.flatMap ExtIncidence.block):=by
    funext i;fin_cases i
    · exact zero.1
    · exact (h 0).trans (congrArg (fun c=>c.heads 0) rf)
    · exact (h 1).trans (congrArg (fun c=>c.heads 1) rf)
    · exact three.1
  have ht:r.final.tapes=data C left (pre++m.flatMap ExtIncidence.block++false::tail)
      (out++m.flatMap ExtIncidence.block):=by
    funext i;fin_cases i
    · exact zero.2
    · exact (t 0).trans (congrArg (fun c=>c.tapes 0) rf)
    · exact (t 1).trans (congrArg (fun c=>c.tapes 1) rf)
    · exact three.2
  exact Step.of_run rr hh ht

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductFields
