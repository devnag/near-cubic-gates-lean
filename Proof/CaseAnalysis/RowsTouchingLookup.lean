import Proof.CaseAnalysis.RowsTouchingFrameSeek
import Proof.PCP.PCPPQueryRows
import Proof.MachineModel.OrdinaryCellLoad
import Proof.MachineModel.Layout

/-! Binomial lookup uses paid row and field scans followed by the existing
bounded frame loader. The original table and all query drivers survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Lookup
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowSlots : Fin 4→Fin 7:=![1,0,5,2]
def fieldSlots : Fin 2→Fin 7:=![0,3]
def loadSlots : Fin 3→Fin 7:=![0,4,6]
noncomputable def rows:=RecoveryFocus.machine rowSlots PCPPQueryRows.skip
noncomputable def fields:=RecoveryFocus.machine fieldSlots FrameSeek.machine
noncomputable def load:=RecoveryFocus.machine loadSlots FrameLoad.machine
noncomputable def machine:=Composition.machine (Composition.machine rows fields) load

def heads (pos : ℕ) : Fin 7→ℕ:=![pos,1,1,1,0,0,0]
def data (B w m k : ℕ) (table backing : List Bool) : Fin 7→List Bool:=
  ![table,UnaryTemplate.tape B,CompareMachine.word m,CompareMachine.word k,backing,[],List.replicate (2*w+1) false]
def budget (B w m k : ℕ):=m*(2*B+7)+3+1+FrameSeek.budget w k+1+(4*w+3)

theorem lookup_run (B w : ℕ) (before : List (List Bool)) (front : List (List Bool))
    (bits tail backing : List Bool) (hB:∀ row∈before,row.length=B)
    (hw:∀ word∈front,word.length≤w) (hb:bits.length=w) (hback:backing.length≤2*w+1):
    Step machine (budget B w before.length front.length) (heads 0)
      (data B w before.length front.length (before.flatten++front.flatMap frame++frame bits++tail) backing)
      (heads (before.flatten.length+(front.flatMap frame).length+2*w+1))
      (data B w before.length front.length (before.flatten++front.flatMap frame++frame bits++tail) (frame bits)):=by
  let table:=before.flatten++front.flatMap frame++frame bits++tail
  let p:=before.flatten.length
  let z:=p+(front.flatMap frame).length
  obtain ⟨r,run,rf,_⟩:=PCPPQueryRows.skip_run B [] before (front.flatMap frame++frame bits++tail) [] hB
  have rowStep:Step rows (before.length*(2*B+7)+3) (heads 0)
      (data B w before.length front.length table backing) (heads p)
      (data B w before.length front.length table backing):=by
    have actual:Step PCPPQueryRows.skip (before.length*(2*B+7)+3) ![1,0,0,1]
        ![UnaryTemplate.tape B,table,[],CompareMachine.word before.length]
        ![1,p,0,1] ![UnaryTemplate.tape B,table,[],CompareMachine.word before.length]:=by
      have actual:=Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
      refine actual.congr_in ?_ ?_ |>.congr ?_ ?_
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> first | rfl | (change ([]++before.flatten++(front.flatMap frame++frame bits++tail))=table; simp only [table,List.nil_append,List.append_assoc])
      · funext i;fin_cases i <;> first | rfl | exact Nat.zero_add _
      · funext i;fin_cases i <;> first | rfl | (change ([]++before.flatten++(front.flatMap frame++frame bits++tail))=table; simp only [table,List.nil_append,List.append_assoc])
    have focused:=actual.focus rowSlots (by decide) (heads 0) (data B w before.length front.length table backing)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot rowSlots (by decide) _ _ 0 | exact install_slot rowSlots (by decide) _ _ 1 | exact install_slot rowSlots (by decide) _ _ 2 | exact install_slot rowSlots (by decide) _ _ 3
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot rowSlots (by decide) _ _ 0 | exact dockH_slot rowSlots (by decide) _ _ 1 | exact dockH_slot rowSlots (by decide) _ _ 2 | exact dockH_slot rowSlots (by decide) _ _ 3
    · funext i;fin_cases i <;> first | rfl | exact install_slot rowSlots (by decide) _ _ 0 | exact install_slot rowSlots (by decide) _ _ 1 | exact install_slot rowSlots (by decide) _ _ 2 | exact install_slot rowSlots (by decide) _ _ 3
  obtain ⟨s,srun,sf,_⟩:=FrameSeek.seek_run front before.flatten (frame bits++tail) w hw
  have fieldStep:Step fields (FrameSeek.budget w front.length) (heads p)
      (data B w before.length front.length table backing) (heads z)
      (data B w before.length front.length table backing):=by
    have actual:Step FrameSeek.machine (FrameSeek.budget w front.length) ![p,1] ![table,CompareMachine.word front.length]
        ![z,1] ![table,CompareMachine.word front.length]:=by
      have actual:=Step.of_run srun (congrArg Configuration.heads sf) (congrArg Configuration.tapes sf)
      refine actual.congr_in ?_ ?_ |>.congr ?_ ?_
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> first | rfl | (change (before.flatten++front.flatMap frame++(frame bits++tail))=table; simp only [table,List.append_assoc])
      · simp only [FrameSeek.entry,List.take_length]
        funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> first | rfl | (change (before.flatten++front.flatMap frame++(frame bits++tail))=table; simp only [table,List.append_assoc])
    have focused:=actual.focus fieldSlots (by decide) (heads p) (data B w before.length front.length table backing)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot fieldSlots (by decide) _ _ 0 | exact install_slot fieldSlots (by decide) _ _ 1
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot fieldSlots (by decide) _ _ 0 | exact dockH_slot fieldSlots (by decide) _ _ 1
    · funext i;fin_cases i <;> first | rfl | exact install_slot fieldSlots (by decide) _ _ 0 | exact install_slot fieldSlots (by decide) _ _ 1
  obtain ⟨l,lrun,lf,_,_⟩:=CellLoad.loader_run (before.flatten++front.flatMap frame) bits tail backing (by rw [hb];exact hback)
  rw [hb,List.length_append] at lrun lf
  have loadStep:Step load (4*w+3) (heads z) (data B w before.length front.length table backing)
      (heads (z+2*w+1)) (data B w before.length front.length table (frame bits)):=by
    have actual:Step FrameLoad.machine (4*w+3) ![z,0,0] ![table,backing,List.replicate (2*w+1) false]
        ![z+2*w+1,0,0] ![table,frame bits,List.replicate (2*w+1) false]:=by
      refine Step.of_run (r:=l) ?_ ?_ ?_
      · exact lrun
      · rw [lf];rfl
      · rw [lf];rfl
    have focused:=actual.focus loadSlots (by decide) (heads z) (data B w before.length front.length table backing)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot loadSlots (by decide) _ _ 0 | exact install_slot loadSlots (by decide) _ _ 1 | exact install_slot loadSlots (by decide) _ _ 2
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot loadSlots (by decide) _ _ 0 | exact dockH_slot loadSlots (by decide) _ _ 1 | exact dockH_slot loadSlots (by decide) _ _ 2
    · funext i;fin_cases i <;> first | rfl | exact install_slot loadSlots (by decide) _ _ 0 | exact install_slot loadSlots (by decide) _ _ 1 | exact install_slot loadSlots (by decide) _ _ 2
  exact (rowStep.seq fieldStep).seq loadStep

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Lookup
