import Proof.CaseAnalysis.RowsTouchingPascalCell
import Proof.CaseAnalysis.RowsFamilyLoop

/-! One physical Pascal row is an existing counted loop of streaming
addition cells. Both original row tapes and every output prefix persist. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalRow
open LocalBitMultitape SignedSortKey CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def field (w n : ℕ):=frame (binary w n)
def leftWord (w : ℕ) (pair : ℕ×ℕ):=field w pair.1
def rightWord (w : ℕ) (pair : ℕ×ℕ):=field w pair.2
def sumWord (w : ℕ) (pair : ℕ×ℕ):=field w (pair.1+pair.2)
noncomputable def machine:=CloseoutRowsDegreeLoop.machine PascalCell.machine
def budget (w count : ℕ):=count*(2*w+6)+3
def entry (w : ℕ) (pairs : List (ℕ×ℕ)) (leftPre rightPre leftTail rightTail : List Bool)
    (j : ℕ) (out : List Bool):=
  (⟨PascalCell.machine.start,
    ![leftPre.length+((pairs.take j).flatMap (leftWord w)).length,
      rightPre.length+((pairs.take j).flatMap (rightWord w)).length,out.length],
    ![leftPre++pairs.flatMap (leftWord w)++leftTail,rightPre++pairs.flatMap (rightWord w)++rightTail,out]⟩ :
    Configuration 3 _)

theorem row_run (w : ℕ) (pairs : List (ℕ×ℕ)) (leftPre rightPre leftTail rightTail out : List Bool)
    (hfit:∀ pair∈pairs,pair.1+pair.2<2^w):
    ∃ r,runFrom machine (budget w pairs.length)
      (RepeatMachine.cfg 0 (entry w pairs leftPre rightPre leftTail rightTail 0 out) pairs.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (entry w pairs leftPre rightPre leftTail rightTail pairs.length (out++pairs.flatMap (sumWord w))) pairs.length 1 ∧
      r.steps≤budget w pairs.length:=by
  let source:=entry w pairs leftPre rightPre leftTail rightTail
  let emit:=fun j=>sumWord w (pairs.getD j (0,0))
  have supplier:∀ j<pairs.length,∀ acc,∃ r,runFrom PascalCell.machine (PascalCell.budget w) (source j acc)=some r ∧
      r.final.heads=(source (j+1) (acc++emit j)).heads ∧
      r.final.tapes=(source (j+1) (acc++emit j)).tapes ∧ r.steps≤PascalCell.budget w:=by
    intro j hj acc
    let pair:=pairs.getD j (0,0)
    have mem:pair∈pairs:=by
      dsimp only [pair]
      rw [List.getD_eq_getElem pairs (0,0) hj]
      exact List.getElem_mem hj
    let lp:=leftPre++(pairs.take j).flatMap (leftWord w)
    let rp:=rightPre++(pairs.take j).flatMap (rightWord w)
    let lt:=(pairs.drop (j+1)).flatMap (leftWord w)++leftTail
    let rt:=(pairs.drop (j+1)).flatMap (rightWord w)++rightTail
    have leftSplit:lp++field w pair.1++lt=leftPre++pairs.flatMap (leftWord w)++leftTail:=by
      rw [split_word pairs (0,0) (leftWord w) j hj]
      simp only [lp,lt,leftWord,pair,List.append_assoc]
    have rightSplit:rp++field w pair.2++rt=rightPre++pairs.flatMap (rightWord w)++rightTail:=by
      rw [split_word pairs (0,0) (rightWord w) j hj]
      simp only [rp,rt,rightWord,pair,List.append_assoc]
    obtain ⟨r,run,rs,rh,rtapes⟩:=PascalCell.cell_run w pair.1 pair.2 lp rp lt rt acc (hfit pair mem)
    change runFrom PascalCell.machine _ ⟨_,_,![lp++field w pair.1++lt,rp++field w pair.2++rt,acc]⟩=some r at run
    rw [leftSplit,rightSplit] at run
    have actual:runFrom PascalCell.machine (PascalCell.budget w) (source j acc)=some r:=by
      simpa only [source,entry,lp,rp,List.length_append] using run
    refine ⟨r,actual,?_,?_,rs⟩
    · rw [rh]
      simp only [source,entry,next_word pairs (0,0) (leftWord w) j hj,
        next_word pairs (0,0) (rightWord w) j hj,leftWord,rightWord,field,frame_length,binary_length,
        lp,rp,List.length_append,emit,sumWord,pair,Nat.add_assoc]
    · rw [rtapes]
      change ![lp++field w pair.1++lt,rp++field w pair.2++rt,acc++field w (pair.1+pair.2)]=_
      rw [leftSplit,rightSplit]
      rfl
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run PascalCell.machine source emit (PascalCell.budget w)
    pairs.length (by intro j hj acc;rfl) supplier out
  rw [flatMap_index pairs (0,0) (sumWord w)] at rf
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalRow
