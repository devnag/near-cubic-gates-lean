import Proof.CaseAnalysis.CaseTwoSliceFrame
import Proof.MachineModel.OrdinaryMatrixUnaryTemplate

/-! One real binary address field produces its exact unary query index.
The width and offset are paid input scalars. The original slice/framer and
native binary counter execute the conversion, including the zero-width case. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sliceSlots (i : Fin 8) : Fin 13:=i.castAdd 5
def countSlots : Fin 7→Fin 13:=![3,8,9,10,11,6,12]
def first:=RecoveryFocus.machine sliceSlots SliceFrame.machine
def last:=RecoveryFocus.machine countSlots MatrixUnaryTemplate.machine
def machine:=Composition.machine first last
def input (pre tail : List Bool) (w n : ℕ) (i : Fin 13):=
  if i=0 then frame (pre++binary w n++tail) else if i=2 then List.replicate pre.length true
  else if i=3 then List.replicate w true else []
def budget (offset w n : ℕ):=SliceFrame.budget offset w+1+MatrixUnaryTemplate.budget w n
theorem slice_injective : Function.Injective sliceSlots:=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin 13=>x.val) he

theorem index_run (pre tail : List Bool) (w n : ℕ) (hn : n<2^w) : ∃ r,
    run machine (budget pre.length w n) (input pre tail w n)=some r ∧ r.steps≤budget pre.length w n ∧
      r.final.tapes 12=UnaryTemplate.tape n ∧ r.final.heads 12=1 ∧
      (∀ i,i≠12 → r.final.heads i=0) ∧
      r.final.tapes 0=frame (pre++binary w n++tail) ∧ r.final.tapes 1=binary w n ∧
      r.final.tapes 6=frame (binary w n):=by
  obtain ⟨sliced,hs,sframe,sraw,skeep,_,sw⟩:=SliceFrame.slice_run pre (binary w n) tail
  have width:(binary w n).length=w:=by simp
  rw [width] at hs sw
  have firstReady:=hs.focus sliceSlots slice_injective (input pre tail w n) (by
    intro i;fin_cases i <;>simp [input,sliceSlots,SliceFrame.input,width])
  obtain ⟨firstReceipt,hfirst,ft,fh,fs⟩:=firstReady
  obtain ⟨count,hc,_,cbits,cindex,cih,ch,cs⟩:=MatrixUnaryTemplate.template_run w n hn
  have ht (i : Fin 7) : firstReceipt.final.tapes (countSlots i)=MatrixUnaryTemplate.input w n i:=by
    rw [ft]
    fin_cases i
    · exact (install_slot sliceSlots slice_injective _ sliced 3).trans sw
    · exact install_other sliceSlots (input pre tail w n) sliced 8 (by decide)
    · exact install_other sliceSlots (input pre tail w n) sliced 9 (by decide)
    · exact install_other sliceSlots (input pre tail w n) sliced 10 (by decide)
    · exact install_other sliceSlots (input pre tail w n) sliced 11 (by decide)
    · exact (install_slot sliceSlots slice_injective _ sliced 6).trans sframe
    · exact install_other sliceSlots (input pre tail w n) sliced 12 (by decide)
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,keep⟩:=RecoveryFocus.dock countSlots (by decide)
    MatrixUnaryTemplate.machine _ firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input w n))
    (by intro i;exact fh _) ht count hc
  have whole:=Composition.run_join first last _ _ _ firstReceipt lastReceipt hfirst hl
  refine ⟨_,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · change firstReceipt.steps+1+lastReceipt.steps≤_
    rw [ls]
    unfold budget
    omega
  · exact (lt 6).trans cindex
  · exact (lh 6).trans cih
  · intro i hi
    by_cases hs : ∃ j,countSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (lh j).trans (ch j (by intro he;subst j;exact hi rfl))
    · exact (keep i (by intro j he;exact hs ⟨j,he⟩)).1.trans (fh i)
  · change lastReceipt.final.tapes 0=_
    rw [(keep 0 (by decide)).2,ft]
    exact (install_slot sliceSlots slice_injective _ sliced 0).trans skeep
  · change lastReceipt.final.tapes 1=_
    rw [(keep 1 (by decide)).2,ft]
    exact (install_slot sliceSlots slice_injective _ sliced 1).trans sraw
  · exact (lt 5).trans cbits

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField
