import Proof.Amplification.RecoveryRowStructureField

/-! The streamed certificate row feeds its actual code word to the existing
unpair input. The clause payload, valuation table, width driver and global
witness cursor are retained; one reusable copy-work tape is explicit. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copied (d : Data) : Data := {d with state:=setField d.state 0 (frame d.code)}
def copySlots : Fin 4→Fin 52 := ![46,24,51,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine

def cfg {s : Nat} (d : Data) (capacity : Nat) (q : Fin s) : Configuration 52 s :=
  ⟨q,Fin.addCases (m:=51) (n:=1) (motive:=fun _=>Nat) (d.cfg q).heads (fun _=>0),
    Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool) (d.cfg q).tapes
      (fun _=>List.replicate capacity false)⟩

theorem clause_field (s : State) (e : RecoveryClauseEvaluation.Extra) (word : List Bool) :
    RecoveryClauseEvaluation.tapes (setField s 0 word) e=
      Function.update (RecoveryClauseEvaluation.tapes s e) 24 word := by
  change Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool) (setField s 0 word).tapes (e.tapes s)=_
  rw [setField_tapes,bank_update_left]
  rfl

theorem left_field (d : Data) (word : List Bool) :
    ({d with state:=setField d.state 0 word} : Data).left=Function.update d.left 24 word := by
  change Fin.addCases (m:=42) (n:=4) (motive:=fun _=>List Bool)
    (RecoveryClauseEvaluation.tapes (setField d.state 0 word) d.extra) (RecoveryRowLeaf.extra d.kind d.flags)=_
  rw [clause_field,bank_update_left]
  rfl

theorem row_field (d : Data) (word : List Bool) :
    (({d with state:=setField d.state 0 word} : Data).cfg (0 : Fin 1)).tapes=
      Function.update (d.cfg (0 : Fin 1)).tapes 24 word := by
  change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool)
    ({d with state:=setField d.state 0 word} : Data).left d.right=_
  rw [left_field,bank_update_left]
  rfl

theorem copied_tapes (d : Data) (capacity : Nat) :
    (cfg (copied d) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes 24 (frame d.code) := by
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    (({d with state:=setField d.state 0 (frame d.code)} : Data).cfg (0 : Fin 1)).tapes
    (fun _=>List.replicate capacity false)=_
  rw [row_field,bank_update_left]
  rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem copy_output (ambient : Fin 52→List Bool) (word : List Bool) (capacity reset : Nat)
    (hsource : ambient 46=frame word) (hcopy : ambient 51=List.replicate capacity false)
    (hreset : ambient 22=List.replicate reset false) :
    install copySlots ambient ![frame word,frame word,List.replicate capacity false,List.replicate reset false]=
      Function.update ambient 24 (frame word) := by
  apply install_eq copySlots copySlots_injective
  · intro j
    fin_cases j
    · exact hsource.symm
    · simp [copySlots]
    · exact hcopy.symm
    · exact hreset.symm
  · intro i hi
    have hne : i≠24 := by intro he; exact hi 1 he.symm
    simp only [Function.update_of_ne hne]

theorem copied_valid (d : Data) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) : (copied d).Valid word := by
  refine ⟨setField_valid d.state 0 (frame d.code) hd.1 ?_,?_,hd.2.2⟩
  · rw [frame_length,hw]
  · exact ⟨hd.2.1.source,hd.2.1.row,hd.2.1.counter,hd.2.1.count,
      hd.2.1.committed,hd.2.1.cap,hd.2.1.prefixBound,hd.2.1.reset⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
