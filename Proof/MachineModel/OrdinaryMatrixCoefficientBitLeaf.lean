import Proof.MachineModel.OrdinaryMatrixCoefficientBounds

/-! The bit-plane consumer physically reads a coefficient sign and its
selected magnitude bit. The sign test and selected output are actual tape
writes; the coefficient source and mask output retain streaming cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitLeaf
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos offset : ℕ) (flag : Bool) (out : List Bool) : Configuration 4 s :=
  ⟨q,![pos,1,0,out.length],![source,UnaryTemplate.tape offset,[flag],out]⟩
def nextFlag (select negative bit flag : Bool) := if select then flag else bit==negative
def nextOut (select bit flag : Bool) (out : List Bool) := if select then out++[flag && bit] else out

def machine (select negative : Bool) : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then
    some ⟨1,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=1 then some ⟨2,
      ![none,none,if select then none else some (scan 0==negative),if select then some (scan 2 && scan 0) else none],
      ![.right,.stay,.stay,if select then .right else .stay]⟩ else none

theorem start_step (select negative flag : Bool) (source out : List Bool) (pos offset : ℕ) :
    step (machine select negative) (cfg 0 source pos offset flag out)=
      some (cfg 1 source (pos+1) offset flag out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem bit_step (select negative flag bit : Bool) (source out : List Bool) (pos offset : ℕ)
    (hb : readTapeBit source pos=bit) :
    step (machine select negative) (cfg 1 source pos offset flag out)=
      some (cfg 2 source (pos+1) offset (nextFlag select negative bit flag) (nextOut select bit flag out)) := by
  have hflag : readTapeBit [flag] 0=flag := rfl
  simp [step,machine,cfg,Configuration.scanned,hb,hflag]
  apply configuration_ext
  · rfl
  · funext i; cases select <;> fin_cases i <;> simp [applyAction,HeadMove.apply,nextOut]
  · funext i; cases select <;> fin_cases i <;> simp [applyAction,nextFlag,nextOut,Streaming.write_append,
      MatrixScoreWeightSelect.overwrite_flag [flag] _ (by simp)]

theorem read_run (select negative flag bit : Bool) (pre suffix out : List Bool) (offset : ℕ) : ∃ actual,
    runFrom (machine select negative) 2 (cfg 0 (pre++[true,bit]++suffix) pre.length offset flag out)=some actual ∧
    actual.final=cfg 2 (pre++[true,bit]++suffix) (pre.length+2) offset
      (nextFlag select negative bit flag) (nextOut select bit flag out) ∧ actual.steps=2 := by
  let source := pre++[true,bit]++suffix
  have hbit : readTapeBit source (pre.length+1)=bit := by
    simpa [source,List.append_assoc] using Streaming.read_append (pre++[true]) suffix bit
  have ht := (Timed.single (by rfl) (start_step select negative flag source out pre.length offset)).trans
    (Timed.single (by rfl) (bit_step select negative flag bit source out (pre.length+1) offset hbit))
  simpa only [source,Nat.add_assoc] using ht.run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitLeaf
