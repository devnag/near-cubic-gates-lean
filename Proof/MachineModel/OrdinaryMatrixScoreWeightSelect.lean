import Proof.MachineModel.OrdinaryMatrixScoreHeaders

/-! Read a real sign-magnitude field sign and the current framed assignment
bit. Both global cursors advance; the two arithmetic branch flags are actual
writes, including the false case and initially blank flag tapes. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightSelect
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (assignment : List Bool) (apos : ℕ)
    (positive negative magnitude : List Bool) (cap : ℕ) : Configuration 6 s :=
  ⟨q,![pos,apos,0,0,0,0],![source,assignment,positive,negative,magnitude,List.replicate cap false]⟩
def machine : Machine 6 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then some ⟨1,fun _ => none,![.right,.right,.stay,.stay,.stay,.stay]⟩
    else if q.val=1 then some ⟨2,![none,none,some (scan 1 && !(scan 0)),some (scan 1 && scan 0),none,none],
      ![.right,.right,.stay,.stay,.stay,.stay]⟩ else none

theorem overwrite_flag (old : List Bool) (bit : Bool) (hb : old.length≤1) :
    writeTapeBit old 0 bit=[bit] := by
  cases old with
  | nil => rfl
  | cons a rest =>
    have hr : rest=[] := by
      cases rest with
      | nil => rfl
      | cons b tail => simp at hb
    subst rest
    rfl

theorem start_step (source assignment positive negative magnitude : List Bool) (pos apos cap : ℕ) :
    step machine (cfg 0 source pos assignment apos positive negative magnitude cap)=
      some (cfg 1 source (pos+1) assignment (apos+1) positive negative magnitude cap) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem flags_step (source assignment positive negative magnitude : List Bool) (pos apos cap : ℕ)
    (sign bit : Bool) (hs : readTapeBit source pos=sign) (ha : readTapeBit assignment apos=bit)
    (hp : positive.length≤1) (hn : negative.length≤1) :
    step machine (cfg 1 source pos assignment apos positive negative magnitude cap)=
      some (cfg 2 source (pos+1) assignment (apos+1) [bit && !sign] [bit && sign] magnitude cap) := by
  simp [step,machine,cfg,Configuration.scanned,hs,ha]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,overwrite_flag positive _ hp,overwrite_flag negative _ hn]

theorem select_run (pre suffix apre asuffix positive negative magnitude bits : List Bool)
    (cap : ℕ) (sign bit : Bool) (hp : positive.length≤1) (hn : negative.length≤1) :
    ∃ actual : ExecutionReceipt 6 3,
      runFrom machine 2 (cfg 0 (pre++frame (sign::bits)++suffix) pre.length
        (apre++[true,bit]++asuffix) apre.length positive negative magnitude cap)=some actual ∧
      actual.final=cfg 2 (pre++frame (sign::bits)++suffix) (pre.length+2)
        (apre++[true,bit]++asuffix) (apre.length+2) [bit && !sign] [bit && sign] magnitude cap ∧
      actual.steps=2 := by
  let source := pre++frame (sign::bits)++suffix
  let assignment := apre++[true,bit]++asuffix
  have hs : readTapeBit source (pre.length+1)=sign := by
    have h := Streaming.read_append (pre++[true]) (frame bits++suffix) sign
    simpa [source,frame,List.append_assoc] using h
  have ha : readTapeBit assignment (apre.length+1)=bit := by
    have h := Streaming.read_append (apre++[true]) asuffix bit
    simpa [assignment,List.append_assoc] using h
  have ht := (RecoveryExecution.Timed.single (by rfl)
    (start_step source assignment positive negative magnitude pre.length apre.length cap)).trans
    (RecoveryExecution.Timed.single (by rfl)
      (flags_step source assignment positive negative magnitude (pre.length+1) (apre.length+1) cap sign bit hs ha hp hn))
  simpa [source,assignment,Nat.add_assoc,List.append_assoc] using ht.run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixScoreWeightSelect
