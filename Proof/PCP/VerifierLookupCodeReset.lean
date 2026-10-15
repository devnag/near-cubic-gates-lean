import Proof.PCP.VerifierLookupPosition

/-! A previous lookup or decoder may leave the code cursor anywhere through
its delimiter. The retained capped code length pays the complete rewind. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupCodeReset
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (code : List Bool) (pos c : ℕ) : Configuration 2 s :=
  ⟨q,![pos,1],![code,CapMachine.counter c c]⟩

def left : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,![.left,.stay]⟩ else none

theorem left_step (code : List Bool) (pos c : ℕ) :
    step left (cfg 0 code pos c)=some (cfg 1 code (pos-1) c) := by
  simp [step,left,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

def machine := Composition.machine left (LookupWalk.machine .left)

theorem reset_run (code : List Bool) (pos c : ℕ) (hp : pos≤2*c+1) :
    ∃ r,runFrom machine (3*c+4) (cfg machine.start code pos c)=some r ∧
      r.final=cfg 5 code 0 c ∧ r.steps=3*c+4 := by
  obtain ⟨first,hfirst,hff,hfs⟩ :=
    (Timed.single (by rfl : left.halted (0 : Fin 2)=false) (left_step code pos c)).run (by rfl)
  obtain ⟨last,hlast,hlf,hls⟩ := LookupWalk.capped_walk_run .left code (pos-1) c c
  have hmid : Composition.restart first.final (LookupWalk.machine .left).start=
      LookupWalk.cappedCfg 0 code (pos-1) c c 1 := by rw [hff]; rfl
  rw [←hmid] at hlast
  have hj := Composition.run_join left (LookupWalk.machine .left) 1 (3*c+2)
    (cfg 0 code pos c) first last hfirst hlast
  have htime : 1+1+(3*c+2)=3*c+4 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · simp only [Composition.joinedReceipt,hlf,LookupWalk.shift]
    have hzero : pos-1-2*c=0 := by omega
    rw [hzero]
    rfl
  · simp only [Composition.joinedReceipt,hfs,hls]
    omega

end NearCubicWires.RepairSource.VerifierDecoding.LookupCodeReset
