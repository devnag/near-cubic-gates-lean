import Proof.PCP.PCPPNativeClauseBlock
import Proof.MachineModel.OrdinaryRewindWorkspace

/-! Split the actual compact literal code 2*j+negative into its raw index
and sign. This is parity on the original code, never Nat.unpair decoding. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeLiteralSplit
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bs=>
    if q.val=0 then some ⟨1,fun _=>none,![.right,.stay,.stay]⟩
    else if q.val=1 then some (if bs 0 then ⟨2,fun _=>none,![.right,.stay,.stay]⟩
      else ⟨3,![none,none,some false],fun _=>.stay⟩)
    else if q.val=2 then some (if bs 0 then ⟨1,![none,some true,none],![.right,.right,.stay]⟩
      else ⟨3,![none,none,some true],fun _=>.stay⟩)
    else none
def cfg (state : Fin 4) (count pos done : ℕ) (flag : List Bool) : Configuration 3 4 :=
  ⟨state,![pos,done,0],![UnaryTemplate.tape count,List.replicate done true,flag]⟩

theorem first_step (count : ℕ) : step raw (cfg 0 count 0 0 [])=some (cfg 1 count 1 0 []) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
theorem even_step (count done : ℕ) (h : 2*done<count) :
    step raw (cfg 1 count (2*done+1) done [])=some (cfg 2 count (2*done+2) done []) := by
  have hm:=UnaryTemplate.tape_mark count (2*done) h
  simp [step,raw,cfg,Configuration.scanned,hm]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem odd_step (count done : ℕ) (h : 2*done+1<count) :
    step raw (cfg 2 count (2*done+2) done [])=some (cfg 1 count (2*(done+1)+1) (done+1) []) := by
  have hm:=UnaryTemplate.tape_mark count (2*done+1) h
  have hw : writeTapeBit (List.replicate done true) done true=List.replicate (done+1) true := by
    have hx:=Streaming.write_append (List.replicate done true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using hx
  simp [step,raw,cfg,Configuration.scanned,hm]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction,hw]

theorem pairs (count done remaining : ℕ) (h : 2*(done+remaining) ≤ count) :
    Timed raw (2*remaining) (cfg 1 count (2*done+1) done [])
      (cfg 1 count (2*(done+remaining)+1) (done+remaining) []) := by
  induction remaining generalizing done with
  | zero => simpa only [Nat.mul_zero,Nat.add_zero] using Timed.refl raw (cfg 1 count (2*done+1) done [])
  | succ remaining ih =>
    have he:=Timed.single (by rfl) (even_step count done (by omega))
    have ho:=Timed.single (by rfl) (odd_step count done (by omega))
    have hs:=ih (done+1) (by omega)
    convert (he.trans ho).trans hs using 1 <;> congr 1 <;> omega

theorem stop_even (done : ℕ) :
    step raw (cfg 1 (2*done) (2*done+1) done [])=some (cfg 3 (2*done) (2*done+1) done [false]) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
theorem stop_odd (done : ℕ) :
    step raw (cfg 2 (2*done+1) (2*done+2) done [])=some (cfg 3 (2*done+1) (2*done+2) done [true]) := by
  have hm:=UnaryTemplate.tape_end (2*done+1)
  simp [step,raw,cfg,Configuration.scanned,hm]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl

theorem cfg_initial (count : ℕ) : cfg 0 count 0 0 []=initialConfiguration raw
    ![UnaryTemplate.tape count,[],[]] := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem raw_run (index : ℕ) (negative : Bool) : ∃ r,
    run raw (2*index+negative.toNat+2) ![UnaryTemplate.tape (2*index+negative.toNat),[],[]]=some r ∧
      r.final=cfg 3 (2*index+negative.toNat) (2*index+negative.toNat+1) index [negative] ∧
      r.steps=2*index+negative.toNat+2 := by
  cases negative
  · have hp:=pairs (2*index) 0 index (by omega)
    simp only [Nat.zero_add] at hp
    have hs:=Timed.single (by rfl) (first_step (2*index))
    have he:=Timed.single (by rfl) (stop_even index)
    have ht:=(hs.trans hp).trans he
    have hf:=ht.run (by rfl)
    rw [cfg_initial,show 1+2*index+1=2*index+2 by omega] at hf
    exact hf
  · have hp:=pairs (2*index+1) 0 index (by omega)
    simp only [Nat.zero_add] at hp
    have hs:=Timed.single (by rfl) (first_step (2*index+1))
    have hm:=Timed.single (by rfl) (even_step (2*index+1) index (by omega))
    have he:=Timed.single (by rfl) (stop_odd index)
    have ht:=((hs.trans hp).trans hm).trans he
    have hf:=ht.run (by rfl)
    rw [cfg_initial,show 1+2*index+1+1=2*index+1+2 by omega] at hf
    exact hf

end NearCubicWires.RepairOrdinary.PCPPNativeLiteralSplit
