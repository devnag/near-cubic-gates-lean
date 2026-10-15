import Proof.MachineModel.OrdinaryMatrixPacketPrefix

/-! An actual full packet append: sign/factor from the retained offset,
then exactly the native raw count block. Both dimension drivers reset;
the global output cursor advances without a per-packet rewind. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketAppend
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots : Fin 2 → Fin 4 := ![0,3]
def lastSlots : Fin 3 → Fin 4 := ![1,2,3]
theorem first_injective : Function.Injective firstSlots := by decide
theorem last_injective : Function.Injective lastSlots := by decide
theorem first_pick (i : Fin 4) : RecoveryFocus.pick firstSlots i=(![some 0,none,none,some 1] : Fin 4 → Option (Fin 2)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot firstSlots first_injective 0
  · decide
  · decide
  · exact RecoveryFocus.pick_slot firstSlots first_injective 1
theorem last_pick (i : Fin 4) : RecoveryFocus.pick lastSlots i=(![none,some 0,some 1,some 2] : Fin 4 → Option (Fin 3)) i := by
  fin_cases i
  · decide
  · exact RecoveryFocus.pick_slot lastSlots last_injective 0
  · exact RecoveryFocus.pick_slot lastSlots last_injective 1
  · exact RecoveryFocus.pick_slot lastSlots last_injective 2
noncomputable def first (negative : Bool) := RecoveryFocus.machine firstSlots (MatrixPacketPrefix.machine negative)
noncomputable def last := RecoveryFocus.machine lastSlots (MatrixRawBlock.machine true)
noncomputable def machine (negative : Bool) := Composition.machine (first negative) last
def cfg (state : Fin 12) (bit count pos : ℕ) (source out : List Bool) : Configuration 4 12 :=
  ⟨state,![1,1,pos,out.length],![UnaryTemplate.tape (2*bit),UnaryTemplate.tape count,source,out]⟩
def input (bit : ℕ) (bits suffix out : List Bool) := cfg 0 bit bits.length 0 (bits++suffix) out

theorem append_run (negative : Bool) (bit : ℕ) (bits suffix out : List Bool) : ∃ actual,
    runFrom (machine negative) (4*bit+2*bits.length+10) (input bit bits suffix out)=some actual ∧
    actual.final=cfg 11 bit bits.length bits.length (bits++suffix)
      (out++MatrixPacketPrefix.prefixWord negative bit++bits) ∧
    actual.steps=4*bit+2*bits.length+10 := by
  obtain ⟨pre,hp,pf,ps⟩ := MatrixPacketPrefix.prefix_run negative bit out
  let start := input bit bits suffix out
  obtain ⟨left,hl,lf,ls⟩ := RecoveryFocus.run_config firstSlots first_injective (MatrixPacketPrefix.machine negative)
    start.heads start.tapes _ _ pre hp
  have hli : RecoveryFocus.config firstSlots start.heads start.tapes (MatrixPacketPrefix.cfg 0 (2*bit) 1 out)=
      ⟨(first negative).start,start.heads,start.tapes⟩ := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,first_pick,start,input,cfg,MatrixPacketPrefix.cfg]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,first_pick,start,input,cfg,MatrixPacketPrefix.cfg]
  rw [hli] at hl
  have lfinal : left.final.heads=(![1,1,0,(out++MatrixPacketPrefix.prefixWord negative bit).length] : Fin 4 → ℕ) ∧
      left.final.tapes=(![UnaryTemplate.tape (2*bit),UnaryTemplate.tape bits.length,bits++suffix,
        out++MatrixPacketPrefix.prefixWord negative bit] : Fin 4 → List Bool) := by
    rw [lf,pf]
    constructor
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,first_pick,start,input,cfg,MatrixPacketPrefix.cfg]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,first_pick,start,input,cfg,MatrixPacketPrefix.cfg]
  obtain ⟨post,hq,qf,qs,_⟩ := MatrixRawBlock.block_run true [] bits suffix
    (out++MatrixPacketPrefix.prefixWord negative bit)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hq qf
  let middle := MatrixRawBlock.config (s := 5) 0 (UnaryTemplate.tape bits.length) 1 (bits++suffix) 0
    (out++MatrixPacketPrefix.prefixWord negative bit)
  have hri : RecoveryFocus.config lastSlots left.final.heads left.final.tapes middle=
      Composition.restart left.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; rw [lfinal.1]; fin_cases j <;> rfl
    · intro j; rw [lfinal.2]; fin_cases j <;> rfl
  obtain ⟨right,hr,rf,rs⟩ := RecoveryFocus.run_config lastSlots last_injective (MatrixRawBlock.machine true)
    left.final.heads left.final.tapes _ middle post hq
  rw [hri] at hr
  have hj := Composition.run_join (first negative) last _ _ _ left right hl hr
  have htime : (4*bit+5)+1+(2*bits.length+4)=4*bit+2*bits.length+10 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt left right,hj,?_,?_⟩
  · change Composition.rightConfig 7 right.final=_
    rw [rf,qf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,last_pick,lfinal.1,
        Composition.rightConfig,MatrixRawBlock.config,MatrixRawBlock.selected,cfg]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,last_pick,lfinal.2,
        Composition.rightConfig,MatrixRawBlock.config,MatrixRawBlock.selected,cfg]
  · change left.steps+1+right.steps=_
    rw [ls,ps,rs,qs]
    omega

end NearCubicWires.RepairOrdinary.MatrixPacketAppend
