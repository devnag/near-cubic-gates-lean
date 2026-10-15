import Proof.Supplier.RowMaskConsume
import Proof.Supplier.RowMaskIndexClear

/-! Return the selected-mask bank's two short cursors to reusable zero
values by paid writes, while preserving cache, address, output, and count. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBankClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RowMaskConsume SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexSlots : Fin 2→Fin 9 := ![1,4]
theorem index_injective : Function.Injective indexSlots := by decide
noncomputable def indexMachine := RecoveryFocus.machine indexSlots RowMaskIndexClear.machine

theorem index_pick (i : Fin 9) : RecoveryFocus.pick indexSlots i=
    if i=1 then some 0 else if i=4 then some 1 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot indexSlots index_injective 0
    | exact RecoveryFocus.pick_slot indexSlots index_injective 1
    | decide

theorem pad_index (N : ℕ) : ZeroPadding.pad (N+2) (UnaryTemplate.tape N)=UnaryTemplate.tape N := by
  simp [ZeroPadding.pad,UnaryTemplate.tape_length]
theorem zero_index (N : ℕ) : ZeroPadding.pad (N+2) (UnaryTemplate.tape 0)=List.replicate (N+2) false := by
  simp [ZeroPadding.pad,UnaryTemplate.tape,List.replicate_succ]

theorem index_run (N w : ℕ) (x : Data) (hi : x.index=N) :
    ∃ r,runFrom indexMachine (2*N+2) (bank indexMachine.start N w x)=some r ∧
      r.final.heads=(bank indexMachine.start N w {x with index:=0}).heads ∧
      r.final.tapes=(bank indexMachine.start N w {x with index:=0}).tapes ∧ r.steps=2*N+2 := by
  obtain ⟨base,hbase,bf,bs⟩ := RowMaskIndexClear.clear_run N
  let ambient := bank indexMachine.start N w x
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config indexSlots index_injective RowMaskIndexClear.machine
    ambient.heads ambient.tapes _ _ base hbase
  have he : RecoveryFocus.config indexSlots ambient.heads ambient.tapes
      (RowMaskIndexClear.cfg 0 (UnaryTemplate.tape N) N 1)=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · simpa [ambient,bank,capacities,ZeroPadding.config,cfg,tapes,indexSlots,hi,RowMaskIndexClear.cfg] using pad_index N
      · simp [ambient,bank,capacities,ZeroPadding.config,cfg,tapes,indexSlots,RowMaskIndexClear.cfg]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,index_pick,ambient,bank,cfg,heads,
      RowMaskIndexClear.cfg,ZeroPadding.config]
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,index_pick,ambient,bank,cfg,tapes,capacities,
      RowMaskIndexClear.cfg,ZeroPadding.config,zero_index]

def counterSlots : Fin 2→Fin 9 := ![5,8]
theorem counter_injective : Function.Injective counterSlots := by decide
noncomputable def counterMachine := RecoveryFocus.machine counterSlots RowBinaryClear.machine

theorem counter_pick (i : Fin 9) : RecoveryFocus.pick counterSlots i=
    if i=5 then some 0 else if i=8 then some 1 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 0
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 1
    | decide

theorem counter_run (N w : ℕ) (x : Data) :
    ∃ r,runFrom counterMachine (4*w+4) (bank counterMachine.start N w x)=some r ∧
      r.final.heads=(bank counterMachine.start N w {x with counter:=0}).heads ∧
      r.final.tapes=(bank counterMachine.start N w {x with counter:=0}).tapes ∧ r.steps=4*w+4 := by
  let ambient := bank counterMachine.start N w x
  obtain ⟨r,hr,rh,rt,rs⟩ := (RowBinaryClear.binary_ready w x.counter).focus_at counterSlots counter_injective
    ambient.heads ambient.tapes (by intro i; fin_cases i <;> simp [ambient,bank,ZeroPadding.config,capacities,cfg,tapes,counterSlots])
    (by intro i; fin_cases i <;> rfl)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt]
  funext i; fin_cases i <;> simp [install,counter_pick,ambient,bank,cfg,tapes,capacities,ZeroPadding.config]

noncomputable def machine := Composition.machine indexMachine counterMachine

theorem clear_run (N w : ℕ) (x : Data) (hi : x.index=N) :
    ∃ r,runFrom machine (2*N+4*w+7) (bank machine.start N w x)=some r ∧
      r.final.heads=(bank machine.start N w {x with index:=0,counter:=0}).heads ∧
      r.final.tapes=(bank machine.start N w {x with index:=0,counter:=0}).tapes ∧ r.steps=2*N+4*w+7 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := index_run N w x hi
  obtain ⟨b,hb,bh,bt,bs⟩ := counter_run N w {x with index:=0}
  have he : bank counterMachine.start N w {x with index:=0}=Composition.restart a.final counterMachine.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atapes.symm
  rw [he] at hb
  have whole := Composition.run_join indexMachine counterMachine _ _ _ a b ha hb
  have ht : 2*N+2+1+(4*w+4)=2*N+4*w+7 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh,bt,?_⟩
  change a.steps+1+b.steps=_
  omega

end NearCubicWires.RepairOrdinary.RowMaskBankClear
