import Proof.PCP.ProjectionNormalizationQueryBytes

/-! Paid conversion of a short binary dimension into its actual unary
driver. Each successful predecessor emits one mark; the predecessor's
physical nonzero result controls termination. The output cursor is retained. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.UnaryCore
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (bits : List Bool) (flag : Bool) (capacity : ℕ) (out : List Bool) :
    Configuration 4 s := ⟨q,![0,0,0,out.length],![frame bits,[flag],List.replicate capacity false,out]⟩
def predSlots : Fin 3 → Fin 4 := ![0,1,2]
noncomputable def predProgram := RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
def emitProgram : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,none,none,some true],![.stay,.stay,.stay,.right]⟩ else none
def sizes : Fin 2 → ℕ := ![7,2]
noncomputable def programs : (j : Fin 2) → Machine 4 (sizes j)
  | ⟨0,_⟩ => predProgram
  | ⟨1,_⟩ => emitProgram
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scanned : Fin 4 → Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned 1 then some 1 else none else some 0
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def nodeCfg (node : Fin 2) (bits : List Bool) (flag : Bool) (capacity : ℕ) (out : List Bool) :=
  cfg (RecoveryCalls.code sizes node (programs node).start) bits flag capacity out
noncomputable def stopped (bits : List Bool) (capacity : ℕ) (out : List Bool) :=
  cfg (RecoveryCalls.controlCode sizes none) bits false capacity out

theorem pred_place (q : Fin 7) (bits oldBits out : List Bool) (oldFlag flag : Bool) (oldCapacity capacity : ℕ) :
    RecoveryFocus.config predSlots (cfg q oldBits oldFlag oldCapacity out).heads
      (cfg q oldBits oldFlag oldCapacity out).tapes
      (⟨q,fun _ => 0,![frame bits,[flag],List.replicate capacity false]⟩ : Configuration 3 7)=
      cfg q bits flag capacity out := by
  apply TransitionEvent.focused_eq predSlots (by decide) (cfg q oldBits oldFlag oldCapacity out)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i
    · exact False.elim (h 0 rfl)
    · exact False.elim (h 1 rfl)
    · exact False.elim (h 2 rfl)
    · rfl

theorem pred_run (bits out : List Bool) (flag : Bool) (capacity : ℕ) :
    ∃ r,runFrom predProgram (4*bits.length+4) (cfg predProgram.start bits flag capacity out)=some r ∧
      r.final=cfg r.final.control (RecoveryListPredecessor.result bits true) (decide (value bits≠0))
        (max capacity (2*bits.length+1)) out ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := RecoveryListPredecessor.predecessor_ready bits flag capacity
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config predSlots (by decide) RecoveryListPredecessor.machine
    (cfg predProgram.start bits flag capacity out).heads
    (cfg predProgram.start bits flag capacity out).tapes _ _ base hb
  change runFrom predProgram (4*bits.length+4) (RecoveryFocus.config predSlots _ _
    ⟨predProgram.start,fun _ => 0,![frame bits,[flag],List.replicate capacity false]⟩)=some r at hr
  rw [pred_place] at hr
  have hbase : base.final=⟨base.final.control,fun _ => 0,
      ![frame (RecoveryListPredecessor.result bits true),[decide (value bits≠0)],
        List.replicate (max capacity (2*bits.length+1)) false]⟩ := by
    apply configuration_ext
    · rfl
    · exact funext hbh
    · exact hbt
  refine ⟨r,hr,?_,hs.trans hbs⟩
  rw [hf,hbase]
  exact pred_place _ _ _ _ _ _ _ _

theorem emit_run (bits out : List Bool) (flag : Bool) (capacity : ℕ) :
    ∃ r,runFrom emitProgram 1 (cfg 0 bits flag capacity out)=some r ∧
      r.final=cfg 1 bits flag capacity (out++[true]) ∧ r.steps=1 := by
  have h : step emitProgram (cfg 0 bits flag capacity out)=some (cfg 1 bits flag capacity (out++[true])) := by
    simp [step,emitProgram,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
  exact (Timed.single (by rfl) h).run (by rfl)

theorem call_prefix (node dest : Fin 2) (fuel : ℕ) (input : Configuration 4 (sizes node))
    (r : ExecutionReceipt 4 (sizes node)) (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  exact (RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩).trans
    (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
      (RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn))

theorem stop_prefix (node : Fin 2) (fuel : ℕ) (input : Configuration 4 (sizes node))
    (r : ExecutionReceipt 4 (sizes node)) (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  exact (RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩).trans
    (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
      (RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn))

theorem loop (n : ℕ) (bits out : List Bool) (flag : Bool) (capacity : ℕ) (hn : value bits=n) :
    ∃ finalBits, finalBits.length=bits.length ∧
      Timed machine (n*(4*bits.length+7)+4*bits.length+5)
        (nodeCfg 0 bits flag capacity out)
        (stopped finalBits (max capacity (2*bits.length+1)) (out++List.replicate n true)) := by
  induction n generalizing bits out flag capacity with
  | zero =>
    obtain ⟨r,hr,hf,hs⟩ := pred_run bits out flag capacity
    have h := stop_prefix 0 _ _ r hr (by rw [hf]; simp [next,cfg,Configuration.scanned,hn,readTapeBit,List.getD])
    rw [hf,hs] at h
    refine ⟨_,RecoveryListPredecessor.result_length bits true,?_⟩
    simpa [nodeCfg,stopped,hn,cfg,controlConfig,RecoveryCalls.stopped,programs,Nat.add_assoc] using h
  | succ n ih =>
    have hnz : value bits≠0 := by omega
    have hp : value (RecoveryListPredecessor.result bits true)=n := by
      rw [RecoveryListPredecessor.predecessor_value bits hnz,hn]
      omega
    obtain ⟨r,hr,hf,hs⟩ := pred_run bits out flag capacity
    have h1 := call_prefix 0 1 _ _ r hr
      (by rw [hf]; simp [next,cfg,Configuration.scanned,hnz,readTapeBit,List.getD])
    rw [hf,hs] at h1
    obtain ⟨e,he,hef,hes⟩ := emit_run (RecoveryListPredecessor.result bits true) out true
      (max capacity (2*bits.length+1))
    have h2 := call_prefix 1 0 _ _ e he (by rfl)
    rw [hef,hes] at h2
    obtain ⟨finalBits,hlen,ht⟩ := ih (RecoveryListPredecessor.result bits true) (out++[true]) true
      (max capacity (2*bits.length+1)) hp
    simp only [RecoveryListPredecessor.result_length,max_self,max_assoc] at ht hlen
    have h12 : Timed machine ((4*bits.length+4+1)+2)
        (nodeCfg 0 bits flag capacity out)
        (nodeCfg 0 (RecoveryListPredecessor.result bits true) true (max capacity (2*bits.length+1)) (out++[true])) := by
      have h1' : Timed machine (4*bits.length+4+1) (nodeCfg 0 bits flag capacity out)
          (nodeCfg 1 (RecoveryListPredecessor.result bits true) true (max capacity (2*bits.length+1)) out) := by
        simpa [nodeCfg,cfg,controlConfig,RecoveryCalls.restarted,programs,hnz] using h1
      exact h1'.trans h2
    have hall := h12.trans ht
    have heq : (4*bits.length+4+1+2)+(n*(4*bits.length+7)+4*bits.length+5)=
        (n+1)*(4*bits.length+7)+4*bits.length+5 := by ring
    rw [heq] at hall
    refine ⟨finalBits,hlen,?_⟩
    simpa only [List.append_assoc,List.replicate_succ,List.singleton_append] using hall

end NearCubicWires.RepairSource.ProjectionNormalization.UnaryCore
