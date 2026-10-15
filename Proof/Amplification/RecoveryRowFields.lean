import Proof.Amplification.RecoveryClauseEvaluationRun
import Proof.Amplification.RecoveryCertificateRow

/-! The certificate row reader retains all four scalar fields on separate
ordinary tapes. It advances the shared source cursor and restores each field
head and the one reusable width driver after every successful read. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  source : List Bool
  pos : Nat
  width : Nat
  fields : Fin 4 → List Bool
  valid : Bool

def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 7 s :=
  ⟨q,![d.pos,0,0,0,0,1,0],
    ![d.source,d.fields 0,d.fields 1,d.fields 2,d.fields 3,CompareMachine.word d.width,[d.valid]]⟩
def Data.Valid (d : Data) : Prop := ∀ i,(d.fields i).length ≤ 2*d.width+1
def fieldSlot (i : Fin 4) : Fin 7 := ⟨i.val+1,by omega⟩
def fieldSlots (i : Fin 4) : Fin 3 → Fin 7 := ![0,fieldSlot i,5]
theorem fieldSlots_injective (i : Fin 4) : Function.Injective (fieldSlots i) := by
  fin_cases i <;> decide
noncomputable def fieldMachine (i : Fin 4) := RecoveryFocus.machine (fieldSlots i) FieldMachine.machine

def Data.after (d : Data) (i : Fin 4) (bits : List Bool) : Data :=
  {d with pos:=d.pos+2*bits.length,fields:=Function.update d.fields i (frame bits)}

theorem after_valid (d : Data) (i : Fin 4) (bits : List Bool)
    (hd : d.Valid) (hw : bits.length ≤ d.width) : (d.after i bits).Valid := by
  intro j
  by_cases hj : j=i
  · subst j
    simp only [Data.after,Function.update_self,frame_length]
    omega
  · simpa only [Data.after,Function.update_of_ne hj] using hd j

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem field_input (d : Data) (i : Fin 4) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length) :
    RecoveryFocus.config (fieldSlots i) (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes
      (FieldMachine.scan 0 (pre++frame bits) pre.length d.width 0 [] (d.fields i))=d.cfg 0 := by
  apply focus_configuration (fieldSlots i) (fieldSlots_injective i)
  · rfl
  · intro j; fin_cases j <;> fin_cases i <;> simp [FieldMachine.scan,Data.cfg,fieldSlots,fieldSlot,hp]
  · intro j; fin_cases j <;> fin_cases i <;>
      simp [FieldMachine.scan,Data.cfg,fieldSlots,fieldSlot,hs,StablePartition.Workspace.overlay]
  · intro j _; rfl
  · intro j _; rfl

theorem field_output (d : Data) (i : Fin 4) (bits : List Bool) (hw : bits.length=d.width) :
    RecoveryFocus.config (fieldSlots i) (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes
      (FieldMachine.finished d.source (frame bits) (d.pos+2*bits.length) d.width)=
      (d.after i bits).cfg 4 := by
  apply focus_configuration (fieldSlots i) (fieldSlots_injective i)
  · rfl
  · intro j; fin_cases j <;> fin_cases i <;> simp [FieldMachine.finished,Data.cfg,fieldSlots,fieldSlot,Data.after]
  · intro j; fin_cases j <;> fin_cases i <;>
      simp [FieldMachine.finished,Data.cfg,fieldSlots,fieldSlot,Data.after,hw]
  · intro j hj
    have h0 := hj 0
    fin_cases j <;> first | rfl | exact False.elim (h0 rfl)
  · intro j hj
    have hi := hj 1
    fin_cases i <;> fin_cases j <;>
      simp_all [fieldSlots,fieldSlot,Data.cfg,Data.after]

theorem field_read (d : Data) (i : Fin 4) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length) (hd : d.Valid) :
    ∃ r : ExecutionReceipt 7 6,
      runFrom (fieldMachine i) (4*d.width+2) (d.cfg 0)=some r ∧
      (r.final.control=4 ↔ d.width ≤ bits.length) ∧
      r.final.heads 6=0 ∧ r.final.tapes 6=[d.valid] ∧
      (d.width ≤ bits.length → r.final=(d.after i (bits.take d.width)).cfg 4) := by
  obtain ⟨base,hr,ha,hf⟩ := RecoveryCertificateField.bounded_read d.width pre bits (d.fields i) (hd i)
  obtain ⟨r,hrun,hfinal,_⟩ := RecoveryFocus.run_config (fieldSlots i) (fieldSlots_injective i)
    FieldMachine.machine (d.cfg (0 : Fin 6)).heads (d.cfg (0 : Fin 6)).tapes _ _ base hr
  rw [field_input d i pre bits hs hp] at hrun
  have hnot : ¬∃ j,fieldSlots i j=6 := by fin_cases i <;> decide
  have h6 : RecoveryFocus.pick (fieldSlots i) 6=none := by simp [RecoveryFocus.pick,hnot]
  refine ⟨r,hrun,?_,?_,?_,?_⟩
  · rw [hfinal]
    change base.final.control=4 ↔ d.width ≤ bits.length
    rw [ha]
    simp [readField]
  · simp [hfinal,RecoveryFocus.config,h6,Data.cfg]
  · simp [hfinal,RecoveryFocus.config,h6,Data.cfg]
  · intro hw
    rw [hfinal,hf hw]
    have hl : (bits.take d.width).length=d.width := by simp [List.length_take,hw]
    simpa only [hs,hp,hl] using field_output d i (bits.take d.width) hl

def flagMachine (bit : Bool) : Machine 7 6 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q _=>if q.val=0 then
    some ⟨4,fun i=>if i=6 then some bit else none,fun _=>.stay⟩ else none

theorem flag_raw {s : Nat} (c : Configuration 7 s) (old bit : Bool)
    (hh : c.heads 6=0) (ht : c.tapes 6=[old]) :
    ∃ r : ExecutionReceipt 7 6,
      runFrom (flagMachine bit) 1 (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=some r ∧
      r.final=⟨4,c.heads,Function.update c.tapes 6 [bit]⟩ ∧ r.steps=1 := by
  have hs : step (flagMachine bit) (RecoveryCalls.restarted (flagMachine bit) c.heads c.tapes)=
      some (⟨4,c.heads,Function.update c.tapes 6 [bit]⟩ : Configuration 7 6) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=6
      · subst i
        simp [applyAction,flagMachine,RecoveryCalls.restarted,hh,ht,writeTapeBit]
      · simp [applyAction,flagMachine,RecoveryCalls.restarted,hi]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem flag_run (d : Data) (bit : Bool) :
    ∃ r : ExecutionReceipt 7 6,runFrom (flagMachine bit) 1 (d.cfg 0)=some r ∧
      r.final=({d with valid:=bit} : Data).cfg 4 ∧ r.steps=1 := by
  obtain ⟨r,hr,hf,ht⟩ := flag_raw (d.cfg (0 : Fin 6)) d.valid bit rfl rfl
  refine ⟨r,hr,?_,ht⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [Data.cfg]

abbrev sizes : Fin 6 → Nat := fun _=>6
noncomputable def programs (j : Fin 6) : Machine 7 (sizes j) :=
  if hj : j.val<4 then fieldMachine ⟨j.val,hj⟩ else flagMachine (j.val==4)
def next (j : Fin 6) (q : Fin (sizes j)) (_ : Fin 7 → Bool) : Option (Fin 6) :=
  if hj : j.val<4 then
    if q.val=4 then some ⟨j.val+1,by omega⟩ else some 5
  else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next

def index (k : Nat) : Fin 4 := ⟨k%4,Nat.mod_lt _ (by decide)⟩
def afterReads (d : Data) (start : Nat) : Nat → List Bool → Data
  | 0,_=>d
  | count+1,bits=>afterReads (d.after (index start) (bits.take d.width)) (start+1) count (bits.drop d.width)

end NearCubicWires.RepairOrdinary.RecoveryRowFields
