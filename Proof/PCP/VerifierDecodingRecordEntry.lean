import Proof.PCP.VerifierDecodingScans
import Proof.PCP.VerifierDecodingRangeReject
import Proof.PCP.VerifierDecodingRejectingRepeat

/-! The literal single-record validator and its retained eight-tape entry.
This controller uses the existing bounded readers; failed calls halt at once.
Success alone must restore the reusable field, count and scratch boundaries. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {q : ℕ} (state : Fin q) (source backing bound : List Bool)
    (pos j t cap : ℕ) (rangeFlag result : Bool) : Configuration 8 q :=
  ⟨state,![pos,0,1,0,0,0,1,0],
    ![source,backing,CompareMachine.word j,frame bound,[rangeFlag],
      List.replicate cap false,CompareMachine.word t,[result]]⟩

def clearProgram : Machine 8 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=4 || i.val=7 then some false else none,fun _ => .stay⟩
    else none
def successProgram : Machine 8 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=7 then some true else none,fun _ => .stay⟩ else none
noncomputable def presenceProgram := TapeEmbedding.machine 7 (TagMachine.machine 1)
noncomputable def rangeProgram := TapeEmbedding.machine 2 RangeMachine.machine
def zeroSlots : Fin 2 → Fin 8 := ![0,2]
def tagSlots : Fin 2 → Fin 8 := ![0,6]
noncomputable def zeroProgram := RecoveryFocus.machine zeroSlots (TagScan.machine 1 (fun word => !(word 0)))
noncomputable def tagProgram (present : Bool) :=
  RecoveryFocus.machine tagSlots (TagScan.machine 4 (TagMachine.valid present))
def sizes : Fin 7 → ℕ :=
  ![2,Fintype.card TagMachine.Control,Fintype.card (RecoveryCalls.Control RangeMachine.sizes),
    Fintype.card (RepeatMachine.Control (Fintype.card TagMachine.Control)),
    Fintype.card (RepeatMachine.Control (Fintype.card TagMachine.Control)),
    Fintype.card (RepeatMachine.Control (Fintype.card TagMachine.Control)),2]
noncomputable def programs : (j : Fin 7) → Machine 8 (sizes j)
  | ⟨0,_⟩ => clearProgram
  | ⟨1,_⟩ => presenceProgram
  | ⟨2,_⟩ => rangeProgram
  | ⟨3,_⟩ => zeroProgram
  | ⟨4,_⟩ => tagProgram true
  | ⟨5,_⟩ => tagProgram false
  | ⟨6,_⟩ => successProgram
  | ⟨n+7,h⟩ => False.elim (by omega)

noncomputable def next : (j : Fin 7) → Fin (sizes j) → (Fin 8 → Bool) → Option (Fin 7)
  | ⟨0,_⟩,_,_ => some 1
  | ⟨1,_⟩,q,_ => match TagMachine.code.symm q with
    | none => none
    | some (phase,bits) => if phase.val=2 then if bits 0 then some 2 else some 3 else none
  | ⟨2,_⟩,_,bits => if bits 4 then some 4 else none
  | ⟨3,_⟩,q,_ => if q=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3 then some 5 else none
  | ⟨4,_⟩,q,_ => if q=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3 then some 6 else none
  | ⟨5,_⟩,q,_ => if q=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3 then some 6 else none
  | ⟨6,_⟩,_,_ => none
  | ⟨n+7,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem clear_run (source backing bound : List Bool) (pos j t cap : ℕ) (rangeFlag result : Bool) :
    ∃ r : ExecutionReceipt 8 2,
      runFrom clearProgram 1 (cfg 0 source backing bound pos j t cap rangeFlag result)=some r ∧
      r.final=cfg 1 source backing bound pos j t cap false false ∧ r.steps=1 := by
  have hs : step clearProgram (cfg 0 source backing bound pos j t cap rangeFlag result)=
      some (cfg 1 source backing bound pos j t cap false false) := by
    simp [step,clearProgram,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]
  exact (Timed.single (by rfl : clearProgram.halted (0 : Fin 2)=false) hs).run (by rfl)

theorem success_run (source backing bound : List Bool) (pos j t cap : ℕ) (rangeFlag : Bool) :
    ∃ r : ExecutionReceipt 8 2,
      runFrom successProgram 1 (cfg 0 source backing bound pos j t cap rangeFlag false)=some r ∧
      r.final=cfg 1 source backing bound pos j t cap rangeFlag true ∧ r.steps=1 := by
  have hs : step successProgram (cfg 0 source backing bound pos j t cap rangeFlag false)=
      some (cfg 1 source backing bound pos j t cap rangeFlag true) := by
    simp [step,successProgram,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]
  exact (Timed.single (by rfl : successProgram.halted (0 : Fin 2)=false) hs).run (by rfl)

noncomputable def presenceOutput (pre bits backing bound : List Bool) (j t cap : ℕ)
    (rangeFlag result : Bool) : Configuration 8 (Fintype.card TagMachine.Control) :=
  if bits=[] then
    cfg (TagMachine.code none) (pre++frame bits) backing bound (pre.length+1) j t cap rangeFlag result
  else
    cfg (TagMachine.code (some (2,TagMachine.received (TagMachine.extend bits) 1)))
      (pre++frame bits) backing bound (pre.length+2) j t cap rangeFlag result

theorem presence_run (pre bits backing bound : List Bool) (j t cap : ℕ) (rangeFlag result : Bool) :
    ∃ r : ExecutionReceipt 8 (Fintype.card TagMachine.Control),
      runFrom presenceProgram 3
        (cfg presenceProgram.start (pre++frame bits) backing bound pre.length j t cap rangeFlag result)=some r ∧
      r.final=presenceOutput pre bits backing bound j t cap rangeFlag result ∧ r.steps≤3 := by
  obtain ⟨base,hr,hs,hf⟩ := TagMachine.bounded_run pre bits 1
  let eh : Fin 7 → ℕ := ![0,1,0,0,0,1,0]
  let et : Fin 7 → List Bool :=
    ![backing,CompareMachine.word j,frame bound,[rangeFlag],List.replicate cap false,CompareMachine.word t,[result]]
  have he := TapeEmbedding.run_embed (TagMachine.machine 1) eh et _ _ base hr
  have hi : TapeEmbedding.config eh et (TagMachine.cfg 0 (fun _ => false) (pre++frame bits) pre.length)=
      cfg presenceProgram.start (pre++frame bits) backing bound pre.length j t cap rangeFlag result := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,et,Fin.addCases]
  have hrun : runFrom presenceProgram 3
      (cfg presenceProgram.start (pre++frame bits) backing bound pre.length j t cap rangeFlag result)=
      some (TapeEmbedding.receipt eh et base) := by
    rw [← hi]
    exact he
  refine ⟨_,hrun,?_,hs⟩
  by_cases hb : bits=[]
  · subst bits
    simp [TagMachine.Result] at hf
    simp only [TapeEmbedding.receipt,hf,presenceOutput,↓reduceIte]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.rejected,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.rejected,cfg,et,Fin.addCases]
  · have hlen : 1≤bits.length := by
      have := List.length_pos_iff.mpr hb
      omega
    simp [TagMachine.Result,hlen] at hf
    simp only [TapeEmbedding.receipt,hf,presenceOutput,hb,↓reduceIte]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,TagMachine.cfg,cfg,et,Fin.addCases]

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
