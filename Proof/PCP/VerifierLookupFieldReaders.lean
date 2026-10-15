import Proof.PCP.VerifierLookupNavigation

/-! Literal payload extraction at the selected code cursor, and the capped
version of the claimed-field copier used by the lookup entry. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupReadBit
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {n : ℕ} (q : Fin n) (source : List Bool) (pos : ℕ) (bit : Bool) : Configuration 2 n :=
  ⟨q,![pos,0],![source,[bit]]⟩
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q bits=>if q.val=0 then some ⟨1,fun _=>none,![.right,.stay]⟩
    else if q.val=1 then some ⟨2,![none,some (bits 0)],![.right,.stay]⟩ else none

theorem marker_step (source : List Bool) (pos : ℕ) (old : Bool) :
    step machine (cfg 0 source pos old)=some (cfg 1 source (pos+1) old) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem payload_step (pre tail : List Bool) (bit old : Bool) :
    step machine (cfg 1 (pre++bit::tail) pre.length old)=some (cfg 2 (pre++bit::tail) (pre.length+1) bit) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem read_run (pre tail : List Bool) (bit old : Bool) :
    ∃ r,runFrom machine 2 (cfg 0 (pre++true::bit::tail) pre.length old)=some r ∧
      r.final=cfg 2 (pre++true::bit::tail) (pre.length+2) bit ∧ r.steps=2 := by
  have h1 := payload_step (pre++[true]) tail bit old
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.add_assoc] at h1
  have h := (Timed.single (by rfl : machine.halted (0 : Fin 3)=false)
    (marker_step (pre++true::bit::tail) pre.length old)).trans
      (Timed.single (by rfl : machine.halted (1 : Fin 3)=false) h1)
  exact h.run (by rfl)

def clear : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>some false,fun _=>.stay⟩ else none

theorem clear_ready (bit : Bool) : RecoveryRootRound.ReadyRun clear 1 (fun _=>[bit]) (fun _=>[false]) := by
  let input : Configuration 1 2 := ⟨0,fun _=>0,fun _=>[bit]⟩
  let output : Configuration 1 2 := ⟨1,fun _=>0,fun _=>[false]⟩
  have hs : step clear input=some output := by rfl
  obtain ⟨r,hr,hrf,hrs⟩ := (Timed.single (by rfl : clear.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i; rw [hrf],hrs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupReadBit

namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRetainField
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cappedCfg {n : ℕ} (q : Fin n) (source : List Bool) (pos : ℕ) (target : List Bool) (width c : ℕ) : Configuration 3 n :=
  ⟨q,![pos,0,1],![source,target,CapMachine.counter c width]⟩

theorem pad_cfg {n : ℕ} (q : Fin n) (source : List Bool) (pos : ℕ) (target : List Bool) (width c : ℕ) :
    ZeroPadding.config (![0,0,c+2] : Fin 3→ℕ) (cfg q source pos target width)=
      cappedCfg q source pos target width c := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · rfl

theorem capped_field_run (pre bits tail backing : List Bool) (c : ℕ) (hb : backing.length≤2*bits.length+1) :
    let source := pre++Streaming.marks bits++tail
    ∃ r,runFrom machine (7*bits.length+5) (cappedCfg machine.start source pre.length backing bits.length c)=some r ∧
      r.final=cappedCfg 9 source pre.length (frame bits) bits.length c ∧ r.steps=7*bits.length+5 := by
  dsimp only
  obtain ⟨base,hbase,hbf,hbs⟩ := field_run pre bits tail backing hb
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config machine (![0,0,c+2] : Fin 3→ℕ) _ _ base hbase
  rw [pad_cfg] at hr
  rw [hbf,pad_cfg] at hrf
  exact ⟨r,hr,hrf,hrs.trans hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRetainField
