import Proof.Hierarchy.CompetitorSameBucketGroupFields
import Proof.Hierarchy.CompetitorSameBucketKeys

/-! One complete original signed key is parsed in place. The tag and sign
are read before the fixed-width magnitude and BOTH concatenated IDs; the
actual source delimiter is passed once. The record cursor stays streaming. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorSameBucketGroupFields
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 6 → ℕ := ![pos,0,0,1,1,0]
def data (source native ids flag : List Bool) (p k cap : ℕ) : Fin 6 → List Bool :=
  ![source,ZeroPadding.pad cap native,ZeroPadding.pad cap ids,
    CompareMachine.word p,CompareMachine.word k,flag]
def cfg {s : ℕ} (q : Fin s) (source native ids flag : List Bool) (pos p k cap : ℕ) :
    Configuration 6 s := ⟨q,heads pos,data source native ids flag p k cap⟩

def signMachine : Machine 6 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bs => if h : q.val<4 then
    some ⟨⟨q.val+1,by omega⟩,fun i => if q.val=3 ∧ i=5 then some (bs 0) else none,
      fun i => if i=0 then .right else .stay⟩ else none

theorem move_step (q : Fin 5) (hq : q.val<3) (source native ids flag : List Bool) (pos p k cap : ℕ) :
    step signMachine (cfg q source native ids flag pos p k cap)=
      some (cfg ⟨q.val+1,by omega⟩ source native ids flag (pos+1) p k cap) := by
  simp [step,signMachine,show q.val<4 by omega,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,heads]
  · funext i; fin_cases i <;> simp [applyAction,show q.val≠3 by omega]

theorem sign_step (source native ids flag : List Bool) (pos p k cap : ℕ) (sign : Bool)
    (hs : readTapeBit source pos=sign) (hf : flag.length≤1) :
    step signMachine (cfg 3 source native ids flag pos p k cap)=
      some (cfg 4 source native ids [sign] (pos+1) p k cap) := by
  simp [step,signMachine,cfg,Configuration.scanned,heads,data,hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,MatrixScoreWeightSelect.overwrite_flag flag sign hf]

theorem sign_run (pre suffix native ids flag : List Bool) (p k cap : ℕ) (sign : Bool)
    (hf : flag.length≤1) :
    ∃ r,runFrom signMachine 4
      (cfg 0 (pre++[true,true,true,sign]++suffix) native ids flag pre.length p k cap)=some r ∧
      r.final=cfg 4 (pre++[true,true,true,sign]++suffix) native ids [sign] (pre.length+4) p k cap ∧
      r.steps=4 := by
  let source := pre++[true,true,true,sign]++suffix
  have hs : readTapeBit source (pre.length+3)=sign := by
    have h := Streaming.read_append (pre++[true,true,true]) suffix sign
    simpa [source,List.append_assoc] using h
  have h0 := Timed.single (by rfl) (move_step 0 (by decide) source native ids flag pre.length p k cap)
  have h1 := Timed.single (by rfl) (move_step 1 (by decide) source native ids flag (pre.length+1) p k cap)
  have h2 := Timed.single (by rfl) (move_step 2 (by decide) source native ids flag (pre.length+2) p k cap)
  have h3 := Timed.single (by rfl) (sign_step source native ids flag (pre.length+3) p k cap sign hs hf)
  have ht := h0.trans (h1.trans (h2.trans h3))
  simpa only [source,Nat.add_assoc] using ht.run (by rfl)

def delimiter : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=0 then .right else .stay⟩ else none

theorem delimiter_run (source native ids flag : List Bool) (pos p k cap : ℕ) :
    ∃ r,runFrom delimiter 1 (cfg 0 source native ids flag pos p k cap)=some r ∧
      r.final=cfg 1 source native ids flag (pos+1) p k cap ∧ r.steps=1 := by
  have h : step delimiter (cfg 0 source native ids flag pos p k cap)=
      some (cfg 1 source native ids flag (pos+1) p k cap) := by
    simp [step,delimiter,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,heads]
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

noncomputable def nativeProgram := program (0 : Fin 6) 1 3
noncomputable def idProgram := program (0 : Fin 6) 2 4
noncomputable def tail := Composition.machine idProgram delimiter
noncomputable def fields := Composition.machine nativeProgram tail
noncomputable def machine := Composition.machine signMachine fields
def budget (p k : ℕ) := 4*p+4*k+12

theorem native_run (pre bits suffix backing ids flag : List Bool) (k cap : ℕ)
    (hb : backing.length≤2*bits.length+1) :
    ∃ r,runFrom nativeProgram (4*bits.length+2)
      (cfg nativeProgram.start (pre++Streaming.marks bits++suffix) backing ids flag pre.length bits.length k cap)=some r ∧
      r.final.heads=heads (pre.length+2*bits.length) ∧
      r.final.tapes=data (pre++Streaming.marks bits++suffix) (frame bits) ids flag bits.length k cap ∧
      r.steps=4*bits.length+2 := by
  obtain ⟨r,hr,hh,ht,hs⟩ := field_run (0 : Fin 6) 1 3 (by decide) pre bits suffix backing cap
    (heads pre.length) (data (pre++Streaming.marks bits++suffix) backing ids flag bits.length k cap)
    hb rfl rfl rfl rfl rfl rfl
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hh]
    funext i; fin_cases i <;> rfl
  · rw [ht]
    funext i; fin_cases i <;> rfl

theorem id_run (pre bits suffix native backing flag : List Bool) (p cap : ℕ)
    (hb : backing.length≤2*bits.length+1) :
    ∃ r,runFrom idProgram (4*bits.length+2)
      (cfg idProgram.start (pre++Streaming.marks bits++suffix) native backing flag pre.length p bits.length cap)=some r ∧
      r.final.heads=heads (pre.length+2*bits.length) ∧
      r.final.tapes=data (pre++Streaming.marks bits++suffix) native (frame bits) flag p bits.length cap ∧
      r.steps=4*bits.length+2 := by
  obtain ⟨r,hr,hh,ht,hs⟩ := field_run (0 : Fin 6) 2 4 (by decide) pre bits suffix backing cap
    (heads pre.length) (data (pre++Streaming.marks bits++suffix) native backing flag p bits.length cap)
    hb rfl rfl rfl rfl rfl rfl
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hh]
    funext i; fin_cases i <;> rfl
  · rw [ht]
    funext i; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
