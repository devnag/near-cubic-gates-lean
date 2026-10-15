import Proof.PCP.VerifierDecodingHeaderLayoutTotal

/-! Guarded entry controller: count the code, compare with the physical input
limit, parse both unary dimensions, construct sentinels, then test t≥2/s>0.
The result tape starts blank and is written true only at the successful exit.
No table size or table expansion occurs in this controller. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {s : ℕ} (limit : ℕ) (base : Configuration 4 s) : Configuration 6 s :=
  TapeEmbedding.config ![1,0] ![CompareMachine.word limit,[]] base

def compareLayout : Fin 6 ≃ Fin 6 where
  toFun := ![3,4,0,1,2,5]
  invFun := ![2,3,4,0,1,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def compareProgram : Machine 6 7 :=
  TapeRenaming.machine compareLayout (TapeEmbedding.machine 4 CompareMachine.machine)
def compareInput (word : List Bool) (limit : ℕ) : Configuration 6 7 :=
  ⟨0,(extend limit (Preparation.headerInput word)).heads,
    (extend limit (Preparation.headerInput word)).tapes⟩

theorem compare_layout (word : List Bool) (limit : ℕ) :
    ∃ r, runFrom compareProgram (2*min word.length limit+3) (compareInput word limit)=some r ∧
      r.final=⟨if word.length≤limit then 5 else 6,
        (compareInput word limit).heads,(compareInput word limit).tapes⟩ ∧
      r.steps=2*min word.length limit+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := CompareMachine.compare_run word.length limit
  obtain ⟨p,hrp,hfp,hsp,_⟩ := ZeroPadding.run_config CompareMachine.machine
    ![word.length+2,0] _ _ r hr
  let eh : Fin 4 → ℕ := fun _ => 0
  let et : Fin 4 → List Bool := ![frame word,Preparation.zeros word.length,
    Preparation.zeros word.length,[]]
  have he := TapeEmbedding.run_embed CompareMachine.machine eh et _ _ p hrp
  have hren := TapeRenaming.run_rename compareLayout (TapeEmbedding.machine 4 CompareMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt compareLayout (TapeEmbedding.receipt eh et p)
  have hi : TapeRenaming.config compareLayout (TapeEmbedding.config eh et
      (ZeroPadding.config ![word.length+2,0] (CompareMachine.cfg 0 word.length limit 1)))=
      compareInput word limit := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,
        ZeroPadding.config,CompareMachine.cfg,CompareMachine.word,compareInput,extend,
        Preparation.headerInput,Preparation.cap,CapMachine.counter,compareLayout,et,Fin.addCases]
  rw [hi] at hren
  refine ⟨result,hren,?_,hsp.trans hs⟩
  apply configuration_ext
  · change p.final.control=_
    simp [hfp,hf,ZeroPadding.config,CompareMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hfp,hf,ZeroPadding.config,CompareMachine.cfg,
      compareInput,extend,Preparation.headerInput,compareLayout,eh,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hfp,hf,ZeroPadding.config,CompareMachine.cfg,
      compareInput,extend,Preparation.headerInput,Preparation.cap,CapMachine.counter,
      compareLayout,et,Fin.addCases,CompareMachine.word]

def successProgram : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,(fun i => if i=5 then some true else none),fun _ => .stay⟩ else none

def sizes : Fin 7 → ℕ := ![6,7,8,4,4,4,2]
def programs : (j : Fin 7) → Machine 6 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 2 Preparation.lengthProgram
  | ⟨1,_⟩ => compareProgram
  | ⟨2,_⟩ => TapeEmbedding.machine 2 Preparation.headerProgram
  | ⟨3,_⟩ => TapeEmbedding.machine 2 Preparation.tProgram
  | ⟨4,_⟩ => TapeEmbedding.machine 2 Preparation.sProgram
  | ⟨5,_⟩ => TapeEmbedding.machine 2 DimensionGuard.machine
  | ⟨6,_⟩ => successProgram
  | ⟨n+7,h⟩ => False.elim (by omega)
def next : (j : Fin 7) → Fin (sizes j) → (Fin 6 → Bool) → Option (Fin 7)
  | ⟨0,_⟩,_,_ => some 1
  | ⟨1,_⟩,q,_ => if q.val=5 then some 2 else none
  | ⟨2,_⟩,q,_ => if q.val=6 then some 3 else none
  | ⟨3,_⟩,_,_ => some 4
  | ⟨4,_⟩,_,_ => some 5
  | ⟨5,_⟩,q,_ => if q.val=2 then some 6 else none
  | ⟨6,_⟩,_,_ => none
  | ⟨n+7,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_prefix (node dest : Fin 7) (fuel : ℕ)
    (input : Configuration 6 (sizes node)) (r : ExecutionReceipt 6 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_prefix (node : Fin 7) (fuel : ℕ)
    (input : Configuration 6 (sizes node)) (r : ExecutionReceipt 6 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

end NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
