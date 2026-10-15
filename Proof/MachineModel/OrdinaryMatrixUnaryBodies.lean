import Proof.MachineModel.OrdinaryMatrixUnaryFinish
import Proof.Amplification.RecoveryCursorCalls

/-! Literal arithmetic and tape-writing calls for expansion of a binary
dimension into a physical unary template. The growing tape cursor is
preserved across every local arithmetic reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (q : Fin s) (w n a k : ℕ) (flag : Bool) : Configuration 5 s :=
  ⟨q,![0,0,0,0,k+1],![frame (binary w n),frame (binary w a),[flag],
    List.replicate (2*w+1) false,false::List.replicate k true]⟩
def finished {s : ℕ} (q : Fin s) (w n : ℕ) : Configuration 5 s :=
  ⟨q,![0,0,0,0,1],![frame (binary w n),frame (binary w n),[true],
    List.replicate (2*w+1) false,UnaryTemplate.tape n]⟩

def compare : Machine 5 7 := TapeEmbedding.machine 1 CompetitorSignedDecision.compareMachine
def incrementSlots : Fin 2 → Fin 5 := ![1,3]
noncomputable def increment : Machine 5 5 := RecoveryFocus.machine incrementSlots FramedIncrement.machine
def outSlot : Fin 1 → Fin 5 := fun _ => 4
noncomputable def emit : Machine 5 2 := RecoveryFocus.machine outSlot (MatrixUnaryFinish.append true)
noncomputable def finish : Machine 5 5 := RecoveryFocus.machine outSlot MatrixUnaryFinish.machine

theorem increment_pick : ∀ i : Fin 5, RecoveryFocus.pick incrementSlots i =
    (![none,some 0,none,some 1,none] : Fin 5 → Option (Fin 2)) i := by
  intro i; fin_cases i
  · decide
  · exact RecoveryFocus.pick_slot incrementSlots (by decide) 0
  · decide
  · exact RecoveryFocus.pick_slot incrementSlots (by decide) 1
  · decide

theorem out_pick : ∀ i : Fin 5, RecoveryFocus.pick outSlot i =
    (![none,none,none,none,some 0] : Fin 5 → Option (Fin 1)) i := by
  intro i; fin_cases i
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot outSlot (by decide) 0

theorem compare_run (w n a k : ℕ) (hn : n<2^w) (ha : a<2^w) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom compare (4*w+4) (config compare.start w n a k false)=some r ∧
      r.final=config r.final.control w n a k (decide (n≤a)) ∧ r.steps=4*w+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := MatrixUnaryCompare.compare_ready w n a hn ha
  have hrun := TapeEmbedding.run_embed CompetitorSignedDecision.compareMachine
    (fun _ : Fin 1 => k+1) (fun _ : Fin 1 => false::List.replicate k true) _ _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 1 => k+1) (fun _ : Fin 1 => false::List.replicate k true)
      (initialConfiguration CompetitorSignedDecision.compareMachine
        ![frame (binary w n),frame (binary w a),[false],List.replicate (2*w+1) false]) =
      config compare.start w n a k false := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1 => k+1)
    (fun _ : Fin 1 => false::List.replicate k true) base,hrun,?_,hs⟩
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,config,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,config,Fin.addCases,ht]

theorem increment_run (w n a k : ℕ) (flag : Bool) (ha : a+1<2^w) :
    ∃ r : ExecutionReceipt 5 5,
      runFrom increment (4*w+2) (config increment.start w n a k flag)=some r ∧
      r.final=config r.final.control w n (a+1) k flag ∧ r.steps≤4*w+2 := by
  obtain ⟨base,hr,h0,h1,hh,hs,_⟩ := FramedIncrement.increment_run w a (2*w+1) ha (by omega)
  let ambient := config increment.start w n a k flag
  let source := initialConfiguration FramedIncrement.machine
    (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame (binary w a)) (fun _ : Fin 1 => List.replicate (2*w+1) false))
  have hi : RecoveryFocus.config incrementSlots ambient.heads ambient.tapes source=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨r,hp,hf,hsteps⟩ := RecoveryFocus.run_config incrementSlots (by decide)
    FramedIncrement.machine ambient.heads ambient.tapes (4*w+2) source base hr
  rw [hi] at hp
  have hpick : ∀ i : Fin 5, RecoveryFocus.pick incrementSlots i =
      (![none,some 0,none,some 1,none] : Fin 5 → Option (Fin 2)) i := increment_pick
  refine ⟨r,hp,?_,hsteps.trans_le hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,hh]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,h0,h1]

theorem emit_run (w n a k : ℕ) (flag : Bool) :
    ∃ r : ExecutionReceipt 5 2,
      runFrom emit 1 (config emit.start w n a k flag)=some r ∧
      r.final=config 1 w n a (k+1) flag ∧ r.steps=1 := by
  obtain ⟨base,hr,hf,hs⟩ := MatrixUnaryFinish.append_run true (false::List.replicate k true)
  let ambient := config emit.start w n a k flag
  let source := MatrixUnaryFinish.config (s:=2) 0 (false::List.replicate k true) (k+1)
  have hi : RecoveryFocus.config outSlot ambient.heads ambient.tapes source=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i; rfl
  obtain ⟨r,hp,hfinal,hsteps⟩ := RecoveryFocus.run_config outSlot (by decide)
    (MatrixUnaryFinish.append true) ambient.heads ambient.tapes 1 source base (by simpa [source] using hr)
  rw [hi] at hp
  have hpick : ∀ i : Fin 5, RecoveryFocus.pick outSlot i =
      (![none,none,none,none,some 0] : Fin 5 → Option (Fin 1)) i := out_pick
  refine ⟨r,hp,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,MatrixUnaryFinish.config]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,MatrixUnaryFinish.config,List.replicate_add]

theorem finish_run (w n : ℕ) :
    ∃ r : ExecutionReceipt 5 5,
      runFrom finish (n+4) (config finish.start w n n n true)=some r ∧
      r.final=finished 4 w n ∧ r.steps=n+4 := by
  obtain ⟨base,hr,hf,hs⟩ := MatrixUnaryFinish.finish_run n
  let ambient := config finish.start w n n n true
  let source := MatrixUnaryFinish.config (s:=5) 0 (false::List.replicate n true) (n+1)
  have hi : RecoveryFocus.config outSlot ambient.heads ambient.tapes source=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i; rfl
  obtain ⟨r,hp,hfinal,hsteps⟩ := RecoveryFocus.run_config outSlot (by decide)
    MatrixUnaryFinish.machine ambient.heads ambient.tapes (n+4) source base hr
  rw [hi] at hp
  have hpick : ∀ i : Fin 5, RecoveryFocus.pick outSlot i =
      (![none,none,none,none,some 0] : Fin 5 → Option (Fin 1)) i := out_pick
  refine ⟨r,hp,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,finished,MatrixUnaryFinish.config]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,hpick,config,ambient,finished,MatrixUnaryFinish.config]

end NearCubicWires.RepairOrdinary.MatrixUnary
