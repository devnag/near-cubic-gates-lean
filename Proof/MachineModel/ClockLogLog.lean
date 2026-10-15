import Proof.MachineModel.ClockEnvelope
import Proof.PCP.VerifierDecodingBitWidth

/-! Reuse the decoder's actual unary-to-bitwidth program at all-zero heads.
For U, its input is ell and its result is ceil(log2(q)). -/
namespace NearCubicWires.RepairOrdinary.ClockLogLog
open LocalBitMultitape ClockJoin
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def moveMachine (moves : Fin 6 → HeadMove) : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun _ => none,moves⟩ else none
def cfg (state : Fin 2) (heads : Fin 6 → ℕ) (tapes : Fin 6 → List Bool) : Configuration 6 2 :=
  ⟨state,heads,tapes⟩
theorem move_run (moves : Fin 6 → HeadMove) (heads : Fin 6 → ℕ) (tapes : Fin 6 → List Bool) :
    ∃ r : ExecutionReceipt 6 2,
      runFrom (moveMachine moves) 1 (cfg 0 heads tapes)=some r ∧
      r.final=cfg 1 (fun i => (moves i).apply (heads i)) tapes ∧ r.steps=1 := by
  have he : step (moveMachine moves) (cfg 0 heads tapes)=
      some (cfg 1 (fun i => (moves i).apply (heads i)) tapes) := by
    simp [step,moveMachine,cfg]
    rfl
  let bound := ∑ i,(tapes i).length
  have hp := Prefix.step (by rfl : (cfg 0 heads tapes).tapeCells≤bound)
    (by rfl : (moveMachine moves).halted (0 : Fin 2)=false) he
    (Prefix.refl _ (by rfl))
  obtain ⟨r,hr,hf,hs,_⟩ := hp.run (by rfl) (by rfl)
  exact ⟨r,hr,hf,hs⟩

def entryMoves : Fin 6 → HeadMove := ![.right,.stay,.stay,.stay,.stay,.stay]
def exitMoves : Fin 6 → HeadMove := ![.left,.stay,.stay,.stay,.stay,.left]
def entry := moveMachine entryMoves
def leave := moveMachine exitMoves
def first : Machine 6 27 := Composition.machine entry BitWidthMachine.machine
def machine : Machine 6 29 := Composition.machine first leave
def input (n : ℕ) : Fin 6 → List Bool := ![false::List.replicate n true,[],[],[],[],[]]
def output (n a b : ℕ) : Fin 6 → List Bool :=
  ![false::List.replicate n true,frame (List.replicate n true),frame (ClockBinary.word n),
    List.replicate a false,List.replicate b false,false::List.replicate (ClockBinary.word n).length true]

theorem loglog_ready (n : ℕ) (hn : 0<n) :
    ∃ a b, a≤2*PCPResourceLedger.ell n+3 ∧ b≤ClockInputLength.cost n (List.replicate n true) ∧
      ReadyRun machine (8*n^2+34*n+15) (input n) (output n a b) := by
  obtain ⟨a,b,ha,hb,mid,hm,hmf,hms⟩ := BitWidthMachine.bit_width_run n hn
  obtain ⟨start,hs,hsf,hss⟩ := move_run entryMoves (fun _ => 0) (input n)
  have hmstart : Composition.restart start.final BitWidthMachine.machine.start=BitWidthMachine.input n := by
    rw [hsf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have hmid : runFrom BitWidthMachine.machine (BitWidthMachine.budget n)
      (Composition.restart start.final BitWidthMachine.machine.start)=some mid := by rw [hmstart]; exact hm
  have hfirst := Composition.run_join entry BitWidthMachine.machine 1 (BitWidthMachine.budget n) _ start mid hs hmid
  let base := Composition.joinedReceipt start mid
  obtain ⟨last,hl,hlf,hls⟩ := move_run exitMoves ![1,0,0,0,0,1] (output n a b)
  have hlstart : Composition.restart base.final leave.start=cfg 0 ![1,0,0,0,0,1] (output n a b) := by
    change Composition.restart (Composition.rightConfig 2 mid.final) leave.start=_
    rw [hmf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  have hlast : runFrom leave 1 (Composition.restart base.final leave.start)=some last := by rw [hlstart]; exact hl
  have hj := Composition.run_join first leave (1+1+BitWidthMachine.budget n) 1 _ base last hfirst hlast
  have hready : ReadyRun machine ((1+1+BitWidthMachine.budget n)+1+1) (input n) (output n a b) := by
    refine ⟨Composition.joinedReceipt base last,?_,?_,?_,?_⟩
    · exact hj
    · change last.final.tapes=output n a b
      rw [hlf]
      rfl
    · change ∀ i,last.final.heads i=0
      rw [hlf]
      intro i; fin_cases i <;> rfl
    · change (start.steps+1+mid.steps)+1+last.steps≤_
      omega
  have hbound := BitWidthMachine.budget_bound n n (Nat.le_refl _)
  exact ⟨a,b,ha,hb,ClockJoin.enlarge machine _ _ _ _ hready (by omega)⟩

theorem clock_log_run (N : ℕ) (hn : 0<N) :
    ∃ a b, ReadyRun machine (8*(PCPResourceLedger.ell N)^2+34*PCPResourceLedger.ell N+15)
      (input (PCPResourceLedger.ell N)) (output (PCPResourceLedger.ell N) a b) ∧
      output (PCPResourceLedger.ell N) a b 5=false::List.replicate (ClockEnvelope.logWidth N) true := by
  have hell : 0<PCPResourceLedger.ell N := by
    have h := (ClockDyadicLedger.pow_ell_bounds N (by omega)).1
    by_contra hnot
    have he : PCPResourceLedger.ell N=0 := by omega
    rw [he] at h
    simp at h
    omega
  obtain ⟨a,b,_,_,hr⟩ := loglog_ready (PCPResourceLedger.ell N) hell
  exact ⟨a,b,hr,by simp [output,ClockEnvelope.logWidth_eq]⟩

end NearCubicWires.RepairOrdinary.ClockLogLog
