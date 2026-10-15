import Proof.MachineModel.UWitnessOrdinary

/-! Allocate the actual walk cap, four independent reset tapes, and the
one-cell-longer array rewind tape in one paid scan of a short unary product. -/
namespace NearCubicWires.RepairOrdinary.UWalkCapacity
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (state : Fin 3) (M p k extra : ℕ) : Configuration 7 3 :=
  ⟨state,fun i => if i.val=0 then p else if i.val=6 then k+extra else k,
    fun i => if i.val=0 then List.replicate M true
      else if i.val=6 then List.replicate (k+extra) false
      else List.replicate k (i.val==1)⟩
def raw : Machine 7 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==2
  rule := fun s bits => if s.val=0 then some
      ⟨if bits 0 then 0 else 1,fun i => if i.val=0 then none else some (i.val==1),
        fun i => if i.val=0 && !bits 0 then .stay else .right⟩
    else if s.val=1 then some
      ⟨2,fun i => if i.val=6 then some false else none,fun i => if i.val=6 then .right else .stay⟩
    else none

theorem write_rep (n : ℕ) (b : Bool) : writeTapeBit (List.replicate n b) n b=List.replicate (n+1) b := by
  have h := Streaming.write_append (List.replicate n b) b
  simpa [List.replicate_add] using h

theorem copy_step (M p : ℕ) (hp : p<M) :
    step raw (cfg 0 M p p 0)=some (cfg 0 M (p+1) (p+1) 0) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_rep]

theorem end_step (M : ℕ) : step raw (cfg 0 M M M 0)=some (cfg 1 M M (M+1) 0) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_rep]

theorem extra_step (M : ℕ) : step raw (cfg 1 M M (M+1) 0)=some (cfg 2 M M (M+1) 1) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_rep]

theorem loop (M p remaining : ℕ) (hp : p+remaining=M) :
    Timed raw (remaining+2) (cfg 0 M p p 0) (cfg 2 M M (M+1) 1) := by
  induction remaining generalizing p with
  | zero =>
    have he : p=M := by omega
    subst p
    exact Timed.step (by rfl) (end_step M) (Timed.step (by rfl) (extra_step M) (Timed.refl _ _))
  | succ remaining ih =>
    simpa [Nat.add_assoc] using Timed.step (by rfl) (copy_step M p (by omega)) (ih (p+1) (by omega))

def rawInput (M : ℕ) : Fin 7 → List Bool := fun i => if i.val=0 then List.replicate M true else []
theorem raw_run (M : ℕ) :
    ∃ r,run raw (M+2) (rawInput M)=some r ∧ r.final=cfg 2 M M (M+1) 1 ∧ r.steps=M+2 := by
  obtain ⟨r,hr,hf,hs⟩ := (loop M 0 M (by omega)).run (by rfl)
  have hi : cfg 0 M 0 0 0=initialConfiguration raw (rawInput M) := by
    apply configuration_ext
    · rfl
    · funext i; simp [cfg,initialConfiguration]
    · funext i; simp [cfg,rawInput,initialConfiguration]
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

def machine := Rewind.machine raw
def input (M : ℕ) : Fin 8 → List Bool := fun i => if i.val=0 then List.replicate M true else []
def result (M : ℕ) : Fin 8 → List Bool := fun i =>
  if i.val=0 then List.replicate M true else if i.val=1 then List.replicate (M+1) true
  else if i.val=6 || i.val=7 then List.replicate (M+2) false else List.replicate (M+1) false

theorem ready (M : ℕ) : ClockJoin.ReadyRun machine (2*M+6) (input M) (result M) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run M
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (7+1) => List Bool)
      (rawInput M) (fun _ : Fin 1 => []))=input M := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (7+1) => List Bool)
      (rawInput M) (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have he : 2*base.steps+2=2*M+6 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [result,hf,cfg] using ht 0
  · simpa [result,hf,cfg] using ht 1
  · simpa [result,hf,cfg] using ht 2
  · simpa [result,hf,cfg] using ht 3
  · simpa [result,hf,cfg] using ht 4
  · simpa [result,hf,cfg] using ht 5
  · simpa [result,hf,cfg] using ht 6
  · simpa [result,hs] using hcount

def amount (w t j : ℕ) := 128*(t+j+1)*(w+1)+1
theorem amount_bounds (w t j : ℕ) : t*(52*w+97)+1 ≤ amount w t j ∧
    4*w+3 ≤ amount w t j ∧ 2*(t+j)+2 ≤ amount w t j := by
  dsimp [amount]
  constructor
  · nlinarith
  constructor <;> nlinarith
theorem amount_short (w t j c : ℕ) (ht : t ≤ c) (hj : j ≤ c) :
    amount w t j ≤ 257*(c+1)*(w+1) := by
  dsimp [amount]
  nlinarith

end NearCubicWires.RepairOrdinary.UWalkCapacity
