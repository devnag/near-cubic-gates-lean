import Proof.MachineModel.UWitnessOrdinary

/-! Small unary fields copied from their paid sentinel inputs. Optional
leading sentinel and successor are fixed finite-control choices. -/
namespace NearCubicWires.RepairOrdinary.UWalkUnary
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source (cap n : ℕ) := ZeroPadding.pad cap (CompareMachine.word n)
def lead (sentinel : Bool) : List Bool := if sentinel then [false] else []
def output (sentinel extra : Bool) (n : ℕ) := lead sentinel ++ List.replicate (n+extra.toNat) true
def raw (sentinel extra : Bool) : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==2
  rule := fun s bits => if s.val=0 then
      some ⟨1,![none,if sentinel then some false else none],![.right,if sentinel then .right else .stay]⟩
    else if s.val=1 then
      some (if bits 0 then ⟨1,![none,some true],![.right,.right]⟩ else
        ⟨2,![none,if extra then some true else none],![.stay,if extra then .right else .stay]⟩)
    else none
def cfg (state : Fin 3) (cap n p : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨state,![p,out.length],![source cap n,out]⟩

theorem read_source (cap n p : ℕ) : readTapeBit (source cap n) (p+1)=decide (p<n) := by
  rw [source,ZeroPadding.read_pad]
  exact CompareMachine.read_mark n p

theorem copy_step (sentinel extra : Bool) (cap n p : ℕ) (out : List Bool) (hp : p<n) :
    step (raw sentinel extra) (cfg 1 cap n (p+1) out)=
      some (cfg 1 cap n (p+2) (out++[true])) := by
  simp [step,raw,cfg,Configuration.scanned,read_source,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem end_step (sentinel extra : Bool) (cap n : ℕ) (out : List Bool) :
    step (raw sentinel extra) (cfg 1 cap n (n+1) out)=
      some (cfg 2 cap n (n+1) (out++List.replicate extra.toNat true)) := by
  cases extra <;> simp [step,raw,cfg,Configuration.scanned,read_source]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Streaming.write_append])

theorem loop (sentinel extra : Bool) (cap n p k : ℕ) (out : List Bool) (hk : p+k=n) :
    Timed (raw sentinel extra) (k+1) (cfg 1 cap n (p+1) out)
      (cfg 2 cap n (n+1) (out++List.replicate (k+extra.toNat) true)) := by
  induction k generalizing p out with
  | zero =>
    have hp : p=n := by omega
    subst p
    simpa using Timed.step (by rfl) (end_step sentinel extra cap n out) (Timed.refl _ _)
  | succ k ih =>
    have ht := ih (p+1) (out++[true]) (by omega)
    have ho : (out++[true])++List.replicate (k+extra.toNat) true=
        out++List.replicate (k+1+extra.toNat) true := by
      have he : k+1+extra.toNat=(k+extra.toNat)+1 := by omega
      simp [he,List.replicate_succ,List.append_assoc]
    rw [ho] at ht
    simpa [Nat.add_assoc] using Timed.step (by rfl)
      (copy_step sentinel extra cap n p out (by omega)) ht

theorem boot_step (sentinel extra : Bool) (cap n : ℕ) :
    step (raw sentinel extra) (cfg 0 cap n 0 [])=some (cfg 1 cap n 1 (lead sentinel)) := by
  cases sentinel <;> simp [step,raw,cfg,lead]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,writeTapeBit])

theorem raw_run (sentinel extra : Bool) (cap n : ℕ) :
    ∃ r,run (raw sentinel extra) (n+2) ![source cap n,[]]=some r ∧
      r.final=cfg 2 cap n (n+1) (output sentinel extra n) ∧ r.steps=n+2 := by
  have hp := loop sentinel extra cap n 0 n (lead sentinel) (by omega)
  have h := Timed.step (by rfl) (boot_step sentinel extra cap n) hp
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  have hi : cfg 0 cap n 0 []=initialConfiguration (raw sentinel extra) ![source cap n,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

def machine (sentinel extra : Bool) := Rewind.machine (raw sentinel extra)
def input (cap n : ℕ) : Fin 3 → List Bool := ![source cap n,[],[]]
def result (sentinel extra : Bool) (cap n : ℕ) : Fin 3 → List Bool :=
  ![source cap n,output sentinel extra n,List.replicate (n+2) false]

theorem ready (sentinel extra : Bool) (cap n : ℕ) :
    ClockJoin.ReadyRun (machine sentinel extra) (2*n+6) (input cap n) (result sentinel extra cap n) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run sentinel extra cap n
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (raw sentinel extra) _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![source cap n,[]] (fun _ : Fin 1 => []))=input cap n := by
    funext i; fin_cases i <;> rfl
  change run (machine sentinel extra) (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![source cap n,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have he : 2*base.steps+2=2*n+6 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [result,hf,cfg] using ht 0
  · simpa [result,hf,cfg] using ht 1
  · simpa [result,hs] using hcount

end NearCubicWires.RepairOrdinary.UWalkUnary
