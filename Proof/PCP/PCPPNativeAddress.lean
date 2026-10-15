import Proof.MachineModel.ClockUnarySum
import Proof.PCP.PCPPNativeCopyNodes

/-! The exact shared DAG address, produced by actual bounded unary scans.
The base is copied once, each index mark twice, and one final mark is paid. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeAddress
open LocalBitMultitape RecoveryExecution ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 4) (base index p j : ℕ) (out : List Bool) : Configuration 3 4 :=
  ⟨q,![p,j,out.length],![List.replicate base true,List.replicate index true,out]⟩
def raw : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bs => if q.val=0 then
      some (if bs 0 then ⟨0,![none,none,some true],![.right,.stay,.right]⟩
        else ⟨1,fun _ => none,fun _ => .stay⟩)
    else if q.val=1 then
      some (if bs 1 then ⟨2,![none,none,some true],![.stay,.stay,.right]⟩
        else ⟨3,![none,none,some true],![.stay,.stay,.right]⟩)
    else if q.val=2 then some ⟨1,![none,none,some true],![.stay,.right,.right]⟩
    else none

theorem base_step (base index p : ℕ) (out : List Bool) (hp : p<base) :
    step raw (cfg 0 base index p 0 out)=some (cfg 0 base index (p+1) 0 (out++[true])) := by
  have hr := ClockUnaryProduct.read_unary base p
  simp [step,raw,cfg,Configuration.scanned,hr,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem base_stop (base index : ℕ) (out : List Bool) :
    step raw (cfg 0 base index base 0 out)=some (cfg 1 base index base 0 out) := by
  have hr := ClockUnaryProduct.read_unary base base
  simp [step,raw,cfg,Configuration.scanned,hr]
  rfl
theorem index_step (base index j : ℕ) (out : List Bool) (hj : j < index) :
    step raw (cfg 1 base index base j out)=some (cfg 2 base index base j (out++[true])) := by
  have hr := ClockUnaryProduct.read_unary index j
  simp [step,raw,cfg,Configuration.scanned,hr,hj]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem index_second (base index j : ℕ) (out : List Bool) :
    step raw (cfg 2 base index base j out)=some (cfg 1 base index base (j+1) (out++[true])) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem index_stop (base index : ℕ) (out : List Bool) :
    step raw (cfg 1 base index base index out)=some (cfg 3 base index base index (out++[true])) := by
  have hr := ClockUnaryProduct.read_unary index index
  simp [step,raw,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem base_loop (remaining p index : ℕ) (out : List Bool) :
    Timed raw (remaining+1) (cfg 0 (p+remaining) index p 0 out)
      (cfg 1 (p+remaining) index (p+remaining) 0 (out++List.replicate remaining true)) := by
  induction remaining generalizing p out with
  | zero => simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using
      Timed.single (by rfl) (base_stop p index out)
  | succ remaining ih =>
    have h := ih (p+1) (out++[true])
    rw [show p+1+remaining=p+(remaining+1) by omega] at h
    have hall := Timed.step (by rfl) (base_step _ index p out (by omega)) h
    simpa only [List.replicate_succ,List.append_assoc,List.singleton_append,Nat.add_assoc] using hall

theorem index_loop (remaining j base : ℕ) (out : List Bool) :
    Timed raw (2*remaining+1) (cfg 1 base (j+remaining) base j out)
      (cfg 3 base (j+remaining) base (j+remaining) (out++List.replicate (2*remaining+1) true)) := by
  induction remaining generalizing j out with
  | zero => simpa only [Nat.add_zero,Nat.mul_zero,Nat.zero_add,List.replicate_one] using
      Timed.single (by rfl) (index_stop base j out)
  | succ remaining ih =>
    have h := ih (j+1) (out++[true,true])
    rw [show j+1+remaining=j+(remaining+1) by omega] at h
    have htwo := (Timed.single (by rfl) (index_step base (j+(remaining+1)) j out (by omega))).trans
      (Timed.single (by rfl) (index_second base (j+(remaining+1)) j (out++[true])))
    simp only [List.append_assoc,List.singleton_append] at htwo
    have hall := htwo.trans h
    have ht : 1+1+(2*remaining+1)=2*(remaining+1)+1 := by omega
    have hr : 2*(remaining+1)+1=2+(2*remaining+1) := by omega
    rw [ht] at hall
    simpa only [hr,List.replicate_add,List.replicate_succ,List.replicate_zero,
      List.append_assoc,List.cons_append,List.nil_append] using hall

theorem raw_run (base index : ℕ) :
    ∃ r,run raw (base+2*index+2)
      ![List.replicate base true,List.replicate index true,[]]=some r ∧
      r.final=cfg 3 base index base index (List.replicate (PCPPSubstitution.address base index) true) ∧
      r.steps=base+2*index+2 := by
  have hl := base_loop base 0 index []
  have hr := index_loop index 0 base (List.replicate base true)
  simp only [Nat.zero_add,List.nil_append] at hl hr
  have hall := hl.trans hr
  rw [←List.replicate_add] at hall
  have ht : base+1+(2*index+1)=base+2*index+2 := by omega
  rw [ht] at hall
  have hi : cfg 0 base index 0 0 []=initialConfiguration raw
      ![List.replicate base true,List.replicate index true,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hall
  obtain ⟨r,run,final,steps⟩ := hall.run (by rfl)
  exact ⟨r,run,by simpa only [PCPPSubstitution.address,Nat.add_assoc] using final,steps⟩

def machine : Machine 4 6 := Rewind.machine raw
theorem address_ready (base index : ℕ) :
    ReadyRun machine (2*base+4*index+6)
      ![List.replicate base true,List.replicate index true,[],[]]
      ![List.replicate base true,List.replicate index true,
        List.replicate (PCPPSubstitution.address base index) true,
        List.replicate (base+2*index+2) false] := by
  obtain ⟨r,hr,hf,hs⟩ := raw_run base index
  obtain ⟨result,hresult,htapes,hcounter,hheads,hsteps,_⟩ :=
    Rewind.Workspace.reset_workspace raw _ _ r hr 0
  have hin : Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate base true,List.replicate index true,[]] (fun _ : Fin 1 => [])=
      ![List.replicate base true,List.replicate index true,[],[]] := by
    funext i; fin_cases i <;> rfl
  have htime : 2*r.steps+2=2*base+4*index+6 := by omega
  change run machine (2*r.steps+2) (Fin.addCases
    (motive := fun _ : Fin (3+1) => List Bool)
    ![List.replicate base true,List.replicate index true,[]] (fun _ : Fin 1 => []))=some result at hresult
  rw [hin,htime] at hresult
  refine ⟨result,hresult,?_,hheads,by omega⟩
  funext i; fin_cases i
  · simpa [hf,cfg] using htapes 0
  · simpa [hf,cfg] using htapes 1
  · simpa [hf,cfg] using htapes 2
  · simpa [hs] using hcounter

end NearCubicWires.RepairOrdinary.PCPPNativeAddress
