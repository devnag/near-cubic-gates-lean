import Proof.MachineModel.ClockLogLog

/-! Sum two paid unary drivers by two linear physical scans. -/
namespace NearCubicWires.RepairOrdinary.ClockUnarySum
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (state : Fin 3) (r s p q : ℕ) (out : List Bool) : Configuration 3 3 :=
  ⟨state,![p,q,out.length],![List.replicate r true,List.replicate s true,out]⟩
@[simp] theorem cfg_cells (state : Fin 3) (r s p q : ℕ) (out : List Bool) :
    (cfg state r s p q out).tapeCells=r+s+out.length := by
  simp [cfg,Configuration.tapeCells,Fin.sum_univ_succ]; omega
def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val==2
  rule := fun state scan => if state.val=0 then
      some (if scan 0 then ⟨0,![none,none,some true],![.right,.stay,.right]⟩
        else ⟨1,fun _ => none,fun _ => .stay⟩)
    else if state.val=1 then
      some (if scan 1 then ⟨1,![none,none,some true],![.stay,.right,.right]⟩
        else ⟨2,fun _ => none,fun _ => .stay⟩)
    else none

theorem left_step (r s p : ℕ) (out : List Bool) (hp : p<r) :
    step raw (cfg 0 r s p 0 out)=some (cfg 0 r s (p+1) 0 (out++[true])) := by
  have hr := ClockUnaryProduct.read_unary r p
  simp [step,raw,cfg,Configuration.scanned,hr,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem left_stop (r s : ℕ) (out : List Bool) :
    step raw (cfg 0 r s r 0 out)=some (cfg 1 r s r 0 out) := by
  have hr := ClockUnaryProduct.read_unary r r
  simp [step,raw,cfg,Configuration.scanned,hr]
  rfl
theorem right_step (r s p : ℕ) (out : List Bool) (hp : p<s) :
    step raw (cfg 1 r s r p out)=some (cfg 1 r s r (p+1) (out++[true])) := by
  have hr := ClockUnaryProduct.read_unary s p
  simp [step,raw,cfg,Configuration.scanned,hr,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
theorem right_stop (r s : ℕ) (out : List Bool) :
    step raw (cfg 1 r s r s out)=some (cfg 2 r s r s out) := by
  have hr := ClockUnaryProduct.read_unary s s
  simp [step,raw,cfg,Configuration.scanned,hr]
  rfl

theorem left_prefix (r s p remaining : ℕ) (out : List Bool) (hp : p+remaining=r) :
    Prefix raw (r+s+out.length+remaining) (remaining+1)
      (cfg 0 r s p 0 out) (cfg 1 r s r 0 (out++List.replicate remaining true)) := by
  induction remaining generalizing p out with
  | zero =>
    have he : p=r := by omega
    subst p
    simpa using Prefix.step (by simp) (by rfl) (left_stop r s out) (Prefix.refl _ (by simp))
  | succ remaining ih =>
    have ht := ih (p+1) (out++[true]) (by omega)
    have htail : Prefix raw (r+s+out.length+(remaining+1)) (remaining+1)
        (cfg 0 r s (p+1) 0 (out++[true]))
        (cfg 1 r s r 0 (out++List.replicate (remaining+1) true)) := by
      simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    exact Prefix.step (by simp) (by rfl) (left_step r s p out (by omega)) htail
theorem right_prefix (r s p remaining : ℕ) (out : List Bool) (hp : p+remaining=s) :
    Prefix raw (r+s+out.length+remaining) (remaining+1)
      (cfg 1 r s r p out) (cfg 2 r s r s (out++List.replicate remaining true)) := by
  induction remaining generalizing p out with
  | zero =>
    have he : p=s := by omega
    subst p
    simpa using Prefix.step (by simp) (by rfl) (right_stop r s out) (Prefix.refl _ (by simp))
  | succ remaining ih =>
    have ht := ih (p+1) (out++[true]) (by omega)
    have htail : Prefix raw (r+s+out.length+(remaining+1)) (remaining+1)
        (cfg 1 r s r (p+1) (out++[true]))
        (cfg 2 r s r s (out++List.replicate (remaining+1) true)) := by
      simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    exact Prefix.step (by simp) (by rfl) (right_step r s p out (by omega)) htail

theorem raw_run (r s : ℕ) :
    ∃ receipt : ExecutionReceipt 3 3,
      run raw (r+s+2) ![List.replicate r true,List.replicate s true,[]]=some receipt ∧
      receipt.final=cfg 2 r s r s (List.replicate (r+s) true) ∧ receipt.steps=r+s+2 := by
  have hl := left_prefix r s 0 r [] (by omega)
  have hr := right_prefix r s 0 s (List.replicate r true) (by omega)
  simp only [List.length_nil,List.nil_append] at hl
  simp only [List.length_replicate,←List.replicate_add] at hr
  obtain ⟨last,hrun,hrf,hrs,_⟩ := hr.run (by rfl) (by simp; omega)
  obtain ⟨receipt,he,hf,hs,_⟩ := hl.followedBy last hrun
  have hi : initialConfiguration raw ![List.replicate r true,List.replicate s true,[]]=cfg 0 r s 0 0 [] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  refine ⟨receipt,?_,hf.trans hrf,by omega⟩
  change runFrom raw _ _=some receipt
  rw [hi]
  have htime : (r+1)+(s+1)=r+s+2 := by omega
  simpa only [htime] using he

def machine : Machine 4 5 := Rewind.machine raw
theorem sum_ready (r s : ℕ) :
    ReadyRun machine (2*(r+s)+6) ![List.replicate r true,List.replicate s true,[],[]]
      ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false] := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run r s
  obtain ⟨receipt,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate r true,List.replicate s true,[]] (fun _ : Fin 1 => []))=
      ![List.replicate r true,List.replicate s true,[],[]] := by funext i; fin_cases i <;> rfl
  have htime : 2*base.steps+2=2*(r+s)+6 := by omega
  change run machine (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate r true,List.replicate s true,[]] (fun _ : Fin 1 => []))=some receipt at hr
  rw [hi,htime] at hr
  refine ⟨receipt,hr,?_,hh,by omega⟩
  funext i; fin_cases i
  · simpa [hf,cfg] using ht 0
  · simpa [hf,cfg] using ht 1
  · simpa [hf,cfg] using ht 2
  · simpa [hs] using hcounter

end NearCubicWires.RepairOrdinary.ClockUnarySum
