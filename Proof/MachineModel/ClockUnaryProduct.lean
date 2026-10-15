import Proof.MachineModel.ClockDegree

/-! Literal multiplication of two short unary clock fields. Both input
words are retained; the inner cursor returns to its leading false sentinel
on each round. The product is physically written, one mark at a time. -/
namespace NearCubicWires.RepairOrdinary.ClockUnaryProduct
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 5) (dMove eMove outMove : HeadMove) (write : Option Bool := none) : Action 3 5 :=
  ⟨state,![none,none,write],![dMove,eMove,outMove]⟩
def raw : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 4
  rule := fun state bits =>
    if state.val=0 then some (action 1 .stay .right .stay)
    else if state.val=1 then some (if bits 0 then action 2 .right .stay .stay else action 4 .stay .stay .stay)
    else if state.val=2 then some (if bits 1 then action 2 .stay .right .right (some true)
      else action 3 .stay .left .stay)
    else if state.val=3 then some (if bits 1 then action 3 .stay .left .stay else action 1 .stay .right .stay)
    else none

def config (state : Fin 5) (d e : ℕ) (i j : ℕ) (out : List Bool) : Configuration 3 5 :=
  ⟨state,![i,j,out.length],![List.replicate d true,false::List.replicate e true,out]⟩
@[simp] theorem config_cells (state : Fin 5) (d e i j : ℕ) (out : List Bool) :
    (config state d e i j out).tapeCells=d+(e+1)+out.length := by
  simp [config,Configuration.tapeCells,Fin.sum_univ_succ]
  omega

theorem read_unary (n pos : ℕ) : readTapeBit (List.replicate n true) pos = decide (pos<n) := by
  induction pos generalizing n with
  | zero => cases n <;> simp [List.replicate_succ,readTapeBit,List.getD]
  | succ pos ih =>
    cases n with
    | zero => simp [readTapeBit,List.getD]
    | succ n => simpa [List.replicate_succ,readTapeBit,List.getD] using ih n

theorem read_sentinel (n pos : ℕ) :
    readTapeBit (false::List.replicate n true) (pos+1)=decide (pos<n) := by
  simpa [readTapeBit,List.getD] using read_unary n pos

theorem copy_step (d e i j : ℕ) (out : List Bool) (hj : j<e) :
    step raw (config 2 d e i (j+1) out)=
      some (config 2 d e i (j+2) (out++[true])) := by
  have hr := read_sentinel e j
  simp only [hj,decide_true] at hr
  simp [step,raw,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action,Streaming.write_append]

theorem end_step (d e i : ℕ) (out : List Bool) :
    step raw (config 2 d e i (e+1) out)=some (config 3 d e i e out) := by
  have hr := read_sentinel e e
  simp only [Nat.lt_irrefl,decide_false] at hr
  simp [step,raw,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem back_step (d e i j : ℕ) (out : List Bool) (hj : j<e) :
    step raw (config 3 d e i (j+1) out)=some (config 3 d e i j out) := by
  have hr := read_sentinel e j
  simp only [hj,decide_true] at hr
  simp [step,raw,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem return_step (d e i : ℕ) (out : List Bool) :
    step raw (config 3 d e i 0 out)=some (config 1 d e i 1 out) := by
  simp [step,raw,config,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem back_prefix (d e i j : ℕ) (out : List Bool) (hj : j≤e) :
    Prefix raw (d+(e+1)+out.length) (j+1)
      (config 3 d e i j out) (config 1 d e i 1 out) := by
  induction j with
  | zero => exact Prefix.step (by simp) (by rfl) (return_step d e i out) (Prefix.refl _ (by simp))
  | succ j ih => exact Prefix.step (by simp) (by rfl) (back_step d e i j out (by omega)) (ih (by omega))

theorem copy_prefix (d e i j remaining : ℕ) (out : List Bool) (hj : j+remaining=e) :
    Prefix raw (d+(e+1)+out.length+remaining) (remaining+e+2)
      (config 2 d e i (j+1) out)
      (config 1 d e i 1 (out++List.replicate remaining true)) := by
  induction remaining generalizing j out with
  | zero =>
    have he : j=e := by omega
    subst j
    have hp := Prefix.step (by simp : (config 2 d e i (e+1) out).tapeCells≤d+(e+1)+out.length)
      (by rfl : raw.halted (2 : Fin 5)=false) (end_step d e i out)
      (back_prefix d e i e out (Nat.le_refl _))
    simpa [Nat.add_assoc] using hp
  | succ remaining ih =>
    have hi := ih (j+1) (out++[true]) (by omega)
    have hspace : d+(e+1)+(out++[true]).length+remaining=d+(e+1)+out.length+(remaining+1) := by simp; omega
    rw [hspace] at hi
    have ht : Prefix raw (d+(e+1)+out.length+(remaining+1)) (remaining+e+2)
        (config 2 d e i (j+2) (out++[true]))
        (config 1 d e i 1 (out++List.replicate (remaining+1) true)) := by
      simpa [List.replicate_succ,List.append_assoc] using hi
    have hp := Prefix.step (by simp :
        (config 2 d e i (j+1) out).tapeCells≤d+(e+1)+out.length+(remaining+1))
      (by rfl : raw.halted (2 : Fin 5)=false) (copy_step d e i j out (by omega)) ht
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp

theorem enter_step (d e i : ℕ) (out : List Bool) (hi : i<d) :
    step raw (config 1 d e i 1 out)=some (config 2 d e (i+1) 1 out) := by
  have hr := read_unary d i
  simp only [hi,decide_true] at hr
  simp [step,raw,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem stop_step (d e : ℕ) (out : List Bool) :
    step raw (config 1 d e d 1 out)=some (config 4 d e d 1 out) := by
  have hr := read_unary d d
  simp only [Nat.lt_irrefl,decide_false] at hr
  simp [step,raw,config,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

private theorem mono_space {t s old new n : ℕ} {p : Machine t s}
    {a b : Configuration t s} (h : Prefix p old n a b) (hn : old≤new) : Prefix p new n a b := by
  induction h with
  | refl c hc => exact Prefix.refl c (hc.trans hn)
  | step hc hh hs _ ih => exact Prefix.step (hc.trans hn) hh hs ih

theorem loop_prefix (d e i remaining : ℕ) (out : List Bool) (hi : i+remaining=d) :
    Prefix raw (d+(e+1)+out.length+remaining*e) (remaining*(2*e+3)+1)
      (config 1 d e i 1 out)
      (config 4 d e d 1 (out++List.replicate (remaining*e) true)) := by
  induction remaining generalizing i out with
  | zero =>
    have he : i=d := by omega
    subst i
    simpa using Prefix.step (by simp : (config 1 d e d 1 out).tapeCells≤d+(e+1)+out.length)
      (by rfl : raw.halted (1 : Fin 5)=false) (stop_step d e out) (Prefix.refl _ (by simp))
  | succ remaining ih =>
    have ht := ih (i+1) (out++List.replicate e true) (by omega)
    have hspace : d+(e+1)+(out++List.replicate e true).length+remaining*e =
        d+(e+1)+out.length+(remaining+1)*e := by simp; ring
    rw [hspace] at ht
    have houtput : (out++List.replicate e true)++List.replicate (remaining*e) true =
        out++List.replicate ((remaining+1)*e) true := by
      rw [List.append_assoc,← List.replicate_add]
      congr 2
      ring
    rw [houtput] at ht
    have hc := copy_prefix d e (i+1) 0 e out (by simp)
    have hc' := mono_space hc (by nlinarith : d+(e+1)+out.length+e≤d+(e+1)+out.length+(remaining+1)*e)
    have round := Prefix.step (by simp :
        (config 1 d e i 1 out).tapeCells≤d+(e+1)+out.length+(remaining+1)*e)
      (by rfl : raw.halted (1 : Fin 5)=false) (enter_step d e i out (by omega)) hc'
    have result := round.trans ht
    have htime : (e+e+2+1)+(remaining*(2*e+3)+1)=(remaining+1)*(2*e+3)+1 := by ring
    simpa only [htime] using result

theorem boot_step (d e : ℕ) :
    step raw (config 0 d e 0 0 [])=some (config 1 d e 0 1 []) := by
  simp [step,raw,config]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem raw_run (d e : ℕ) :
    ∃ r : ExecutionReceipt 3 5,
      run raw (d*(2*e+3)+2) ![List.replicate d true,false::List.replicate e true,[]]=some r ∧
      r.final.tapes 0=List.replicate d true ∧
      r.final.tapes 1=false::List.replicate e true ∧
      r.final.tapes 2=List.replicate (d*e) true ∧ r.steps=d*(2*e+3)+2 := by
  have hp := loop_prefix d e 0 d [] (by simp)
  have h := Prefix.step (by simp : (config 0 d e 0 0 []).tapeCells≤d+(e+1)+d*e)
    (by rfl : raw.halted (0 : Fin 5)=false) (boot_step d e) (by simpa using hp)
  obtain ⟨r,hr,hf,hs,_⟩ := h.run (by rfl) (by simp)
  refine ⟨r,?_,by simp [hf,config],by simp [hf,config],by simp [hf,config],by omega⟩
  have hi : initialConfiguration raw ![List.replicate d true,false::List.replicate e true,[]]=config 0 d e 0 0 [] := by
    apply configuration_ext
    · rfl
    · funext k; fin_cases k <;> rfl
    · rfl
  change runFrom raw _ _=some r
  rw [hi]
  simpa [Nat.add_assoc] using hr

def machine : Machine 4 7 := Rewind.machine raw

theorem product_run (d e : ℕ) :
    ∃ r : ExecutionReceipt 4 7,
      run machine (2*(d*(2*e+3)+2)+2)
        (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
          ![List.replicate d true,false::List.replicate e true,[]] (fun _ : Fin 1 => []))=some r ∧
      r.final.tapes 0=List.replicate d true ∧
      r.final.tapes 1=false::List.replicate e true ∧
      r.final.tapes 2=List.replicate (d*e) true ∧
      r.final.tapes 3=List.replicate (d*(2*e+3)+2) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=2*(d*(2*e+3)+2)+2 := by
  obtain ⟨base,hb,h0,h1,h2,hs⟩ := raw_run d e
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  refine ⟨r,by simpa [hs,machine] using hr,(ht 0).trans h0,(ht 1).trans h1,(ht 2).trans h2,
    by simpa [hs] using hcounter,hh,by omega⟩

end NearCubicWires.RepairOrdinary.ClockUnaryProduct
