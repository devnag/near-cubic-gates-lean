import Proof.MachineModel.ClockSmallInput

/-! Physically normalize a framed scalar to a paid unary width. The scanner
never follows an overlong suffix: its final marker is the overflow guard. -/
namespace NearCubicWires.RepairOrdinary.ClockNormalize
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resize : ℕ → List Bool → List Bool
  | 0, _ => []
  | n+1, [] => false :: resize n []
  | n+1, b::bs => b :: resize n bs

@[simp] theorem resize_length (n : ℕ) (bits : List Bool) : (resize n bits).length=n := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => cases bits <;> simp [resize,ih]

theorem resize_eq (n : ℕ) (bits : List Bool) (h : bits.length≤n) :
    resize n bits=bits++List.replicate (n-bits.length) false := by
  induction n generalizing bits with
  | zero => have hb : bits=[] := List.length_eq_zero_iff.mp (by omega); subst bits; rfl
  | succ n ih => cases bits with
    | nil => simp [resize,ih,List.replicate_succ]
    | cons b bs => simp only [List.length_cons] at h; simp [resize,ih bs (by omega)]

def cfg (state : Fin 4) (driver source : List Bool) (p q : ℕ) (out flag : List Bool) : Configuration 4 4 :=
  ⟨state,![p,q,out.length,flag.length],![driver,source,out,flag]⟩
@[simp] theorem cfg_cells (state : Fin 4) (driver source : List Bool) (p q : ℕ) (out flag : List Bool) :
    (cfg state driver source p q out flag).tapeCells=driver.length+source.length+out.length+flag.length := by
  simp [cfg,Configuration.tapeCells,Fin.sum_univ_succ]
  omega

def first (copy : Bool) : Action 4 4 :=
  ⟨if copy then 1 else 2,![none,none,some true,none],
    ![.stay,if copy then .right else .stay,.right,.stay]⟩
def second (copy bit : Bool) : Action 4 4 :=
  ⟨0,![none,none,some bit,none],![.right,if copy then .right else .stay,.right,.stay]⟩
def raw : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==3
  rule := fun s scan => if s.val=0 then
      some (if scan 0 then first (scan 1)
        else ⟨3,![none,none,some false,some (!scan 1)],![.stay,.stay,.right,.right]⟩)
    else if s.val=1 then some (second true (scan 1))
    else if s.val=2 then some (second false false) else none

theorem first_step (driver source out : List Bool) (p q : ℕ) (copy : Bool)
    (hd : readTapeBit driver p=true) (hs : readTapeBit source q=copy) :
    step raw (cfg 0 driver source p q out [])=
      some (cfg (if copy then 1 else 2) driver source p
        (q+if copy then 1 else 0) (out++[true]) []) := by
  cases copy <;> simp [step,raw,cfg,Configuration.scanned,hd,hs] <;> apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,first,HeadMove.apply,Streaming.write_append])

theorem second_step (driver source out : List Bool) (p q : ℕ) (copy bit : Bool)
    (hb : copy=true → readTapeBit source q=bit) (hz : copy=false → bit=false) :
    step raw (cfg (if copy then 1 else 2) driver source p q out [])=
      some (cfg 0 driver source (p+1) (q+if copy then 1 else 0) (out++[bit]) []) := by
  cases copy <;> simp_all [step,raw,cfg,Configuration.scanned] <;> apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,second,HeadMove.apply,Streaming.write_append])

theorem stop_step (driver source out : List Bool) (p q : ℕ) (copy : Bool)
    (hd : readTapeBit driver p=false) (hs : readTapeBit source q=copy) :
    step raw (cfg 0 driver source p q out [])=
      some (cfg 3 driver source p q (out++[false]) [!copy]) := by
  simp [step,raw,cfg,Configuration.scanned,hd,hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append,writeTapeBit]

theorem process_prefix (pre bits out : List Bool) (p n : ℕ) :
    Prefix raw ((p+n)+(pre++frame bits).length+out.length+2*n+2) (2*n+1)
      (cfg 0 (List.replicate (p+n) true) (pre++frame bits) p pre.length out [])
      (cfg 3 (List.replicate (p+n) true) (pre++frame bits) (p+n)
        (pre.length+2*min n bits.length) (out++Streaming.marks (resize n bits)++[false])
        [decide (bits.length≤n)]) := by
  induction n generalizing pre bits p out with
  | zero =>
    have hd : readTapeBit (List.replicate p true) p=false := by simp [readTapeBit]
    cases bits with
    | nil =>
      have hs : readTapeBit (pre++frame []) pre.length=false := by
        simpa [frame] using Streaming.read_append pre [] false
      have hp := Prefix.step (by simp : (cfg 0 (List.replicate p true) (pre++frame []) p pre.length out []).tapeCells≤
          p+(pre++frame []).length+out.length+2)
        (by rfl : raw.halted (0 : Fin 4)=false) (stop_step _ _ _ _ _ false hd hs)
        (Prefix.refl _ (by simp; omega))
      simpa [resize,Streaming.marks] using hp
    | cons b bs =>
      have hs : readTapeBit (pre++frame (b::bs)) pre.length=true := by
        simpa [frame,List.append_assoc] using Streaming.read_append pre (b::frame bs) true
      have hp := Prefix.step (by simp : (cfg 0 (List.replicate p true) (pre++frame (b::bs)) p pre.length out []).tapeCells≤
          p+(pre++frame (b::bs)).length+out.length+2)
        (by rfl : raw.halted (0 : Fin 4)=false) (stop_step _ _ _ _ _ true hd hs)
        (Prefix.refl _ (by simp; omega))
      simpa [resize,Streaming.marks] using hp
  | succ n ih =>
    have hd : readTapeBit (List.replicate (p+(n+1)) true) p=true := by simp [readTapeBit]
    cases bits with
    | nil =>
      let source := pre++frame []
      let driver := List.replicate (p+(n+1)) true
      let bound := (p+(n+1))+source.length+out.length+2*(n+1)+2
      have hs : readTapeBit source pre.length=false := by
        simpa [source,frame] using Streaming.read_append pre [] false
      have ht := ih pre [] (out++[true,false]) (p+1)
      have hbody : Prefix raw bound (2*n+1)
          (cfg 0 driver source (p+1) pre.length (out++[true,false]) [])
          (cfg 3 driver source (p+(n+1)) pre.length
            (out++Streaming.marks (resize (n+1) [])++[false]) [true]) := by
        convert ht using 1 <;> simp [driver,source,bound,resize,Streaming.marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add]; omega
      have hsecond := Prefix.step (by simp [bound,driver]; omega :
          (cfg 2 driver source p pre.length (out++[true]) []).tapeCells≤bound)
        (by rfl : raw.halted (2 : Fin 4)=false)
        (second_step driver source (out++[true]) p pre.length false false (by simp) (by simp))
        (by simpa [List.append_assoc] using hbody)
      have hfirst := Prefix.step (by simp [bound,driver]; omega :
          (cfg 0 driver source p pre.length out []).tapeCells≤bound)
        (by rfl : raw.halted (0 : Fin 4)=false)
        (first_step driver source out p pre.length false hd hs) (by simpa using hsecond)
      simpa [driver,source,bound,Nat.mul_add,Nat.add_assoc] using hfirst
    | cons b bs =>
      let source := pre++frame (b::bs)
      let driver := List.replicate (p+(n+1)) true
      let bound := (p+(n+1))+source.length+out.length+2*(n+1)+2
      have hs : readTapeBit source pre.length=true := by
        simpa [source,frame,List.append_assoc] using Streaming.read_append pre (b::frame bs) true
      have hb : readTapeBit source (pre.length+1)=b := by
        simpa [source,frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame bs) b
      have ht := ih (pre++[true,b]) bs (out++[true,b]) (p+1)
      have hbody : Prefix raw bound (2*n+1)
          (cfg 0 driver source (p+1) (pre.length+2) (out++[true,b]) [])
          (cfg 3 driver source (p+(n+1)) (pre.length+2*min (n+1) (b::bs).length)
            (out++Streaming.marks (resize (n+1) (b::bs))++[false]) [decide ((b::bs).length≤n+1)]) := by
        simpa [driver,source,bound,frame,resize,Streaming.marks,List.append_assoc,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
      have hsecond := Prefix.step (by simp [bound,driver]; omega :
          (cfg 1 driver source p (pre.length+1) (out++[true]) []).tapeCells≤bound)
        (by rfl : raw.halted (1 : Fin 4)=false)
        (second_step driver source (out++[true]) p (pre.length+1) true b (by simpa using hb) (by simp))
        (by simpa [List.append_assoc,Nat.add_assoc] using hbody)
      have hfirst := Prefix.step (by simp [bound,driver]; omega :
          (cfg 0 driver source p pre.length out []).tapeCells≤bound)
        (by rfl : raw.halted (0 : Fin 4)=false)
        (first_step driver source out p pre.length true hd hs) (by simpa using hsecond)
      simpa [driver,source,bound,Nat.mul_add,Nat.add_assoc] using hfirst

theorem raw_run (width : ℕ) (bits : List Bool) :
    ∃ r : ExecutionReceipt 4 4,
      run raw (2*width+1) ![List.replicate width true,frame bits,[],[]]=some r ∧
      r.final.tapes=![List.replicate width true,frame bits,frame (resize width bits),[decide (bits.length≤width)]] ∧
      r.steps=2*width+1 := by
  obtain ⟨r,hr,hf,hs,_⟩ := (process_prefix [] bits [] 0 width).run (by rfl) (by simp; omega)
  have hi : initialConfiguration raw ![List.replicate width true,frame bits,[],[]]=
      cfg 0 (List.replicate width true) (frame bits) 0 0 [] [] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  refine ⟨r,?_,?_,hs⟩
  · simpa [run,hi] using hr
  · rw [hf]
    funext i; fin_cases i <;> simp [cfg]
    simpa [frame] using (Streaming.frame_append (resize width bits) []).symm

def machine : Machine 5 6 := Rewind.machine raw
def input (width : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (4+1) => List Bool)
    ![List.replicate width true,frame bits,[],[]] (fun _ : Fin 1 => [])

theorem normalize_run (width : ℕ) (bits : List Bool) :
    ∃ r : ExecutionReceipt 5 6,
      run machine (4*width+4) (input width bits)=some r ∧
      r.final.tapes 0=List.replicate width true ∧ r.final.tapes 1=frame bits ∧
      r.final.tapes 2=frame (resize width bits) ∧ r.final.tapes 3=[decide (bits.length≤width)] ∧
      r.final.tapes 4=List.replicate (2*width+1) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*width+4 := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run width bits
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  refine ⟨r,?_,?_,?_,?_,?_,by simpa [hs] using hcounter,hh,by omega⟩
  · have htime : 2*base.steps+2=4*width+4 := by omega
    rw [htime] at hr
    exact hr
  · simpa [hf] using ht 0
  · simpa [hf] using ht 1
  · simpa [hf] using ht 2
  · simpa [hf] using ht 3

end NearCubicWires.RepairOrdinary.ClockNormalize
