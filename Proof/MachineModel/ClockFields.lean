import Proof.MachineModel.ClockUnaryProduct

/-! One linear pass over the paid dyadic exponent emits the binary cap and
all raw unary event-width drivers. Constant suffixes are ordinary writes. -/
namespace NearCubicWires.RepairOrdinary.ClockFields
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def suffix : Fin 5 → List Bool := ![[],[true,true,false],[true,true,true],
  [true,true,true,true,true,true],[true,true,true,true,true,true,true,true]]
def appendCfg (state : Fin 9) (initial : Fin 5 → List Bool) (k : ℕ) : Configuration 5 9 :=
  ⟨state,fun i => (initial i++(suffix i).take k).length,fun i => initial i++(suffix i).take k⟩
def suffixAction (k : ℕ) (hk : k<8) : Action 5 9 :=
  ⟨⟨k+1,by omega⟩,fun i => (suffix i)[k]?,
    fun i => if ((suffix i)[k]?).isSome then .right else .stay⟩
def tail : Machine 5 9 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==8
  rule := fun s _ => if h : s.val<8 then some (suffixAction s.val h) else none

def space (initial : Fin 5 → List Bool) : ℕ := ∑ i,((initial i).length+(suffix i).length)

theorem append_cells (state : Fin 9) (initial : Fin 5 → List Bool) (k : ℕ) :
    (appendCfg state initial k).tapeCells≤ space initial := by
  unfold Configuration.tapeCells space appendCfg
  apply Finset.sum_le_sum
  intro i _
  simp only [List.length_append,List.length_take]
  omega

theorem write_suffix (pre bits : List Bool) (bit : Bool) :
    writeTapeBit (pre++bits) (pre.length+bits.length) bit=pre++(bits++[bit]) := by
  simpa [List.append_assoc] using Streaming.write_append (pre++bits) bit

-- reason: Exhaust the fixed eight suffix controls and five physical tape labels once.
set_option maxHeartbeats 1000000 in
theorem suffix_step (initial : Fin 5 → List Bool) (k : ℕ) (hk : k<8) :
    step tail (appendCfg ⟨k,by omega⟩ initial k)=
      some (appendCfg ⟨k+1,by omega⟩ initial (k+1)) := by
  interval_cases k <;> simp [step,tail,appendCfg] <;> apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction,suffixAction,suffix,HeadMove.apply,Streaming.write_append])
  all_goals exact write_suffix _ _ _

theorem suffix_prefix (initial : Fin 5 → List Bool) (k remaining : ℕ) (h : k+remaining=8) :
    Prefix tail (space initial) remaining (appendCfg ⟨k,by omega⟩ initial k) (appendCfg 8 initial 8) := by
  induction remaining generalizing k with
  | zero =>
    have hk : k=8 := by omega
    subst k
    exact Prefix.refl _ (append_cells _ _ _)
  | succ remaining ih =>
    have hn : tail.halted (⟨k,by omega⟩ : Fin 9)=false := by simp [tail]; omega
    exact Prefix.step (append_cells _ _ _) hn (suffix_step initial k (by omega)) (ih (k+1) (by omega))

theorem suffix_run (initial : Fin 5 → List Bool) :
    ∃ r : ExecutionReceipt 5 9,
      runFrom tail 8 (appendCfg 0 initial 0)=some r ∧
      r.final=appendCfg 8 initial 8 ∧ r.steps=8 := by
  obtain ⟨r,hr,hf,hs,_⟩ := (suffix_prefix initial 0 8 rfl).run (by rfl) (append_cells _ _ _)
  exact ⟨r,hr,hf,hs⟩

def tapes (r p : ℕ) : Fin 5 → List Bool :=
  ![List.replicate r true,Streaming.marks (List.replicate p false),List.replicate p true,
    List.replicate (2*p) true,List.replicate (2*p) true]
def cfg (state : Fin 3) (r p : ℕ) : Configuration 5 3 :=
  ⟨state,![p,2*p,p,2*p,2*p],tapes r p⟩
def middle (r p : ℕ) : Configuration 5 3 :=
  ⟨1,![p,2*p+1,p+1,2*p+1,2*p+1],
    ![List.replicate r true,Streaming.marks (List.replicate p false)++[true],
      List.replicate p true++[true],List.replicate (2*p) true++[true],
      List.replicate (2*p) true++[true]]⟩
def first : Action 5 3 :=
  ⟨1,![none,some true,some true,some true,some true],![.stay,.right,.right,.right,.right]⟩
def second : Action 5 3 :=
  ⟨0,![none,some false,none,some true,some true],![.right,.right,.stay,.right,.right]⟩
def loop : Machine 5 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==2
  rule := fun s bits => if s.val=0 then
      some (if bits 0 then first else ⟨2,fun _ => none,fun _ => .stay⟩)
    else if s.val=1 then some second else none

@[simp] theorem cfg_cells (state : Fin 3) (r p : ℕ) : (cfg state r p).tapeCells=r+7*p := by
  simp [cfg,tapes,Configuration.tapeCells,Fin.sum_univ_succ,Streaming.marks_length]
  omega
@[simp] theorem middle_cells (r p : ℕ) : (middle r p).tapeCells=r+7*p+4 := by
  simp [middle,Configuration.tapeCells,Fin.sum_univ_succ,Streaming.marks_length]
  omega

theorem write_marks (p : ℕ) (bit : Bool) :
    writeTapeBit (Streaming.marks (List.replicate p false)) (2*p) bit =
      Streaming.marks (List.replicate p false)++[bit] := by
  simpa using Streaming.write_append (Streaming.marks (List.replicate p false)) bit

theorem write_unary (p : ℕ) (bit : Bool) :
    writeTapeBit (List.replicate p true) p bit=List.replicate p true++[bit] := by
  simpa using Streaming.write_append (List.replicate p true) bit

theorem write_marks_one (p : ℕ) (a bit : Bool) :
    writeTapeBit (Streaming.marks (List.replicate p false)++[a]) (2*p+1) bit =
      Streaming.marks (List.replicate p false)++[a,bit] := by
  simpa [List.append_assoc] using Streaming.write_append (Streaming.marks (List.replicate p false)++[a]) bit

theorem write_unary_one (p : ℕ) (a bit : Bool) :
    writeTapeBit (List.replicate p true++[a]) (p+1) bit=List.replicate p true++[a,bit] := by
  simpa [List.append_assoc] using Streaming.write_append (List.replicate p true++[a]) bit

theorem first_step (r p : ℕ) (h : p<r) : step loop (cfg 0 r p)=some (middle r p) := by
  have hr := ClockUnaryProduct.read_unary r p
  simp only [h,decide_true] at hr
  simp [step,loop,cfg,tapes,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,first,middle,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,first,middle,write_marks,write_unary]

theorem second_step (r p : ℕ) : step loop (middle r p)=some (cfg 0 r (p+1)) := by
  have hm : Streaming.marks (List.replicate (p+1) false)=Streaming.marks (List.replicate p false)++[true,false] := by
    rw [List.replicate_add,Streaming.marks_append]
    rfl
  have hrep : List.replicate (2*(p+1)) true=List.replicate (2*p) true++[true,true] := by
    rw [Nat.mul_add,List.replicate_add]
    rfl
  have hp : List.replicate (p+1) true=List.replicate p true++[true] := by rw [List.replicate_add]; rfl
  simp [step,loop,middle]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,second,cfg,HeadMove.apply,Nat.mul_add,Nat.add_assoc]
  · funext i; fin_cases i <;>
      simp [applyAction,second,cfg,tapes,hm,hrep,hp,write_marks_one,write_unary_one]

theorem stop_step (r : ℕ) : step loop (cfg 0 r r)=some (cfg 2 r r) := by
  have hr := ClockUnaryProduct.read_unary r r
  simp only [Nat.lt_irrefl,decide_false] at hr
  simp [step,loop,cfg,tapes,Configuration.scanned,hr]
  rfl

theorem loop_prefix (r p remaining : ℕ) (h : p+remaining=r) :
    Prefix loop (8*r) (2*remaining+1) (cfg 0 r p) (cfg 2 r r) := by
  induction remaining generalizing p with
  | zero =>
    have hp : p=r := by omega
    subst p
    exact Prefix.step (by simp; omega) (by rfl) (stop_step r) (Prefix.refl _ (by simp; omega))
  | succ remaining ih =>
    have ht := ih (p+1) (by omega)
    have hp := Prefix.step (by simp; omega : (middle r p).tapeCells≤8*r)
      (by rfl : loop.halted (1 : Fin 3)=false) (second_step r p) ht
    have result := Prefix.step (by simp; omega : (cfg 0 r p).tapeCells≤8*r)
      (by rfl : loop.halted (0 : Fin 3)=false) (first_step r p (by omega)) hp
    simpa [Nat.mul_add,Nat.add_assoc] using result

theorem loop_run (r : ℕ) :
    ∃ receipt : ExecutionReceipt 5 3,
      run loop (2*r+1) ![List.replicate r true,[],[],[],[]]=some receipt ∧
      receipt.final=cfg 2 r r ∧ receipt.steps=2*r+1 := by
  obtain ⟨receipt,hr,hf,hs,_⟩ := (loop_prefix r 0 r (by omega)).run (by rfl) (by simp; omega)
  have hi : initialConfiguration loop ![List.replicate r true,[],[],[],[]]=cfg 0 r 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact ⟨receipt,by change runFrom loop _ _=some receipt; rw [hi]; exact hr,hf,hs⟩

def raw : Machine 5 12 := Composition.machine loop tail

theorem raw_run (r : ℕ) :
    ∃ receipt : ExecutionReceipt 5 12,
      run raw (2*r+10) ![List.replicate r true,[],[],[],[]]=some receipt ∧
      receipt.final.tapes 0=List.replicate r true ∧
      receipt.final.tapes 1=frame (List.replicate r false++[true]) ∧
      receipt.final.tapes 2=List.replicate (r+3) true ∧
      receipt.final.tapes 3=List.replicate (2*(r+3)) true ∧
      receipt.final.tapes 4=List.replicate (2*(r+3)+2) true ∧ receipt.steps=2*r+10 := by
  obtain ⟨base,hb,hf,hs⟩ := loop_run r
  obtain ⟨last,hl,hlf,hls⟩ := suffix_run (tapes r r)
  have hjump : Composition.restart base.final tail.start=appendCfg 0 (tapes r r) 0 := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.restart,cfg,tapes,appendCfg,Streaming.marks_length]
    · simp [Composition.restart,cfg,appendCfg]
  have hl' : runFrom tail 8 (Composition.restart base.final tail.start)=some last := by rw [hjump]; exact hl
  have hr := Composition.run_join loop tail (2*r+1) 8 _ base last hb hl'
  let receipt := Composition.joinedReceipt base last
  have ht (i : Fin 5) : receipt.final.tapes i=(tapes r r i)++suffix i := by
    fin_cases i <;> simp [receipt,Composition.joinedReceipt,hlf,Composition.rightConfig,appendCfg,suffix]
  refine ⟨receipt,?_,?_,?_,?_,?_,?_,?_⟩
  · have hi : Composition.leftConfig 9 (initialConfiguration loop ![List.replicate r true,[],[],[],[]])=
        initialConfiguration raw ![List.replicate r true,[],[],[],[]] := rfl
    rw [hi] at hr
    simpa [raw,run,Nat.add_assoc] using hr
  · simpa [tapes,suffix] using ht 0
  · have hm := Streaming.frame_append (List.replicate r false) [true]
    simpa [tapes,suffix,frame,List.append_assoc] using (ht 1).trans hm.symm
  · simpa [tapes,suffix,List.replicate_add] using ht 2
  · simpa [tapes,suffix,Nat.mul_add,List.replicate_add] using ht 3
  · simpa [tapes,suffix,Nat.mul_add,List.replicate_add,List.append_assoc] using ht 4
  · simp [receipt,Composition.joinedReceipt,hs,hls,Nat.add_assoc]

def machine : Machine 6 14 := Rewind.machine raw

theorem fields_run (r : ℕ) :
    ∃ receipt : ExecutionReceipt 6 14,
      run machine (4*r+22)
        (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
          ![List.replicate r true,[],[],[],[]] (fun _ : Fin 1 => []))=some receipt ∧
      receipt.final.tapes 0=List.replicate r true ∧
      receipt.final.tapes 1=frame (List.replicate r false++[true]) ∧
      receipt.final.tapes 2=List.replicate (r+3) true ∧
      receipt.final.tapes 3=List.replicate (2*(r+3)) true ∧
      receipt.final.tapes 4=List.replicate (2*(r+3)+2) true ∧
      receipt.final.tapes 5=List.replicate (2*r+10) false ∧
      (∀ i,receipt.final.heads i=0) ∧ receipt.steps=4*r+22 := by
  obtain ⟨base,hb,h0,h1,h2,h3,h4,hs⟩ := raw_run r
  obtain ⟨receipt,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  refine ⟨receipt,?_,(ht 0).trans h0,(ht 1).trans h1,(ht 2).trans h2,(ht 3).trans h3,(ht 4).trans h4,
    by simpa [hs] using hcounter,hh,by omega⟩
  have htime : 2*base.steps+2=4*r+22 := by omega
  rw [htime] at hr
  exact hr

end NearCubicWires.RepairOrdinary.ClockFields
