import Proof.PCP.ProjectionNormalizationFieldEquality
import Proof.Amplification.RecoveryPrefixCompare

/-! Numeric equality for the canonical reencoder. A shorter frame waits at
its delimiter and supplies zero high bits. The scan proof reuses the existing
framed field equality layout and pays the same complete return scan. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NumericEquality
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev State := Sum Bool (Sum (Bool×Bool×Bool) Unit)
noncomputable def code : State ≃ Fin (Fintype.card State) := Fintype.equivFin _
noncomputable def scanCode (same : Bool) := code (.inl same)
noncomputable def bitCode (same left right : Bool) := code (.inr (.inl (same,left,right)))
noncomputable def finalCode := code (.inr (.inr ()))
noncomputable def action (q : Fin (Fintype.card State)) (left right : Bool) (out : Option Bool := none) :
    Action 3 (Fintype.card State) :=
  ⟨q,![none,none,out],![if left then .right else .stay,if right then .right else .stay,.stay]⟩
noncomputable def machine : Machine 3 (Fintype.card State) where
  descriptionBits := 0
  start := scanCode true
  halted := fun q => match code.symm q with | .inr (.inr _) => true | _ => false
  rule := fun q bits => match code.symm q with
    | .inl same => if bits 0 || bits 1 then
        some (action (bitCode same (bits 0) (bits 1)) (bits 0) (bits 1))
      else some (action finalCode true true (some (bits 2 && same)))
    | .inr (.inl (same,left,right)) =>
        some (action (scanCode (same && decide (bits 0=bits 1))) left right)
    | .inr (.inr _) => none
def cfg (q : Fin (Fintype.card State)) (left right : List Bool) (lp rp : ℕ) (flag : Bool) :
    Configuration 3 (Fintype.card State) := ⟨q,![lp,rp,0],![left,right,[flag]]⟩

theorem marker_step (same l r old : Bool) (left right : List Bool) (lp rp : ℕ)
    (hl : readTapeBit left lp=l) (hr : readTapeBit right rp=r) (hactive : (l||r)=true) :
    step machine (cfg (scanCode same) left right lp rp old)=
      some (cfg (bitCode same l r) left right (lp+l.toNat) (rp+r.toNat) old) := by
  have ha : l=true ∨ r=true := by cases l <;> cases r <;> simp_all
  simp [step,machine,cfg,scanCode,Configuration.scanned,hl,hr,ha]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> cases l <;> cases r <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem payload_step (same l r a b old : Bool) (left right : List Bool) (lp rp : ℕ)
    (hl : readTapeBit left lp=a) (hr : readTapeBit right rp=b) :
    step machine (cfg (bitCode same l r) left right lp rp old)=
      some (cfg (scanCode (same && decide (a=b))) left right (lp+l.toNat) (rp+r.toNat) old) := by
  simp [step,machine,cfg,bitCode,Configuration.scanned,hl,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> cases l <;> cases r <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem finish_step (same old : Bool) (left right : List Bool) (lp rp : ℕ)
    (hl : readTapeBit left lp=false) (hr : readTapeBit right rp=false) :
    step machine (cfg (scanCode same) left right lp rp old)=
      some (cfg finalCode left right (lp+1) (rp+1) (old&&same)) := by
  have ho : readTapeBit [old] 0=old := rfl
  simp [step,machine,cfg,scanCode,Configuration.scanned,hl,hr,ho]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem scan_halted (same : Bool) : machine.halted (scanCode same)=false := by simp [machine,scanCode]
theorem bit_halted (same left right : Bool) : machine.halted (bitCode same left right)=false := by simp [machine,bitCode]
theorem final_halted : machine.halted finalCode=true := by simp [machine,finalCode]

theorem scan_prefix (left right preLeft preRight tailLeft tailRight : List Bool) (old same : Bool) :
    Timed machine (2*max left.length right.length+1)
      (cfg (scanCode same) (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        preLeft.length preRight.length old)
      (cfg finalCode (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        (preLeft.length+2*left.length+1) (preRight.length+2*right.length+1)
        (old && same && decide (value left=value right))) := by
  induction left generalizing right preLeft preRight same with
  | nil =>
    induction right generalizing preRight same with
    | nil =>
      have h := Timed.single (scan_halted same)
        (finish_step same old (preLeft++frame []++tailLeft) (preRight++frame []++tailRight)
          preLeft.length preRight.length
          (by simpa [frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preLeft tailLeft false)
          (by simpa [frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preRight tailRight false))
      simpa using h
    | cons b right ih =>
      let ls := preLeft++frame []++tailLeft
      let rs := preRight++frame (b::right)++tailRight
      have hl : readTapeBit ls preLeft.length=false := by
        simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preLeft tailLeft false
      have hr : readTapeBit rs preRight.length=true := by
        simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preRight (b::frame right++tailRight) true
      have hp : readTapeBit rs (preRight.length+1)=b := by
        simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using
          Streaming.read_append (preRight++[true]) (frame right++tailRight) b
      have h1 := Timed.single (scan_halted same) (marker_step same false true old ls rs _ _ hl hr (by rfl))
      have h2 := Timed.single (bit_halted same false true) (payload_step same false true false b old ls rs _ _ hl hp)
      simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at h1 h2
      have ht := ih (preRight++[true,b]) (same && decide (false=b))
      have htime : 1+(1+(2*right.length+1))=2*(b::right).length+1 := by simp; omega
      have hm : preRight.length+1+1=(preRight++[true,b]).length := by simp
      have he : (preRight++[true,b])++frame right++tailRight=rs := by
        simp [rs,frame,RepairOrdinary.frame,List.append_assoc]
      rw [he] at ht
      have h2' : Timed machine 1
          (cfg (bitCode same false true) ls rs preLeft.length (preRight.length+1) old)
          (cfg (scanCode (same && decide (false=b))) ls rs preLeft.length (preRight++[true,b]).length old) := by
        simpa only [hm] using h2
      have hall := h1.trans (h2'.trans ht)
      have heq : (old && (same && decide (false=b)) && decide (value []=value right))=
          (old && same && decide (value []=value (b::right))) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,decide_eq_true_eq,value]
        cases b <;> simp <;> omega
      rw [heq] at hall
      have htime' : 1+(1+(2*max ([] : List Bool).length right.length+1))=2*max ([] : List Bool).length (b::right).length+1 := by simp; omega
      rw [htime'] at hall
      simpa [ls,rs,List.length_append,List.length_cons,frame_length,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,htime] using hall
  | cons a left ih =>
    cases right with
    | nil =>
      let ls := preLeft++frame (a::left)++tailLeft
      let rs := preRight++frame []++tailRight
      have hl : readTapeBit ls preLeft.length=true := by
        simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preLeft (a::frame left++tailLeft) true
      have hr : readTapeBit rs preRight.length=false := by
        simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preRight tailRight false
      have hp : readTapeBit ls (preLeft.length+1)=a := by
        simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using
          Streaming.read_append (preLeft++[true]) (frame left++tailLeft) a
      have h1 := Timed.single (scan_halted same) (marker_step same true false old ls rs _ _ hl hr (by rfl))
      have h2 := Timed.single (bit_halted same true false) (payload_step same true false a false old ls rs _ _ hp hr)
      simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at h1 h2
      have ht := ih [] (preLeft++[true,a]) preRight (same && decide (a=false))
      have hm : preLeft.length+1+1=(preLeft++[true,a]).length := by simp
      have he : (preLeft++[true,a])++frame left++tailLeft=ls := by
        simp [ls,frame,RepairOrdinary.frame,List.append_assoc]
      rw [he] at ht
      have h2' : Timed machine 1
          (cfg (bitCode same true false) ls rs (preLeft.length+1) preRight.length old)
          (cfg (scanCode (same && decide (a=false))) ls rs (preLeft++[true,a]).length preRight.length old) := by
        simpa only [hm] using h2
      have hall := h1.trans (h2'.trans ht)
      have heq : (old && (same && decide (a=false)) && decide (value left=value []))=
          (old && same && decide (value (a::left)=value [])) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,decide_eq_true_eq,value]
        cases a <;> simp
      rw [heq] at hall
      have htime' : 1+(1+(2*max left.length ([] : List Bool).length+1))=2*max (a::left).length ([] : List Bool).length+1 := by simp; omega
      rw [htime'] at hall
      simpa [ls,rs,List.length_append,List.length_cons,frame_length,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall
    | cons b right =>
      let ls := preLeft++frame (a::left)++tailLeft
      let rs := preRight++frame (b::right)++tailRight
      have hl : readTapeBit ls preLeft.length=true := by
        simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preLeft (a::frame left++tailLeft) true
      have hr : readTapeBit rs preRight.length=true := by
        simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preRight (b::frame right++tailRight) true
      have hla : readTapeBit ls (preLeft.length+1)=a := by
        simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append (preLeft++[true]) (frame left++tailLeft) a
      have hrb : readTapeBit rs (preRight.length+1)=b := by
        simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append (preRight++[true]) (frame right++tailRight) b
      have h1 := Timed.single (scan_halted same) (marker_step same true true old ls rs _ _ hl hr (by rfl))
      have h2 := Timed.single (bit_halted same true true) (payload_step same true true a b old ls rs _ _ hla hrb)
      simp only [Bool.toNat_true] at h1 h2
      have ht := ih right (preLeft++[true,a]) (preRight++[true,b]) (same && decide (a=b))
      have hml : preLeft.length+1+1=(preLeft++[true,a]).length := by simp
      have hmr : preRight.length+1+1=(preRight++[true,b]).length := by simp
      have hel : (preLeft++[true,a])++frame left++tailLeft=ls := by simp [ls,frame,RepairOrdinary.frame,List.append_assoc]
      have her : (preRight++[true,b])++frame right++tailRight=rs := by simp [rs,frame,RepairOrdinary.frame,List.append_assoc]
      rw [hel,her] at ht
      have h2' : Timed machine 1
          (cfg (bitCode same true true) ls rs (preLeft.length+1) (preRight.length+1) old)
          (cfg (scanCode (same && decide (a=b))) ls rs (preLeft++[true,a]).length (preRight++[true,b]).length old) := by
        simpa only [hml,hmr] using h2
      have hall := h1.trans (h2'.trans ht)
      have heq : (old && (same && decide (a=b)) && decide (value left=value right))=(old && same && decide (value (a::left)=value (b::right))) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,decide_eq_true_eq,value]
        cases a <;> cases b <;> simp <;> omega
      rw [heq] at hall
      have htime : 1+(1+(2*max left.length right.length+1))=2*max (a::left).length (b::right).length+1 := by
        simp only [List.length_cons]
        omega
      rw [htime] at hall
      simpa [ls,rs,List.length_append,List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem equality_run (left right preLeft preRight tailLeft tailRight : List Bool) (old : Bool) :
    ∃ r,runFrom machine (2*max left.length right.length+1)
      (cfg machine.start (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        preLeft.length preRight.length old)=some r ∧
      r.final=cfg finalCode (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        (preLeft.length+2*left.length+1) (preRight.length+2*right.length+1) (old && decide (value left=value right)) ∧
      r.steps=2*max left.length right.length+1 := by
  have h := scan_prefix left right preLeft preRight tailLeft tailRight old true
  simp only [Bool.and_true] at h
  exact h.run final_halted

noncomputable def readyMachine := Rewind.machine machine

theorem equality_ready (left right tailLeft tailRight : List Bool) (old : Bool) (capacity : ℕ) :
    ReadyRun readyMachine (4*max left.length right.length+4)
      ![frame left++tailLeft,frame right++tailRight,[old],List.replicate capacity false]
      ![frame left++tailLeft,frame right++tailRight,[old && decide (value left=value right)],
        List.replicate (max capacity (2*max left.length right.length+1)) false] := by
  obtain ⟨base,hb,hf,hs⟩ := equality_run left right [] [] tailLeft tailRight old
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hb hf
  have hi : cfg machine.start (frame left++tailLeft) (frame right++tailRight) 0 0 old=
      initialConfiguration machine ![frame left++tailLeft,frame right++tailRight,[old]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hb
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace machine _ _ base hb capacity
  have he : 2*base.steps+2=4*max left.length right.length+4 := by rw [hs]; omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hf,cfg] using ht 1
    · simpa [hf,cfg] using ht 2
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.CloseoutWitness.NumericEquality
