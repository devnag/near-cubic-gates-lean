import Proof.Supplier.RowBinLiftWidth
import Proof.MachineModel.ClockNormalize
import Proof.MachineModel.OrdinaryMaskedReset

/-! One actual radix digit for the row stack. A physical unary width drives
simultaneous positive/negative block emission. Magnitudes are padded in bits,
never expanded into unary. The two output cursors remain at their delimiters. -/
namespace NearCubicWires.RepairOrdinary.RowPowerBlock
open LocalBitMultitape Streaming RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def part (negative sign bit : Bool) : Bool := bit && (sign==negative)
def digits (negative sign : Bool) (bits : List Bool) := bits.map (part negative sign)
def cfg (state : Fin 4) (driver source : List Bool) (p q : ℕ)
    (sign : Bool) (positive negative : List Bool) : Configuration 5 4 :=
  ⟨state,![p,q,0,positive.length,negative.length],![driver,source,[sign],positive,negative]⟩
def first (copy : Bool) : Action 5 4 :=
  ⟨if copy then 1 else 2,![none,none,none,some true,some true],
    ![.stay,if copy then .right else .stay,.stay,.right,.right]⟩
def second (copy sign bit : Bool) : Action 5 4 :=
  ⟨0,![none,none,none,some (part false sign bit),some (part true sign bit)],
    ![.right,if copy then .right else .stay,.stay,.right,.right]⟩
def machine : Machine 5 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bs => if q.val=0 then some
      (if bs 0 then first (bs 1)
       else ⟨3,![none,none,none,some false,some false],fun _ => .stay⟩)
    else if q.val=1 then some (second true (bs 2) (bs 1))
    else if q.val=2 then some (second false (bs 2) false) else none

theorem first_step (driver source positive negative : List Bool) (p q : ℕ) (sign copy : Bool)
    (hd : readTapeBit driver p=true) (hs : readTapeBit source q=copy) :
    step machine (cfg 0 driver source p q sign positive negative)=
      some (cfg (if copy then 1 else 2) driver source p
        (q+if copy then 1 else 0) sign (positive++[true]) (negative++[true])) := by
  cases copy <;> simp [step,machine,cfg,Configuration.scanned,hd,hs]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction,first,HeadMove.apply,Streaming.write_append])

theorem second_step (driver source positive negative : List Bool) (p q : ℕ) (sign copy bit : Bool)
    (hb : copy=true → readTapeBit source q=bit) (hz : copy=false → bit=false) :
    step machine (cfg (if copy then 1 else 2) driver source p q sign positive negative)=
      some (cfg 0 driver source (p+1) (q+if copy then 1 else 0) sign
        (positive++[part false sign bit]) (negative++[part true sign bit])) := by
  have hsign : readTapeBit [sign] 0=sign := rfl
  cases copy <;> simp_all [step,machine,cfg,Configuration.scanned]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction,second,HeadMove.apply,Streaming.write_append])

theorem scan (pre bits suffix positive negative : List Bool) (p n : ℕ) (sign : Bool) :
    Timed machine (2*n)
      (cfg 0 (List.replicate (p+n) true) (pre++frame bits++suffix) p pre.length sign positive negative)
      (cfg 0 (List.replicate (p+n) true) (pre++frame bits++suffix) (p+n)
        (pre.length+2*min n bits.length) sign
        (positive++marks (digits false sign (ClockNormalize.resize n bits)))
        (negative++marks (digits true sign (ClockNormalize.resize n bits)))) := by
  induction n generalizing pre bits p positive negative with
  | zero => simpa [ClockNormalize.resize,digits,marks] using
      (Timed.refl machine (cfg 0 (List.replicate p true) (pre++frame bits++suffix) p pre.length sign positive negative))
  | succ n ih =>
    have hd : readTapeBit (List.replicate (p+(n+1)) true) p=true := by simp [readTapeBit]
    cases bits with
    | nil =>
      have hs : readTapeBit (pre++frame []++suffix) pre.length=false := by
        simpa [frame,List.append_assoc] using Streaming.read_append pre suffix false
      have h0 := Timed.single (by rfl) (first_step _ _ positive negative p pre.length sign false hd hs)
      have h1 := Timed.single (by rfl) (second_step (List.replicate (p+(n+1)) true) (pre++frame []++suffix)
        (positive++[true]) (negative++[true]) p pre.length sign false false (by simp) (by simp))
      have h := ih pre [] (positive++[true,false]) (negative++[true,false]) (p+1)
      have hj := (h0.trans (by simpa [part] using h1)).trans (by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
      simpa [ClockNormalize.resize,digits,marks,part,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using hj
    | cons b bs =>
      have hs : readTapeBit (pre++frame (b::bs)++suffix) pre.length=true := by
        simpa [frame,List.append_assoc] using Streaming.read_append pre (b::(frame bs++suffix)) true
      have hb : readTapeBit (pre++frame (b::bs)++suffix) (pre.length+1)=b := by
        simpa [frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame bs++suffix) b
      have h0 := Timed.single (by rfl) (first_step _ _ positive negative p pre.length sign true hd hs)
      have h1 := Timed.single (by rfl) (second_step (List.replicate (p+(n+1)) true) (pre++frame (b::bs)++suffix)
        (positive++[true]) (negative++[true]) p (pre.length+1) sign true b (by simpa using hb) (by simp))
      have h := ih (pre++[true,b]) bs
        (positive++[true,part false sign b]) (negative++[true,part true sign b]) (p+1)
      have hj := (h0.trans (by simpa [List.append_assoc] using h1)).trans (by
        simpa [frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
      simpa [ClockNormalize.resize,digits,marks,frame,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using hj

def final (driver source : List Bool) (p q : ℕ) (sign : Bool)
    (positive negative : List Bool) : Configuration 5 4 :=
  ⟨3,![p,q,0,positive.length,negative.length],
    ![driver,source,[sign],positive++[false],negative++[false]]⟩

theorem stop_step (driver source positive negative : List Bool) (p q : ℕ) (sign : Bool)
    (hd : readTapeBit driver p=false) :
    step machine (cfg 0 driver source p q sign positive negative)=
      some (final driver source p q sign positive negative) := by
  simp [step,machine,cfg,Configuration.scanned,hd]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,final,Streaming.write_append]

theorem append_run (w : ℕ) (bits suffix positive negative : List Bool) (sign : Bool) :
    ∃ r,runFrom machine (2*w+1)
      (cfg 0 (List.replicate w true) (frame bits++suffix) 0 0 sign positive negative)=some r ∧
      r.final=final (List.replicate w true) (frame bits++suffix) w (2*min w bits.length) sign
        (positive++marks (digits false sign (ClockNormalize.resize w bits)))
        (negative++marks (digits true sign (ClockNormalize.resize w bits))) ∧ r.steps=2*w+1 := by
  have h := scan [] bits suffix positive negative 0 w sign
  simp only [List.nil_append,Nat.zero_add,List.length_nil] at h
  have hs := stop_step (List.replicate w true) (frame bits++suffix)
    (positive++marks (digits false sign (ClockNormalize.resize w bits)))
    (negative++marks (digits true sign (ClockNormalize.resize w bits)))
    w (2*min w bits.length) sign (by simp [readTapeBit])
  exact (h.trans (Timed.single (by rfl) hs)).run (by rfl)

end NearCubicWires.RepairOrdinary.RowPowerBlock
