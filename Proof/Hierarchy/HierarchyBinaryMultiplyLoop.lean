import Proof.Hierarchy.HierarchyBinaryMultiplyControl

/-! Executed loop over the actual framed factor bits. Its numerical invariant
names the accumulator and the current doubled multiplicand; neither the
factor nor a multiplication result is supplied as a machine instruction. -/
namespace NearCubicWires.RepairOrdinary.HierarchyMultiply
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reader_dispatch (s : Store) (w : ℕ) (pre bits : List Bool) (bit : Bool) :
    Timed machine 3 (atNode 0 s w pre.length (pre++frame (bit::bits)))
      (atNode (if bit then 1 else 3) s w (pre.length+2) (pre++frame (bit::bits))) := by
  have hb := RecoveryCalls.body_timed sizes programs 0 next 0 (reader_bit s w pre bits bit)
  have he := RecoveryCalls.return_step sizes programs 0 next 0 (if bit then 1 else 3)
    (readerConfig (if bit then 3 else 2) s w (pre.length+2) (pre++frame (bit::bits)))
    (by cases bit <;> rfl) (by cases bit <;> rfl)
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem reader_stop (s : Store) (w : ℕ) (pre : List Bool) :
    Timed machine 2 (atNode 0 s w pre.length (pre++frame []))
      (RecoveryCalls.stopped sizes (heads pre.length) (s.tapes w (pre++frame []))) := by
  have hb := RecoveryCalls.body_timed sizes programs 0 next 0 (reader_end s w pre)
  have he := RecoveryCalls.stop_step sizes programs 0 next 0
    (readerConfig 4 s w pre.length (pre++frame [])) (by rfl) (by rfl)
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

def round (w : ℕ) (bit : Bool) (s : Store) : Store :=
  shiftedBoth (doubled (if bit then accumulated (added s w) else s) w)
def roundTime (w : ℕ) (bit : Bool) : ℕ := if bit then 32*w+40 else 20*w+26

theorem round_calls (s : Store) (w : ℕ) (pre bits : List Bool) (bit : Bool)
    (hadd : bit=true → s.left+s.accumulator<2^w)
    (hdbl : s.left+s.duplicate<2^w)
    (hsum : s.sum.length≤2*w+1) (hback : s.doubled.length≤2*w+1) :
    Timed machine (roundTime w bit)
      (atNode 0 s w pre.length (pre++frame (bit::bits)))
      (atNode 0 (round w bit s) w (pre.length+2) (pre++frame (bit::bits))) := by
  have hr := reader_dispatch s w pre bits bit
  cases bit with
  | false =>
    have hd := shift_calls s w (pre.length+2) (pre++frame (false::bits)) hdbl hback
    have he : 3+(20*w+23)=20*w+26 := by omega
    simpa only [round,roundTime,Bool.false_eq_true,↓reduceIte,he] using hr.trans hd
  | true =>
    have ha := accumulation_calls s w (pre.length+2) (pre++frame (true::bits)) (hadd rfl) hsum
    have hd := shift_calls (accumulated (added s w)) w (pre.length+2) (pre++frame (true::bits)) hdbl hback
    have he : (3+(12*w+14))+(20*w+23)=32*w+40 := by omega
    simpa only [round,roundTime,↓reduceIte,he] using (hr.trans ha).trans hd

theorem round_values (w : ℕ) (bit : Bool) (s : Store) (hdup : s.duplicate=s.left) :
    (round w bit s).left=2*s.left ∧
    (round w bit s).duplicate=(round w bit s).left ∧
    (round w bit s).accumulator=s.accumulator+bit.toNat*s.left := by
  cases bit <;> simp [round,shiftedBoth,doubled,accumulated,added,hdup] <;> omega

theorem round_backing (w : ℕ) (bit : Bool) (s : Store) (hs : s.sum.length≤2*w+1) :
    (round w bit s).sum.length≤2*w+1 ∧ (round w bit s).doubled.length≤2*w+1 := by
  cases bit <;> simp [round,shiftedBoth,doubled,accumulated,added,hs]

def finish (w : ℕ) (s : Store) : List Bool → Store
  | [] => s
  | b::bs => finish w (round w b s) bs
def time (w : ℕ) : List Bool → ℕ
  | [] => 2
  | b::bs => roundTime w b+time w bs

theorem time_bound (w : ℕ) (bits : List Bool) : time w bits≤bits.length*(32*w+40)+2 := by
  induction bits with
  | nil => simp [time]
  | cons b bs ih =>
    have hr : roundTime w b≤32*w+40 := by cases b <;> simp [roundTime]; omega
    simp only [time,List.length_cons,Nat.add_mul]
    omega

theorem loop (w : ℕ) (pre bits : List Bool) (s : Store)
    (hdup : s.duplicate=s.left) (hsum : s.sum.length≤2*w+1) (hback : s.doubled.length≤2*w+1)
    (hacc : s.accumulator+s.left*value bits<2^w) (hshift : s.left*2^bits.length<2^w) :
    Timed machine (time w bits) (atNode 0 s w pre.length (pre++frame bits))
      (RecoveryCalls.stopped sizes (heads (pre.length+2*bits.length))
        ((finish w s bits).tapes w (pre++frame bits))) := by
  induction bits generalizing pre s with
  | nil => simpa only [time,finish,List.length_nil,Nat.mul_zero,Nat.add_zero] using reader_stop s w pre
  | cons b bs ih =>
    have hp : 1≤2^bs.length := Nat.one_le_pow _ _ (by decide)
    have hd : s.left+s.duplicate<2^w := by
      simp only [List.length_cons,pow_succ] at hshift
      rw [hdup]
      nlinarith
    have ha : b=true → s.left+s.accumulator<2^w := by
      intro hb
      rw [hb] at hacc
      simp only [value,Bool.toNat_true] at hacc
      nlinarith
    have hv := round_values w b s hdup
    have hb := round_backing w b s hsum
    have hacc' : (round w b s).accumulator+(round w b s).left*value bs<2^w := by
      rw [hv.1,hv.2.2]
      simpa only [value,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc]
        using hacc
    have hshift' : (round w b s).left*2^bs.length<2^w := by
      rw [hv.1]
      simpa only [List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hshift
    have ht := ih (pre++[true,b]) (round w b s) hv.2.1 hb.1 hb.2 hacc' hshift'
    have hr := round_calls s w pre bs b ha hd hsum hback
    have hsource : (pre++[true,b])++frame bs=pre++frame (b::bs) := by simp [frame,List.append_assoc]
    have hpos : (pre++[true,b]).length=pre.length+2 := by simp
    rw [hsource,hpos] at ht
    have h := hr.trans ht
    have hend : pre.length+2+2*bs.length=pre.length+2*(b::bs).length := by simp; omega
    simpa only [time,finish,hend] using h

theorem finish_values (w : ℕ) (bits : List Bool) (s : Store) (hdup : s.duplicate=s.left) :
    (finish w s bits).left=s.left*2^bits.length ∧
    (finish w s bits).duplicate=(finish w s bits).left ∧
    (finish w s bits).accumulator=s.accumulator+s.left*value bits := by
  induction bits generalizing s with
  | nil => simp [finish,hdup,value]
  | cons b bs ih =>
    have hr := round_values w b s hdup
    have ht := ih (round w b s) hr.2.1
    simp only [finish]
    refine ⟨?_,ht.2.1,?_⟩
    · rw [ht.1,hr.1]
      simp only [List.length_cons,pow_succ]
      ring
    · rw [ht.2.2,hr.1,hr.2.2]
      simp only [value]
      ring

theorem multiply_run (w a : ℕ) (bits : List Bool) (sum doubled : List Bool)
    (hsum : sum.length≤2*w+1) (hback : doubled.length≤2*w+1)
    (hfit : a*2^bits.length<2^w) :
    ∃ r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (bits.length*(32*w+40)+2)
        (({left:=a,duplicate:=a,accumulator:=0,sum:=sum,doubled:=doubled} : Store).tapes w (frame bits))=some r ∧
      r.final.tapes 3=frame (binary w (a*value bits)) ∧
      r.final.tapes 0=frame bits ∧ r.final.heads=heads (2*bits.length) ∧
      r.steps≤bits.length*(32*w+40)+2 := by
  let s : Store := {left:=a,duplicate:=a,accumulator:=0,sum:=sum,doubled:=doubled}
  have hacc : s.accumulator+s.left*value bits<2^w := by
    have hv := Nat.mul_le_mul_left a (value_lt bits).le
    dsimp [s]
    omega
  have hp := loop w [] bits s rfl hsum hback hacc hfit
  obtain ⟨r,hr,hf,hs⟩ := hp.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb := time_bound w bits
  have hm := runFrom_moreFuel machine (time w bits) (bits.length*(32*w+40)+2-time w bits) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  have hi : atNode 0 s w 0 (frame bits)=initialConfiguration machine (s.tapes w (frame bits)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  simp only [List.length_nil,List.nil_append] at hm
  rw [hi] at hm
  have hv := (finish_values w bits s rfl).2.2
  refine ⟨r,hm,?_,?_,?_,hs.le.trans hb⟩
  · rw [hf]
    change frame (binary w (finish w s bits).accumulator)=_
    rw [hv]
    simp [s]
  · rw [hf]
    rfl
  · rw [hf]
    simp only [RecoveryCalls.stopped,List.length_nil,Nat.zero_add]

end NearCubicWires.RepairOrdinary.HierarchyMultiply
