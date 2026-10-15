import Proof.MachineModel.OrdinarySourceSATLiftInputs

/-! Closed reusable execution of the literal sourceSAT marker. The unary
capacity and original framed query are retained; every reused work tape is
physically cleared, and the exact canonical lifted code is produced. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputSlot : Fin 156 := bank 3 26

theorem capacity_large (b : ℕ) : 268435456*(b+1) ≤ capacity b := by
  have h : b+1 ≤ (b+1)^2 := by nlinarith
  exact Nat.mul_le_mul_left _ h

theorem run (b log : ℕ) (ambient : Fin 156 → List Bool) (bits padding : List Bool)
    (hbits : bits.length ≤ b) (hb : Bounded (capacity b) ambient)
    (hd : ambient 1=List.replicate (capacity b) true)
    (hl : ambient 2=List.replicate log false) (hz : log ≤ capacity b+1)
    (hsource : ambient 0=frame bits++padding) :
    ∃ out : Fin 156 → List Bool,
      ClockJoin.ReadyRun machine (8*capacity b) ambient out ∧
      out outputSlot=ZeroPadding.pad (capacity b) (frame (fourth (value bits)).bits) ∧
      out 0=ambient 0 ∧ out 1=List.replicate (capacity b) true ∧
      out 2=List.replicate (capacity b+1) false ∧ Bounded (capacity b) out := by
  let cap := capacity b
  have hlarge := capacity_large b
  have hc : 3 ≤ cap := by dsimp [cap]; omega
  have hw : (frame bits).length ≤ cap := by rw [frame_length]; dsimp [cap]; omega
  have oneWidth : [true].length ≤ 23*(b+1) := by simp; omega
  have bitsWidth : bits.length ≤ 23*(b+1) := by omega
  have widths := intermediate_le (value bits)
  have firstWidth : (first (value bits)).bits.length ≤ 23*(b+1) :=
    (node_width bits _ widths.1).trans (by omega)
  have secondWidth : (second (value bits)).bits.length ≤ 23*(b+1) :=
    (node_width bits _ widths.2.1).trans (by omega)
  have thirdWidth : (third (value bits)).bits.length ≤ 23*(b+1) :=
    (node_width bits _ widths.2.2).trans (by omega)
  have c0 := capacity_pair b [true] bits oneWidth bitsWidth
  have c1 := capacity_pair b (first (value bits)).bits [true] firstWidth oneWidth
  have c2 := capacity_pair b (second (value bits)).bits [true] secondWidth oneWidth
  have c3 := capacity_pair b [true] (third (value bits)).bits oneWidth thirdWidth
  have pos0 : 0<Nat.pair (value [true]) (value bits) := by
    change 0<first (value bits)
    have := first_two (value bits)
    omega
  have pos1 : 0<Nat.pair (value (first (value bits)).bits) (value [true]) := by
    rw [CanonicalPositiveOutput.nat_bits_value]
    change 0<second (value bits)
    have := second_two (value bits)
    omega
  have pos2 : 0<Nat.pair (value (second (value bits)).bits) (value [true]) := by
    rw [CanonicalPositiveOutput.nat_bits_value]
    change 0<third (value bits)
    have := third_two (value bits)
    omega
  have pos3 : 0<Nat.pair (value [true]) (value (third (value bits)).bits) := by
    rw [CanonicalPositiveOutput.nat_bits_value]
    have ht := third_two (value bits)
    have hp := Nat.right_le_pair 1 (third (value bits))
    change 0<fourth (value bits)
    omega
  let initial := prepared cap (ambient 0) bits
  have hprepare := prepare_path cap log ambient bits padding hb hd hl hz hc hw hsource
  obtain ⟨out0,r0,f0,b0⟩ := pair_focus 0 cap [true] bits initial
    (input_zero cap (ambient 0) bits) pos0 c0
  have f0' : out0 26=ZeroPadding.pad cap (frame (first (value bits)).bits) := f0
  let after0 := install (pairSlots 0) initial out0
  obtain ⟨out1,r1,f1,b1⟩ := pair_focus 1 cap (first (value bits)).bits [true] after0
    (input_one cap (ambient 0) bits _ out0 f0') pos1 c1
  have f1' : out1 26=ZeroPadding.pad cap (frame (second (value bits)).bits) := by
    simpa only [CanonicalPositiveOutput.nat_bits_value,show value [true]=1 from rfl,second] using f1
  let after1 := install (pairSlots 1) after0 out1
  obtain ⟨out2,r2,f2,b2⟩ := pair_focus 2 cap (second (value bits)).bits [true] after1
    (input_two cap (ambient 0) bits _ out0 out1 f1') pos2 c2
  have f2' : out2 26=ZeroPadding.pad cap (frame (third (value bits)).bits) := by
    simpa only [CanonicalPositiveOutput.nat_bits_value,show value [true]=1 from rfl,third] using f2
  let after2 := install (pairSlots 2) after1 out2
  obtain ⟨out3,r3,f3,b3⟩ := pair_focus 3 cap [true] (third (value bits)).bits after2
    (input_three cap (ambient 0) bits _ out0 out1 out2 f2') pos3 c3
  have f3' : out3 26=ZeroPadding.pad cap (frame (fourth (value bits)).bits) := by
    simpa only [CanonicalPositiveOutput.nat_bits_value,show value [true]=1 from rfl,fourth] using f3
  let final := install (pairSlots 3) after2 out3
  have h0 := ready_path 6 7 _ rfl _ initial after0 r0 (by intro q scanned; rfl)
  have h1 := ready_path 7 8 _ rfl _ after0 after1 r1 (by intro q scanned; rfl)
  have h2 := ready_path 8 9 _ rfl _ after1 after2 r2 (by intro q scanned; rfl)
  have whole := finish_path (((hprepare.trans h0).trans h1).trans h2) r3
  have hbound : 2*cap+4*bits.length+46+
      (PCPPairCanonical.budget [true] bits+1)+
      (PCPPairCanonical.budget (first (value bits)).bits [true]+1)+
      (PCPPairCanonical.budget (second (value bits)).bits [true]+1)+
      PCPPairCanonical.budget [true] (third (value bits)).bits+1 ≤ 8*capacity b := by
    dsimp [cap]
    omega
  refine ⟨final,ClockJoin.enlarge _ _ _ _ _ whole hbound,?_,?_,?_,?_,?_⟩
  · change install (pairSlots 3) after2 out3 (pairSlots 3 26)=_
    rw [install_slot _ (pair_injective 3)]
    exact f3'
  · dsimp [final,after2,after1,after0,initial]
    rw [install_pair_small 3 _ _ _ (by decide),install_pair_small 2 _ _ _ (by decide),
      install_pair_small 1 _ _ _ (by decide),install_pair_small 0 _ _ _ (by decide),prepared_source]
  · dsimp [final,after2,after1,after0,initial]
    rw [install_pair_small 3 _ _ _ (by decide),install_pair_small 2 _ _ _ (by decide),
      install_pair_small 1 _ _ _ (by decide),install_pair_small 0 _ _ _ (by decide),prepared_driver]
  · dsimp [final,after2,after1,after0,initial]
    rw [install_pair_small 3 _ _ _ (by decide),install_pair_small 2 _ _ _ (by decide),
      install_pair_small 1 _ _ _ (by decide),install_pair_small 0 _ _ _ (by decide),prepared_log]
  · exact install_bounded _ cap _ _ (install_bounded _ cap _ _ (install_bounded _ cap _ _
      (install_bounded _ cap _ _ (prepared_bounded cap (ambient 0) bits hc hw) b0) b1) b2) b3

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
