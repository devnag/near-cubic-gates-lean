import Proof.Hierarchy.CompetitorWitnessCapSteps

/-! One exact sixteen-input-bit block, or early rejection at the input
delimiter. No theorem assumes the witness suffix has bounded length. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_pair (k : ℕ) (hk : k<15) (pre tail w : List Bool) (bit : Bool) (pw : ℕ) :
    Timed machine 2 (cfg (marker k (by omega)) (pre++frame (bit::tail)) w pre.length pw)
      (cfg (marker (k+1) (by omega)) (pre++frame (bit::tail)) w (pre.length+2) pw) := by
  have h1 := input_step k (by omega) pre (bit::frame tail) w pw
  have h2 := payload_step k hk (pre++frame (bit::tail)) w (pre.length+1) pw
  have hh1 : machine.halted (marker k (by omega))=false := by simp [machine,marker]; omega
  have hh2 : machine.halted (payload k (by omega))=false := by simp [machine,payload]; omega
  exact (Timed.single hh1 h1).trans (Timed.single hh2 h2)

theorem input_last (pre tail w : List Bool) (bit : Bool) (pw : ℕ) :
    Timed machine 2 (cfg (marker 15 (by decide)) (pre++frame (bit::tail)) w pre.length pw)
      (cfg 0 (pre++frame (bit::tail)) w (pre.length+2) (pw+1)) := by
  have h1 := input_step 15 (by decide) pre (bit::frame tail) w pw
  have h2 := payload_last (pre++frame (bit::tail)) w (pre.length+1) pw
  exact (Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)

theorem short_block (bits pre w : List Bool) (k pw : ℕ) (hk : k+bits.length<16) :
    Timed machine (2*bits.length+1)
      (cfg (marker k (by omega)) (pre++frame bits) w pre.length pw)
      (cfg 33 (pre++frame bits) w (pre.length+2*bits.length) pw [false]) := by
  induction bits generalizing k pre with
  | nil =>
    have hh : machine.halted (marker k (by omega))=false := by simp [machine,marker]; omega
    simpa [frame] using Timed.single hh (reject_step k (by omega) pre w pw)
  | cons bit bits ih =>
    have hp := input_pair k (by simp only [List.length_cons] at hk; omega) pre bits w bit pw
    have hi := ih (pre++[true,bit]) (k+1) (by simp only [List.length_cons] at hk; omega)
    have he : (pre++[true,bit])++frame bits=pre++frame (bit::bits) := by simp [frame,List.append_assoc]
    rw [he,show (pre++[true,bit]).length=pre.length+2 by simp] at hi
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp.trans hi

theorem full_block (bits pre tail w : List Bool) (k pw : ℕ)
    (hk : k<16) (hlen : k+bits.length=16) :
    Timed machine (2*bits.length)
      (cfg (marker k hk) (pre++frame (bits++tail)) w pre.length pw)
      (cfg 0 (pre++frame (bits++tail)) w (pre.length+2*bits.length) (pw+1)) := by
  induction bits generalizing k pre with
  | nil => simp at hlen; omega
  | cons bit bits ih =>
    cases bits with
    | nil =>
      have he : k=15 := by simp at hlen; omega
      subst k
      simpa using input_last pre tail w bit pw
    | cons bit' bits =>
      have hlt : k<15 := by simp only [List.length_cons] at hlen; omega
      have hp := input_pair k hlt pre ((bit'::bits)++tail) w bit pw
      have hi := ih (pre++[true,bit]) (k+1) (by omega)
        (by simp only [List.length_cons] at hlen ⊢; omega)
      have he : (pre++[true,bit])++frame ((bit'::bits)++tail)=pre++frame ((bit::bit'::bits)++tail) := by
        simp [frame,List.append_assoc]
      rw [he,show (pre++[true,bit]).length=pre.length+2 by simp] at hi
      have ht : 2+2*(bit'::bits).length=2*(bit::bit'::bits).length := by simp; omega
      have hpw : (pre.length+2)+2*(bit'::bits).length=pre.length+2*(bit::bit'::bits).length := by simp; omega
      have h := hp.trans hi
      rw [ht,hpw] at h
      exact h

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
