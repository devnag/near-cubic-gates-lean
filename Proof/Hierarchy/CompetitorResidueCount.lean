import Proof.Hierarchy.CompetitorRawScalarAppend

/-! The paper's integer score congruence implies the exact natural count
returned by the paid signed residue/crop consumer, with Q=K+1 available at
the caller. A negative signed score is handled by integer congruence. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSignedResidue
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem residue_int (w q a b : ℕ) (hb : b<2^w) (hq : q≤w) :
    (residue w q a b : ℤ)=((a : ℤ)-b)%(2:ℤ)^q := by
  have hle : b≤a+2^w := by omega
  have hd : (2:ℤ)^q∣(2:ℤ)^w := pow_dvd_pow 2 hq
  simp only [residue,Int.natCast_mod,Int.natCast_sub hle,Int.natCast_add,Int.natCast_pow]
  change ((a : ℤ)+2^w-b)%(2:ℤ)^q=((a:ℤ)-b)%(2:ℤ)^q
  rw [show (a : ℤ)+2^w-b=(a-b)+2^w by ring,Int.add_emod,Int.emod_eq_zero_of_dvd hd]
  simp

theorem residue_eq_count (w q a b count : ℕ) (hb : b<2^w) (hq : q≤w)
    (hcount : count<2^q) (hcongruent : Int.ModEq ((2:ℤ)^q) ((a:ℤ)-b) count) :
    residue w q a b=count := by
  have hcountZ : (count : ℤ)<(2:ℤ)^q := by exact_mod_cast hcount
  have hz : (residue w q a b : ℤ)=count := by
    rw [residue_int w q a b hb hq]
    have he : ((a:ℤ)-b)%(2:ℤ)^q=(count:ℤ)%(2:ℤ)^q := hcongruent
    exact he.trans (Int.emod_eq_of_lt (by positivity) hcountZ)
  exact_mod_cast hz

theorem count_run (w q a b count : ℕ) (ha : a<2^w) (hb : b<2^w) (hq : q≤w)
    (hcount : count<2^q) (hcongruent : Int.ModEq ((2:ℤ)^q) ((a:ℤ)-b) count) :
    ∃ out,ClockJoin.ReadyRun machine (4*w+4*q+9) (input w q a b) out ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧
      out 4=List.replicate q true ∧ out 5=frame (binary q count) := by
  simpa only [residue_eq_count w q a b count hb hq hcount hcongruent] using residue_run w q a b ha hb hq

end NearCubicWires.RepairOrdinary.CompetitorSignedResidue
