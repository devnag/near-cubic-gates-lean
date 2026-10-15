import Proof.Hierarchy.CompetitorSameBucketGroupCalls

/-! The actual copy/mark/signed-add tail of a grouping record cycle. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def added (s : Store) : Store := accumulated (marked (copied s) false) s.sign

theorem tail_run (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hi : s.ids.length=2*m) (hcur : s.current.length≤2*m)
    (hc : 8*m+3≤cap) (hw : s.magnitude.length≤w) (ha : 4*w+3≤cap)
    (hfit : value s.magnitude+selected s s.sign<2^w) :
    Timed machine (2*cap+16*w+16*m+35)
      (boundary 5 cap w p m pos source out s)
      (boundary 0 cap w p m pos source out (added s)) := by
  have hcopy := call_run 5 6 (16*m+8) cap w p m pos pos source out out s (copied s)
    (copy_run s cap w p m pos source out hi hcur hc) (by intro q; rfl)
  cases hsign : s.sign
  · have hmark := call_run 6 7 1 cap w p m pos pos source out out
      (copied s) (marked (copied s) false)
      (mark_run false (copied s) cap w p m pos source out) (by
        intro q
        simp only [next,readBits_sign,marked,copied,hsign]
        rfl)
    have hacc := call_run 7 0 (2*cap+16*w+23) cap w p m pos pos source out out
      (marked (copied s) false) (accumulated (marked (copied s) false) false)
      (arithmetic_run false (marked (copied s) false) cap w p m pos source out hw ha
        (by simpa [marked,copied,selected,hsign] using hfit)) (by intro q; rfl)
    have h := (hcopy.trans hmark).trans hacc
    have he : ((16*m+8+1)+(1+1))+(2*cap+16*w+23+1)=2*cap+16*w+16*m+35 := by omega
    simpa only [he,added,hsign] using h
  · have hmark := call_run 6 8 1 cap w p m pos pos source out out
      (copied s) (marked (copied s) false)
      (mark_run false (copied s) cap w p m pos source out) (by
        intro q
        simp only [next,readBits_sign,marked,copied,hsign]
        rfl)
    have hacc := call_run 8 0 (2*cap+16*w+23) cap w p m pos pos source out out
      (marked (copied s) false) (accumulated (marked (copied s) false) true)
      (arithmetic_run true (marked (copied s) false) cap w p m pos source out hw ha
        (by simpa [marked,copied,selected,hsign] using hfit)) (by intro q; rfl)
    have h := (hcopy.trans hmark).trans hacc
    have he : ((16*m+8+1)+(1+1))+(2*cap+16*w+23+1)=2*cap+16*w+16*m+35 := by omega
    simpa only [he,added,hsign] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
