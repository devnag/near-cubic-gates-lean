import Proof.Amplification.RecoveryQueryCell

/-! The same query arithmetic in an explicitly allocated cleared bank.
Padding transport supplies only false backing; the caller provides the actual
two canonical operands and pays its allocation/clear before this call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedInput (cap a b : Nat) : Fin 39→List Bool :=
  fun i => ZeroPadding.pad cap (input a b i)

theorem pad_suffix (cap : Nat) (bits : List Bool) (padding : Nat)
    (h : bits.length+padding ≤ cap) :
    ZeroPadding.pad cap (bits++List.replicate padding false)=ZeroPadding.pad cap bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

theorem padded_run (successor : Bool) (cap a b : Nat)
    (hcap : budget successor a b+1 ≤ cap)
    (ha : 2*a.bits.length+1 ≤ cap) (hb : 2*b.bits.length+1 ≤ cap) :
    ∃ out : Fin 39→List Bool,
      ClockJoin.ReadyRun (machine successor).2 (budget successor a b) (paddedInput cap a b) out ∧
      out 26=ZeroPadding.pad cap (frame (result successor a b).bits) ∧
      ∀ i,(out i).length ≤ cap := by
  obtain ⟨cold,hcold,padding,hfield⟩ := run successor a b
  have hpad := PCPPairReusable.padded_ready _ _ _ hcold (fun _ => cap)
  obtain ⟨r,hr,ht,hh,hs⟩ := hpad
  have hinput : ∀ i,(paddedInput cap a b i).length ≤ max cap (0+1) := by
    intro i
    simp only [paddedInput,ZeroPadding.pad_length,input,RecoveryQueryPairSuccessor.input]
    split
    · rw [frame_length]; omega
    · split
      · rw [frame_length]; omega
      · simp
  have support := RecoveryTapeSupport.run_support (machine successor).2 _ _ r hr cap 0
    (by intro i; exact Nat.zero_le _) hinput
  have hbnd : ∀ i,(ZeroPadding.pad cap (cold i)).length ≤ cap := by
    intro i
    have h := support i
    rw [ht] at h
    simpa only [Nat.zero_add,max_eq_left (by omega : r.steps+1 ≤ cap)] using h
  refine ⟨_,⟨r,hr,ht,hh,hs⟩,?_,hbnd⟩
  have hlength := hbnd 26
  rw [hfield,ZeroPadding.pad_length,List.length_append,List.length_replicate] at hlength
  rw [hfield]
  exact pad_suffix cap _ padding (by omega)

end NearCubicWires.RepairOrdinary.RecoveryQueryCell
