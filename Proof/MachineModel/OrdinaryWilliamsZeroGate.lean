import Proof.MachineModel.OrdinaryWilliamsZeroGateKernel

/-! The canonical natWord header makes framed cells3 and5 sufficient to
dispatch U=0. The gate ignores and preserves every suffix bit. -/
namespace NearCubicWires.RepairOrdinary.WilliamsZeroGate
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def request (u : ℕ) (suffix : List Bool) := frame (natWord u++suffix)

theorem zero_bits (suffix : List Bool) : readTapeBit (request 0 suffix) 3=false ∧
    readTapeBit (request 0 suffix) 5=false := by
  norm_num [request,WilliamsInputHeader.natWord_eq,natBitLength,binary,frame,readTapeBit,List.getD]

theorem one_bit (suffix : List Bool) : readTapeBit (request 1 suffix) 5=true := by
  norm_num [request,WilliamsInputHeader.natWord_eq,natBitLength,binary,frame,readTapeBit,List.getD]

theorem width_ge_two (u : ℕ) (hu : 2 ≤ u) : 2 ≤ natBitLength u := by
  have h : Nat.log 2 2 ≤ Nat.log 2 u := Nat.log_mono_right hu
  norm_num at h
  dsimp [natBitLength]
  omega

theorem large_bit (u : ℕ) (suffix : List Bool) (hu : 2 ≤ u) : readTapeBit (request u suffix) 3=true := by
  have hw : natBitLength u=2+(natBitLength u-2) := by have := width_ge_two u hu; omega
  rw [request,WilliamsInputHeader.natWord_eq,hw,List.replicate_add]
  simp [frame,readTapeBit,List.getD]

theorem zero_characterization (u : ℕ) (suffix : List Bool) :
    (readTapeBit (request u suffix) 3=false ∧ readTapeBit (request u suffix) 5=false) ↔ u=0 := by
  by_cases h0 : u=0
  · subst u
    simp [(zero_bits suffix).1,(zero_bits suffix).2]
  by_cases h1 : u=1
  · subst u
    simp [one_bit suffix]
  · have h2 : 2 ≤ u := by omega
    simp [large_bit u suffix h2,h0]

theorem gate_run (u : ℕ) (suffix : List Bool) :
    ∃ r,run machine 10 (fun _ => request u suffix)=some r ∧
      r.final.tapes=(fun _ => request u suffix) ∧ (∀ i,r.final.heads i=0) ∧
      r.final.control=(if u=0 then 15 else 10) ∧
      (r.final.control=15 ↔ u=0) ∧ (r.final.control=10 ↔ 0<u) ∧ r.steps ≤ 10 := by
  obtain ⟨r,hr,ht,hh,hc,hs⟩ := total_run (request u suffix)
  have hctrl : r.final.control=(if u=0 then 15 else 10) := by
    rw [hc]
    by_cases hz : u=0
    · subst u
      simp [(zero_bits suffix).1,(zero_bits suffix).2]
    · have hn : ¬(readTapeBit (request u suffix) 3=false ∧ readTapeBit (request u suffix) 5=false) := by
        intro h
        exact hz ((zero_characterization u suffix).mp h)
      have ho : (readTapeBit (request u suffix) 3 || readTapeBit (request u suffix) 5)=true := by
        cases h3 : readTapeBit (request u suffix) 3 <;>
          cases h5 : readTapeBit (request u suffix) 5 <;> simp_all
      simp [ho,hz]
  refine ⟨r,hr,ht,hh,hctrl,?_,?_,hs⟩
  · simp [hctrl]
  · by_cases hz : u=0 <;> simp [hctrl,hz]; omega

@[simp] theorem zero_halted : machine.halted 15=true := rfl
@[simp] theorem positive_halted : machine.halted 10=true := rfl

end NearCubicWires.RepairOrdinary.WilliamsZeroGate
