import Proof.MachineModel.OrdinarySourceSATLiftRequestGraph

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cold (D n : ℕ) : Fin (tapes D) → List Bool :=
  fun i => if i.val=0 then frame (List.replicate n true) else []
noncomputable def copied (D n : ℕ) :=
  Function.update (Function.update (cold D n) (nSlot D) (List.replicate n true))
    (logSlot D) (List.replicate n false)
def prepareBudget (C D n : ℕ) := 4*n+3+(PCPSerializerCapacity.Power.budget D C n+1)

theorem copied_power (D n : ℕ) (i : Fin (DimensionPolynomial.tapes D)) :
    copied D n (powerSlot D i)=DimensionPolynomial.input D n i := by
  have hl : powerSlot D i≠logSlot D := by intro h; have hv := congrArg Fin.val h; dsimp [powerSlot,logSlot] at hv; omega
  have hn : powerSlot D i=nSlot D ↔ i.val=0 := by
    constructor
    · intro h; exact congrArg Fin.val ((power_injective D) h)
    · intro h; exact congrArg (powerSlot D) (Fin.ext h)
  have hz : (powerSlot D i).val≠0 := by dsimp [powerSlot]; omega
  simp [copied,Function.update,hl,hn,cold,hz,DimensionPolynomial.input]

theorem copied_out (D n : ℕ) : copied D n (outSlot D)=[] := by
  have hn : outSlot D≠nSlot D := Ne.symm (power_ne_out D _)
  have hl : outSlot D≠logSlot D := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [outSlot,logSlot] at hv
    omega
  simp only [copied,Function.update_of_ne hl,Function.update_of_ne hn]
  rfl

theorem powered_ready (C D n : ℕ) (out : Fin (DimensionPolynomial.tapes D) → List Bool)
    (hn : out ⟨0,by simp [DimensionPolynomial.tapes]⟩=List.replicate n true)
    (hb : out (PCPSerializerCapacity.Power.outputSlot D)=List.replicate (C*(n+1)^D) true) :
    Ready D n (C*(n+1)^D) 0 0 [] (fun _ => 0) (install (powerSlot D) (copied D n) out) := by
  refine ⟨rfl,?_,rfl,?_,rfl,?_⟩
  · exact (install_slot _ (power_injective D) _ out _).trans hn
  · exact (install_slot _ (power_injective D) _ out _).trans hb
  · exact (install_other _ _ out (outSlot D) (power_ne_out D)).trans (copied_out D n)

theorem cold_prepare (code : List Bool) (C D n : ℕ) : ∃ data,
    Path code C D 0 2 (prepareBudget C D n) (fun _ => 0) (fun _ => 0) (cold D n) data ∧
      Ready D n (C*(n+1)^D) 0 0 [] (fun _ => 0) data := by
  obtain ⟨raw,hr,rh,rt,rs⟩ := Full.raw_copy (copySlots D) (copy_injective D)
    (fun _ => 0) (cold D n) (List.replicate n true) (fun _ => rfl) rfl
    (by simp [cold,copySlots,nSlot,powerSlot]) (by simp [cold,copySlots,logSlot])
  simp only [List.length_replicate] at hr rt rs
  have first := call_run code C D 0 1 (4*n+2) _ _ raw hr rs (fun _ => rfl) rfl
  rw [rh,rt] at first
  change Path code C D 0 1 (4*n+2+1) (fun _ => 0) (fun _ => 0) (cold D n) (copied D n) at first
  obtain ⟨out,hpower,hn,hb⟩ := PCPSerializerCapacity.Power.capacity_run D C n
  obtain ⟨r,hrr,hh,ht,hs⟩ := hpower.focus_at (powerSlot D) (power_injective D)
    (fun _ => 0) (copied D n) (copied_power D n) (fun _ => rfl)
  have second := call_run code C D 1 2 (PCPSerializerCapacity.Power.budget D C n) _ _ r hrr hs (fun _ => rfl) rfl
  rw [hh,ht] at second
  refine ⟨_,?_,powered_ready C D n out hn hb⟩
  have whole := first.trans second
  convert whole using 1
  unfold prepareBudget
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
