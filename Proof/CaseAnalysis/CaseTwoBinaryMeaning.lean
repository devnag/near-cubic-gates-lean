import Proof.CaseAnalysis.CaseTwoBinaryField
import Proof.MachineModel.GeneratedAmplifierSemantics

/-! The physical little-endian field is the original PCPP clause address. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField
open LocalBitMultitape SourceInterfaces SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_address {n : ℕ} (u : BitInput n) : value (List.ofFn u)=(binaryAddress u).val:=by
  have he : (fun i : Fin n=>(value (List.ofFn u)).testBit i.val)=u:=funext (GeneratedAmplifier.address_bit u)
  have h:=binaryAddress_testBit (GeneratedAmplifier.address_lt u)
  rw [he] at h
  exact (congrArg Fin.val h).symm
theorem binary_address {n : ℕ} (u : BitInput n) : binary n (binaryAddress u).val=List.ofFn u:=by
  have h:=BoundedCounter.binary_of_value (List.ofFn u)
  simpa only [List.length_ofFn,value_address] using h

theorem address_run {n : ℕ} (pre tail : List Bool) (u : BitInput n) : ∃ r,
    run machine (budget pre.length n (binaryAddress u).val)
      (fun i : Fin 13=>if i=0 then frame (pre++List.ofFn u++tail)
        else if i=2 then List.replicate pre.length true else if i=3 then List.replicate n true else [])=some r ∧
      r.steps≤budget pre.length n (binaryAddress u).val ∧
      r.final.tapes 12=UnaryTemplate.tape (binaryAddress u).val ∧ r.final.heads 12=1 ∧
      (∀ i,i≠12 → r.final.heads i=0) ∧
      r.final.tapes 0=frame (pre++List.ofFn u++tail) ∧ r.final.tapes 1=List.ofFn u ∧
      r.final.tapes 6=frame (List.ofFn u):=by
  obtain ⟨r,hr,rs,rt,rh,hh,keep,raw,framed⟩:=index_run pre tail n (binaryAddress u).val (binaryAddress u).isLt
  have hi : input pre tail n (binaryAddress u).val=
      (fun i : Fin 13=>if i=0 then frame (pre++List.ofFn u++tail)
        else if i=2 then List.replicate pre.length true else if i=3 then List.replicate n true else []):=by
    funext i
    simp only [input,binary_address]
  rw [hi] at hr
  rw [binary_address] at keep raw framed
  exact ⟨r,hr,rs,rt,rh,hh,keep,raw,framed⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField
