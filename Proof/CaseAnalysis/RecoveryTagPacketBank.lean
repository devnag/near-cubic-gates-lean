import Proof.CaseAnalysis.RecoveryTagPacketReset

/-! Install the actual packet beside the original 51-tape node bank. The
four extra ports are packet, retained tag index, tag limit and tag count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeTagPacket
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 9→Fin 55:=![25,48,31,30,32,22,23,51,39]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedTagPacketReset.machine
def input (constant current C D : ℕ) : Fin 9→List Bool:=
  ![List.replicate current true,ZeroPadding.pad C (List.replicate constant true),
    List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C true,List.replicate (C+1) false,List.replicate C false,List.replicate D false]
def output (A : Fin 55→List Bool) (constant current C : ℕ) (i : Fin 55):=
  if i=25 then List.replicate (current+4) true
  else if i=51 then ZeroPadding.pad C (RecoveryBoundedTagPacket.word constant current)
  else A i

theorem input_tapes (constant current C D : ℕ) :
    (RecoveryBoundedTagPacketReset.entry constant current C D).tapes=input constant current C D := by
  rw [RecoveryBoundedTagPacketReset.entry_tapes]
  funext i
  fin_cases i <;> rfl

theorem output_slot (A : Fin 55→List Bool) (constant current C D : ℕ)
    (hA : ∀ j,A (slots j)=input constant current C D j) (j : Fin 9) :
    output A constant current C (slots j)=RecoveryBoundedTagPacketReset.finalData constant current C D j := by
  have hj:=hA j
  fin_cases j <;> first | rfl | exact hj

theorem packet_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (constant current C D : ℕ)
    (hH : ∀ j,H (slots j)=0) (hA : ∀ j,A (slots j)=input constant current C D j)
    (hk : 2*constant+1 ≤ C) (hi : 2*(current+3)+1 ≤ C)
    (hD : RecoveryBoundedTagPacket.budget constant current C ≤ D) :
    ∃ r,runFrom machine (RecoveryBoundedTagPacketReset.budget constant current C)
      ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedTagPacketReset.budget constant current C ∧
      r.final.heads=H ∧ r.final.tapes=output A constant current C := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTagPacketReset.reset_run constant current C D hk hi hD
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedTagPacketReset.machine _ H A
    (RecoveryBoundedTagPacketReset.entry constant current C D)
    (by rw [RecoveryBoundedTagPacketReset.entry_heads];exact hH)
    (by rw [input_tapes];exact hA) p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (hH j).symm
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).1
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      exact (output_slot A constant current C D hA j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      have h25 : i≠25:=fun h=>hi ⟨0,h.symm⟩
      have h51 : i≠51:=fun h=>hi ⟨7,h.symm⟩
      simp only [output,if_neg h25,if_neg h51]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeTagPacket
