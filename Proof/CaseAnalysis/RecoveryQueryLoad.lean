import Proof.CaseAnalysis.RecoveryQueryTable
import Proof.Hierarchy.CompetitorSameBucketRecordCopy

/-! Reuse the fixed-width raw loader for one projected query address. The
external address cursor advances and the local address/log heads reset. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryLoad
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 60:=![50,58,49,32]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots CompetitorSameBucketRecordCopy.machine
def heads (H : Fin 60→ℕ) (position : ℕ):=Function.update H 58 position
def output (A : Fin 60→List Bool) (C : ℕ) (bits : List Bool):=Function.update A 49 (ZeroPadding.pad C bits)

theorem load_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (C : ℕ) (pre bits tail : List Bool)
    (hH : ∀ j,H (slots j)=(![1,pre.length,0,0] : Fin 4→ℕ) j)
    (hA : ∀ j,A (slots j)=(![UnaryTemplate.tape bits.length,pre++bits++tail,
      List.replicate C false,List.replicate C false] : Fin 4→List Bool) j)
    (hC : 2*bits.length+4 ≤ C) :
    ∃ r,runFrom machine (CompetitorSameBucketRecordCopy.budget bits.length) ⟨machine.start,H,A⟩=some r ∧
      r.steps=CompetitorSameBucketRecordCopy.budget bits.length ∧
      r.final.heads=heads H (pre.length+bits.length) ∧ r.final.tapes=output A C bits := by
  obtain ⟨p,pr,ph,pt,ps⟩:=CompetitorSameBucketRecordCopy.padded_run C pre bits tail hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective CompetitorSameBucketRecordCopy.machine _ H A
    (CompetitorSameBucketRecordCopy.paddedInput C pre bits tail)
    (by rw [CompetitorSameBucketRecordCopy.padded_heads];exact hH)
    (by rw [CompetitorSameBucketRecordCopy.padded_tapes];exact hA) p pr
  refine ⟨r,hr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · exact (hH 0).symm
      · rfl
      · exact (hH 2).symm
      · exact (hH 3).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h58 : i≠58:=fun h=>hi ⟨1,h.symm⟩
      simp only [heads,Function.update_of_ne h58]
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · exact (hA 0).symm
      · exact (hA 1).symm
      · rfl
      · exact (hA 3).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      have h49 : i≠49:=fun h=>hi ⟨2,h.symm⟩
      simp only [output,Function.update_of_ne h49]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryLoad
