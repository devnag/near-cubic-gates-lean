import Proof.CaseAnalysis.CaseTwoConverter
import Proof.PCP.PCPPNativeCanonicalBounds
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! The complete executed cold converter has one fixed polynomial bound in
the actual arity and full size cap. Existing native descriptor bounds and
ordinary unary-power costs supply every term; no new simulation is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdBudget
open RepairRepresentation OuterPCPRecovery PaddedRunnerBudgetClosure
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_polynomial {measure : ℕ→ℕ} (hm : SourcePoly measure) (D C : ℕ) :
    SourcePoly (fun n=>PCPSerializerCapacity.Power.budget D C (measure n)) := by
  have hp:=((sourcePoly_pow (hm.add (polyDominated_const 2)) (D+1)).const_mul (6*C)).add
    (polyDominated_const 7)
  have h:=((hm.const_mul 2).add (polyDominated_const 9)).add
    ((polyDominated_const (2*C+2)).add (hp.const_mul D))
  apply h.mono
  intro n
  have hb:=DimensionPower.cost_bound D C (measure n+1) D le_rfl
  simpa only [PCPSerializerCapacity.Power.budget,Nat.add_assoc] using
    Nat.add_le_add_left hb (2*measure n+9)

theorem prepare_bound (C : ℕ) : Cold.prepareBudget C≤64*(C+1) := by
  unfold Cold.prepareBudget Cold.allocationBudget Cold.loadsBudget
  omega

theorem framed_bound {R B : ℕ} (C : ℕ) (c : BooleanCircuit R) (hc : c.size≤B) :
    NativeConverter.framedBudget C c≤1024*(R+B+1)*(C+1)+
      1248*(R+B+5)^2+4096*(R+B+1)^2+64 := by
  have hd:=PCPPNative.descriptor_cap c hc
  have hb : (CanonicalWalk.body c).length≤(PCPPNative.descriptor c).length := by
    rw [PCPPNative.descriptor_eq]
    simp only [CanonicalWalk.body,List.length_append]
    omega
  have hh : PCPPNativeColdHeader.budget R c.size≤1024*(R+B+1)^2 :=
    (PCPPNativeColdHeader.budget_bound R c.size).trans
      (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left (by omega) 2))
  have hm:=Nat.mul_le_mul_right (C+1) (show c.size+1≤R+B+1 by omega)
  unfold NativeConverter.framedBudget NativeConverter.budget CanonicalWalk.budget NativeHeaderJoin.budget
  nlinarith only [hd,hb,hh,hm]

def envelope (n : ℕ) := ColdLogs.budget 1048576 n 0+
  64*(ColdFits.capacity n 0+1)+1024*(n+1)*(ColdFits.capacity n 0+1)+
    1248*(n+5)^2+4096*(n+1)^2+100

theorem budget_bound {R B : ℕ} (c : BooleanCircuit R) (hc : c.size≤B) :
    Cold.budget B c≤envelope (R+B) := by
  have hf:=framed_bound (ColdFits.capacity R B) c hc
  have hp:=prepare_bound (ColdFits.capacity R B)
  have hC : ColdFits.capacity R B=ColdFits.capacity (R+B) 0 := by simp [ColdFits.capacity]
  have hL : ColdLogs.budget 1048576 R B=ColdLogs.budget 1048576 (R+B) 0 := by
    simp [ColdLogs.budget,ColdScalars.budget]
  rw [hC] at hf hp
  unfold Cold.budget envelope
  rw [hC,hL]
  omega

theorem envelope_polynomial : SourcePoly envelope := by
  have hi:=sourcePoly_id
  have hC : SourcePoly (fun n=>ColdFits.capacity n 0) := by
    simpa only [ColdFits.capacity,Nat.add_zero] using
      (sourcePoly_pow (hi.add (polyDominated_const 1)) 4).const_mul 1048576
  have h4:=power_polynomial hi 4 1048576
  have h1:=power_polynomial hi 1 1
  have h16:=power_polynomial hC 1 16
  have hlogs : SourcePoly (fun n=>ColdLogs.budget 1048576 n 0) := by
    simpa only [ColdLogs.budget,ColdScalars.budget,ColdFits.capacity,Nat.add_zero] using
      (((((((((hi.const_mul 2).add (polyDominated_const 6)).add
        (polyDominated_const 1)).add h4).add (polyDominated_const 1)).add h1).add
          (polyDominated_const 1)).add h16).add (polyDominated_const 1)).add
            (polyDominated_const 14)
  have hCp:=hC.add (polyDominated_const 1)
  have hwalk:=((hi.add (polyDominated_const 1)).mul hCp).const_mul 1024
  have hd:=(sourcePoly_pow (hi.add (polyDominated_const 5)) 2).const_mul 1248
  have hh:=(sourcePoly_pow (hi.add (polyDominated_const 1)) 2).const_mul 4096
  apply (((((hlogs.add (hCp.const_mul 64)).add hwalk).add hd).add hh).add
    (polyDominated_const 100)).mono
  intro n
  dsimp only [envelope]
  rw [Nat.mul_assoc]

theorem polynomial : ∃ coefficient degree : ℕ, 1≤coefficient ∧
    ∀ (R B : ℕ) (c : BooleanCircuit R), c.size≤B →
      Cold.budget B c≤coefficient*(R+B+1)^degree := by
  obtain ⟨degree,coefficient,hbound⟩:=envelope_polynomial
  refine ⟨coefficient+1,degree,by omega,fun R B c hc=>?_⟩
  exact (budget_bound c hc).trans ((hbound (R+B)).trans
    (Nat.mul_le_mul_right _ (by omega)))

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdBudget
