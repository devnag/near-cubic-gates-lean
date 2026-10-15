import Proof.CaseAnalysis.RecoveryLiteralLoad

/-! Original framed-code source → actual sign and unary query index. The
original reader and decoder share their input tape and the final48/49 ports;
all heads except the retained source cursor return to their entry positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralLoad
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loaded_driver (A : Fin 71→List Bool) (index C : ℕ) (negative : Bool)
    (hA : ∀ j,A (driverSlots j)=List.replicate C false) :
    ∀ j,loaded A (RecoveryBoundedLiteralDriver.code index negative) C (driverSlots j)=
      RecoveryBoundedLiteralDriver.input index C negative j := by
  intro j
  have h:=hA j
  fin_cases j
  · rfl
  all_goals
    simp only [RecoveryBoundedLiteralDriver.input,RepairSource.RecoverySourceLiteral.driverInput]
    norm_num
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    exact h

theorem loaded_heads (H : Fin 71→ℕ) (position : ℕ)
    (hH : ∀ j,H (driverSlots j)=0) : ∀ j,heads H position (driverSlots j)=0 := by
  intro j
  have h:=hH j
  fin_cases j <;> exact h

theorem decode_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (index W C : ℕ)
    (negative : Bool) (pre tail : List Bool)
    (hRead : ∀ j,H (readSlots j)=(![pre.length,0,0] : Fin 3→ℕ) j)
    (aRead : ∀ j,A (readSlots j)=(![pre++frame (RecoveryBoundedLiteralDriver.code index negative)++tail,
      List.replicate C false,List.replicate (C+1) false] : Fin 3→List Bool) j)
    (hDriver : ∀ j,H (driverSlots j)=0)
    (aDriver : ∀ j,A (driverSlots j)=List.replicate C false)
    (hi : index ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ out r,runFrom machine (budget index negative) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ budget index negative ∧
      r.final.heads=heads H (pre.length+2*(RecoveryBoundedLiteralDriver.code index negative).length+1) ∧
      r.final.tapes=install driverSlots (loaded A (RecoveryBoundedLiteralDriver.code index negative) C) out ∧
      out 6=ZeroPadding.pad C [negative] ∧
      out 9=ZeroPadding.pad C (RepairSource.VerifierDecoding.CompareMachine.word index) ∧
      (∀ j,(out j).length ≤ C) := by
  obtain ⟨_,hfield⟩:=RecoveryBoundedLiteralDriver.driver_capacity index W C negative hi hC
  obtain ⟨p,pr,ps,ph,pt⟩:=read_run H A C pre (RecoveryBoundedLiteralDriver.code index negative) tail hRead aRead hfield
  obtain ⟨out,hr,hflag,hindex,hout⟩:=RecoveryBoundedLiteralDriver.driver_run index W C negative hi hC
  obtain ⟨q,qr,qh,qt,qs⟩:=hr.focus_at driverSlots driver_injective
    (heads H (pre.length+2*(RecoveryBoundedLiteralDriver.code index negative).length+1))
    (loaded A (RecoveryBoundedLiteralDriver.code index negative) C)
    (loaded_driver A index C negative aDriver) (loaded_heads H _ hDriver)
  have qr' : runFrom driver (RepairSource.RecoverySourceLiteral.driverBudget index negative)
      (restart p.final driver.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join read driver _ _ _ p q pr qr'
  refine ⟨out,joinedReceipt p q,full,?_,qh,qt,hflag,hindex,hout⟩
  change p.steps+1+q.steps ≤ budget index negative
  unfold budget
  omega

theorem budget_bound (index W C : ℕ) (negative : Bool) (hi : index ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) : budget index negative ≤ 4*C+8 := by
  obtain ⟨hdriver,hfield⟩:=RecoveryBoundedLiteralDriver.driver_capacity index W C negative hi hC
  rw [frame_length] at hfield
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralLoad
