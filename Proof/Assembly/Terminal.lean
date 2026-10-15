import Proof.Assembly.BankTerminalNativePrefix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.defProp false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairRepresentation RepairSource.VerifierDecoding
open NativeRecipes
namespace TerminalPrefixDriver
attribute [local irreducible] P1TopDownPaidPayload.tapes

noncomputable def slot (g : FamilyInitGenerator.PrefixCode) (k : Fin 17) : Fin (NativeFamilyGenerator.tapes g.printer (7+g.scratch)) := by
 unfold NativeFamilyGenerator.tapes
 exact Fin.natAdd (r_tapes g.printer) ⟨k.val,by have h:=k.isLt;omega⟩
noncomputable def family (g : FamilyInitGenerator.PrefixCode) (k : Fin (r_tapes g.printer)) :
 Fin (NativeFamilyGenerator.tapes g.printer (7+g.scratch)) := by
 unfold NativeFamilyGenerator.tapes
 exact k.castAdd (10+(7+g.scratch))
noncomputable def driver (g : FamilyInitGenerator.PrefixCode) (j : Fin (NativeFamilyGenerator.tapes g.printer (7+g.scratch))) : Bool :=
 decide (r_tapes g.printer+10≤j.val ∧ j.val<r_tapes g.printer+17)

@[simp] theorem slot_val (g : FamilyInitGenerator.PrefixCode) (k : Fin 17) :
 (slot g k).val=r_tapes g.printer+k.val := rfl
@[simp] theorem family_val (g : FamilyInitGenerator.PrefixCode) (k : Fin (r_tapes g.printer)) :
 (family g k).val=k.val := rfl
@[simp] theorem slot_eq (g : FamilyInitGenerator.PrefixCode) (j k : Fin 17) : slot g j=slot g k ↔ j=k := by
 constructor
 · intro h; apply Fin.ext; have hv:=congrArg Fin.val h; simpa only [slot_val,Nat.add_left_cancel_iff] using hv
 · intro h; rw [h]
@[simp] theorem driver_slot (g : FamilyInitGenerator.PrefixCode) (k : Fin 17) :
 driver g (slot g k)=decide (10≤k.val ∧ k.val<17) := by
 simp [driver]
@[simp] theorem driver_family (g : FamilyInitGenerator.PrefixCode) (k : Fin (r_tapes g.printer)) :
 driver g (family g k)=false := by
 have hk:=k.isLt
 simp [driver]; omega
@[simp] theorem family_ne_slot (g : FamilyInitGenerator.PrefixCode) (j : Fin (r_tapes g.printer)) (k : Fin 17) :
 family g j≠slot g k := by
 intro h; have hv:=congrArg Fin.val h; have hj:=j.isLt
 simp only [family_val,slot_val] at hv
 omega

@[simp] theorem input_slot (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) (k : Fin 17) :
 NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i (slot g k)=
  if h:k.val<9 then NativeFamilyGenerator.inputWords i ⟨k.val,h⟩ else [] := by
 change Fin.addCases (m:=r_tapes g.printer) (n:=10+(7+g.scratch))
  (motive:=fun _=>List Bool) (fun _=>[])
  (fun j=>if h:j.val<9 then NativeFamilyGenerator.inputWords i ⟨j.val,h⟩ else [])
  (Fin.natAdd (r_tapes g.printer) ⟨k.val,by have hk:=k.isLt;omega⟩)=_
 rw [Fin.addCases_right]
@[simp] theorem input_family (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) (k : Fin (r_tapes g.printer)) :
 NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i (family g k)=[] := by
 simp [NativeFamilyGenerator.inputBank,family,id]

theorem input_driver (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) :
 ∀ j, driver g j=true → NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i j=[] := by
 unfold NativeFamilyGenerator.tapes
 intro j
 refine Fin.addCases (fun j h=>?_) (fun j h=>?_) j
 · have hj:=j.isLt
   simp [driver] at h
   omega
 · have hj : ¬j.val<9 := by
    simp [driver] at h
    omega
   simp [NativeFamilyGenerator.inputBank,hj,id]

noncomputable def machine (g : FamilyInitGenerator.PrefixCode) : Machine (NativeFamilyGenerator.tapes g.printer (7+g.scratch)) 35 :=
 Bank.machine (slot g 6) (slot g 9) (slot g 14) (driver g)
noncomputable def result (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) : NativeFamilyGenerator.Result (NativeFamilyGenerator.tapes g.printer (7+g.scratch)) :=
 { ds:=[], S:=0, R:=0, B:=0, rowWidth:=0, total:=0, denominator:=1, residual:=0
   fuel:=4*i.recordWidth+32
   H:=Bank.headed (slot g 6) (slot g 9) (driver g) 0
   A:=Bank.output (slot g 6) (slot g 9) (slot g 14) (driver g)
     (NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i) i.recordWidth }
noncomputable def code (g : FamilyInitGenerator.PrefixCode) : FamilyInitGenerator.PrefixCode :=
 NativeTerminalDispatch.branchCode g {states:=35,machine:=machine g,result:=result g}

attribute [local irreducible] Step Bank.machine Bank.headed Bank.output in
theorem run (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) :
 Step (machine g) (result g i).fuel (fun _=>0) (NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i)
 (result g i).H (result g i).A := by
 apply Bank.run (slot g 6) (slot g 9) (slot g 14) (driver g)
  (NativeFamilyGenerator.inputBank g.printer (7+g.scratch) i) i.recordWidth
 · simp
 · simp
 · simp
 · simp
 · simp
 · simp
 · simp [NativeFamilyGenerator.inputWords]
 · simp
 · exact input_driver g i

@[simp] theorem init_family (g : FamilyInitGenerator.PrefixCode) (j : Fin (r_tapes g.printer)) :
 FamilyInitGenerator.initSlots g.printer g.scratch (by unfold FamilyInitGenerator.initTapes;exact j.castAdd 7)=family g j := by
 apply Fin.ext
 have hj:=j.isLt
 simp [FamilyInitGenerator.initSlots,hj,id]
@[simp] theorem init_driver (g : FamilyInitGenerator.PrefixCode) (j : Fin 7) :
 FamilyInitGenerator.initSlots g.printer g.scratch (by unfold FamilyInitGenerator.initTapes;exact j.natAdd (r_tapes g.printer))=
 slot g ⟨10+j.val,by have hj:=j.isLt;omega⟩ := by
 apply Fin.ext
 simp [FamilyInitGenerator.initSlots,slot,id]
 omega

@[simp] theorem result_familyH (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) (j : Fin (r_tapes g.printer)) :
 (result g i).H (family g j)=0 := by
 simp [result,Bank.headed,Bank.heads]
@[simp] theorem result_familyA (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) (j : Fin (r_tapes g.printer)) :
 (result g i).A (family g j)=[] := by
 simp [result,Bank.output,Bank.bank]

theorem ready (g : FamilyInitGenerator.PrefixCode) (i : NativeFamilyGenerator.Input) : FamilyInitGenerator.PrefixReady (code g) i := by
 refine ⟨?_,?_,?_,?_⟩
 · change ∀ j, (result g i).H (FamilyInitGenerator.initSlots g.printer g.scratch j)=FamilyInitGenerator.entryH g.printer j
   unfold FamilyInitGenerator.initTapes
   intro j
   refine Fin.addCases (fun j=>?_) (fun j=>?_) j
   · refine (congrArg (fun p=>(result g i).H p) (init_family g j)).trans ?_
     rw [result_familyH]
     simp [FamilyInitGenerator.entryH,id]
   · refine (congrArg (fun p=>(result g i).H p) (init_driver g j)).trans ?_
     fin_cases j <;> simp [result,Bank.headed,Bank.heads,FamilyInitGenerator.entryH,id]
 · change ∀ j, (result g i).A (FamilyInitGenerator.initSlots g.printer g.scratch j)=
    FamilyInitGenerator.entry g.printer (FamilyInitGenerator.scalars (code g) i) (FamilyInitGenerator.descriptor (code g) i) j
   unfold FamilyInitGenerator.initTapes
   intro j
   refine Fin.addCases (fun j=>?_) (fun j=>?_) j
   · refine (congrArg (fun p=>(result g i).A p) (init_family g j)).trans ?_
     rw [result_familyA]
     simp [FamilyInitGenerator.entry,FamilyInitGenerator.descriptor,code,NativeTerminalDispatch.branchCode,result,id]
   · refine (congrArg (fun p=>(result g i).A p) (init_driver g j)).trans ?_
     fin_cases j <;>
     simp [id,FamilyInitGenerator.entry,FamilyInitGenerator.drivers,FamilyInitGenerator.scalars,FamilyInitGenerator.descriptor,code,NativeTerminalDispatch.branchCode,
       result,Bank.output,Bank.bank,CompareMachine.word]
 · change (result g i).H (NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch))=0
   have he : NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch)=slot g 9 := by apply Fin.ext;rfl
   rw [he]
   simp [result,Bank.headed]
 · change (result g i).A (NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch))=frame (natWord 1)
   have he : NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch)=slot g 9 := by apply Fin.ext;rfl
   rw [he]
   simp [result,Bank.output,Bank.bank,Bank.denWord_eq]

theorem terminal (g : FamilyInitGenerator.PrefixCode) (hSlack : NativeTerminalDispatch.SourceSlack g) :
 NativeTerminalDispatch.TerminalWithDispatch (code g) := by
 intro q L target v mode
 dsimp only
 intro hEnvelope
 refine ⟨⟨?_,ready g _⟩,rfl,rfl,?_⟩
 · exact run g _
 · have hv : v+1≤g.policy.inputCoefficient*(q+1)^g.policy.inputDegree := by
    have h:=hEnvelope (6 : Fin 9)
    change (UnaryTemplate.tape v).length≤g.policy.inputCoefficient*(q+1)^g.policy.inputDegree at h
    rw [UnaryTemplate.tape_length] at h
    omega
   have hpow : (q+1)^g.policy.inputDegree≤(q+1)^g.policy.sourceDegree := by
    have hp : 0<(q+1)^(g.policy.sourceDegree-g.policy.inputDegree) := by positivity
    have he : g.policy.inputDegree+(g.policy.sourceDegree-g.policy.inputDegree)=g.policy.sourceDegree := by
     have h:=hSlack.2;omega
    calc
     _ = (q+1)^g.policy.inputDegree*1 := by simp
     _ ≤ (q+1)^g.policy.inputDegree*(q+1)^(g.policy.sourceDegree-g.policy.inputDegree) :=
      Nat.mul_le_mul_left _ (by omega)
     _ = _ := by rw [←Nat.pow_add,he]
   have hu : v+1≤(r_tapes g.printer+1)*(v+1) := by nlinarith
   have hc : 1103*(r_tapes g.printer+1)*g.policy.inputCoefficient≤
      100000*(r_tapes g.printer+1)*(g.policy.inputCoefficient+1) := by
    have h : 1103*g.policy.inputCoefficient≤100000*(g.policy.inputCoefficient+1) := by omega
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
     Nat.mul_le_mul_left (r_tapes g.printer+1) h
   change 4*v+32+2+1+1000*(r_tapes g.printer+1)*(0+0+0+0+v+0+0*0+1)≤
    g.policy.sourceCoefficient*(q+1)^g.policy.sourceDegree
   simp only [Nat.zero_add,Nat.add_zero,Nat.zero_mul]
   calc
    4*v+32+2+1+1000*(r_tapes g.printer+1)*(v+1)
      ≤1103*(r_tapes g.printer+1)*(v+1) := by nlinarith
    _ ≤1103*(r_tapes g.printer+1)*(g.policy.inputCoefficient*(q+1)^g.policy.inputDegree) :=
      Nat.mul_le_mul_left _ hv
    _ =(1103*(r_tapes g.printer+1)*g.policy.inputCoefficient)*(q+1)^g.policy.inputDegree := by ring
    _ ≤(100000*(r_tapes g.printer+1)*(g.policy.inputCoefficient+1))*(q+1)^g.policy.sourceDegree :=
      Nat.mul_le_mul hc hpow
    _ ≤g.policy.sourceCoefficient*(q+1)^g.policy.sourceDegree := Nat.mul_le_mul_right _ hSlack.1

theorem correct (g : FamilyInitGenerator.PrefixCode) (hSlack : NativeTerminalDispatch.SourceSlack g) :
 NativeTerminalDispatch.TerminalWithDispatch (NativeTerminalDispatch.branchCode g {states:=35,machine:=machine g,result:=result g}) :=
 terminal g hSlack
end TerminalPrefixDriver
