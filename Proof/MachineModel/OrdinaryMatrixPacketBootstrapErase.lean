import Proof.MachineModel.OrdinaryMatrixPacketRequestCopy
import Proof.MachineModel.OrdinaryMatrixPacketWorkClear

/-! The actual first packet and dimension bootstrap feed the physical
workspace erase. The caller's retained source remains outside that erase. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketBootstrapErase
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open MatrixWilliamsProduct (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def old (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : Fin (MatrixPacketWorkClear.tapes a E) :=
  (i.castAdd (MatrixPacketCapacityNative.extra E)).castAdd 2
noncomputable def workIndex (a : WilliamsAlgorithm) (E : ℕ) (j : Fin (MatrixPacketWorkClear.count a)) : Fin (MatrixVariablePacketWorkspace.tapes a) :=
  ⟨(MatrixPacketWorkClear.work a E j).val,MatrixPacketWorkClear.work_bound a E j⟩
theorem work_eq_old (a : WilliamsAlgorithm) (E : ℕ) (j : Fin (MatrixPacketWorkClear.count a)) :
    MatrixPacketWorkClear.work a E j=old a E (workIndex a E j) := Fin.ext rfl
theorem work_working (a : WilliamsAlgorithm) (E : ℕ) (j : Fin (MatrixPacketWorkClear.count a)) :
    MatrixVariablePacketWorkspace.working a (workIndex a E j) := by
  have h:=j.isLt
  unfold MatrixPacketWorkClear.count at h
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  change (MatrixPacketWorkClear.work a E j).val≠424 ∧
    (MatrixPacketWorkClear.work a E j).val≠MatrixVariableProduct.tapes a+16
  rw [MatrixPacketWorkClear.work_val]
  split_ifs <;> omega

noncomputable def first (a : WilliamsAlgorithm) (E C : ℕ) (negative : Bool) :=
  TapeEmbedding.machine 2 (MatrixPacketCapacityNative.machine a E C negative)
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) (negative : Bool) :=
  Composition.machine (first a E C negative) (MatrixPacketWorkClear.machine a E)
def extras (original : List Bool) : Fin 2 → List Bool := ![[],original]
noncomputable def input (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (bit : ℕ) (out original : List Bool) :=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 2 => 0) (extras original)
    (MatrixPacketCapacityNative.input a E C r bit out))
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (negative : Bool) (bit : ℕ) :=
  MatrixPacketCapacityNative.budget a E C r negative bit+1+2*(C*(r.U+1)^2*(r.d+r.p+1)^E)+4

theorem erase_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (negative : Bool) (bit : ℕ) (out original : List Bool)
    (ht : bit<r.p) (hC : MatrixVariablePacketWorkspace.footprint a r bit negative≤C*(r.U+1)^2*(r.d+r.p+1)^E) : ∃ actual,
    runFrom (machine a E C negative) (budget a E C r negative bit) (input a E C r bit out original)=some actual ∧
    (∀ j,actual.final.tapes (MatrixPacketWorkClear.work a E j)=List.replicate (C*(r.U+1)^2*(r.d+r.p+1)^E) false ∧
      actual.final.heads (MatrixPacketWorkClear.work a E j)=0) ∧
    actual.final.tapes (MatrixPacketWorkClear.capTape a E)=List.replicate (C*(r.U+1)^2*(r.d+r.p+1)^E) true ∧
    actual.final.heads (MatrixPacketWorkClear.capTape a E)=0 ∧
    actual.final.tapes (MatrixPacketWorkClear.logTape a E)=List.replicate (C*(r.U+1)^2*(r.d+r.p+1)^E+1) false ∧
    actual.final.heads (MatrixPacketWorkClear.logTape a E)=0 ∧
    actual.final.tapes (old a E ((MatrixVariablePacket.outputTape a).castAdd 1))=out++packet r negative bit ∧
    actual.final.heads (old a E ((MatrixVariablePacket.outputTape a).castAdd 1))=(out++packet r negative bit).length ∧
    actual.final.tapes (old a E ((MatrixVariablePacket.offset a).castAdd 1))=UnaryTemplate.tape (2*bit) ∧
    actual.final.heads (old a E ((MatrixVariablePacket.offset a).castAdd 1))=1 ∧
    actual.final.tapes (MatrixPacketWorkClear.original a E)=original ∧ actual.final.heads (MatrixPacketWorkClear.original a E)=0 ∧
    actual.steps≤budget a E C r negative bit := by
  let cap := C*(r.U+1)^2*(r.d+r.p+1)^E
  obtain ⟨base,hb,capT,capH,outT,outH,offT,offH,work,bs⟩ :=
    MatrixPacketCapacityEndpoint.endpoint_run a E C r negative bit out ht hC
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extras original) base
  have he := TapeEmbedding.run_embed (MatrixPacketCapacityNative.machine a E C negative)
    (fun _ : Fin 2 => 0) (extras original) _ _ base hb
  have oldT (i : Fin (MatrixPacketCapacityNative.tapes a E)) :
      prepared.final.tapes (i.castAdd 2)=base.final.tapes i := by
    change (Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes (extras original)) (i.castAdd 2)=_
    rw [Fin.addCases_left]
  have oldH (i : Fin (MatrixPacketCapacityNative.tapes a E)) :
      prepared.final.heads (i.castAdd 2)=base.final.heads i := by
    change (Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.castAdd 2)=_
    rw [Fin.addCases_left]
  have freshT (i : Fin 2) : prepared.final.tapes (i.natAdd (MatrixPacketCapacityNative.tapes a E))=extras original i := by
    change (Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (motive := fun _ => List Bool)
      base.final.tapes (extras original)) (i.natAdd (MatrixPacketCapacityNative.tapes a E))=_
    rw [Fin.addCases_right]
  have freshH (i : Fin 2) : prepared.final.heads (i.natAdd (MatrixPacketCapacityNative.tapes a E))=0 := by
    change (Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (motive := fun _ => ℕ)
      base.final.heads (fun _ => 0)) (i.natAdd (MatrixPacketCapacityNative.tapes a E))=_
    rw [Fin.addCases_right]
  have selectedH (j : Fin (MatrixPacketWorkClear.count a+2)) : prepared.final.heads (MatrixPacketWorkClear.slots a E j)=0 := by
    refine Fin.addCases (m := MatrixPacketWorkClear.count a+1) (n := 1) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m := MatrixPacketWorkClear.count a) (n := 1) (fun k => ?_) (fun k => ?_) i
      · simp only [MatrixPacketWorkClear.slots,Fin.addCases_left]
        rw [work_eq_old]
        exact (oldH _).trans (work _ (work_working a E k)).1
      · fin_cases k
        simp only [MatrixPacketWorkClear.slots,Fin.addCases_left,Fin.addCases_right]
        exact (oldH _).trans capH
    · fin_cases i
      simp only [MatrixPacketWorkClear.slots,Fin.addCases_right]
      exact freshH 0
  obtain ⟨cleared,hclear,ch,ct,cs⟩ := MatrixPacketWorkClear.clear_run a E cap 0 prepared.final.heads prepared.final.tapes
    ((oldT _).trans capT) (freshT 0)
    (by intro j; rw [work_eq_old]; exact (congrArg List.length (oldT _)).le.trans (work _ (work_working a E j)).2)
    selectedH
  have hi : RecoveryCalls.restarted (MatrixPacketWorkClear.machine a E) prepared.final.heads prepared.final.tapes=
      Composition.restart prepared.final (MatrixPacketWorkClear.machine a E).start := rfl
  rw [hi] at hclear
  have joined := Composition.run_join (first a E C negative) (MatrixPacketWorkClear.machine a E)
    _ _ _ prepared cleared he hclear
  have localT (j : Fin (MatrixPacketWorkClear.count a+2)) :
      cleared.final.tapes (MatrixPacketWorkClear.slots a E j)=
      MatrixPacketWorkClear.eraseData cap (max 0 (cap+1)) (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false) j := by
    rw [ct]
    exact install_slot (MatrixPacketWorkClear.slots a E) (MatrixPacketWorkClear.slots_injective a E) _ _ j
  have untouched (i : Fin (MatrixPacketWorkClear.tapes a E))
      (no : ∀ j,MatrixPacketWorkClear.slots a E j≠i) :
      cleared.final.tapes i=prepared.final.tapes i ∧ cleared.final.heads i=prepared.final.heads i := by
    constructor
    · rw [ct]
      exact install_other _ _ _ i no
    · exact congrFun ch i
  have oldProtected (i : Fin (MatrixVariablePacketWorkspace.tapes a))
      (hi : i.val=424 ∨ i.val=MatrixVariableProduct.tapes a+16) :
      cleared.final.tapes (old a E i)=base.final.tapes (i.castAdd (MatrixPacketCapacityNative.extra E)) ∧
      cleared.final.heads (old a E i)=base.final.heads (i.castAdd (MatrixPacketCapacityNative.extra E)) := by
    have no : ∀ j,MatrixPacketWorkClear.slots a E j≠old a E i := by
      intro j hj
      rw [MatrixPacketWorkClear.slots_cases] at hj
      split_ifs at hj
      · have hw := work_working a E ⟨j.val,by assumption⟩
        have hv:=congrArg Fin.val hj
        change (workIndex a E ⟨j.val,by assumption⟩).val=i.val at hv
        unfold MatrixVariablePacketWorkspace.working at hw
        omega
      · have hc:=MatrixPacketWorkClear.cap_bound a E
        have hv:=congrArg Fin.val hj
        change (MatrixPacketWorkClear.capTape a E).val=i.val at hv
        omega
      · have hv:=congrArg Fin.val hj
        change MatrixPacketCapacityNative.tapes a E=i.val at hv
        unfold MatrixPacketCapacityNative.tapes at hv
        omega
    obtain ⟨kt,kh⟩ := untouched _ no
    exact ⟨kt.trans (oldT _),kh.trans (oldH _)⟩
  have keepOriginal := untouched (MatrixPacketWorkClear.original a E) (by
    intro j hj
    rw [MatrixPacketWorkClear.slots_cases] at hj
    split_ifs at hj
    · have h:=MatrixPacketWorkClear.work_bound a E ⟨j.val,by assumption⟩
      have hv:=congrArg Fin.val hj
      change (MatrixPacketWorkClear.work a E ⟨j.val,by assumption⟩).val=MatrixPacketCapacityNative.tapes a E+1 at hv
      unfold MatrixPacketCapacityNative.tapes at hv
      omega
    · have h:=(MatrixPacketCapacityNative.outputTape a E).isLt
      have hv:=congrArg Fin.val hj
      change (MatrixPacketCapacityNative.outputTape a E).val=MatrixPacketCapacityNative.tapes a E+1 at hv
      omega
    · have hv:=congrArg Fin.val hj
      change MatrixPacketCapacityNative.tapes a E=MatrixPacketCapacityNative.tapes a E+1 at hv
      omega)
  have ko:=oldProtected ((MatrixVariablePacket.outputTape a).castAdd 1) (Or.inr rfl)
  have kx:=oldProtected ((MatrixVariablePacket.offset a).castAdd 1) (Or.inl rfl)
  refine ⟨Composition.joinedReceipt prepared cleared,?_,?_,?_,?_,?_,?_,ko.1.trans outT,ko.2.trans outH,
    kx.1.trans offT,kx.2.trans offH,keepOriginal.1.trans (freshT 1),keepOriginal.2.trans (freshH 1),?_⟩
  · have hbudget : MatrixPacketCapacityNative.budget a E C r negative bit+1+(2*cap+4)=budget a E C r negative bit := by
      unfold budget
      dsimp [cap]
      omega
    rw [hbudget] at joined
    exact joined
  · intro j
    have hT:=localT ((j.castAdd 1).castAdd 1)
    have hH:=selectedH ((j.castAdd 1).castAdd 1)
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_left] at hT
    simp only [MatrixPacketWorkClear.slots,Fin.addCases_left] at hH
    exact ⟨hT,(congrFun ch _).trans hH⟩
  · have h:=localT (((0 : Fin 1).natAdd (MatrixPacketWorkClear.count a)).castAdd 1)
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_left,Fin.addCases_right] at h
    exact h
  · exact (congrFun ch _).trans ((oldH _).trans capH)
  · have h:=localT ((0 : Fin 1).natAdd (MatrixPacketWorkClear.count a+1))
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_right,Nat.zero_max] at h
    exact h
  · exact (congrFun ch _).trans (freshH 0)
  · change base.steps+1+cleared.steps≤_
    rw [cs]
    unfold budget
    dsimp [cap]
    omega

end NearCubicWires.RepairOrdinary.MatrixPacketBootstrapErase
