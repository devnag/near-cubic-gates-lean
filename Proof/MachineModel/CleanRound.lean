import Proof.MachineModel.BodyPorts
import Proof.MachineModel.CleanLayout

/-! One actual occurrence calls the selected constructor and then pays the
masked return and source-bank erase. Live accumulators stay outside the erase. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

noncomputable def resetBody:=MaskedReset.machine (occurrenceBody a) (resetSelected a)
noncomputable def cleanRound:=Composition.machine (resetBody a) (eraseBody a)
def roundCost {q : ℕ} (C : ℕ) (g : SupportedNormalizedGate q):=2*bodyCost a q g+2+1+(2*C+4)
def maskedHeads (H : Fin (T a) → ℕ) : Fin (CT a) → ℕ :=
  Fin.addCases (fun i=>if resetSelected a i then 0 else H i) (fun _=>0)
def loggedTapes (C : ℕ) (A : Fin (T a) → List Bool) : Fin (CT a) → List Bool :=
  Fin.addCases A (fun _=>List.replicate C false)

theorem selected_bank (i : Fin (SB a)) : resetSelected a (bk a i)=true := by
  simp only [resetSelected,decide_eq_true_eq,bk_val]
  exact Or.inl i.isLt
theorem selected_counter : resetSelected a (fcp a)=true := by simp [resetSelected]
theorem selected_extra (j : Fin 12) (hj : j≠7) : resetSelected a (ex a j)=false := by
  unfold resetSelected
  apply decide_eq_false
  intro h
  rcases h with h|h
  · have hv:=ex_val a j
    omega
  · exact hj (ex_injective a h)

theorem cleaned_body (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest c1 c2 c3 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hbankT : ∀ i,A (bk a i)=List.replicate C false) (hbankH : ∀ i,H (bk a i)=0)
    (hstrT : A (str a)=pre++frame (nativeWord g)++rest) (hstrH : H (str a)=pre.length)
    (hfcpT : A (fcp a)=List.replicate C false) (hfcpH : H (fcp a)=0)
    (hcntT : A (cnt a)=c1) (hcntH : H (cnt a)=c1.length)
    (hbodT : A (bod a)=c2) (hbodH : H (bod a)=c2.length)
    (htotT : A (tot a)=c3) (htotH : H (tot a)=c3.length)
    (hdomT : A (dom a)=UnaryTemplate.tape q) (hdomH : H (dom a)=1)
    (hdrvT : A (drv a)=List.replicate C true) (hdrvH : H (drv a)=0)
    (hwspT : A (wsp a)=List.replicate (C+1) false) (hwspH : H (wsp a)=0)
    (hC : bodyCost a q g < C) :
    ∃ (K : Fin (SB a) → List Bool) (KH : Fin (SB a) → ℕ),
      let OH:=tailHeads a g c1 c2 c3 (sourceHeads a pre.length (frame (nativeWord g)).length H KH)
      let OA:=tailTapes a C g c1 c2 c3
        (sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K)
      Step (cleanRound a) (roundCost a C g)
        (Fin.addCases H (fun _ : Fin 1=>0)) (loggedTapes a C A)
        (dockH (eraseSlots a) (maskedHeads a OH) (fun _=>0))
        (install (eraseSlots a) (loggedTapes a C OA) (cleanData a C)) := by
  obtain ⟨K,KH,body,bankLen,copyLen⟩:=body_step a C q g pre rest c1 c2 c3 H A
    hbankT hbankH hstrT hstrH hfcpT hfcpH hcntT hcntH hbodT hbodH htotT htotH hdomT hdomH hC
  let SH:=sourceHeads a pre.length (frame (nativeWord g)).length H KH
  let SA:=sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K
  let OH:=tailHeads a g c1 c2 c3 SH
  let OA:=tailTapes a C g c1 c2 c3 SA
  have start : ∀ i,resetSelected a i=true → H i=0 := by
    intro i hi
    have selected : i.val<SB a ∨ i=fcp a := of_decide_eq_true hi
    rcases selected with hb|hf
    · have he:i=bk a ⟨i.val,hb⟩:=Fin.ext rfl
      rw [he]
      exact hbankH _
    · rw [hf];exact hfcpH
  have masked:=body.mask (resetSelected a) start (Nat.le_of_lt hC)
  have keep8 : OH (drv a)=0 ∧ OA (drv a)=List.replicate C true := by
    obtain ⟨hh,ht⟩:=tail_ports a C q g c1 c2 c3 SH SA 8
    simp only [tailPortHeads,tailPortTapes,Fin.isValue] at hh ht
    exact ⟨hh.trans ((source_extra_heads a _ _ H KH 8 (by decide) (by decide)).trans hdrvH),
      ht.trans ((source_extra_tapes a C _ _ A K 8 (by decide) (by decide)).trans hdrvT)⟩
  have keep9 : OH (wsp a)=0 ∧ OA (wsp a)=List.replicate (C+1) false := by
    obtain ⟨hh,ht⟩:=tail_ports a C q g c1 c2 c3 SH SA 9
    simp only [tailPortHeads,tailPortTapes,Fin.isValue] at hh ht
    exact ⟨hh.trans ((source_extra_heads a _ _ H KH 9 (by decide) (by decide)).trans hwspH),
      ht.trans ((source_extra_tapes a C _ _ A K 9 (by decide) (by decide)).trans hwspT)⟩
  have erase:=erase_body a C (maskedHeads a OH) (loggedTapes a C OA) (by
    intro j
    refine Fin.addCases (m:=SB a+1+1) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=SB a+1) (n:=1) (fun k=>?_) (fun k=>?_) i
      · refine Fin.addCases (m:=SB a) (n:=1) (fun l=>?_) (fun l=>?_) k
        · rw [eraseSlots_bank]
          simp only [maskedHeads,Fin.addCases_left,selected_bank,↓reduceIte]
        · have hl:l=0:=Fin.eq_zero l
          subst hl
          rw [eraseSlots_counter]
          simp only [maskedHeads,Fin.addCases_left,selected_counter,↓reduceIte]
      · have hk:k=0:=Fin.eq_zero k
        subst hk
        rw [eraseSlots_driver]
        simpa only [maskedHeads,Fin.addCases_left,drv,selected_extra a 8 (by decide),Bool.false_eq_true,↓reduceIte] using keep8.1
    · have hi:i=0:=Fin.eq_zero i
      subst hi
      rw [eraseSlots_workspace]
      simpa only [maskedHeads,Fin.addCases_left,wsp,selected_extra a 9 (by decide),Bool.false_eq_true,↓reduceIte] using keep9.1)
    (by
      intro j
      refine Fin.addCases (m:=SB a) (n:=1) (fun i=>?_) (fun i=>?_) j
      · rw [eraseSlots_bank]
        simpa only [loggedTapes,Fin.addCases_left] using Nat.le_of_eq (bankLen i)
      · have hi:i=0:=Fin.eq_zero i
        subst hi
        rw [eraseSlots_counter]
        simpa only [loggedTapes,Fin.addCases_left] using Nat.le_of_eq copyLen)
    (by simpa only [loggedTapes,Fin.addCases_left] using keep8.2)
    (by simpa only [loggedTapes,Fin.addCases_left] using keep9.2)
  exact ⟨K,KH,masked.seq erase⟩

end NearCubicWires.ExtDecompositionBatch
