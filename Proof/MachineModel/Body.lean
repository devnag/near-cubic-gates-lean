import Proof.MachineModel.TailRound

/-! The whole five-stage occurrence body, with a capacity chosen before its
masked return and erase. Grouping existing binary compositions changes no
stage, data order, or paid handoff. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

noncomputable def occurrenceBody:=Composition.machine (sourceRound a) (tailRound a)

theorem source_extra_heads (pre size : ℕ) (H : Fin (T a) → ℕ) (KH : Fin (SB a) → ℕ)
    (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) :
    sourceHeads a pre size H KH (ex a j)=H (ex a j) := by
  rw [source_head_extra]
  exact dockH_other (copySlots a) _ _ _
    (notin_copy a (ex a j) (fun i=>bk_ne_ex a i j) (ex_ne a h0) (ex_ne a h7))

theorem source_extra_tapes (C : ℕ) (word source : List Bool) (A : Fin (T a) → List Bool)
    (K : Fin (SB a) → List Bool) (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) :
    sourceTapes a C word source A K (ex a j)=A (ex a j) := by
  rw [source_tape_extra]
  exact install_other (copySlots a) _ _ _
    (notin_copy a (ex a j) (fun i=>bk_ne_ex a i j) (ex_ne a h0) (ex_ne a h7))

theorem body_step (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest c1 c2 c3 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hbankT : ∀ i,A (bk a i)=List.replicate C false) (hbankH : ∀ i,H (bk a i)=0)
    (hstrT : A (str a)=pre++frame (nativeWord g)++rest) (hstrH : H (str a)=pre.length)
    (hfcpT : A (fcp a)=List.replicate C false) (hfcpH : H (fcp a)=0)
    (hcntT : A (cnt a)=c1) (hcntH : H (cnt a)=c1.length)
    (hbodT : A (bod a)=c2) (hbodH : H (bod a)=c2.length)
    (htotT : A (tot a)=c3) (htotH : H (tot a)=c3.length)
    (hdomT : A (dom a)=UnaryTemplate.tape q) (hdomH : H (dom a)=1)
    (hC : bodyCost a q g < C) :
    ∃ (K : Fin (SB a) → List Bool) (KH : Fin (SB a) → ℕ),
      Step (occurrenceBody a) (bodyCost a q g) H A
        (tailHeads a g c1 c2 c3 (sourceHeads a pre.length (frame (nativeWord g)).length H KH))
        (tailTapes a C g c1 c2 c3
          (sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K)) ∧
      (∀ i,(tailTapes a C g c1 c2 c3
        (sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K) (bk a i)).length=C) ∧
      (tailTapes a C g c1 c2 c3
        (sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K) (fcp a)).length=C := by
  have cap : (frame (nativeWord g)).length+Counted.budget a (request g) ≤ C := by
    unfold bodyCost at hC
    omega
  have childcap : (children a g).length+2 ≤ C := by
    unfold bodyCost at hC
    omega
  obtain ⟨K,KH,first,srcT,srcH,kT,kH,fH,_kb⟩:=source_round a C q g pre rest H A
    hbankT hbankH hstrT hstrH hfcpT hfcpH cap
  let midH:=sourceHeads a pre.length (frame (nativeWord g)).length H KH
  let midA:=sourceTapes a C (nativeWord g) (pre++frame (nativeWord g)++rest) A K
  have keepH (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) : midH (ex a j)=H (ex a j):=
    source_extra_heads a _ _ H KH j h0 h7
  have keepT (j : Fin 12) (h0 : j.val≠0) (h7 : j.val≠7) : midA (ex a j)=A (ex a j):=
    source_extra_tapes a C _ _ A K j h0 h7
  have last:=tail_round a C q g c1 c2 c3 midH midA
    ((source_tape_bank a C _ _ A K _).trans srcT) ((source_head_bank a _ _ H KH _).trans srcH)
    ((source_head_bank a _ _ H KH _).trans fH)
    ((keepT 1 (by decide) (by decide)).trans hcntT) ((keepH 1 (by decide) (by decide)).trans hcntH)
    ((keepT 2 (by decide) (by decide)).trans hbodT) ((keepH 2 (by decide) (by decide)).trans hbodH)
    ((keepT 10 (by decide) (by decide)).trans hdomT) ((keepH 10 (by decide) (by decide)).trans hdomH)
    ((source_tape_bank a C _ _ A K _).trans kT) ((source_head_bank a _ _ H KH _).trans kH)
    ((keepT 3 (by decide) (by decide)).trans htotT) ((keepH 3 (by decide) (by decide)).trans htotH) childcap
  have whole:=first.seq last
  have time:(2*(frame (nativeWord g)).length+2)+1+Counted.budget a (request g)+1+tailCost a g=bodyCost a q g:=by
    unfold tailCost bodyCost
    omega
  rw [time] at whole
  refine ⟨K,KH,whole,?_,?_⟩
  · intro i
    obtain ⟨result,hr,_rh,rt,_rs⟩:=whole
    have bounded:=length_preserved (occurrenceBody a) (bodyCost a q g) _ result (bk a i) hr
      (by simp only [hbankH,hbankT,List.length_replicate,Nat.zero_add];exact hC)
    change (result.final.tapes (bk a i)).length = (A (bk a i)).length at bounded
    rw [rt,hbankT,List.length_replicate] at bounded
    exact bounded
  · obtain ⟨result,hr,_rh,rt,_rs⟩:=whole
    have bounded:=length_preserved (occurrenceBody a) (bodyCost a q g) _ result (fcp a) hr
      (by simp only [hfcpH,hfcpT,List.length_replicate,Nat.zero_add];exact hC)
    change (result.final.tapes (fcp a)).length = (A (fcp a)).length at bounded
    rw [rt,hfcpT,List.length_replicate] at bounded
    exact bounded

end NearCubicWires.ExtDecompositionBatch
