import Proof.MachineModel.OrdinaryMatrixBatchGatePrepare

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateBody
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The gate's 44 tapes in the 48-tape batch: fields `0..26` in place, the `φ` columns (field 27) on
batch tape 42, fields `28..41` on batch tapes `27..40`, the packet output on 41 and its counter on the
shared counter 47. -/
def native : Fin 44 → Fin 48 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,42,
    27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,47]
theorem native_injective : Function.Injective native := by decide
theorem native_cover (j : Fin 48) : (∃ k,native k=j) ∨ j=43 ∨ j=44 ∨ j=45 ∨ j=46 := by
  fin_cases j <;> decide
theorem native_oldSlot (j : Fin 41) : native ((MatrixScorePhiFields.oldSlot j).castAdd 2)=j.castAdd 7 := by
  fin_cases j <;> rfl
theorem heads_native (pos outlen : ℕ) (i : Fin 42) :
    heads pos outlen (native (i.castAdd 2))=MatrixScoreRetainedRanks.retainedHeads i := by
  fin_cases i <;> rfl
theorem ranked_tapes (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (MatrixBatchRankedGate.input r gate out).tapes=
      Fin.addCases (m := 42) (n := 2) (motive := fun _ => List Bool)
        (fun i => ZeroPadding.pad (MatrixScoreReusableRanks.capacities r i) (MatrixScoreReusableRanks.fields r gate i))
        ![out,List.replicate (D r) false] := by
  change (Fin.addCases (m := 42) (n := 2) (motive := fun _ => List Bool)
    (fun i => ZeroPadding.pad (MatrixScoreReusableRanks.capacities r i)
      ((MatrixScoreRetainedRanks.input r gate (MatrixScoreReusableRanks.cold r)).tapes i))
    ![out,List.replicate (D r) false])=_
  rw [MatrixScoreReusableRanks.input_fields]
theorem ranked_heads (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (MatrixBatchRankedGate.input r gate out).heads=
      Fin.addCases (m := 42) (n := 2) (motive := fun _ => ℕ)
        MatrixScoreRetainedRanks.retainedHeads ![out.length,0] := by
  change (Fin.addCases (m := 42) (n := 2) (motive := fun _ => ℕ)
    (MatrixScoreRetainedRanks.input r gate (MatrixScoreReusableRanks.cold r)).heads ![out.length,0])=_
  rw [MatrixScoreReusableRanks.input_heads]
theorem input_tapes (r : Request) (gate : Fin r.Gates) (cap : ℕ) (source out : List Bool) (i : Fin 44) :
    tapes r 0 0 cap source out (MatrixBatchGateBank.loaded r gate) (native i)=
      (MatrixBatchRankedGate.input r gate out).tapes i := by
  rw [ranked_tapes]
  fin_cases i <;> simp [native,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
    MatrixBatchGateClear.stable,MatrixBatchGateBank.loaded,Fin.addCases,MatrixScoreReusableRanks.fields,
    MatrixScorePhiFields.fields,MatrixScoreReusableRanks.capacities,MatrixScoreReusableRanks.fixed,ZeroPadding.pad,
    MatrixScoreWeight.zeros]
theorem input_heads (r : Request) (gate : Fin r.Gates) (pos : ℕ) (out : List Bool) (i : Fin 44) :
    heads pos out.length (native i)=(MatrixBatchRankedGate.input r gate out).heads i := by
  rw [ranked_heads]
  fin_cases i <;> rfl

noncomputable def call := RecoveryFocus.machine native MatrixBatchRankedGate.machine
noncomputable def machine := Composition.machine MatrixBatchGatePrepare.machine call
noncomputable def budget (r : Request) (gate : Fin r.Gates) :=
  MatrixBatchGatePrepare.budget r+1+MatrixBatchRankedGate.budget r gate
noncomputable def input (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 30 → List Bool) :=
  RecoveryCalls.restarted machine (heads pre.length out.length)
    (tapes r assignment id cap (pre++cutWord r.p (r.cuts.get gate)++suffix) out backing)

theorem body_run (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 30 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ final : MatrixScoreLeftLoop.State r,∃ actual,
      runFrom machine (budget r gate) (input r gate assignment id cap pre suffix out backing)=some actual ∧
      actual.final.heads=heads (pre.length+(cutWord r.p (r.cuts.get gate)).length)
        (out++MatrixScoreRawRanks.output r gate).length ∧
      actual.final.tapes 41=out++MatrixScoreRawRanks.output r gate ∧
      actual.final.tapes 43=frame (SignedSortKey.binary r.M 0) ∧
      actual.final.tapes 44=List.replicate (D r) true ∧
      actual.final.tapes 45=List.replicate (max cap (D r+1)) false ∧
      actual.final.tapes 46=pre++cutWord r.p (r.cuts.get gate)++suffix ∧
      actual.final.tapes 47=List.replicate (D r) false ∧
      (∀ i : Fin 30,i≠24 → actual.final.tapes (native (i.castAdd 14))=
        ZeroPadding.pad (MatrixScoreReusableRanks.capacities r (i.castAdd 12))
          (MatrixScoreRetainedRanks.finalFields r gate final i)) ∧
      (∀ j : Fin 41,(actual.final.tapes (j.castAdd 7)).length≤D r) ∧
      actual.steps≤budget r gate := by
  obtain ⟨prepared,hp,ph,pt,ps⟩ := MatrixBatchGatePrepare.prepare_run r gate assignment id cap pre suffix out backing hb
  obtain ⟨final,body,hr,b42,h42,b43,h43,bt,bh,bfit,bs⟩ := MatrixBatchRankedGate.gate_run r gate out
  have hi : RecoveryFocus.config native prepared.final.heads prepared.final.tapes (MatrixBatchRankedGate.input r gate out)=
      Composition.restart prepared.final call.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [ph]
      exact input_heads r gate _ out i
    · intro i
      rw [pt]
      exact input_tapes r gate _ _ out i
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config native native_injective MatrixBatchRankedGate.machine
    prepared.final.heads prepared.final.tapes _ _ body hr
  rw [hi] at hf
  have joined := Composition.run_join MatrixBatchGatePrepare.machine call _ _ _ prepared focused hp hf
  have localT (i : Fin 44) : focused.final.tapes (native i)=body.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot native native_injective]
  have localH (i : Fin 44) : focused.final.heads (native i)=body.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot native native_injective]
  have freshT (j : Fin 48) (hj : RecoveryFocus.pick native j=none) : focused.final.tapes j=prepared.final.tapes j := by
    rw [hff]
    simp only [RecoveryFocus.config,hj]
  have freshH (j : Fin 48) (hj : RecoveryFocus.pick native j=none) : focused.final.heads j=prepared.final.heads j := by
    rw [hff]
    simp only [RecoveryFocus.config,hj]
  have constants : focused.final.tapes 43=frame (SignedSortKey.binary r.M 0) ∧
      focused.final.tapes 44=List.replicate (D r) true ∧
      focused.final.tapes 45=List.replicate (max cap (D r+1)) false ∧
      focused.final.tapes 46=pre++cutWord r.p (r.cuts.get gate)++suffix := by
    have hf0 := (freshT 43 (by decide)).trans (congrFun pt 43)
    have hf1 := (freshT 44 (by decide)).trans (congrFun pt 44)
    have hf2 := (freshT 45 (by decide)).trans (congrFun pt 45)
    have hf3 := (freshT 46 (by decide)).trans (congrFun pt 46)
    simpa [tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
      MatrixBatchGateClear.stable,MatrixBatchGateBank.loaded] using And.intro hf0 (And.intro hf1 (And.intro hf2 hf3))
  refine ⟨final,Composition.joinedReceipt prepared focused,joined,?_,(localT 42).trans b42,
    constants.1,constants.2.1,constants.2.2.1,constants.2.2.2,(localT 43).trans b43,?_,?_,?_⟩
  · change focused.final.heads=_
    funext j
    rcases native_cover j with ⟨k,rfl⟩ | rfl | rfl | rfl | rfl
    · rw [localH k]
      refine Fin.addCases (m := 42) (n := 2) (motive := fun k => body.final.heads k=
        heads (pre.length+(cutWord r.p (r.cuts.get gate)).length) (out++MatrixScoreRawRanks.output r gate).length
          (native k)) ?_ ?_ k
      · intro i
        exact (bh i).trans (heads_native _ _ i).symm
      · intro i
        fin_cases i
        · exact h42
        · exact h43
    · exact (freshH 43 (by decide)).trans (congrFun ph 43)
    · exact (freshH 44 (by decide)).trans (congrFun ph 44)
    · exact (freshH 45 (by decide)).trans (congrFun ph 45)
    · exact (freshH 46 (by decide)).trans (congrFun ph 46)
  · intro i hn
    exact (localT (i.castAdd 14)).trans (bt i hn)
  · intro j
    rw [←native_oldSlot j]
    exact (congrArg List.length (localT _)).trans_le (bfit _)
  · change prepared.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateBody
