import Proof.Amplification.RecoveryProjectionScalarPrepare

/-! Complete execution of the first normalized address row batch from its
literal scalar and source fields. No prepared-bank, unary-driver, random-word
or evaluator-time assumptions remain. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionColdRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization RecoveryProjectionRows RecoveryProjectionScalar
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rowsMachine := RecoveryFocus.machine coreSlots RecoveryProjectionRows.machine
noncomputable def machine (C : Nat) := Composition.machine (prepareMachine C) rowsMachine
def budget (C R Q : Nat) := prepareBudget C R.bits Q.bits+1+(Q*(R*(4*capacity R+11)+8)+3)

theorem zero_word (R : Nat) : List.ofFn (fun _ : Fin R=>false)=List.replicate R false := by
  simp only [List.ofFn_const]

theorem capacity_initialization (R : Nat) : 2*R+3≤capacity R := by
  have hpow : R+1≤(R+1)^4 := Nat.le_self_pow (by decide) _
  unfold capacity
  omega

theorem cold_run (C : Nat) (hC : C=1048576) (p : RawProjectionPCP) (R Q : Nat)
    (hr : p.width≤R) (hq : p.queries≤Q) {n : Nat} (x : BitInput n) : ∃ r,
    run (machine C) (budget C R Q)
      (RecoveryProjectionScalar.input R.bits Q.bits (QueryBytes.framedCodes (normalizedRows p R Q).flatten))=some r ∧
      r.final.tapes 31=FieldList.stream (addressFields p R Q hr hq x (fun _=>false)) ∧
      r.steps≤budget C R Q := by
  have hcap : C*(value R.bits+1)^4=capacity R := by rw [DimensionProducer.bits_value,hC]; rfl
  obtain ⟨first,hfirst,fh,ft,fs⟩ := prepare_run C R.bits Q.bits
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten) (by rw [hcap,DimensionProducer.bits_value]; exact capacity_initialization R)
  rw [hcap,DimensionProducer.bits_value,DimensionProducer.bits_value] at fh ft
  obtain ⟨base,hbase,bf,bs⟩ := normalized_run p R Q hr hq x (fun _=>false) [] [] [] []
  simp only [List.nil_append,List.append_nil,zero_word,List.length_nil] at hbase bf
  obtain ⟨last,hlast,_hcontrol,lastSteps,_lastHeads,lastTapes,_other⟩ := RecoveryFocus.dock coreSlots core_injective
    RecoveryProjectionRows.machine _ first.final.heads first.final.tapes _ fh ft base hbase
  have hall := Composition.run_join (prepareMachine C) rowsMachine _ _ _ first last hfirst hlast
  refine ⟨_,hall,?_,?_⟩
  · change last.final.tapes (coreSlots 31)=_
    rw [lastTapes,bf]
    rfl
  · change first.steps+1+last.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairSource.RecoveryProjectionColdRows
