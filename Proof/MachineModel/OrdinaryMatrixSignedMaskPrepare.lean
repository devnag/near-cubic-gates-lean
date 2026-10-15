import Proof.MachineModel.OrdinaryMatrixCoefficientBitPass

/-! The retained coefficient bank physically produces a padded mask in one
ordinary call: every gate bit is extracted, the bank/output are returned,
bucket copies and trailing zeros are written, and the mask is returned. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedMaskPrepare
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 13 := ![6,3,11,4,7,12]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first (negative : Bool) := TapeEmbedding.machine 7 (MatrixCoefficientBitPass.machine negative)
noncomputable def last := RecoveryFocus.machine slots MatrixMaskPad.machine
noncomputable def machine (negative : Bool) := Composition.machine (first negative) last
def extraHeads : Fin 7 → ℕ := ![1,1,1,1,0,0,0]
noncomputable def extraTapes (r : Request) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape r.Buckets,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.Capacity,
    UnaryTemplate.tape r.U,MatrixBucketLeftPlane.plane r,[],[]]
noncomputable def input (r : Request) (negative flag : Bool) (t : ℕ) :=
  Composition.leftConfig (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (2+3))+5+2) (TapeEmbedding.config extraHeads (extraTapes r) (MatrixCoefficientBitPass.input r negative flag t))
def budget (r : Request) := MatrixCoefficientBitPass.budget r+1+MatrixMaskPad.budget r.Buckets (r.Capacity-r.Used) r.Gates
noncomputable def output (r : Request) (negative flag : Bool) (t nb nm : ℕ) : Fin 13 → List Bool :=
  ![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape (2*t),
    [MatrixCoefficientBitLoop.finalFlag negative flag (MatrixCoefficientBitNative.coefficients r)],
    MatrixCoefficientBitNative.output r negative t,UnaryTemplate.tape r.Gates,List.replicate nb false,
    UnaryTemplate.tape r.Buckets,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.Capacity,
    UnaryTemplate.tape r.U,MatrixBucketLeftPlane.plane r,MatrixMaskSemantics.mask r negative t,List.replicate nm false]
def finalHeads (r : Request) : Fin 13 → ℕ := ![0,1,0,r.Gates,1,0,1,1,1,1,0,0,0]

theorem mask_run (r : Request) (negative flag : Bool) (t : ℕ) (ht : t<r.p) : ∃ nb nm,∃ actual,
    runFrom (machine negative) (budget r) (input r negative flag t)=some actual ∧
    actual.final.tapes=output r negative flag t nb nm ∧ actual.final.heads=finalHeads r ∧
    nb≤MatrixCoefficientBitNative.budget r ∧ nm≤MatrixMaskPad.forwardBudget r.Buckets (r.Capacity-r.Used) r.Gates ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,logH,⟨nb,logT,nbound⟩,bs⟩ := MatrixCoefficientBitPass.pass_run r negative flag t ht
  have he := TapeEmbedding.run_embed (MatrixCoefficientBitPass.machine negative) extraHeads (extraTapes r) _ _ base hb
  let prepared := TapeEmbedding.receipt extraHeads (extraTapes r) base
  obtain ⟨body,hr,rt,rh,rlh,⟨nm,rlt,nmbound⟩,rs⟩ := MatrixMaskPad.mask_run r.Buckets (r.Capacity-r.Used)
    (MatrixCoefficientBitNative.output r negative t)
  have gl := MatrixMaskSemantics.gate_bits_length r negative t
  rw [gl] at hr nmbound rs
  let entry := MatrixMaskPad.input r.Buckets (r.Capacity-r.Used) (MatrixCoefficientBitNative.output r negative t)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · rfl
      · exact bh 3
      · rfl
      · exact bh 4
      · rfl
      · rfl
    · intro j
      fin_cases j
      · rfl
      · exact bt 3
      · rfl
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,MatrixMaskPad.input,Rewind.recording,Rewind.config,MatrixMaskPad.cfg,gl,Fin.addCases] using bt 4
      · rfl
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixMaskPad.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join (first negative) last _ _ _ prepared focused he hf
  have pick (i : Fin 13) : RecoveryFocus.pick slots i=
      (![none,none,none,some 1,some 3,none,some 0,some 4,none,none,none,some 2,some 5] : Fin 13 → Option (Fin 6)) i := by
    fin_cases i <;> first | decide | exact RecoveryFocus.pick_slot slots slots_injective 0 | exact RecoveryFocus.pick_slot slots slots_injective 1 | exact RecoveryFocus.pick_slot slots slots_injective 2 | exact RecoveryFocus.pick_slot slots slots_injective 3 | exact RecoveryFocus.pick_slot slots slots_injective 4 | exact RecoveryFocus.pick_slot slots slots_injective 5
  have pt (i : Fin 13) : prepared.final.tapes i=
      Fin.addCases (m := 6) (n := 7) (motive := fun _ => List Bool)
        (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
          (![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape (2*t),
            [MatrixCoefficientBitLoop.finalFlag negative flag (MatrixCoefficientBitNative.coefficients r)],
            MatrixCoefficientBitNative.output r negative t,UnaryTemplate.tape r.Gates]) (fun _ => List.replicate nb false))
        (extraTapes r) i := by
    fin_cases i <;> first | exact bt 0 | exact bt 1 | exact bt 2 | exact bt 3 | exact bt 4 | exact logT | rfl
  have ph (i : Fin 13) : prepared.final.heads i=
      (![0,1,0,0,1,0,1,1,1,1,0,0,0] : Fin 13 → ℕ) i := by
    fin_cases i <;> first | exact bh 0 | exact bh 1 | exact bh 2 | exact bh 3 | exact bh 4 | exact logH | rfl
  have rt' (i : Fin 6) : body.final.tapes i=
      (![UnaryTemplate.tape r.Buckets,MatrixCoefficientBitNative.output r negative t,MatrixMaskSemantics.mask r negative t,
        UnaryTemplate.tape r.Gates,UnaryTemplate.tape (r.Capacity-r.Used),List.replicate nm false] : Fin 6 → List Bool) i := by
    fin_cases i
    · exact rt 0
    · exact rt 1
    · exact rt 2
    · simpa [MatrixMaskPad.cfg,gl] using rt 3
    · exact rt 4
    · exact rlt
  have rh' (i : Fin 6) : body.final.heads i=(![1,r.Gates,0,1,1,0] : Fin 6 → ℕ) i := by
    fin_cases i
    · exact rh 0
    · exact (rh 1).trans gl
    · exact rh 2
    · exact rh 3
    · exact rh 4
    · exact rlh
  refine ⟨nb,nm,Composition.joinedReceipt prepared focused,hj,?_,?_,nbound,nmbound,?_⟩
  · change focused.final.tapes=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,pick]
    fin_cases i
    all_goals simp [pt,rt',output,extraTapes,Fin.addCases]
  · change focused.final.heads=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,pick]
    fin_cases i <;> simp [ph,rh',finalHeads]
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixSignedMaskPrepare
