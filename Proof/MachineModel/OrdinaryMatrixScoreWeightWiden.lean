import Proof.MachineModel.OrdinaryMatrixScoreAccumulate

/-! Actual streamed selected weight followed by paid native-to-common-width
normalization. Global source and assignment cursors stay outside local resets. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightWiden
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 10 := ![6,4,7,8,9]
noncomputable def first : Machine 10 7 := TapeEmbedding.machine 4 MatrixScoreWeightSelect.fieldMachine
noncomputable def last : Machine 10 6 := RecoveryFocus.machine slots ClockNormalize.machine
noncomputable def machine : Machine 10 13 := Composition.machine first last

def cfg (q : Fin 13) (source assignment : List Bool) (pos apos w : ℕ)
    (positive negative native wide flag : List Bool) (loadCap normCap : ℕ) : Configuration 10 13 :=
  ⟨q,![pos,apos,0,0,0,0,0,0,0,0],
    ![source,assignment,positive,negative,native,List.replicate loadCap false,
      List.replicate w true,wide,flag,List.replicate normCap false]⟩

theorem widen_run (pre suffix apre asuffix bits : List Bool) (w : ℕ) (sign bit : Bool)
    (hw : bits.length≤w) :
    ∃ actual : ExecutionReceipt 10 13,
      runFrom machine (4*bits.length+4*w+11)
        (cfg 0 (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
          pre.length apre.length w [] [] [] [] [] 0 0)=some actual ∧
      actual.final=cfg 12 (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
        (pre.length+2*bits.length+3) (apre.length+2) w [bit && !sign] [bit && sign]
        (frame bits) (frame (binary w (RadixSemantics.value bits))) [true]
        (2*bits.length+1) (2*w+1) ∧ actual.steps=4*bits.length+4*w+11 := by
  let source := pre++frame (sign::bits)++suffix
  let assignment := apre++[true,bit]++asuffix
  obtain ⟨base,hb,hbf,hbs⟩ := MatrixScoreWeightSelect.field_run pre suffix apre asuffix [] [] [] bits 0
    sign bit (by simp) (by simp) (by simp)
  simp only [Nat.zero_max] at hbf
  let extra : Fin 4 → List Bool := ![List.replicate w true,[],[],[]]
  have he := TapeEmbedding.run_embed MatrixScoreWeightSelect.fieldMachine (fun _ : Fin 4 => 0)
    extra _ _ base hb
  let left := TapeEmbedding.receipt (fun _ : Fin 4 => 0) extra base
  obtain ⟨scalar,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w bits hw
  have hhalt := (prefix_of_run ClockNormalize.machine (4*w+4) _ scalar hr).2
  have hctrl : scalar.final.control=5 := by
    apply Fin.ext
    have hv := scalar.final.control.isLt
    revert hhalt
    generalize scalar.final.control=q
    intro hhalt
    fin_cases q <;> simp [ClockNormalize.machine,Rewind.machine,Fin.addCases] at hhalt ⊢
  have hst : scalar.final.tapes=![List.replicate w true,frame bits,
      frame (binary w (RadixSemantics.value bits)),[true],List.replicate (2*w+1) false] := by
    funext i; fin_cases i <;> assumption
  let entry := initialConfiguration ClockNormalize.machine (ClockNormalize.input w bits)
  have hi : RecoveryFocus.config slots left.final.heads left.final.tapes entry=
      Composition.restart left.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i <;> simp [slots,left,TapeEmbedding.receipt,TapeEmbedding.config,
        Fin.addCases,hbf,MatrixScoreWeightSelect.cfg,entry,initialConfiguration]
    · intro i
      fin_cases i <;> simp [slots,left,TapeEmbedding.receipt,TapeEmbedding.config,
        Fin.addCases,hbf,MatrixScoreWeightSelect.cfg,extra,entry,initialConfiguration,ClockNormalize.input]
  obtain ⟨right,hrr,hrf,hrs⟩ := RecoveryFocus.run_config slots (by decide) ClockNormalize.machine
    left.final.heads left.final.tapes _ entry scalar hr
  rw [hi] at hrr
  have hj := Composition.run_join first last (4*bits.length+6) (4*w+4) _ left right he hrr
  have hin : Composition.leftConfig 6
      (TapeEmbedding.config (fun _ : Fin 4 => 0) extra
        (MatrixScoreWeightSelect.cfg 0 source pre.length assignment apre.length [] [] [] 0))=
      cfg 0 source assignment pre.length apre.length w [] [] [] [] [] 0 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have htime : 4*bits.length+6+1+(4*w+4)=4*bits.length+4*w+11 := by omega
  rw [htime] at hj
  have pick (i : Fin 10) : RecoveryFocus.pick slots i=
      (![none,none,none,none,some 1,none,some 0,some 2,some 3,some 4] : Fin 10 → Option (Fin 5)) i := by
    fin_cases i
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 1
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · exact RecoveryFocus.pick_slot slots (by decide) 2
    · exact RecoveryFocus.pick_slot slots (by decide) 3
    · exact RecoveryFocus.pick_slot slots (by decide) 4
  refine ⟨Composition.joinedReceipt left right,hj,?_,?_⟩
  · change Composition.rightConfig 7 right.final=_
    rw [hrf]
    apply configuration_ext
    · change scalar.final.control.natAdd 7=12
      rw [hctrl]
      rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,pick,cfg,hh,left,
        TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hbf,MatrixScoreWeightSelect.cfg]
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,pick,cfg,hst,left,
        TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hbf,MatrixScoreWeightSelect.cfg,extra]
  · change base.steps+1+right.steps=_
    rw [hbs,hrs,hs]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreWeightWiden
