import Proof.Amplification.RecoveryPCPFormulaResumeSparseRows

/-! Exact complete formula entry: the original sources and nine row
drivers, plus the actual unary tautology count. Every other tape is blank. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open CanonicalRecoveryLanguage BalancedCNFSATEncoding RecoveryPCPFormulaResumePrefix
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryData (p : RawProjectionPCP) (R Q cap : Nat) (i : Fin 716) : List Bool :=
  Fin.addCases (m:=319) (n:=397) (motive:=fun _=>List Bool) (rowData p R Q cap)
    (fun j=>if j.val=241 then List.replicate (2^R) true else []) i

theorem prefix_coverage (i : Fin 580) (hi : (319 : Nat)≤(i : Fin 580).val) : ∃ j,prefixSlots j=i := by
  have hil:=i.isLt
  by_cases hj : i.val<558
  · refine ⟨⟨i.val-319,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [prefixSlots]
    split_ifs <;> omega
  · refine ⟨⟨i.val-318,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [prefixSlots]
    split_ifs <;> omega

theorem prefix_entry (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 580) :
    omitBlank (RecoveryPCPFormulaResumePrefix.input p R Q cap logCap resetCap i)=
      omitBlank (entryData p R Q cap (i.castAdd 136)) := by
  by_cases hi : i.val<319
  · let j : Fin 319 := ⟨i.val,hi⟩
    have he : rowSlots j=i := Fin.ext rfl
    rw [←he,input_rows,row_data]
    have hcast : (rowSlots j).castAdd 136=j.castAdd 397 := Fin.ext rfl
    rw [hcast,entryData,Fin.addCases_left]
  · obtain ⟨j,hj⟩ := prefix_coverage i (by omega)
    have hn : j.val≠239 := by
      intro h
      have he : j=239 := Fin.ext h
      subst j
      rw [←hj] at hi
      contradiction
    rw [←hj,RecoveryPCPFormulaResumePrefix.input,install_slot prefixSlots prefix_injective]
    have hlarge : 319≤(prefixSlots j).val := by rw [hj]; omega
    let k : Fin 397 := ⟨(prefixSlots j).val-319,by have hjl:=(prefixSlots j).isLt; omega⟩
    have hcast : (prefixSlots j).castAdd 136=k.natAdd 319 := by
      apply Fin.ext
      simp only [Fin.val_castAdd,Fin.val_natAdd]
      dsimp [k]; omega
    rw [hcast,entryData,Fin.addCases_right]
    simp only [RecoveryTseitinTautology.Cold.driversInput]
    have he : k.val=241 ↔ j=242 := by
      constructor
      · intro h
        have hjl:=j.isLt
        apply Fin.ext
        dsimp [k,prefixSlots] at h
        split_ifs at h <;> omega
      · rintro rfl; rfl
    simp only [he]

theorem sparse_entry (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) :
    sparseInput p R Q cap logCap resetCap=fun i=>omitBlank (entryData p R Q cap i) := by
  funext i
  simp only [sparseInput,RecoveryPCPFormulaResumeSerialize.input,RecoveryPCPFormulaResumePrefix.framedInput,
    ]
  refine Fin.addCases (m:=584) (n:=132) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=582) (n:=2) (fun i=>?_) (fun i=>?_) i
    · refine Fin.addCases (m:=581) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=580) (n:=1) (fun i=>?_) (fun i=>?_) i
        · simp only [Fin.addCases_left,AppendOutputFrame.input,AppendOutputLength.input]
          have he : (((i.castAdd 1).castAdd 1).castAdd 2).castAdd 132=i.castAdd 136 := Fin.ext rfl
          rw [he]
          exact prefix_entry p R Q cap logCap resetCap i
        · fin_cases i; rfl
      · fin_cases i; rfl
    · fin_cases i <;> rfl
  · simp only [Fin.addCases_right]
    let k : Fin 397 := ⟨265+i.val,by have hi:=i.isLt; omega⟩
    have he : i.natAdd 584=k.natAdd 319 := by apply Fin.ext; dsimp [k]; omega
    rw [he,entryData,Fin.addCases_right,if_neg (by dsimp [k]; omega)]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
