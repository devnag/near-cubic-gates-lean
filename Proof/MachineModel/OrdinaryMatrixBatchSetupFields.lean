import Proof.MachineModel.OrdinaryMatrixBatchSetup

/-! Expose the two native arithmetic constants retained by the same
accepted batch setup program for its following physical field initializer. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchSetupFields
open LocalBitMultitape SignedSortKey MatrixScoreBatch RepairRepresentation MatrixBatchSetup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem setup_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=word r ∧ actual.final.heads 1=gatesEnd r ∧
      actual.final.tapes 23=List.replicate r.d true ∧ actual.final.heads 23=0 ∧
      actual.final.tapes 28=List.replicate r.M true ∧ actual.final.heads 28=0 ∧
      actual.final.tapes 32=frame (binary r.M r.U) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=1 ∧
      actual.final.tapes 40=List.replicate r.p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 49=List.replicate (r.S+1) true ∧ actual.final.heads 49=0 ∧
      actual.final.tapes 61=frame (binary (r.S+1) (2^r.S)) ∧ actual.final.heads 61=0 ∧
      actual.final.tapes 65=frame (binary (r.S+1) 0) ∧ actual.final.heads 65=0 ∧
      actual.final.tapes 77=List.replicate (MatrixScoreLeftLoop.C r) true ∧ actual.final.heads 77=0 ∧
      actual.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 80=0 ∧
      actual.final.tapes 83=frame (binary (natBitLength r.Gates) r.Gates) ∧ actual.final.heads 83=0 ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=1 ∧
      actual.steps≤budget r := by
  let suffix := tail r
  have hword : natWord r.d++natWord r.p++(natWord r.Gates++suffix)=word r := word_eq r
  have hwidth : MatrixScoreSetup.width r.d r.p=r.S+1 := rfl
  have hcapacity : MatrixScoreSetup.capacity r.d r.p=MatrixScoreLeftLoop.C r := by
    unfold MatrixScoreSetup.capacity MatrixScoreCommonCapacity.capacity MatrixScoreCapacity.capacity
      MatrixScoreLeftLoop.C
    rw [common_width,hwidth]
  obtain ⟨base,hb,b0,h0,b1,h1,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,b61,h61,b65,h65,b77,h77,bs⟩ :=
    MatrixScoreSetup.setup_run r.d r.p (natWord r.Gates++suffix)
  rw [hword] at hb b0 b1
  have he := TapeEmbedding.run_embed MatrixScoreSetup.machine (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨parsed,hp,pt,ph,pw,pwh,_,_,pg,pgh,pu,puh,ps⟩ := MatrixDimensionPrepare.prepare_run
    (natWord r.d++natWord r.p) suffix (natBitLength r.Gates) r.Gates (Nat.lt_pow_succ_log_self (by decide) _)
  have hsource : (natWord r.d++natWord r.p)++List.replicate (natBitLength r.Gates) true++
      false::(binary (natBitLength r.Gates) r.Gates++suffix)=word r := by
    rw [←word_eq r]
    simp [suffix,WilliamsInputHeader.natWord_eq,List.append_assoc]
  rw [hsource] at hp pt
  let entry : Configuration 11 WilliamsInputHeader.dimensionStates := Composition.leftConfig _ (MatrixDimensionPrepare.input (word r) (natWord r.d++natWord r.p).length)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · change base.final.heads 1=(natWord r.d++natWord r.p).length
        simpa only [List.length_append,MatrixScoreRawGateBounds.natWord_length] using h1
      all_goals rfl
    · intro i
      fin_cases i
      · exact b1
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixDimensionPrepare.machine
    prepared.final.heads prepared.final.tapes _ entry parsed hp
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixScoreSetup.machine (MatrixScoreSetup.input (word r))))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have otherT (i : Fin 80) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 80) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 11) : focused.final.tapes (slots i)=parsed.final.tapes i := by
    rw [hff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have localH (i : Fin 11) : focused.final.heads (slots i)=parsed.final.heads i := by
    rw [hff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  refine ⟨Composition.joinedReceipt prepared focused,joined,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (localT 0).trans pt,?_,(otherT 23 (by decide)).trans b23,(otherH 23 (by decide)).trans h23,
    ?_,(otherH 28 (by decide)).trans h28,?_,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (otherT 40 (by decide)).trans b40,(otherH 40 (by decide)).trans h40,
    ?_,(otherH 49 (by decide)).trans h49,?_,(otherH 61 (by decide)).trans h61,
    ?_,(otherH 65 (by decide)).trans h65,?_,(otherH 77 (by decide)).trans h77,
    (localT 1).trans pw,(localH 1).trans pwh,(localT 4).trans pg,(localH 4).trans pgh,
    (localT 10).trans pu,(localH 10).trans puh,?_⟩
  · change focused.final.heads (slots 0)=_
    rw [localH,ph]
    simp only [gatesEnd,List.length_append,MatrixScoreRawGateBounds.natWord_length]
    omega
  · rw [common_width]
    exact (otherT 28 (by decide)).trans b28
  · rw [common_width]
    exact (otherT 32 (by decide)).trans b32
  · rw [←hwidth]
    exact (otherT 49 (by decide)).trans b49
  · exact (otherT 61 (by decide)).trans b61
  · exact (otherT 65 (by decide)).trans b65
  · rw [←hcapacity]
    exact (otherT 77 (by decide)).trans b77
  · change prepared.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    change base.steps+1+parsed.steps≤_
    dsimp only [suffix] at bs
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchSetupFields
