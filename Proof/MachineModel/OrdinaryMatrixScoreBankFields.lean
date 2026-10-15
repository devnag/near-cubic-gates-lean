import Proof.MachineModel.OrdinaryMatrixScoreBankField

/-! The actual d-driver copies its weight fields into the local cut bank.
Both streams retain their endpoints and the sentinel returns to head1. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBankFields
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted (_ : Fin 3) (_ : Fin 2 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixScoreBankField.machine accepted

theorem driver_run (p total pos : ℕ) (weights : List ℤ) (pre suffix out : List Bool)
    (hpos : pos+weights.length=total) :
    ∃ actual,runFrom machine (weights.length*(2*p+5)+total+3)
      (RepeatMachine.cfg 0 (MatrixScoreBankField.cfg 0
        (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length out) total (pos+1))=some actual ∧
      actual.steps≤weights.length*(2*p+5)+total+3 ∧
      actual.final=RepeatMachine.cfg 3 (MatrixScoreBankField.cfg 0
        (pre++MatrixScoreCanonical.fields p weights++suffix)
        (pre.length+(MatrixScoreCanonical.fields p weights).length) (out++MatrixScoreCanonical.fields p weights)) total 1 := by
  induction weights generalizing pos pre out with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨actual,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixScoreBankField.machine accepted
      (MatrixScoreBankField.cfg 0 (pre++MatrixScoreCanonical.fields p []++suffix) pre.length out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,by simpa [machine] using hr,by simpa using hs.le,by simpa [MatrixScoreCanonical.fields] using hf⟩
  | cons z weights ih =>
    let bits := MatrixScoreBatch.signMagnitude p z
    let field := frame bits
    obtain ⟨body,hbody,hbf,hbs⟩ := MatrixScoreBankField.field_run bits pre (MatrixScoreCanonical.fields p weights++suffix) out
    have hlen : bits.length=p+1 := by simp [bits,MatrixScoreBatch.signMagnitude]
    have iteration := RepeatMachine.iteration MatrixScoreBankField.machine accepted
      (MatrixScoreBankField.cfg 0 (pre++frame bits++(MatrixScoreCanonical.fields p weights++suffix)) pre.length out)
      total pos body rfl (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    rw [hbf] at iteration
    have he : RepeatMachine.cfg 0 (MatrixScoreBankField.cfg 2
        (pre++frame bits++(MatrixScoreCanonical.fields p weights++suffix)) (pre.length+(frame bits).length) (out++frame bits)) total (pos+2)=
      RepeatMachine.cfg 0 (MatrixScoreBankField.cfg 0
        ((pre++field)++MatrixScoreCanonical.fields p weights++suffix) (pre++field).length (out++field)) total (pos+2) := by
      simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixScoreBankField.cfg,field,List.append_assoc]
    rw [he] at iteration
    obtain ⟨tail,htail,hts,htf⟩ := ih (pos+1) (pre++field) (out++field) (by simp only [List.length_cons] at hpos; omega)
    have ht : runFrom machine (weights.length*(2*p+5)+total+3)
        (RepeatMachine.cfg 0 (MatrixScoreBankField.cfg 0
          ((pre++field)++MatrixScoreCanonical.fields p weights++suffix) (pre++field).length (out++field)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,hr,hf,hs,_⟩ := hprefix.followedBy tail ht
    have hc : (body.steps+2)+(weights.length*(2*p+5)+total+3)=
        (z::weights).length*(2*p+5)+total+3 := by rw [hbs,hlen]; simp only [List.length_cons]; ring
    rw [hc] at hr
    refine ⟨actual,?_,?_,?_⟩
    · simpa [machine,MatrixScoreCanonical.fields,bits,List.append_assoc] using hr
    · rw [hs]
      rw [hbs,hlen] at hc
      rw [hbs,hlen]
      omega
    · rw [hf,htf]
      simp [MatrixScoreCanonical.fields,bits,field,List.length_append,List.append_assoc,Nat.add_assoc]

noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos d : ℕ) (out : List Bool) :=
  ZeroPadding.config (![0,0,d+2] : Fin 3 → ℕ)
    (RepeatMachine.cfg phase (MatrixScoreBankField.cfg 0 source pos out) d 1)

theorem fields_run (p : ℕ) (weights : List ℤ) (pre suffix out : List Bool) :
    ∃ actual,runFrom machine (weights.length*(2*p+6)+3)
      (cfg 0 (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length out)=some actual ∧
      actual.steps≤weights.length*(2*p+6)+3 ∧
      actual.final=cfg 3 (pre++MatrixScoreCanonical.fields p weights++suffix)
        (pre.length+(MatrixScoreCanonical.fields p weights).length) weights.length (out++MatrixScoreCanonical.fields p weights) := by
  obtain ⟨base,hb,hs,hf⟩ := driver_run p weights.length 0 weights pre suffix out (by omega)
  have he : weights.length*(2*p+5)+weights.length+3=weights.length*(2*p+6)+3 := by ring
  rw [he] at hb hs
  obtain ⟨actual,hr,ha,hsteps,_⟩ := ZeroPadding.run_config machine (![0,0,weights.length+2] : Fin 3 → ℕ) _ _ base hb
  exact ⟨actual,hr,hsteps.trans_le hs,by rw [ha,hf]; rfl⟩

theorem cfg_tapes (phase : Fin 5) (source : List Bool) (pos d : ℕ) (out : List Bool) :
    (cfg phase source pos d out).tapes=![source,out,UnaryTemplate.tape d] := by
  funext i
  fin_cases i <;> simp [Fin.addCases,cfg,ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    MatrixScoreBankField.cfg,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem physical_run (p : ℕ) (weights : List ℤ) (pre suffix out : List Bool) :
    ∃ actual,runFrom machine (weights.length*(2*p+6)+3)
      (RecoveryCalls.restarted machine ![pre.length,out.length,1]
        ![pre++MatrixScoreCanonical.fields p weights++suffix,out,UnaryTemplate.tape weights.length])=some actual ∧
      actual.final.heads=![pre.length+(MatrixScoreCanonical.fields p weights).length,
        (out++MatrixScoreCanonical.fields p weights).length,1] ∧
      actual.final.tapes=![pre++MatrixScoreCanonical.fields p weights++suffix,
        out++MatrixScoreCanonical.fields p weights,UnaryTemplate.tape weights.length] ∧
      actual.steps≤weights.length*(2*p+6)+3 := by
  obtain ⟨actual,hr,hs,hf⟩ := fields_run p weights pre suffix out
  have hi : cfg 0 (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length out=
      RecoveryCalls.restarted machine ![pre.length,out.length,1]
        ![pre++MatrixScoreCanonical.fields p weights++suffix,out,UnaryTemplate.tape weights.length] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · exact cfg_tapes _ _ _ _ _
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,hs⟩
  · rw [hf]
    funext i; fin_cases i <;> rfl
  · rw [hf,cfg_tapes]

end NearCubicWires.RepairOrdinary.MatrixScoreBankFields
