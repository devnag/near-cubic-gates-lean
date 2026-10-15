import Proof.MachineModel.OrdinaryMatrixScoreSkipField

/-! The actual d-driver skips all intervening right weights on the original
cut stream and returns to head1. This is the literal threshold-address
producer, not an assumed positioned threshold field. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreSkipFields
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted (_ : Fin 3) (_ : Fin 1 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixScoreSkipField.machine accepted

theorem driver_run (p total pos : ℕ) (weights : List ℤ) (pre suffix : List Bool)
    (hpos : pos+weights.length=total) :
    ∃ actual,runFrom machine (weights.length*(2*p+5)+total+3)
      (RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
        (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length) total (pos+1))=some actual ∧
      actual.steps≤weights.length*(2*p+5)+total+3 ∧
      actual.final=RepeatMachine.cfg 3 (MatrixScoreSkipField.cfg 0
        (pre++MatrixScoreCanonical.fields p weights++suffix)
        (pre.length+(MatrixScoreCanonical.fields p weights).length)) total 1 := by
  induction weights generalizing pos pre with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨actual,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixScoreSkipField.machine accepted
      (MatrixScoreSkipField.cfg 0 (pre++MatrixScoreCanonical.fields p []++suffix) pre.length) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,by simpa [machine] using hr,by simpa using hs.le,by simpa [MatrixScoreCanonical.fields] using hf⟩
  | cons z weights ih =>
    let bits := MatrixScoreBatch.signMagnitude p z
    let field := frame bits
    obtain ⟨body,hbody,hbf,hbs⟩ := MatrixScoreSkipField.field_run bits pre (MatrixScoreCanonical.fields p weights++suffix)
    have hlen : bits.length=p+1 := by simp [bits,MatrixScoreBatch.signMagnitude]
    have iteration := RepeatMachine.iteration MatrixScoreSkipField.machine accepted
      (MatrixScoreSkipField.cfg 0 (pre++frame bits++(MatrixScoreCanonical.fields p weights++suffix)) pre.length)
      total pos body rfl (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    rw [hbf] at iteration
    have he : RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 2
        (pre++frame bits++(MatrixScoreCanonical.fields p weights++suffix)) (pre.length+(frame bits).length)) total (pos+2)=
      RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
        ((pre++field)++MatrixScoreCanonical.fields p weights++suffix) (pre++field).length) total (pos+2) := by
      simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixScoreSkipField.cfg,field,List.append_assoc]
    rw [he] at iteration
    obtain ⟨tail,htail,hts,htf⟩ := ih (pos+1) (pre++field) (by simp only [List.length_cons] at hpos; omega)
    have ht : runFrom machine (weights.length*(2*p+5)+total+3)
        (RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
          ((pre++field)++MatrixScoreCanonical.fields p weights++suffix) (pre++field).length) total (pos+2))=some tail := by
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

noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos d : ℕ) :=
  ZeroPadding.config (![0,d+2] : Fin 2 → ℕ)
    (RepeatMachine.cfg phase (MatrixScoreSkipField.cfg 0 source pos) d 1)

theorem fields_run (p : ℕ) (weights : List ℤ) (pre suffix : List Bool) :
    ∃ actual,runFrom machine (weights.length*(2*p+6)+3)
      (cfg 0 (pre++MatrixScoreCanonical.fields p weights++suffix) pre.length weights.length)=some actual ∧
      actual.steps≤weights.length*(2*p+6)+3 ∧
      actual.final=cfg 3 (pre++MatrixScoreCanonical.fields p weights++suffix)
        (pre.length+(MatrixScoreCanonical.fields p weights).length) weights.length := by
  obtain ⟨base,hb,hs,hf⟩ := driver_run p weights.length 0 weights pre suffix (by omega)
  have he : weights.length*(2*p+5)+weights.length+3=weights.length*(2*p+6)+3 := by ring
  rw [he] at hb hs
  obtain ⟨actual,hr,ha,hsteps,_⟩ := ZeroPadding.run_config machine (![0,weights.length+2] : Fin 2 → ℕ) _ _ base hb
  exact ⟨actual,hr,hsteps.trans_le hs,by rw [ha,hf]; rfl⟩

theorem cfg_tapes (phase : Fin 5) (source : List Bool) (pos d : ℕ) :
    (cfg phase source pos d).tapes=![source,UnaryTemplate.tape d] := by
  funext i
  fin_cases i <;> simp [Fin.addCases,cfg,ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    MatrixScoreSkipField.cfg,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

end NearCubicWires.RepairOrdinary.MatrixScoreSkipFields
