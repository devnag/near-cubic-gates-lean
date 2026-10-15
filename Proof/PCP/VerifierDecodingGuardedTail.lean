import Proof.PCP.VerifierDecodingGuardedPreparation

/-! Paid sentinel construction and dimension-guard exit on the guarded
entry controller. The final bit is written only after both dimensions pass. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepared (word : List Bool) (limit t s : ℕ) :=
  extend limit (Preparation.finished word t s)
noncomputable def endpoint (word : List Bool) (limit t s : ℕ) :=
  RecoveryCalls.stopped sizes (prepared word limit t s).heads
    (fun i => if i=5 then [true] else (prepared word limit t s).tapes i)

theorem success_tail (word : List Bool) (limit t s : ℕ) :
    Timed machine 2
      (controlConfig (RecoveryCalls.code sizes 6)
        ⟨(programs 6).start,(prepared word limit t s).heads,(prepared word limit t s).tapes⟩)
      (endpoint word limit t s) := by
  let base := prepared word limit t s
  let final : Configuration 6 2 :=
    ⟨1,base.heads,fun i => if i=5 then [true] else base.tapes i⟩
  have hstep : step successProgram ⟨0,base.heads,base.tapes⟩=some final := by
    simp [step,successProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,final]
    · funext i; by_cases h : i=5
      · subst i
        simp [applyAction,final,base,prepared,extend,TapeEmbedding.config,Fin.addCases,
          writeTapeBit]
      · simp [applyAction,final,h]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single
    (by rfl : successProgram.halted (0 : Fin 2)=false) hstep).run (by rfl)
  have hp := stop_prefix 6 1 _ r hr (by rfl)
  rw [hf,hs] at hp
  exact hp

theorem endpoint_scanned (word : List Bool) (limit t s : ℕ) :
    (endpoint word limit t s).scanned 5=true := by
  rfl

def dimensions (t s : ℕ) : Bool := decide (2≤t ∧ 0<s)

theorem dimensions_tail (word : List Bool) (limit t s : ℕ) :
    ∃ n final, n≤5 ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes 5)
          ⟨(programs 5).start,(prepared word limit t s).heads,(prepared word limit t s).tapes⟩) final ∧
      machine.halted final.control=true ∧ final.scanned 5=dimensions t s ∧
      (2≤t ∧ 0<s → final=endpoint word limit t s) := by
  obtain ⟨r,hr,hf,hs⟩ := DimensionGuard.guard_run word (2*t+2*s+4) t s
  have he := TapeEmbedding.run_embed DimensionGuard.machine ![1,0]
    ![CompareMachine.word limit,[]] _ _ r hr
  let result := TapeEmbedding.receipt ![1,0] ![CompareMachine.word limit,[]] r
  change runFrom (programs 5) 2
    ⟨(programs 5).start,(prepared word limit t s).heads,(prepared word limit t s).tapes⟩=some result at he
  have hfinal : result.final=⟨if 2≤t ∧ 0<s then 2 else 3,
      (prepared word limit t s).heads,(prepared word limit t s).tapes⟩ := by
    change extend limit r.final=_
    rw [hf]
    rfl
  have hsteps : result.steps=2 := hs
  by_cases hgood : 2≤t ∧ 0<s
  · have hp := call_prefix 5 6 2 _ result he (by simp [next,hfinal,hgood])
    rw [hsteps,hfinal] at hp
    have hall := hp.trans (success_tail word limit t s)
    refine ⟨5,endpoint word limit t s,by omega,?_,?_,?_,by intro _; rfl⟩
    · exact hall
    · simp [machine,endpoint,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simpa [dimensions,hgood] using endpoint_scanned word limit t s
  · have hp := stop_prefix 5 2 _ result he (by simp [next,hfinal,hgood])
    rw [hsteps] at hp
    refine ⟨3,RecoveryCalls.stopped sizes result.final.heads result.final.tapes,
      by omega,hp,?_,?_,by intro h; exact (hgood h).elim⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · rw [hfinal]
      simp [Configuration.scanned,RecoveryCalls.stopped,dimensions,hgood,prepared,
        extend,TapeEmbedding.config,Fin.addCases,readTapeBit]

theorem sentinel_tail (word : List Bool) (limit t s : ℕ)
    (ht : t≤word.length) (hs : s≤word.length) :
    ∃ n final, n≤4*word.length+13 ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes 3) (extend limit (Preparation.tInput word t s))) final ∧
      machine.halted final.control=true ∧ final.scanned 5=dimensions t s ∧
      (2≤t ∧ 0<s → final=endpoint word limit t s) := by
  obtain ⟨tr,htr,htf,hts⟩ := Preparation.t_layout word t s ht
  have hte := TapeEmbedding.run_embed Preparation.tProgram ![1,0]
    ![CompareMachine.word limit,[]] _ _ tr htr
  let tp := TapeEmbedding.receipt ![1,0] ![CompareMachine.word limit,[]] tr
  have hp := call_prefix 3 4 (2*word.length+3) _ tp hte (by rfl)
  have htf' : tp.final=⟨3,(extend limit (Preparation.sInput word t s)).heads,
      (extend limit (Preparation.sInput word t s)).tapes⟩ := by
    change extend limit tr.final=_
    rw [htf]; rfl
  have hts' : tp.steps=2*word.length+3 := hts
  rw [htf',hts'] at hp
  obtain ⟨sr,hsr,hsf,hss⟩ := Preparation.s_layout word t s hs
  have hse := TapeEmbedding.run_embed Preparation.sProgram ![1,0]
    ![CompareMachine.word limit,[]] _ _ sr hsr
  let sp := TapeEmbedding.receipt ![1,0] ![CompareMachine.word limit,[]] sr
  have hp' := call_prefix 4 5 (2*word.length+3) _ sp hse (by rfl)
  have hsf' : sp.final=prepared word limit t s := by
    change extend limit sr.final=_
    rw [hsf]; rfl
  have hss' : sp.steps=2*word.length+3 := hss
  rw [hsf',hss'] at hp'
  obtain ⟨n,final,hn,hd,hh,hbit,hgood⟩ := dimensions_tail word limit t s
  have hall := hp.trans (hp'.trans hd)
  exact ⟨_,final,by omega,hall,hh,hbit,hgood⟩

end NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
