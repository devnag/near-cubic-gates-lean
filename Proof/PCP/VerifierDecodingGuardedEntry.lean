import Proof.PCP.VerifierDecodingGuardedHeader

/-! Complete guarded code/header entry from framed code, a physical input-limit
counter, and blank scratch. The code-length check precedes header processing;
both header terminators and dimensions are checked before dependent expansion. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def valid (word : List Bool) (limit : ℕ) : Bool :=
  decide (word.length≤limit) && headerValid word

def Outcome (word : List Bool) (limit : ℕ)
    (final : Configuration 6 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 5=valid word limit ∧
    (valid word limit=true → ∃ t s fields,
      HeaderMachine.parts word=some (t,s,fields) ∧ 2≤t ∧ 0<s ∧ final=endpoint word limit t s)

theorem compare_tail (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤8*word.length+23 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (compareInput word limit)) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨r,hr,hf,hs⟩ := compare_layout word limit
  by_cases hc : word.length≤limit
  · have hp := call_prefix 1 2 (2*min word.length limit+3) _ r hr (by simp [next,hf,hc])
    rw [hf,hs] at hp
    obtain ⟨n,final,hn,hheader,hh,hout⟩ := header_tail word limit
    have hall := hp.trans hheader
    refine ⟨_,final,by have hm := Nat.min_le_left word.length limit; omega,hall,hh,?_,?_⟩
    · simpa [valid,hc] using hout.1
    · intro hv
      have hhvalid : headerValid word=true := by simpa [valid,hc] using hv
      cases hparts : HeaderMachine.parts word with
      | none => simp [headerValid,hparts] at hhvalid
      | some value =>
        rcases value with ⟨t,s,fields⟩
        have hdim : 2≤t ∧ 0<s := by simpa [headerValid,hparts,dimensions] using hhvalid
        exact ⟨t,s,fields,rfl,hdim.1,hdim.2,hout.2 t s fields hparts hdim⟩
  · have hp := stop_prefix 1 (2*min word.length limit+3) _ r hr (by simp [next,hf,hc])
    rw [hs] at hp
    refine ⟨_,_,by have hm := Nat.min_le_left word.length limit; omega,hp,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · rw [hf]
      simp [valid,hc,Configuration.scanned,RecoveryCalls.stopped,compareInput,extend,
        TapeEmbedding.config,Fin.addCases,readTapeBit]
    · simp [valid,hc]

noncomputable def initial (word : List Bool) (limit : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0) (extend limit (Preparation.initial word))

theorem guarded_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤12*word.length+27 ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨r,hr,hf,hs⟩ := Preparation.length_layout word
  have he := TapeEmbedding.run_embed Preparation.lengthProgram ![1,0]
    ![CompareMachine.word limit,[]] _ _ r hr
  let result := TapeEmbedding.receipt ![1,0] ![CompareMachine.word limit,[]] r
  have hp := call_prefix 0 1 (4*word.length+3) _ result he (by rfl)
  have hfinal : result.final=⟨5,(compareInput word limit).heads,(compareInput word limit).tapes⟩ := by
    change extend limit r.final=_
    rw [hf]; rfl
  have hsteps : result.steps=4*word.length+3 := hs
  rw [hfinal,hsteps] at hp
  obtain ⟨n,final,hn,ht,hh,hout⟩ := compare_tail word limit
  have hall := hp.trans ht
  exact ⟨_,final,by omega,hall,hh,hout⟩

def inputCapacity (word : List Bool) : Fin 6 → ℕ :=
  ![0,word.length+2,word.length+2,word.length+2,0,0]

noncomputable def blankEntry (word : List Bool) (limit : ℕ) :
    Configuration 6 (Fintype.card (RecoveryCalls.Control sizes)) :=
  ⟨machine.start,![0,0,0,0,1,0],![frame word,[],[],[],CompareMachine.word limit,[]]⟩

/-- No false workspace is assumed physically allocated. The retained padded
endpoint is obtained by the actual reverse interpreter simulation. The limit
counter at head1 is a named, still-paid upstream input, not a free logarithm. -/
theorem guarded_entry_run (word : List Bool) (limit : ℕ) :
    ∃ r, runFrom machine (12*word.length+27) (blankEntry word limit)=some r ∧
      r.steps≤12*word.length+27 ∧ r.final.scanned 5=valid word limit ∧
      Outcome word limit (ZeroPadding.config (inputCapacity word) r.final) := by
  obtain ⟨n,final,hn,hp,hh,hout⟩ := guarded_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hi : ZeroPadding.config (inputCapacity word) (blankEntry word limit)=initial word limit := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,inputCapacity,blankEntry,
        initial,controlConfig,extend,TapeEmbedding.config,Preparation.initial,
        Preparation.zeros,Fin.addCases]
  rw [←hi] at hr
  obtain ⟨actual,ha,hfa,hsa,_⟩ := ZeroPadding.run_unpad machine (inputCapacity word) _ _ r hr
  have hm := runFrom_moreFuel machine n (12*word.length+27-n) _ actual ha
  rw [Nat.add_sub_of_le hn] at hm
  have hend : ZeroPadding.config (inputCapacity word) actual.final=final := hfa.trans hf
  have hbit : actual.final.scanned 5=valid word limit := by
    rw [←ZeroPadding.scanned_config (inputCapacity word) actual.final,hend]
    exact hout.1
  exact ⟨actual,hm,by omega,hbit,by rw [hend]; exact hout⟩

end NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
