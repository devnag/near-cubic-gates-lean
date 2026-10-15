import Proof.PCP.VerifierDecodingPreparedWidth

/-! Guarded header plus actual binary-state/width construction. The finite
controller branches on the header's physical result before calling the width
producer, and every new work tape is blank at entry. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Dimensions
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev guardStates := Fintype.card (RecoveryCalls.Control GuardedPreparation.sizes)
def sizes : Fin 2 → ℕ := ![guardStates,25]
noncomputable def programs : (j : Fin 2) → Machine 11 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 5 GuardedPreparation.machine
  | ⟨1,_⟩ => PreparedWidth.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next : (j : Fin 2) → Fin (sizes j) → (Fin 11 → Bool) → Option (Fin 2)
  | ⟨0,_⟩,_,bits => if bits 5 then some 1 else none
  | ⟨1,_⟩,_,_ => none
  | ⟨n+2,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def budget (c : ℕ) := 8*c^2+46*c+40
noncomputable def initial (word : List Bool) (limit : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) (GuardedPreparation.initial word limit))
noncomputable def endpoint (word : List Bool) (limit t s x y : ℕ) :=
  let out := PreparedWidth.output (GuardedPreparation.endpoint word limit t s) s x y
  RecoveryCalls.stopped sizes out.heads out.tapes
def Outcome (word : List Bool) (limit : ℕ)
    (final : Configuration 11 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 5=GuardedPreparation.valid word limit ∧
    (GuardedPreparation.valid word limit=true → ∃ t s fields x y,
      HeaderMachine.parts word=some (t,s,fields) ∧ 2≤t ∧ 0<s ∧
      final=endpoint word limit t s x y)

theorem stop_prefix (node : Fin 2) (fuel : ℕ)
    (input : Configuration 11 (sizes node)) (r : ExecutionReceipt 11 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem dimensions_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤budget word.length ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨n,base,hn,hguard,hh,hout⟩ := GuardedPreparation.guarded_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hguard.run hh
  have he := TapeEmbedding.run_embed GuardedPreparation.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 5=GuardedPreparation.valid word limit := by
    change readTapeBit (r.final.tapes 5) (r.final.heads 5)=_
    rw [hf]
    exact hout.1
  cases hv : GuardedPreparation.valid word limit with
  | false =>
    have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit.trans hv)
    rw [htime] at hp
    refine ⟨_,_,by dsimp [budget]; nlinarith,hp,?_,?_,by simp [hv]⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simpa only [RecoveryCalls.stopped,Configuration.scanned] using hbit
  | true =>
    obtain ⟨t,s,fields,hparts,ht,hspos,hendpoint⟩ := hout.2 hv
    have hlen := GuardedPreparation.parts_lengths hparts
    have hfirst : first.final=TapeEmbedding.config (fun _ : Fin 5 => 0)
        (fun _ : Fin 5 => []) (GuardedPreparation.endpoint word limit t s) := by
      change TapeEmbedding.config _ _ r.final=_
      rw [hf,hendpoint]
    have hp0 := prefix_of_run (programs 0) n _ first he
    have hb := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨first.peakTapeCells,hp0.1⟩
    have hreturn := RecoveryCalls.return_step sizes programs 0 next 0 1 first.final hp0.2
      (by simp [next]; exact hbit.trans hv)
    have hp := hb.trans (Timed.single
      (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hreturn)
    rw [htime,hfirst] at hp
    obtain ⟨x,y,_,_,tail,hrun,hfinal,hsteps⟩ := PreparedWidth.width_run
      (GuardedPreparation.endpoint word limit t s) word.length s (by rfl) (by rfl) hspos (by omega)
    have htail := stop_prefix 1 (8*word.length^2+34*word.length+11) _ tail hrun (by rfl)
    rw [hfinal] at htail
    have hall := hp.trans htail
    refine ⟨_,endpoint word limit t s x y,by dsimp [budget]; nlinarith,hall,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,endpoint,RecoveryCalls.stopped]
    · change true=GuardedPreparation.valid word limit
      exact hv.symm
    · intro _
      exact ⟨t,s,fields,x,y,hparts,ht,hspos,rfl⟩

def inputCapacity (word : List Bool) : Fin 11 → ℕ :=
  fun i => Fin.addCases (GuardedPreparation.inputCapacity word) (fun _ : Fin 5 => 0) i
noncomputable def blankEntry (word : List Bool) (limit : ℕ) :
    Configuration 11 (Fintype.card (RecoveryCalls.Control sizes)) :=
  ⟨machine.start,
    fun i => Fin.addCases (GuardedPreparation.blankEntry word limit).heads (fun _ : Fin 5 => 0) i,
    fun i => Fin.addCases (GuardedPreparation.blankEntry word limit).tapes (fun _ : Fin 5 => []) i⟩

theorem dimensions_run (word : List Bool) (limit : ℕ) :
    ∃ r, runFrom machine (budget word.length) (blankEntry word limit)=some r ∧
      r.steps≤budget word.length ∧ r.final.scanned 5=GuardedPreparation.valid word limit ∧
      Outcome word limit (ZeroPadding.config (inputCapacity word) r.final) := by
  obtain ⟨n,final,hn,hp,hh,hout⟩ := dimensions_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hi : ZeroPadding.config (inputCapacity word) (blankEntry word limit)=initial word limit := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,inputCapacity,blankEntry,initial,
        controlConfig,TapeEmbedding.config,GuardedPreparation.inputCapacity,
        GuardedPreparation.blankEntry,GuardedPreparation.initial,GuardedPreparation.extend,
        Preparation.initial,Preparation.zeros,Fin.addCases]
  rw [←hi] at hr
  obtain ⟨actual,ha,hfa,hsa,_⟩ := ZeroPadding.run_unpad machine (inputCapacity word) _ _ r hr
  have hm := runFrom_moreFuel machine n (budget word.length-n) _ actual ha
  rw [Nat.add_sub_of_le hn] at hm
  have hend : ZeroPadding.config (inputCapacity word) actual.final=final := hfa.trans hf
  have hbit : actual.final.scanned 5=GuardedPreparation.valid word limit := by
    rw [←ZeroPadding.scanned_config (inputCapacity word) actual.final,hend]
    exact hout.1
  exact ⟨actual,hm,by omega,hbit,by rw [hend]; exact hout⟩

end NearCubicWires.RepairSource.VerifierDecoding.Dimensions
