import Proof.PCP.VerifierDecodingFrontLayout

/-! Whole guarded decoder front: header/dimensions/width, start-state range,
and state flags. The actual table follows only after this physical result. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Front
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev dimensionStates := Fintype.card (RecoveryCalls.Control Dimensions.sizes)
abbrev fieldStates := Fintype.card (RecoveryCalls.Control StartFlags.sizes)
def sizes : Fin 2 → ℕ := ![dimensionStates,fieldStates]
noncomputable def programs : (j : Fin 2) → Machine 14 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 3 Dimensions.machine
  | ⟨1,_⟩ => StartFlags.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next : (j : Fin 2) → Fin (sizes j) → (Fin 14 → Bool) → Option (Fin 2)
  | ⟨0,_⟩,_,bits => if bits 5 then some 1 else none
  | ⟨1,_⟩,_,_ => none
  | ⟨n+2,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (c : ℕ) := 8*c^2+62*c+64
def valid (word : List Bool) (limit : ℕ) : Bool :=
  GuardedPreparation.valid word limit &&
    match HeaderMachine.parts word with
    | none => false
    | some (_,s,fields) => StartFlags.valid fields (bound s) s
noncomputable def initial (word : List Bool) (limit : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (TapeEmbedding.config (fun _ : Fin 3 => 0) ![[],[false],[]] (Dimensions.initial word limit))
noncomputable def endpoint (word fields : List Bool) (limit t s x y : ℕ) :=
  let out := StartFlags.endpoint (Dimensions.endpoint word limit t s x y)
    (StartLayout.headerPrefix t s) fields (bound s) s
  RecoveryCalls.stopped sizes out.heads out.tapes
def Outcome (word : List Bool) (limit : ℕ)
    (final : Configuration 14 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 12=valid word limit ∧
    (valid word limit=true → ∃ t s fields x y,
      HeaderMachine.parts word=some (t,s,fields) ∧ 2≤t ∧ 0<s ∧
      final=endpoint word fields limit t s x y)

theorem stop_prefix (node : Fin 2) (fuel : ℕ)
    (input : Configuration 14 (sizes node)) (r : ExecutionReceipt 14 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem front_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤budget word.length ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨n,base,hn,hdim,hh,hout⟩ := Dimensions.dimensions_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hdim.run hh
  have he := TapeEmbedding.run_embed Dimensions.machine (fun _ : Fin 3 => 0)
    ![[],[false],[]] _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 3 => 0) ![[],[false],[]] r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 5=GuardedPreparation.valid word limit := by
    change readTapeBit (r.final.tapes 5) (r.final.heads 5)=_
    rw [hf]
    exact hout.1
  cases hv : GuardedPreparation.valid word limit with
  | false =>
    have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit.trans hv)
    rw [htime] at hp
    refine ⟨_,_,by dsimp [budget,Dimensions.budget] at *; omega,hp,?_,?_,by simp [valid,hv]⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simp [valid,hv,RecoveryCalls.stopped,Configuration.scanned,first,
        TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,readTapeBit]
  | true =>
    obtain ⟨t,s,fields,x,y,hparts,ht,hspos,hendpoint⟩ := hout.2 hv
    have hfirst : first.final=TapeEmbedding.config (fun _ : Fin 3 => 0)
        ![[],[false],[]] (Dimensions.endpoint word limit t s x y) := by
      change TapeEmbedding.config _ _ r.final=_
      rw [hf,hendpoint]
    have hp0 := prefix_of_run (programs 0) n _ first he
    have hb := RecoveryCalls.body_timed sizes programs 0 next 0 ⟨first.peakTapeCells,hp0.1⟩
    have hreturn := RecoveryCalls.return_step sizes programs 0 next 0 1 first.final hp0.2
      (by simp [next]; exact hbit.trans hv)
    have hp := hb.trans (Timed.single
      (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hreturn)
    rw [htime,hfirst] at hp
    have hcount := dimension_count word limit t s x y
    obtain ⟨tail,hrun,htimeTail,hbitTail,hgood⟩ := StartFlags.start_flags_run
      (Dimensions.endpoint word limit t s x y) (StartLayout.headerPrefix t s) fields
      (bound s) word.length s (dimension_entry word fields limit t s x y hparts hspos) hcount.1 hcount.2
    have htail := stop_prefix 1 (8*(bound s).length+8*s+20) _ tail hrun (by rfl)
    have hall := hp.trans htail
    have htBudget := start_budget word fields t s hparts hspos
    refine ⟨_,_,by dsimp [budget,Dimensions.budget] at *; omega,hall,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simpa [valid,hv,hparts,RecoveryCalls.stopped,Configuration.scanned] using hbitTail
    · intro hvalid
      have hfields : StartFlags.valid fields (bound s) s=true := by simpa [valid,hv,hparts] using hvalid
      refine ⟨t,s,fields,x,y,hparts,ht,hspos,?_⟩
      rw [hgood hfields]
      rfl

def inputCapacity (word : List Bool) : Fin 14 → ℕ :=
  fun i => Fin.addCases (Dimensions.inputCapacity word) ![0,1,0] i
noncomputable def blankEntry (word : List Bool) (limit : ℕ) :
    Configuration 14 (Fintype.card (RecoveryCalls.Control sizes)) :=
  ⟨machine.start,
    fun i => Fin.addCases (Dimensions.blankEntry word limit).heads (fun _ : Fin 3 => 0) i,
    fun i => Fin.addCases (Dimensions.blankEntry word limit).tapes (fun _ : Fin 3 => []) i⟩

theorem front_run (word : List Bool) (limit : ℕ) :
    ∃ r, runFrom machine (budget word.length) (blankEntry word limit)=some r ∧
      r.steps≤budget word.length ∧ r.final.scanned 12=valid word limit ∧
      Outcome word limit (ZeroPadding.config (inputCapacity word) r.final) := by
  obtain ⟨n,final,hn,hp,hh,hout⟩ := front_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hi : ZeroPadding.config (inputCapacity word) (blankEntry word limit)=initial word limit := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,inputCapacity,blankEntry,initial,
        controlConfig,TapeEmbedding.config,Dimensions.inputCapacity,Dimensions.blankEntry,Dimensions.initial,
        GuardedPreparation.inputCapacity,GuardedPreparation.blankEntry,GuardedPreparation.initial,
        GuardedPreparation.extend,Preparation.initial,Preparation.zeros,Fin.addCases,ZeroPadding.pad]
  rw [←hi] at hr
  obtain ⟨actual,ha,hfa,hsa,_⟩ := ZeroPadding.run_unpad machine (inputCapacity word) _ _ r hr
  have hm := runFrom_moreFuel machine n (budget word.length-n) _ actual ha
  rw [Nat.add_sub_of_le hn] at hm
  have hend : ZeroPadding.config (inputCapacity word) actual.final=final := hfa.trans hf
  have hbit : actual.final.scanned 12=valid word limit := by
    rw [←ZeroPadding.scanned_config (inputCapacity word) actual.final,hend]
    exact hout.1
  exact ⟨actual,hm,by omega,hbit,by rw [hend]; exact hout⟩

end NearCubicWires.RepairSource.VerifierDecoding.Front
