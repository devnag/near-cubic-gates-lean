import Proof.CaseAnalysis.RowsGateMetadataBounds

/-! Dock the original-description/support metadata scans after the SAME
public gate guard. Only accepted syntax reaches these native-field scans. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads CanonicalWitnessCodec SupplierPipeline
open RadixSemantics CloseoutRowsGateSupport RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 1038) : Fin 1049 := i.castAdd 11
def heads : Fin 1049→ℕ := Fin.addCases (m:=1038) (n:=11) (motive:=fun _=>ℕ)
  CloseoutRowsGateGuard.heads (fun _=>0)
def extend (bank : Fin 1038→List Bool) : Fin 1049→List Bool :=
  Fin.addCases (m:=1038) (n:=11) (motive:=fun _=>List Bool) bank (fun _=>[])
def input (core : ℕ) (bits : List Bool) := extend (CloseoutRowsGateGuard.input core bits)
def slots : Fin 15→Fin 1049 := ![361,1038,1039,994,1040,368,1041,1042,808,1043,1044,1045,1046,1047,1048]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first (compressed : Bool) := TapeEmbedding.machine 11 (CloseoutRowsGateGuard.machine compressed)
noncomputable def second := RecoveryFocus.machine slots CloseoutRowsGateMetadata.machine
noncomputable def machine (compressed : Bool) :=
  CloseoutRowsGateColdPair.machine (first compressed) second (fun scanned=>scanned (old 1037))
def budget (bits : List Bool) := CloseoutRowsGateGuard.budget bits+1+64*(bits.length+2)^2+1

theorem first_run (compressed : Bool) (core : ℕ) (bits : List Bool) (out : Fin 1038→List Bool)
    (h : ReadyAt (CloseoutRowsGateGuard.machine compressed) (CloseoutRowsGateGuard.budget bits)
      CloseoutRowsGateGuard.heads (CloseoutRowsGateGuard.input core bits) out) :
    ReadyAt (first compressed) (CloseoutRowsGateGuard.budget bits) heads (input core bits) (extend out) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := h
  have run := TapeEmbedding.run_embed (CloseoutRowsGateGuard.machine compressed)
    (fun _ : Fin 11=>0) (fun _=>[]) _ _ r hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 11=>0) (fun _=>[]) r,run,?_,?_,rs⟩
  · change (TapeEmbedding.config (fun _ : Fin 11=>0) (fun _=>[]) r.final).tapes=_
    simp only [TapeEmbedding.config,rt];rfl
  · change (TapeEmbedding.config (fun _ : Fin 11=>0) (fun _=>[]) r.final).heads=_
    simp only [TapeEmbedding.config,rh];rfl

theorem guard_count {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (fuel : ℕ) (out : Fin 1038→List Bool)
    (run : ReadyAt (CloseoutRowsGateGuard.machine compressed) fuel CloseoutRowsGateGuard.heads
      (CloseoutRowsGateGuard.input n bits) out) : out 368=CompareMachine.word n := by
  obtain ⟨raw,hr,_meaning⟩ := CloseoutRowsGateRawRun.allraw compressed bits
  obtain ⟨_weights,_members,_threshold,nw,nm,flag⟩ := CloseoutRowsGateGuard.raw_ports compressed g bits h _ raw hr
  have joined := CloseoutRowsGatePairHeads.joined (CloseoutRowsGateGuard.first compressed)
    CloseoutRowsGateGuard.second (fun scanned=>scanned 1018) _ _ CloseoutRowsGateGuard.heads _ _ _
    (CloseoutRowsGateGuard.first_run compressed n bits raw hr)
    (CloseoutRowsGateGuard.second_run n n n raw nw nm) (by
      change readTapeBit (raw 1018) 0=true;rw [flag];rfl)
  obtain ⟨a,ha,aT,_aH,_aS⟩ := run
  obtain ⟨b,hb,bT,_bH,_bS⟩ := joined
  have he := CloseoutRowsGateGuard.receipt_unique _ _ _ _ a b ha hb
  subst b
  rw [←aT,bT]
  change install CloseoutRowsGateGuard.slots _ _ (CloseoutRowsGateGuard.slots 0)=_
  rw [install_slot _ CloseoutRowsGateGuard.injective]
  rfl

theorem selected_heads (i : Fin 15) : heads (slots i)=0 := by fin_cases i <;> rfl

theorem metadata_input {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (bank : Fin 1038→List Bool)
    (run : ReadyAt (CloseoutRowsGateGuard.machine compressed) (CloseoutRowsGateGuard.budget bits)
      CloseoutRowsGateGuard.heads (CloseoutRowsGateGuard.input n bits) bank) :
    ∀ i,extend bank (slots i)=CloseoutRowsGateMetadata.input (gateFields g.gate)
      (gateMembers g.support) g.gate.threshold.natAbs i := by
  obtain ⟨weights,members,threshold⟩ := CloseoutRowsGateGuard.guard_ports compressed g bits h _ bank run
  have count := guard_count compressed g bits h _ bank run
  intro i;fin_cases i
  · change bank 361=(gateFields g.gate).flatMap fieldWord
    rw [gateFields_word];exact weights
  · rfl
  · rfl
  · exact members
  · rfl
  · change bank 368=CompareMachine.word (gateFields g.gate).length
    simpa only [gateFields,List.length_ofFn] using count
  · rfl
  · rfl
  · exact threshold
  all_goals rfl

theorem second_run {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (bank : Fin 1038→List Bool)
    (run : ReadyAt (CloseoutRowsGateGuard.machine compressed) (CloseoutRowsGateGuard.budget bits)
      CloseoutRowsGateGuard.heads (CloseoutRowsGateGuard.input n bits) bank) : ∃ out,
    ReadyAt second (64*(bits.length+2)^2) heads (extend bank) (install slots (extend bank) out) ∧
      out 6=List.replicate ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length true ∧
      out 11=List.replicate (RepairRepresentation.natWord g.gate.threshold.natAbs).length true ∧
      out 13=List.replicate g.wireCount true := by
  obtain ⟨out,⟨base,hbase,bt,bh,bs⟩,hw,ht,hc⟩ := CloseoutRowsGateMetadata.gate_run g bits h
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slots slots_injective CloseoutRowsGateMetadata.machine
    heads (extend bank) _ _ base hbase
  have start := WilliamsSourceCrop.focus_same slots
    (⟨0,heads,extend bank⟩ : Configuration 1049 1)
    (initialConfiguration CloseoutRowsGateMetadata.machine
      (CloseoutRowsGateMetadata.input (gateFields g.gate) (gateMembers g.support) g.gate.threshold.natAbs))
    selected_heads (metadata_input compressed g bits h bank run)
  rw [start] at hr
  refine ⟨out,⟨r,hr,?_,?_,hs ▸ bs⟩,hw,ht,hc⟩
  · rw [hf];change install slots (extend bank) base.final.tapes=_;rw [bt]
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none=>simp only [RecoveryFocus.config,hp]
    | some j=>
      have he := RecoveryFocus.slot_of_pick slots hp
      rw [←he]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
      exact (selected_heads j).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
