import Proof.MachineModel.UDecoderRetained
import Proof.MachineModel.UWitnessOrdinary

/-! The actual decoder-retained fields supply witness preparation. This
connection uses only the checked finite focus and fresh appended workspace. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev decoderStates := Fintype.card (RecoveryCalls.Control UDecoder.sizes)
abbrev witnessStates := Fintype.card (RecoveryCalls.Control UWitness.sizes)
def extended {s : ℕ} (base : Configuration 69 s) : Configuration 81 s :=
  TapeEmbedding.config (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) base
noncomputable def witnessInput {s : ℕ} (base : Configuration 69 s) : Configuration 81 witnessStates :=
  UWitnessOrdinary.entry (extended base).heads (extended base).tapes

def Accepted (raw witness : List Bool) : Prop := ∃ code x bound padding,
  raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
  (∃ v,RepairSource.VerifierDecoding.decode raw.length code=some v) ∧
  UWitness.Valid (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness

theorem accepted_decoder (raw witness : List Bool) : Accepted raw witness → UDecoder.Accepted raw := by
  rintro ⟨code,x,bound,padding,he,hg,hd,_⟩
  exact ⟨code,x,bound,padding,he,hg,hd⟩

theorem accepted_iff (raw witness code x bound padding : List Bool)
    (he : raw=VerifierInputFields.source code x bound padding)
    (hg : UInputScalars.Guards raw x bound) (hd : UDecoder.Accepted raw) :
    Accepted raw witness ↔ UWitness.Valid (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness := by
  constructor
  · rintro ⟨code',x',bound',padding',he',_,_,hv⟩
    have hu := UInputEntry.source_unique _ _ _ _ _ _ _ _ (he.symm.trans he')
    simpa only [hu.2.2.1] using hv
  · intro hv
    exact ⟨code,x,bound,padding,he,hg,(UDecoder.accepted_iff raw code x bound padding he hg).mp hd,hv⟩

theorem witness_run {s : ℕ} (raw witness : List Bool) (base : Configuration 69 s)
    (hfield : UDecoder.FieldSuppliers raw witness base.heads base.tapes) :
    ∃ code x bound padding, raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
      ∃ r,runFrom UWitnessOrdinary.machine
        (UWitness.budget (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound)) (witnessInput base)=some r ∧
      UWitness.Outcome (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness
        (UWitnessOrdinary.project r.final) ∧
      UWitnessOrdinary.Preserved (extended base).heads (extended base).tapes r.final ∧
      r.steps≤128*(RadixSemantics.value bound+1)*(ClockDyadicLedger.width raw.length+1) := by
  obtain ⟨code,x,bound,padding,he,hg,hraw,hwit,hx,hw,hI,hK,hB,h1,h8,h20,h21,h22,h26⟩ := hfield
  have hb : RadixSemantics.value bound+1<2^ClockDyadicLedger.width raw.length := by
    have := (ClockDyadicLedger.width_bounds raw.length).1
    have := hg.2.2
    omega
  have hh : ∀ j,(extended base).heads (UWitnessOrdinary.slots j)=0 := by
    intro j
    fin_cases j <;> simp [extended,TapeEmbedding.config,Fin.addCases,UWitnessOrdinary.slots,h1,h20,h26]
  have ht : ∀ j,(extended base).tapes (UWitnessOrdinary.slots j)=
      UWitness.input (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness j := by
    intro j
    fin_cases j <;> simp [extended,TapeEmbedding.config,Fin.addCases,UWitnessOrdinary.slots,
      UWitness.input,hwit,hw,hB]
  obtain ⟨r,hr,hout,hpres,hsteps⟩ := UWitnessOrdinary.entry_run
    (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness
    (extended base).heads (extended base).tapes hb hh ht
  exact ⟨code,x,bound,padding,he,hg,r,hr,hout,hpres,hsteps⟩

end NearCubicWires.RepairOrdinary.UFront
