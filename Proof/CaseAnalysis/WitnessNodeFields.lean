import Proof.CaseAnalysis.WitnessNodeFieldsLayout
import Proof.CaseAnalysis.WitnessNativePayload

/-! The actual node parser now obtains all three natural fields from one
raw canonical node code. It executes the same cold field decoder three times,
retains exact native words and decoder flags, and preserves tuple markers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeFields
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def header:=RecoveryFocus.machine headerSlots CompetitorWitnessTriple.machine
noncomputable def part (j : Fin 3):=RecoveryFocus.machine (slots j) NatNative.machine
noncomputable def first:=Composition.machine header (part 0)
noncomputable def second:=Composition.machine first (part 1)
noncomputable def machine:=Composition.machine second (part 2)
def time (bits : List Bool):=
  ((CompetitorWitnessTriple.time bits+1+NatNative.budget (NodeMeaning.codeWord bits 0))+1+
    NatNative.budget (NodeMeaning.codeWord bits 1))+1+NatNative.budget (NodeMeaning.codeWord bits 2)
def budget (bits : List Bool):=55000000000000000000*(bits.length+1)^24

theorem time_bound (bits : List Bool) : time bits ≤ budget bits:=by
  have hh:=CompetitorWitnessTriple.time_bound bits
  have hp:(bits.length+1)^2 ≤ (bits.length+1)^24:=Nat.pow_le_pow_right (by omega) (by decide)
  have hpos:1 ≤ (bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold time NatNative.budget
  rw [codeWord_length,codeWord_length,codeWord_length]
  unfold CompetitorWitnessTriple.budget budget at *
  omega

theorem fields_run_full (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      (∀ j,output (slots j 180)=NativeWord.word (BitFields.payload (NodeMeaning.codeWord bits j))) ∧
      (∀ j,readTapeBit (output (slots j 175)) 0=true ↔ BitFields.passes (NodeMeaning.codeWord bits j)) ∧
      (∀ j n,CanonicalBinary.decodeNat (value (NodeMeaning.codeWord bits j))=some n →
        output (slots j 180)=RepairRepresentation.natWord n) ∧
      (∀ i : Fin 122,(∀ j,sourceSlot j≠headerSlots i) →
        output (headerSlots i)=CompetitorWitnessTriple.stage [] bits 6 i) ∧
      (∀ j,output (slots j 174)=frame (BitFields.payload (NodeMeaning.codeWord bits j))) := by
  obtain ⟨h,hh,ht,hhds,hsteps⟩:=CompetitorWitnessTriple.triple_ready [] bits
  have hheader:=bounded_focus headerSlots header_injective _ _ _ ⟨h,hh,ht,hhds,hsteps.le⟩
    (input bits) (by intro i;simp only [input,headerSlots,Fin.addCases_left])
  choose out hout hword hflag hnative using (fun j : Fin 3=>NatNative.nat_run (NodeMeaning.codeWord bits j))
  have hp (j : Fin 3):ClockJoin.ReadyRun (part j) (NatNative.budget (NodeMeaning.codeWord bits j))
      (stage bits out j.val) (stage bits out (j.val+1)):=by
    have hf:=bounded_focus (slots j) (slots_injective j) _ _ _ (hout j)
      (stage bits out j.val) (stage_input bits out j)
    simpa only [stage,dif_pos j.isLt,part] using hf
  have h0:=ClockJoin.join header (part 0) _ _ _ _ _ hheader (hp 0)
  have h1:=ClockJoin.join first (part 1) _ _ _ _ _ h0 (hp 1)
  have h2:=ClockJoin.join second (part 2) _ _ _ _ _ h1 (hp 2)
  have hr:=ClockJoin.enlarge machine (time bits) (budget bits) _ _ h2 (time_bound bits)
  refine ⟨stage bits out 3,hr,?_,?_,?_,?_,?_⟩
  · intro j
    rw [stage_done bits out j 3 j.isLt (by rfl)]
    exact hword j
  · intro j
    rw [stage_done bits out j 3 j.isLt (by rfl)]
    exact (hflag j).trans (BitFields.passes_iff _).symm
  · intro j n hd
    rw [stage_done bits out j 3 j.isLt (by rfl)]
    exact hnative j n hd
  · intro i hi
    exact header_retained bits out 3 (by rfl) i hi
  · intro j
    rw [stage_done bits out j 3 j.isLt (by rfl)]
    exact NativePayload.nat_payload _ _ (hout j)

theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      (∀ j,output (slots j 180)=NativeWord.word (BitFields.payload (NodeMeaning.codeWord bits j))) ∧
      (∀ j,readTapeBit (output (slots j 175)) 0=true ↔ BitFields.passes (NodeMeaning.codeWord bits j)) ∧
      (∀ j n,CanonicalBinary.decodeNat (value (NodeMeaning.codeWord bits j))=some n →
        output (slots j 180)=RepairRepresentation.natWord n) ∧
      (∀ i : Fin 122,(∀ j,sourceSlot j≠headerSlots i) →
        output (headerSlots i)=CompetitorWitnessTriple.stage [] bits 6 i) := by
  obtain ⟨output,hr,hn,hf,ht,hh,_⟩:=fields_run_full bits
  exact ⟨output,hr,hn,hf,ht,hh⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeFields
