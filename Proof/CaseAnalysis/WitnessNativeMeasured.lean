import Proof.CaseAnalysis.WitnessSelectedCounters
import Proof.CaseAnalysis.WitnessOracle

/-! The retained source word and decoded oracle feed the original stream
and measured-counter workers. This is the actual post-decoder continuation;
neither source selection nor canonical oracle parsing is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeMeasured
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlots : Fin 5 → Fin 125:=![0,13,14,48,49]
def slots (i : Fin 75) : Fin 125:=
  if i=0 then 49 else if i=40 then 48 else if i=47 then 46
  else if i=52 then 29 else if i=54 then 25 else if i=57 then 38 else i.natAdd 50
def extra {R : ℕ} (oracle : BooleanCircuit R) (Q : ℕ) : Fin 77 → List Bool:=
  Fin.addCases (m:=2) (n:=75) (motive:=fun _=>List Bool) ![frame Q.bits,PCPPNative.descriptor oracle] (fun _=>[])
def input {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) : Fin 125 → List Bool:=
  Fin.addCases (m:=48) (n:=77) (motive:=fun _=>List Bool) (Streams.input p R Q) (extra oracle Q)
def first:=TapeEmbedding.machine 77 Streams.machine
def second:=RecoveryFocus.machine slots PCPPNativeColdCounters.machine
def machine:=Composition.machine first second
def budget (p : RawProjectionPCP) (R Q size : ℕ):=Streams.budget p R Q+1+PCPPNativeColdCounters.budget p R Q size

theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg (fun z : Fin 125=>z.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

theorem input_fields {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) (i : Fin 125) :
    input oracle p Q i=if i=0 then p.word else if i=13 then List.replicate R true
      else if i=14 then List.replicate Q true else if i=48 then frame Q.bits
      else if i=49 then PCPPNative.descriptor oracle else []:=by
  refine Fin.addCases (m:=48) (n:=77) ?_ ?_ i
  · intro j
    rw [input,Fin.addCases_left,Streams.input_literal]
    simp only [Fin.ext_iff,Fin.val_castAdd]
    change (if j.val=0 then p.word else if j.val=13 then List.replicate R true
      else if j.val=14 then List.replicate Q true else [])=
      (if j.val=0 then p.word else if j.val=13 then List.replicate R true
      else if j.val=14 then List.replicate Q true else if j.val=48 then frame Q.bits
      else if j.val=49 then PCPPNative.descriptor oracle else [])
    rw [if_neg (show j.val≠48 by omega),if_neg (show j.val≠49 by omega)]
  · intro j
    rw [input,Fin.addCases_right]
    refine Fin.addCases (m:=2) (n:=75) ?_ ?_ j
    · intro a;fin_cases a <;> rfl
    · intro a
      rw [extra,Fin.addCases_right]
      simp only [Fin.ext_iff,Fin.val_natAdd]
      change []=(if 48+(2+a.val)=0 then p.word else if 48+(2+a.val)=13 then List.replicate R true
        else if 48+(2+a.val)=14 then List.replicate Q true else if 48+(2+a.val)=48 then frame Q.bits
        else if 48+(2+a.val)=49 then PCPPNative.descriptor oracle else [])
      split_ifs <;> first | rfl | omega

theorem measured_run {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) :
    ∃ actual,run machine (budget p R Q oracle.size) (input oracle p Q)=some actual ∧
      actual.steps ≤ budget p R Q oracle.size ∧
      (∀ j,actual.final.heads (slots (PCPPNativeColdCounters.ports j))=0 ∧
        actual.final.tapes (slots (PCPPNativeColdCounters.ports j))=PCPPNativeMetadataMass.values oracle p Q j) ∧
      actual.final.heads (slots 72)=0 ∧ actual.final.tapes (slots 72)=List.replicate R true:=by
  obtain ⟨a,ha,asteps,query,queryCount,clause,clauseCount,qh,qch,ch,cch⟩:=Streams.streams_run p R Q hR hQ
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 77=>0) (extra oracle Q) a
  have firstRun:=TapeEmbedding.run_embed Streams.machine (fun _ : Fin 77=>0) (extra oracle Q) _ _ a ha
  rw [StreamPrepare.embed_initial] at firstRun
  have empty (j : Fin 75) : lifted.final.heads (j.natAdd 50)=0 ∧ lifted.final.tapes (j.natAdd 50)=[]:=by
    have hi:(j.natAdd 50 : Fin 125)=(j.natAdd 2).natAdd 48:=by
      apply Fin.ext;simp only [Fin.val_natAdd];omega
    rw [hi]
    exact ⟨TapeEmbedding.receipt_heads_new _ _ _ _,(TapeEmbedding.receipt_tapes_new _ _ _ _).trans
      (by rw [extra,Fin.addCases_right])⟩
  have localFields (i : Fin 75) : lifted.final.heads (slots i)=PCPPNativeColdCounters.heads i ∧
      lifted.final.tapes (slots i)=PCPPNativeColdCounters.input (PCPPNative.descriptor oracle) p R Q i:=by
    by_cases h0:i=0
    · subst i;exact ⟨rfl,rfl⟩
    by_cases h40:i=40
    · subst i;exact ⟨rfl,rfl⟩
    by_cases h47:i=47
    · subst i;exact ⟨cch,clauseCount⟩
    by_cases h52:i=52
    · subst i;exact ⟨qh,query⟩
    by_cases h54:i=54
    · subst i;exact ⟨qch,queryCount⟩
    by_cases h57:i=57
    · subst i;exact ⟨ch,clause⟩
    simp only [slots,if_neg h0,if_neg h40,if_neg h47,if_neg h52,if_neg h54,if_neg h57,
      PCPPNativeHierarchyCounters.counter_heads,PCPPNativeHierarchyCounters.counter_input]
    exact empty i
  obtain ⟨b,hb,bs,bfields,b72h,b72t⟩:=PCPPNativeColdCounters.counters_run oracle p Q hR hQ
  obtain ⟨last,lastRun,_,lastSteps,lastHeads,lastTapes,_⟩:=RecoveryFocus.dock slots slots_injective
    PCPPNativeColdCounters.machine _ lifted.final.heads lifted.final.tapes
    (PCPPNativeColdCounters.entry (PCPPNative.descriptor oracle) p R Q)
    (fun i=>(localFields i).1) (fun i=>(localFields i).2) b hb
  have whole:=Composition.run_join first second _ _ _ lifted last firstRun lastRun
  refine ⟨Composition.joinedReceipt lifted last,whole,?_,?_,?_,?_⟩
  · change a.steps+1+last.steps ≤ budget p R Q oracle.size
    rw [lastSteps]
    exact Nat.add_le_add (Nat.add_le_add_right asteps 1) bs
  · intro j
    exact ⟨(lastHeads _).trans (bfields j).1,(lastTapes _).trans (bfields j).2⟩
  · exact (lastHeads _).trans b72h
  · exact (lastTapes _).trans b72t

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeMeasured
