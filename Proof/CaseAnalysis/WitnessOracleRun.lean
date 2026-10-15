import Proof.CaseAnalysis.WitnessOracleFlags

/-! Complete cold Boolean-oracle decoding: exact public decoder flag and the
same typed native descriptor, with every head physically rewound. All bank
allocation, canonical traversals, node rounds, scalar comparison and footer
are included in this one ordinary machine and its additive budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem descriptor_of_decode (arityBits bits : List Bool)
    (c : BooleanCircuit (value arityBits))
    (hd : decodeBooleanCircuit (value arityBits) (value bits)=some c) :
    descriptor arityBits bits=PCPPNative.descriptor c:=by
  have h:=DAGChecks.checks_of_typed c bits (encodeBooleanCircuit_of_decode hd).symm
  obtain ⟨c',_,hc,_,_,hn⟩:=DAGChecks.typed_of_checks (value arityBits) bits h
  have he:c'=c:=Option.some.inj (hc.symm.trans hd)
  subst c'
  have hcan:(outputPayload bits)=[] ∨ (outputPayload bits).getLast?=some true:=
    (BitFields.last_iff _).mp h.2.2.1.2.2
  have hw:=NativeWord.word_eq (outputPayload bits) hcan
  rw [descriptor,nodesDescriptor,DAGNodes.nativeHeader,hw]
  simpa only [DAGChecks.output,outputPayload,List.append_assoc] using hn.symm

noncomputable def rawMachine:=Composition.machine described verdict
def rawBudget (x bits arityBits : List Bool):=describedBudget x bits arityBits+1+1

theorem raw_run (x bits arityBits : List Bool) (hN : 2 ≤ x.length)
    (hcap : 16*bits.length ≤ x.length) (hb : arityBits.length ≤ x.length+1) : ∃ actual,
    run rawMachine (rawBudget x bits arityBits) (input x bits arityBits)=some actual ∧
      actual.steps ≤ rawBudget x bits arityBits ∧
      actual.final.tapes 1379=[(decodeBooleanCircuit (value arityBits) (value bits)).isSome] ∧
      (∀ c : BooleanCircuit (value arityBits),decodeBooleanCircuit (value arityBits) (value bits)=some c →
        actual.final.tapes 1299=PCPPNative.descriptor c):=by
  obtain ⟨d,hd,ds,dout⟩:=described_cold_run x bits arityBits hN hcap hb
  have vr:=DAGVerdict.verdict_run (fun i=>d.final.tapes (verdictSlots (i.castAdd 1)))
  obtain ⟨v,hv,_,vt,vs⟩:=vr.focus_at verdictSlots verdict_injective d.final.heads d.final.tapes
    (verdict_input dout) (verdict_heads dout)
  have hall:=Composition.run_join described verdict _ _ _ d v hd hv
  have eqBool : ∀ a b : Bool,(a=true ↔ b=true) → a=b:=by decide
  have heq:=eqBool _ _ (dout.flag_meaning hb)
  refine ⟨Composition.joinedReceipt d v,hall,?_,?_,?_⟩
  · change d.steps+1+v.steps ≤ rawBudget x bits arityBits
    unfold rawBudget
    omega
  · rw [PCPTripleGlobal.joined_tapes,vt]
    change install verdictSlots _ _ (verdictSlots 5)=_
    rw [install_slot _ verdict_injective]
    change DAGVerdict.output _ ((0 : Fin 1).natAdd 5)=_
    rw [DAGVerdict.output,Fin.addCases_right]
    exact congrArg (fun b=>[b]) heq
  · intro c hc
    rw [PCPTripleGlobal.joined_tapes,vt,install_other _ _ _ _ (by decide)]
    obtain ⟨_,_,_,_,ht,_⟩:=dout
    exact ht.trans (descriptor_of_decode arityBits bits c hc)

noncomputable def machine:=Rewind.machine rawMachine
def budget (x bits arityBits : List Bool):=2*rawBudget x bits arityBits+2
def coldInput (x bits arityBits : List Bool) : Fin (tapes+1)→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (tapes+1)=>List Bool) (input x bits arityBits) (fun _=>[])
def flagSlot : Fin (tapes+1):=(1379 : Fin tapes).castAdd 1
def descriptorSlot : Fin (tapes+1):=(1299 : Fin tapes).castAdd 1

theorem cold_run (x bits arityBits : List Bool) (hN : 2 ≤ x.length)
    (hcap : 16*bits.length ≤ x.length) (hb : arityBits.length ≤ x.length+1) : ∃ out,
    ClockJoin.ReadyRun machine (budget x bits arityBits) (coldInput x bits arityBits) out ∧
      out flagSlot=[(decodeBooleanCircuit (value arityBits) (value bits)).isSome] ∧
      (∀ c : BooleanCircuit (value arityBits),decodeBooleanCircuit (value arityBits) (value bits)=some c →
        out descriptorSlot=PCPPNative.descriptor c):=by
  obtain ⟨r,hr,rs,rflag,rnative⟩:=raw_run x bits arityBits hN hcap hb
  obtain ⟨a,ha,atape,ah,asteps,_⟩:=Rewind.reset_run rawMachine (rawBudget x bits arityBits)
    (input x bits arityBits) r hr
  have htime:2*r.steps+2 ≤ budget x bits arityBits:=by unfold budget;omega
  have hmore:=run_moreFuel machine (2*r.steps+2) (budget x bits arityBits-(2*r.steps+2)) _ a ha
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨a.final.tapes,⟨a,hmore,rfl,ah,asteps.trans_le htime⟩,?_,?_⟩
  · exact (atape 1379).trans rflag
  · intro c hc
    exact (atape 1299).trans (rnative c hc)

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
