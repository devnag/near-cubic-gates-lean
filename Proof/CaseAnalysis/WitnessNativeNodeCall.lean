import Proof.CaseAnalysis.WitnessOracleCapCall
import Proof.PCP.PCPPNativeCounterNodesDock
import Proof.PCP.PCPPNativeClauseQueryForward
import Proof.Amplification.RecoveryAllCodeLayout

/-! Reuse the original complete node emitter on the measured nine-field
bank. The cap checker preserves these fields, so no metadata scan is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeNodeCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old {t : ℕ} (i : Fin t) : Fin (t+363):=i.castAdd 363
def bank {t : ℕ} (counter : Fin 75→Fin t) : Fin 438→Fin (t+363):=
  Fin.addCases (m:=75) (n:=363) (motive:=fun _=>Fin (t+363))
    (fun i=>old (counter i)) (fun i=>i.natAdd t)
def slots {t : ℕ} (counter : Fin 75→Fin t):=bank counter ∘ PCPPNativeCounterNodes.slots

theorem bank_injective {t : ℕ} (counter : Fin 75→Fin t) (hc : Function.Injective counter) :
    Function.Injective (bank counter):=by
  apply RecoveryColdAllCode.join_injective
  · intro a b h
    have hv:=congrArg Fin.val h
    exact hc (Fin.ext hv)
  · intro a b h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  · intro a b h
    have hv:=congrArg Fin.val h
    dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    have hlt:=(counter a).isLt
    omega

theorem bank_small {t : ℕ} (counter : Fin 75→Fin t) (i : Fin 438) (hi : i.val<75) :
    bank counter i=old (counter ⟨i.val,hi⟩):=by
  have he:i=(⟨i.val,hi⟩ : Fin 75).castAdd 363:=Fin.ext rfl
  conv_lhs => rw [he]
  simp only [bank,Fin.addCases_left]

theorem slots_injective {t : ℕ} (counter : Fin 75→Fin t) (hc : Function.Injective counter) :
    Function.Injective (slots counter):=
  (bank_injective counter hc).comp PCPPNativeCounterNodes.slots_injective

def input {t : ℕ} (data : Fin t→List Bool) : Fin (t+363)→List Bool:=Fin.addCases data (fun _=>[])
def heads {t : ℕ} (cursor : Fin t→ℕ) : Fin (t+363)→ℕ:=Fin.addCases cursor (fun _=>0)
def machine {t : ℕ} (counter : Fin 75→Fin t):=RecoveryFocus.machine (slots counter) PCPPNativeClauseOracle.machine

theorem forward {t : ℕ} (counter : Fin 75→Fin t) (hc : Function.Injective counter) :
    CursorRestore.NoLeft (machine counter) (slots counter 102):=
  CursorRestore.focus_forward (slots counter) (slots_injective counter hc) _ 102 PCPPNativeClauseForward.whole

theorem input_fields {t R : ℕ} (counter : Fin 75→Fin t) (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hf : ∀ j,cursor (counter (PCPPNativeColdCounters.ports j))=0 ∧
      data (counter (PCPPNativeColdCounters.ports j))=PCPPNativeMetadataMass.values oracle p Q j)
    (i : Fin 363) :
    heads cursor (slots counter i)=0 ∧ input data (slots counter i)=
      PCPPNativeCounterNodes.nodeInput (PCPPNative.descriptor oracle) (PCPPNativeMetadataMass.queryBytes p R Q)
        (DedupBytes.fields p) R Q oracle.size (Codec.clauses p).length
        (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length i:=by
  by_cases h0:i=0
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 3
  by_cases h1:i=1
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 1
  by_cases h2:i=2
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 4
  by_cases h18:i=18
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 2
  by_cases h19:i=19
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 6
  by_cases h20:i=20
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 8
  by_cases h95:i=95
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 0
  by_cases h96:i=96
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 5
  by_cases h291:i=291
  · subst i
    simpa [input,heads,slots,bank_small,old,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
      PCPPNativeColdCounters.ports,PCPPNativeMetadataMass.values] using hf 7
  simp [input,heads,slots,bank,PCPPNativeCounterNodes.slots,PCPPNativeCounterNodes.nodeInput,
    h0,h1,h2,h18,h19,h20,h95,h96,h291]

theorem raw_arity_outside {t : ℕ} (counter : Fin 75→Fin t) (hc : Function.Injective counter) :
    ∀ j,slots counter j≠old (counter 72):=by
  intro j h
  have he:old (counter 72)=bank counter ((72 : Fin 75).castAdd 363):=by
    simp only [bank,Fin.addCases_left]
  have hj:=bank_injective counter hc (h.trans he)
  exact (by decide : ∀ i : Fin 363,PCPPNativeCounterNodes.slots i≠(72 : Fin 438)) j hj

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeNodeCall
