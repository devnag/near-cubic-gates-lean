import Proof.CaseAnalysis.WitnessNativeGuard
import Proof.CaseAnalysis.WitnessOracleCallRun
import Proof.PCP.ProjectionDimensionCanonical
import Proof.CaseAnalysis.RowsGatePair

/-! The paid actual native-width comparison precedes the complete cold
oracle parser. Its rejecting branch does not enter the parser; both branches
retain the entire selected source bank and the original input-length field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GuardedOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization ExecutableInterfaces CanonicalWitnessCodec
open RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (t : ℕ):=OracleCall.tapes (t+4)
def fields {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t) : Fin 2 → Fin t:=![parser 2,length]
def parserFields {t : ℕ} (parser : Fin 3 → Fin t) : Fin 3 → Fin (t+4):=fun i=>(parser i).castAdd 4
def old {t : ℕ} (i : Fin t) : Fin (tapes t):=OracleCall.old (i.castAdd 4)
def gate (t : ℕ) : Fin (tapes t):=OracleCall.old (NativeGuard.flagSlot t)
def flagSlot (t : ℕ):=OracleCall.parserSlots (t+4) Oracle.flagSlot
def descriptorSlot (t : ℕ):=OracleCall.parserSlots (t+4) Oracle.descriptorSlot
def input {t : ℕ} (base : Fin t → List Bool) (bits : List Bool):=OracleCall.input (NativeGuard.input base) bits
def first {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t):=
  RecoveryFocus.machine (@OracleCall.old (t+4)) (NativeGuard.machine (fields parser length))
def second {t : ℕ} (parser : Fin 3 → Fin t):=OracleCall.machine (parserFields parser)
def machine {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t):=
  CloseoutRowsGateColdPair.machine (first parser length) (second parser) (fun scanned=>scanned (gate t))
def budget (R : ℕ) (x bits : List Bool):=
  RawCompare.budget R x.length+1+(if R ≤ x.length then OracleCall.budget x bits R.bits else 0)+1
def passed (R : ℕ) (x bits : List Bool):=
  decide (R ≤ x.length) && (decodeBooleanCircuit R (value bits)).isSome

private theorem initial_install {t : ℕ} (base : Fin t → List Bool) (bits : List Bool)
    (prior : Fin (t+4) → List Bool) :
    install (@OracleCall.old (t+4)) (input base bits) prior=OracleCall.input prior bits:=by
  funext i
  refine Fin.addCases (m:=t+4) (n:=1385) ?_ ?_ i
  · intro j
    change install (@OracleCall.old (t+4)) _ _ (OracleCall.old j)=_
    rw [install_slot _ (OracleCall.old_injective _)]
    exact (OracleCall.input_old prior bits j).symm
  · intro j
    rw [install_other _ _ _ _ (by intro l hl;exact OracleCall.old_ne_extra l j hl)]
    simp only [input,OracleCall.input,Fin.addCases_right]

theorem oracle_run {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t)
    (distinct : parser 2 ≠ length) (base : Fin t → List Bool) (R : ℕ) (x bits : List Bool)
    (hx : base (parser 0)=frame x) (hbits : base (parser 1)=frame R.bits)
    (hraw : base (parser 2)=List.replicate R true)
    (hNraw : base length=List.replicate x.length true)
    (hN : 2 ≤ x.length) (hcap : 16*bits.length ≤ x.length) :
    ∃ out,ClockJoin.ReadyRun (machine parser length) (budget R x bits) (input base bits) out ∧
      (∀ i,out (old i)=base i) ∧ out (gate t)=[decide (R ≤ x.length)] ∧
      readTapeBit (out (flagSlot t)) 0=passed R x bits ∧
      (R ≤ x.length → ∀ c : BooleanCircuit R,decodeBooleanCircuit R (value bits)=some c →
        out (descriptorSlot t)=PCPPNative.descriptor c):=by
  have hf:Function.Injective (fields parser length):=by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [fields] at h ⊢
    · exact False.elim (distinct h)
    · exact False.elim (distinct h.symm)
  obtain ⟨prior,hprior,retained,guard⟩:=NativeGuard.guard_run (fields parser length) hf R x.length base hraw hNraw
  have hfirst:=hprior.focus (@OracleCall.old (t+4)) (OracleCall.old_injective _) (input base bits)
    (by intro i;exact OracleCall.input_old _ _ i)
  rw [initial_install] at hfirst
  have hgate:OracleCall.input prior bits (gate t)=[decide (R ≤ x.length)]:=
    (OracleCall.input_old _ _ _).trans guard
  by_cases live:R ≤ x.length
  · have hb:R.bits.length ≤ x.length+1:=by
      rw [Nat.size_eq_bits_len]
      apply Nat.size_le.mpr
      have hp:x.length+1 < 2^(x.length+1):=Nat.lt_two_pow_self
      omega
    obtain ⟨out,hcall,oldCall,flag,descriptor⟩:=OracleCall.call_run (parserFields parser) prior bits x R.bits
      ((retained _).trans hx) ((retained _).trans hbits)
      (by rw [DimensionProducer.bits_value];exact (retained _).trans hraw) hN hcap hb
    rw [DimensionProducer.bits_value] at flag descriptor
    have joined:=CloseoutRowsGateColdPair.joined (first parser length) (second parser)
      (fun scanned=>scanned (gate t)) _ _ _ _ _ hfirst hcall
      (by change readTapeBit (OracleCall.input prior bits (gate t)) 0=true
          rw [hgate];simp [live,readTapeBit])
    have ready:ClockJoin.ReadyRun (machine parser length) (budget R x bits) (input base bits) out:=by
      simpa only [machine,budget,if_pos live] using joined
    refine ⟨out,ready,fun i=>(oldCall _).trans (retained i),(oldCall _).trans guard,?_,fun _ c hc=>descriptor c hc⟩
    rw [flagSlot,flag]
    simp [passed,live,readTapeBit]
  · have rejected:=CloseoutRowsGateColdPair.rejected (first parser length) (second parser)
      (fun scanned=>scanned (gate t)) _ _ _ hfirst
      (by change readTapeBit (OracleCall.input prior bits (gate t)) 0=false
          rw [hgate];simp [live,readTapeBit])
    have ready:=ClockJoin.enlarge (machine parser length) (RawCompare.budget R x.length+1)
      (budget R x bits) _ _ rejected (by unfold budget;rw [if_neg live];omega)
    refine ⟨_,ready,fun i=>(OracleCall.input_old _ _ _).trans (retained i),hgate,?_,fun h=>False.elim (live h)⟩
    have blank:OracleCall.input prior bits (flagSlot t)=[]:=by
      change OracleCall.input prior bits (OracleCall.extra (t+4) ⟨1379,by decide⟩)=[]
      rw [OracleCall.input_extra]
      rfl
    rw [blank]
    simp [passed,live,readTapeBit]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.GuardedOracle
