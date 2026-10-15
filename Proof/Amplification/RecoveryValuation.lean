import Proof.Amplification.RecoveryPreliminaryBound

/-! The selected capped valuation parser on physically produced dimensions.
Only its false-only comparison backing is omitted by inverse padding;
source, zero-index frame and both true unary drivers are literal inputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (bits : List Bool) := RecoveryColdHeader.width bits
def cap (bits : List Bool) := RecoveryColdHeaderCap.limit bits
def capacity (bits : List Bool) := 8192*(width bits+1)^2
def data (bits word : List Bool) : RecoveryValuationStream.Data :=
  ⟨frame word,0,width bits,RecoveryColdHeader.zeroWord bits,[],false,false,false,capacity bits⟩
def heads : Fin 10→Nat := ![0,0,1,0,0,0,0,0,1,1]
def tapes (bits word : List Bool) : Fin 10→List Bool :=
  ![frame word,[],CompareMachine.word (width bits+1),frame (RecoveryColdHeader.zeroWord bits),
    [false],[false],[],[false],[false],CompareMachine.word (cap bits)]
def caps (bits : List Bool) (i : Fin 10) : Nat := if i.val=6 then capacity bits else 0
noncomputable def machine := RecoveryValuationCount.machine

theorem padded_input (bits word : List Bool) :
    ZeroPadding.config (caps bits) (⟨machine.start,heads,tapes bits word⟩ : Configuration 10 _)=
      RecoveryValuationCount.cfg (data bits word) 0 (cap bits) machine.start := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,tapes,RecoveryValuationCount.cfg,
      RecoveryValuationStream.Data.cfg,data,TapeEmbedding.config,Fin.addCases,CompareMachine.word,
      ZeroPadding.pad]

theorem parser_run (bits word : List Bool) :
    ∃ r,runFrom machine (RecoveryValuationCount.limit (width bits) (cap bits))
        ⟨machine.start,heads,tapes bits word⟩=some r ∧
      r.steps≤RecoveryValuationCount.limit (width bits) (cap bits) ∧
      r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList (cap bits) (readEntry (width bits)) word).isSome] := by
  have hi : (data bits word).index.length=(data bits word).width :=
    RecoveryColdHeader.zero_length bits
  have hc : 2*(data bits word).index.length+2≤(data bits word).capacity := by
    rw [hi]
    change 2*width bits+2≤8192*(width bits+1)^2
    nlinarith
  obtain ⟨base,hbase,hs,hh,ht,_⟩ := RecoveryValuationCount.ready_return (data bits word) [] word (cap bits)
    rfl rfl hi (by simp [data]) hc rfl rfl
  change runFrom machine (RecoveryValuationCount.limit (width bits) (cap bits))
    (RecoveryValuationCount.cfg (data bits word) 0 (cap bits) machine.start)=some base at hbase
  rw [←padded_input bits word] at hbase
  obtain ⟨r,hr,hf,hsteps,_⟩ := ZeroPadding.run_unpad machine (caps bits)
    (RecoveryValuationCount.limit (width bits) (cap bits)) _ base hbase
  refine ⟨r,hr,hsteps.le.trans hs,?_,?_⟩
  · have h := congrArg (fun c=>c.heads (7 : Fin 10)) hf
    exact h.trans hh
  · have h := congrArg (fun c=>c.tapes (7 : Fin 10)) hf
    simp only [ZeroPadding.config,caps,Fin.isValue,show (7 : Fin 10).val≠6 by decide,if_false,ZeroPadding.pad_zero] at h
    exact h.trans ht

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
