import Proof.CaseAnalysis.RowsGatePorts

/-! Original gate metadata through the SAME all-raw public guard receipt.
Only already executed tape projections are exposed for circuit accounting. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
open LocalBitMultitape CanonicalBinary CanonicalWitnessCodec SupplierPipeline RadixSemantics
open RecoveryRootRound CloseoutRowsGatePairHeads CloseoutRowsGateSupport
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem receipt_unique {t s : ℕ} (p : Machine t s) (f g : ℕ) (c : Configuration t s)
    (a b : ExecutionReceipt t s) (ha : runFrom p f c=some a) (hb : runFrom p g c=some b) : a=b := by
  have ha' := runFrom_moreFuel p f g c a ha
  have hb' := runFrom_moreFuel p g f c b hb
  rw [Nat.add_comm g f] at hb'
  exact Option.some.inj (ha'.symm.trans hb')

theorem raw_ports {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (fuel : ℕ) (out : Fin 1035 → List Bool)
    (run : ClockJoin.ReadyRun (CloseoutRowsGateCold.actualMachine compressed) fuel (CloseoutRowsGateCold.input bits) out) :
    out 361=(List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord ∧
      out 994=frame (gateMembers g.support) ∧ out 808=RepairRepresentation.natWord g.gate.threshold.natAbs ∧
      out 368=CompareMachine.word n ∧ out 861=CompareMachine.word n ∧ out 1018=[true] := by
  obtain ⟨other,check,_word,flag,weights,members,threshold,nw,nm⟩ := CloseoutRowsGateCold.cold_ports compressed g bits h
  obtain ⟨a,ha,aT,_ah,_as⟩ := run
  obtain ⟨b,hb,bt,_bh,_bs⟩ := check
  have he := receipt_unique _ _ _ _ a b ha hb
  subst b
  have output : out=other := aT.symm.trans bt
  rw [output]
  exact ⟨weights,members,threshold,nw,nm,flag⟩

theorem guard_ports {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (fuel : ℕ) (out : Fin 1038 → List Bool)
    (run : ReadyAt (machine compressed) fuel heads (input n bits) out) :
    out 361=(List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord ∧
      out 994=frame (gateMembers g.support) ∧ out 808=RepairRepresentation.natWord g.gate.threshold.natAbs := by
  obtain ⟨raw,hr,_meaning⟩ := CloseoutRowsGateRawRun.allraw compressed bits
  obtain ⟨weights,members,threshold,nw,nm,flag⟩ := raw_ports compressed g bits h _ raw hr
  have joined := CloseoutRowsGatePairHeads.joined (first compressed) second (fun scanned => scanned 1018)
    _ _ heads _ _ _ (first_run compressed n bits raw hr) (second_run n n n raw nw nm) (by
      change readTapeBit (raw 1018) 0=true
      rw [flag];rfl)
  obtain ⟨a,ha,aT,_ah,_as⟩ := run
  obtain ⟨b,hb,bt,_bh,_bs⟩ := joined
  have he := receipt_unique _ _ _ _ a b ha hb
  subst b
  have output : out=install slots (extend n raw) (CloseoutRowsGateCounts.output n n n) := aT.symm.trans bt
  rw [output]
  refine ⟨?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    exact weights
  · rw [install_other _ _ _ _ (by decide)]
    exact members
  · rw [install_other _ _ _ _ (by decide)]
    exact threshold

end NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
