import Proof.CaseAnalysis.RowsCircuitBottomPublish

/-! Complete all-raw bottom decoder and guarded request/resource publisher.
Rejected syntax never enters the native append stage. Accepted requests are
the SAME strict source words, selected in original serialized order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound CloseoutRowsGatePairHeads
open CanonicalWitnessCodec SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeWord {core : ℕ} (g : SupportedNormalizedGate core):=
  RepairRepresentation.thresholdWord (CloseoutRowsGateSource.request false g).gate
def descriptionBytes {core : ℕ} (g : SupportedNormalizedGate core):=
  ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length+
    (RepairRepresentation.natWord g.gate.threshold.natAbs).length
def emitted (core : ℕ) (keep : Bool) (bits : List Bool):=
  match decodeSupportedNormalizedGate core (value bits) with
  | none=>[]
  | some g=>keptOutput keep (nativeWord g) []
def descriptionCost (core : ℕ) (bits : List Bool):=
  match decodeSupportedNormalizedGate core (value bits) with
  | none=>0
  | some g=>descriptionBytes g
def wireCost (core : ℕ) (keep : Bool) (bits : List Bool):=
  match decodeSupportedNormalizedGate core (value bits) with
  | none=>0
  | some g=>keptWires keep g.wireCount 0
def passed (core : ℕ) (bits : List Bool):=(decodeSupportedNormalizedGate core (value bits)).isSome
noncomputable def checked (threshold : Bool):=CloseoutRowsGateColdPair.machine parser (publish threshold) (fun scanned=>scanned 1037)

theorem keptOutput_append (keep : Bool) (bits out : List Bool) :
    keptOutput keep bits out=out++keptOutput keep bits []:=by cases keep <;> simp [keptOutput]
theorem keptWires_add (keep : Bool) (support n : ℕ) : keptWires keep support n=n+keptWires keep support 0:=by
  cases keep <;> simp [keptWires]

theorem checked_run_retained (threshold : Bool) (cap core pos memberPos : ℕ) (bits out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (hin : 2*bits.length+1 ≤ cap)
    (hcap : 2*CloseoutRowsGateMeasured.budget bits+4 ≤ cap) : ∃ r,
    runFrom (checked threshold) (7*cap+12)
      (cfg (checked threshold).start cap core pos memberPos bits out source membership description wireCount flag)=some r ∧
      r.steps ≤ 7*cap+12 ∧
      r.final.heads=heads pos memberPos (out++emitted core (kept threshold membership memberPos) bits)
        (description+descriptionCost core bits) (wireCount+wireCost core (kept threshold membership memberPos) bits) ∧
      readTapeBit (r.final.tapes 1037) 0=passed core bits ∧
      Stored cap core (out++emitted core (kept threshold membership memberPos) bits) source membership
        (description+descriptionCost core bits) (wireCount+wireCost core (kept threshold membership memberPos) bits) flag r.final.tapes ∧
      (∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
        r.final.tapes 994=ZeroPadding.pad cap (frame (CloseoutRowsGateSupport.gateMembers g.support))) := by
  obtain ⟨bank,p,pr,ps,ph,pt,meaning,stored,bitmap⟩:=parse_run_retained cap core pos memberPos bits out source membership
    description wireCount flag hin (by omega)
  let A:=p.final.tapes
  have first : ReadyAt parser (CloseoutRowsGateMeasured.budget bits)
      (heads pos memberPos out description wireCount)
      (data cap core bits out source membership description wireCount flag) A:=⟨p,pr,rfl,ph,ps⟩
  have flagPort : A 1037=ZeroPadding.pad cap (bank 1037):=pt 1037
  have flagValue : readTapeBit (A 1037) 0=passed core bits:=by
    rw [flagPort,ZeroPadding.read_pad]
    exact Bool.eq_iff_iff.mpr meaning.2.1
  cases hd:decodeSupportedNormalizedGate core (value bits) with
  | none =>
    have falseFlag : readTapeBit (A 1037) 0=false:=by simpa only [passed,hd,Option.isSome_none] using flagValue
    have stopped:=CloseoutRowsGatePairHeads.rejected parser (publish threshold) (fun scanned=>scanned 1037)
      _ (heads pos memberPos out description wireCount) _ _ first falseFlag
    obtain ⟨r,hr,rt,rh,rs⟩:=enlarge _ _ (7*cap+12) _ _ _ stopped (by omega)
    refine ⟨r,hr,rs,?_,?_,?_,?_⟩
    · simpa only [emitted,descriptionCost,wireCost,hd,List.append_nil,Nat.add_zero] using rh
    · rw [rt];exact flagValue
    · rw [rt]
      simpa only [emitted,descriptionCost,wireCost,hd,List.append_nil,Nat.add_zero] using stored
    · intro g hg
      cases hg
  | some g =>
    obtain ⟨nativeMeaning,weightMeaning,thresholdMeaning,supportMeaning⟩:=meaning.2.2 g hd
    have nativePort : A 1033=ZeroPadding.pad cap (frame (nativeWord g)):=by
      have h:A 1033=ZeroPadding.pad cap (bank 1033):=pt 1033
      change bank 1033=_ at nativeMeaning
      rw [h,nativeMeaning];rfl
    have weightPort : A 1041=ZeroPadding.pad cap
        (List.replicate ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length true):=by
      have h:A 1041=ZeroPadding.pad cap (bank 1041):=pt 1041
      change bank 1041=_ at weightMeaning
      rw [h,weightMeaning]
    have thresholdPort : A 1045=ZeroPadding.pad cap
        (List.replicate (RepairRepresentation.natWord g.gate.threshold.natAbs).length true):=by
      have h:A 1045=ZeroPadding.pad cap (bank 1045):=pt 1045
      change bank 1045=_ at thresholdMeaning
      rw [h,thresholdMeaning]
    have supportPort : A 1047=ZeroPadding.pad cap (List.replicate g.wireCount true):=by
      have h:A 1047=ZeroPadding.pad cap (bank 1047):=pt 1047
      change bank 1047=_ at supportMeaning
      rw [h,supportMeaning]
    have nativeFit : 2*(nativeWord g).length+1 ≤ cap:=by
      have h:=stored.scratch 1033
      change (A 1033).length ≤ cap at h
      rw [nativePort,ZeroPadding.pad_length,frame_length] at h
      omega
    have counts:=gate_counter_bounds g bits hd
    obtain ⟨q,qr,qs,qh,qt,qstored⟩:=publish_run threshold cap core pos memberPos
      ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length
      (RepairRepresentation.natWord g.gate.threshold.natAbs).length g.wireCount
      (nativeWord g) out source membership description wireCount flag A stored
      nativePort weightPort thresholdPort supportPort nativeFit (by omega) (by omega)
    have trueFlag : readTapeBit (A 1037) 0=true:=by simpa only [passed,hd,Option.isSome_some] using flagValue
    obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsGateSourceCalls.joined parser (publish threshold)
      (fun scanned=>scanned 1037) _ (6*cap+10) (heads pos memberPos out description wireCount) _ _ first q qr trueFlag
    have bound:CloseoutRowsGateMeasured.budget bits+1+(6*cap+10)+1 ≤ 7*cap+12:=by omega
    have more:=runFrom_moreFuel (checked threshold) _
      (7*cap+12-(CloseoutRowsGateMeasured.budget bits+1+(6*cap+10)+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨r,more,rs.trans bound,?_,?_,?_,?_⟩
    · rw [rh,qh,keptOutput_append,keptWires_add]
      simp only [emitted,descriptionCost,wireCost,hd,descriptionBytes]
    · rw [rt]
      change readTapeBit (q.final.tapes (coreSlots 1037)) 0=passed core bits
      rw [qt];exact flagValue
    · rw [rt]
      rw [keptOutput_append,keptWires_add] at qstored
      simpa only [emitted,descriptionCost,wireCost,hd,descriptionBytes] using qstored
    · intro gate hg
      rw [rt]
      exact (qt 994).trans (bitmap gate (hd.trans hg))

theorem checked_run (threshold : Bool) (cap core pos memberPos : ℕ) (bits out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (hin : 2*bits.length+1 ≤ cap)
    (hcap : 2*CloseoutRowsGateMeasured.budget bits+4 ≤ cap) : ∃ r,
    runFrom (checked threshold) (7*cap+12)
      (cfg (checked threshold).start cap core pos memberPos bits out source membership description wireCount flag)=some r ∧
      r.steps ≤ 7*cap+12 ∧
      r.final.heads=heads pos memberPos (out++emitted core (kept threshold membership memberPos) bits)
        (description+descriptionCost core bits) (wireCount+wireCost core (kept threshold membership memberPos) bits) ∧
      readTapeBit (r.final.tapes 1037) 0=passed core bits ∧
      Stored cap core (out++emitted core (kept threshold membership memberPos) bits) source membership
        (description+descriptionCost core bits) (wireCount+wireCost core (kept threshold membership memberPos) bits) flag r.final.tapes := by
  obtain ⟨r,hr,hs,hh,hf,store,_⟩:=checked_run_retained threshold cap core pos memberPos
    bits out source membership description wireCount flag hin hcap
  exact ⟨r,hr,hs,hh,hf,store⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
