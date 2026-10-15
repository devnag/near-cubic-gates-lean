import Proof.CaseAnalysis.WitnessLegalLayout
import Proof.CaseAnalysis.WitnessLegalReadyFields

/-! The original input and raw oracle reach the exact legal-family policy
only after every actual source/oracle guard, retaining N and actual V. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem legal_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (hpad : k+3 ≤ Cpad) (hD : 1 ≤ D) (hden : 0<den) (hcap : 16*raw.length ≤ n) :
    ∃ actual,run (machine source a k CH Cpad cutoff D G copies e den delta code sym)
      (budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
      (input source a k D G e (List.ofFn x) raw)=some actual ∧
      actual.steps≤budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad ∧
      actual.final.tapes (lengthSlot source a k D G e)=List.replicate n true ∧
      actual.final.heads (lengthSlot source a k D G e)=0 ∧
      actual.final.heads (flagSlot source a k D G e)=0 ∧
      readTapeBit (actual.final.tapes (flagSlot source a k D G e)) 0=
        ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw ∧
      (∀ oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)),
        decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle →
        ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true →
        let r:=ColdNative.request source a k CH Cpad code x hpad oracle
        actual.final.tapes (old source a k D G e (countSlot source a k D G))=
          List.replicate ((a.output r).systematicBits+(a.output r).auxiliaryBits) true ∧
        actual.final.heads (old source a k D G e (countSlot source a k D G))=0 ∧
        (∀ i,actual.final.heads (slots source a k D G e i)=LegalTemplate.heads e i) ∧
        LegalTemplate.Call.Fields e den delta copies sym r.arity (CorePolicy.q0 D r.arity) (a.output r).clauseBits
          (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*max 1 (2*2^(a.output r).clauseBits)))
          (actual.final.tapes ∘ slots source a k D G e)):=by
  have priorExists:=ColdNative.native_run source a k CH Cpad cutoff D G copies delta code x raw hpad hD hcap
  let prior:=Classical.choose priorExists
  have pf:=Classical.choose_spec priorExists
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (LegalTemplate.Call.extra e)=>0) (fun _=>[]) prior
  have firstRun:=TapeEmbedding.run_embed (ColdNative.machine source a k CH Cpad cutoff D G copies delta code)
    (fun _ : Fin (LegalTemplate.Call.extra e)=>0) (fun _=>[]) _ _ prior pf.1
  rw [StreamPrepare.embed_initial] at firstRun
  have flagH:lifted.final.heads (flagSlot source a k D G e)=0:=
    (TapeEmbedding.receipt_heads_old _ _ prior _).trans pf.2.2.2.2.1
  have flagT:readTapeBit (lifted.final.tapes (flagSlot source a k D G e)) 0=
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw:=by
    rw [show lifted.final.tapes (flagSlot source a k D G e)=prior.final.tapes (ColdNative.flagSlot source a k D G) from
      TapeEmbedding.receipt_tapes_old _ _ prior _]
    exact pf.2.2.2.2.2.1
  have scan:(fun scanned=>scanned (flagSlot source a k D G e)) lifted.final.scanned=
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw:=by
    change readTapeBit _ (lifted.final.heads (flagSlot source a k D G e))=_
    rw [flagH];exact flagT
  by_cases live:ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true
  · have guards:ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true ∧
        (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).any
          (fun oracle=>decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
            (SelectedOracle.width source k CH Cpad code (List.ofFn x))))=true:=
      by simpa only [ColdNative.passed,Bool.and_eq_true] using live
    have existsOracle:∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
        (value raw)=some oracle ∧ oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
          (SelectedOracle.width source k CH Cpad code (List.ofFn x)):=by
      cases hd:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw) with
      | none => simp [hd] at guards
      | some oracle => exact ⟨oracle,rfl,by simpa [hd] using guards.2⟩
    let oracle:=Classical.choose existsOracle
    have hd:=(Classical.choose_spec existsOracle).1
    have sizeGood:=(Classical.choose_spec existsOracle).2
    let r:=ColdNative.request source a k CH Cpad code x hpad oracle
    have retained:=pf.2.2.2.2.2.2 oracle guards.1 hd sizeGood
    have inputs:=retained_fields source a k D G copies delta prior.final r (retained.1 13) retained.2.2
    have lastExists:=LegalTemplate.Call.call_run e den delta copies sym (fields source a k D G)
      (fields_injective source a k D G) prior.final.tapes prior.final.heads r.arity (CorePolicy.q0 D r.arity)
      (a.output r).clauseBits (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*
        max 1 (2*2^(a.output r).clauseBits))) hden (core_positive source a k CH Cpad code x hpad oracle) inputs.1 inputs.2
    let last:=Classical.choose lastExists
    have lf:=Classical.choose_spec lastExists
    have actualExists:=CloseoutRowsCircuitGuarded.accepted
      (first source a k CH Cpad cutoff D G copies e delta code) (second source a k D G e den copies delta sym)
      (fun scanned=>scanned (flagSlot source a k D G e))
      (ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad)
      (tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle) (fun _=>0)
      (input source a k D G e (List.ofFn x) raw) lifted last firstRun lf.1 (scan.trans live)
    let actual:=Classical.choose actualExists
    have af:=Classical.choose_spec actualExists
    have he:budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad=
        ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad+1+
          tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle+1:=by
      rw [budget,if_pos live,hd]
      exact (Nat.add_assoc _ _ _).symm
    have keepN:=lf.2.2.2.2 (ColdNative.lengthSlot source a k D G) (fields_ne_length source a k D G)
    have keepF:=lf.2.2.2.2 (ColdNative.flagSlot source a k D G) (fields_ne_flag source a k D G)
    refine ⟨actual,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [he];exact af.1
    · rw [he];exact af.2.1
    · rw [af.2.2.2];exact keepN.2.trans pf.2.2.1
    · rw [af.2.2.1];exact keepN.1.trans pf.2.2.2.1
    · rw [af.2.2.1];exact keepF.1.trans pf.2.2.2.2.1
    · rw [af.2.2.2]
      simp only [flagSlot,old]
      rw [keepF.2]
      exact pf.2.2.2.2.2.1
    · intro other otherDecode _
      have same:other=oracle:=Option.some.inj (otherDecode.symm.trans hd)
      subst other
      have countKeep:=lf.2.2.2.2 (countSlot source a k D G) (fields_ne_count source a k D G)
      refine ⟨?_,?_,?_,?_⟩
      · rw [af.2.2.2];exact countKeep.2.trans retained.2.2.count
      · rw [af.2.2.1]
        exact countKeep.1.trans (retained.2.2.cursor (SourcePolicy.countSlots D 40))
      · intro i;rw [af.2.2.1];exact lf.2.2.1 i
      · rw [af.2.2.2];exact lf.2.2.2.1
  · have stopped:=CloseoutRowsCircuitGuarded.rejected
      (first source a k CH Cpad cutoff D G copies e delta code) (second source a k D G e den copies delta sym)
      (fun scanned=>scanned (flagSlot source a k D G e))
      (ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad) (fun _=>0)
      (input source a k D G e (List.ofFn x) raw) lifted firstRun (scan.trans (Bool.eq_false_iff.mpr live))
    let actual:=Classical.choose stopped
    have af:=Classical.choose_spec stopped
    have he:budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad=
        ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad+1:=by
      simp only [budget,if_neg live,Nat.add_zero]
    refine ⟨actual,?_,?_,?_,?_,?_,?_,fun _ _ hp=>False.elim (live hp)⟩
    · rw [he];exact af.1
    · rw [he];exact af.2.1
    · rw [af.2.2.2];exact (TapeEmbedding.receipt_tapes_old _ _ prior _).trans pf.2.2.1
    · rw [af.2.2.1];exact (TapeEmbedding.receipt_heads_old _ _ prior _).trans pf.2.2.2.1
    · rw [af.2.2.1];exact flagH
    · rw [af.2.2.2];exact flagT

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
