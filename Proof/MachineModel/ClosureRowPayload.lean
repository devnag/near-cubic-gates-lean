import Proof.MachineModel.ClosureActualRow
import Proof.MachineModel.GeneratedAmplifierCopy
import Proof.MachineModel.OrdinaryMatrixScoreSkipField

/-! The immediate raw-family consumer requires binary counts, whereas the
checked row printer emits six framed fields. Reuse the existing field skipper
and unframer: five skips, then one copy. The machine depends on no runtime row,
width, coefficient or answer. This is paid per-row input/output processing in
the A.13.9/A.13.10 supplier charge. Source positioning remains explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RowPayload
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open CloseoutRowsEstimatorCoefficients CompetitorRationalDecision SignedSortKey

private def states : Nat → Nat
  | 0 => 3
  | k+1 => 3+states k
private def reader : (k : Nat) → Machine 2 (states k)
  | 0 => GeneratedAmplifier.Copy.machine
  | k+1 => Composition.machine (TapeEmbedding.machine 1 MatrixScoreSkipField.machine) (reader k)
private def fieldPrefix (fields : List (List Bool)) := fields.flatMap frame

private theorem skip (bits pre tail out : List Bool) :
    Step (TapeEmbedding.machine 1 MatrixScoreSkipField.machine) (2*bits.length+1)
      ![pre.length,out.length] ![pre++frame bits++tail,out]
      ![pre.length+(frame bits).length,out.length] ![pre++frame bits++tail,out] := by
  obtain ⟨r,hr,hf,_⟩ := MatrixScoreSkipField.field_run bits pre tail
  have h := (Step.of_run hr (congrArg Configuration.heads hf)
    (congrArg Configuration.tapes hf)).embed (fun _ : Fin 1 => out.length) (fun _ => out)
  convert h using 1 <;> (first | rfl | (funext i; fin_cases i <;> rfl))

private theorem reader_run (fields : List (List Bool)) (bits pre tail out : List Bool) :
    Step (reader fields.length) ((fieldPrefix fields).length+fields.length+(2*bits.length+1))
      ![pre.length,out.length] ![pre++fieldPrefix fields++frame bits++tail,out]
      ![pre.length+(fieldPrefix fields).length+(frame bits).length,(out++bits).length]
      ![pre++fieldPrefix fields++frame bits++tail,out++bits] := by
  induction fields generalizing pre with
  | nil =>
    obtain ⟨r,hr,hf,_⟩ := GeneratedAmplifier.Copy.copy_run pre bits tail out
    have h := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
    simpa only [reader,states,fieldPrefix,List.flatMap_nil,List.length_nil,Nat.zero_add,
      Nat.add_zero,List.append_nil,frame_length,GeneratedAmplifier.Copy.cfg,Nat.add_assoc] using h
  | cons field fields ih =>
    have first := skip field pre (fieldPrefix fields++frame bits++tail) out
    have last := ih (pre++frame field)
    simp only [List.length_append,List.append_assoc] at first last
    have joined := first.seq last
    convert joined using 1 <;>
      simp only [reader,states,List.length_cons,fieldPrefix,List.flatMap_cons,List.length_append,
        frame_length,List.append_assoc,Nat.add_assoc] <;> (first | omega | rfl)

def machine := reader 5
def budget (b : Nat) := 20*b+27

/-- Exactly the scalar field consumed by `RowAnswerWord.raw_family_run`.
No parsed answer or answer tape is assumed. -/
theorem run (b : Nat) (q : CompetitorValidity.Estimate) (count den : Nat)
    (pre tail out : List Bool) :
    Step machine (budget b)
      ![pre.length,out.length] ![pre++Stream.recordWord b q count den++tail,out]
      ![pre.length+(Stream.recordWord b q count den).length,(out++binary b count).length]
      ![pre++Stream.recordWord b q count den++tail,out++binary b count] := by
  let fields := [binary (width b) q.positive,binary (width b) q.negative,
    binary (width b) q.denominator,binary (width b) 0,binary b den]
  have h := reader_run fields (binary b count) pre tail out
  have he : fieldPrefix fields++frame (binary b count)=Stream.recordWord b q count den := by
    simp [fieldPrefix,fields,Stream.recordWord,Stream.recordFields,
      CompetitorMonomialStream.fieldStream,CompetitorMonomialStream.allFields,List.append_assoc]
  have hl : (fieldPrefix fields).length+fields.length+(2*(binary b count).length+1)=budget b := by
    simp [fieldPrefix,fields,width,budget]
    omega
  rw [hl] at h
  change Step machine _ _ _ _ _ at h
  have ht : pre++fieldPrefix fields++frame (binary b count)++tail =
      pre++Stream.recordWord b q count den++tail := by
    rw [List.append_assoc pre,he]
  have hh : pre.length+(fieldPrefix fields).length+(frame (binary b count)).length =
      pre.length+(Stream.recordWord b q count den).length := by
    rw [Nat.add_assoc,←List.length_append,he]
  simpa only [ht,hh] using h

/-- A byte-level negative control against using the framed record directly. -/
theorem record_ne_raw (b : Nat) (q : CompetitorValidity.Estimate) (count den : Nat) :
    Stream.recordWord b q count den ≠ binary b count := by
  intro h
  have hl := congrArg List.length h
  rw [Stream.record_length,binary_length] at hl
  omega

end NearCubicWires.P1Closure.RowPayload
