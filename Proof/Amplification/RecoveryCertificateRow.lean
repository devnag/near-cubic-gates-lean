import Proof.Amplification.RecoveryCertificateField
import Proof.MachineModel.OrdinaryBoundedCounter

/-! A physical row is retained as its four fixed-width fields in one frame.
One existing bounded field read therefore parses an entire row. Scalar
extraction is paid later at the table-check consumer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateRow
open LocalBitMultitape RadixSemantics
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_length {width n : Nat} {bits rest : List Bool} (h : readField width bits=some (n,rest)) :
    bits.length=width+rest.length := by
  unfold readField at h
  split at h
  next hw =>
    have he : bits.drop width=rest := (congrArg Prod.snd (Option.some.inj h))
    rw [← he,List.length_drop]
    omega
  next => contradiction

theorem field_none {width : Nat} {bits : List Bool} (h : readField width bits=none) : bits.length<width := by
  unfold readField at h
  split at h
  next => contradiction
  next => omega

theorem row_isSome (width : Nat) (word : List Bool) :
    (readRow width word).isSome=decide (4*width≤word.length) := by
  cases h1 : readField width word with
  | none => simp [readRow,h1,show ¬4*width≤word.length by have h:=field_none h1; omega]
  | some p1 =>
    rcases p1 with ⟨kind,r1⟩
    have hl1 := field_length h1
    cases h2 : readField width r1 with
    | none => simp [readRow,h1,h2,show ¬4*width≤word.length by have h:=field_none h2; omega]
    | some p2 =>
      rcases p2 with ⟨code,r2⟩
      have hl2 := field_length h2
      cases h3 : readField width r2 with
      | none => simp [readRow,h1,h2,h3,show ¬4*width≤word.length by have h:=field_none h3; omega]
      | some p3 =>
        rcases p3 with ⟨count,r3⟩
        have hl3 := field_length h3
        cases h4 : readField width r3 with
        | none => simp [readRow,h1,h2,h3,h4,show ¬4*width≤word.length by have h:=field_none h4; omega]
        | some p4 =>
          rcases p4 with ⟨payload,r4⟩
          have hl4 := field_length h4
          simp [readRow,h1,h2,h3,h4,show 4*width≤word.length by omega]

theorem bounded_read (width : Nat) (pre word backing : List Bool) (hb : backing.length≤8*width+1) :
    ∃ receipt : ExecutionReceipt 3 6,
      runFrom FieldMachine.machine (16*width+2)
        (FieldMachine.scan 0 (pre++frame word) pre.length (4*width) 0 [] backing)=some receipt ∧
      (receipt.final.control=4 ↔ (readRow width word).isSome=true) ∧
      ((readRow width word).isSome=true → receipt.final=FieldMachine.finished (pre++frame word)
        (frame (word.take (4*width))) (pre.length+8*width) (4*width)) := by
  obtain ⟨r,hr,ha,hf⟩ := RecoveryCertificateField.bounded_read (4*width) pre word backing (by omega)
  have hc : 4*(4*width)+2=16*width+2 := by omega
  rw [hc] at hr
  refine ⟨r,hr,?_,?_⟩
  · rw [ha,row_isSome]
    simp [readField]
  · intro hs
    rw [row_isSome,decide_eq_true_eq] at hs
    simpa only [show 2*(4*width)=8*width by omega] using hf hs

theorem encoded_run (width : Nat) (row : Row) (pre suffix backing : List Bool)
    (hb : backing.length≤8*width+1) :
    let word := packRow width row++suffix
    ∃ receipt : ExecutionReceipt 3 6,
      runFrom FieldMachine.machine (16*width+2)
        (FieldMachine.scan 0 (pre++frame word) pre.length (4*width) 0 [] backing)=some receipt ∧
      receipt.final=FieldMachine.finished (pre++frame word) (frame (packRow width row))
        (pre.length+8*width) (4*width) := by
  obtain ⟨r,hr,_,hf⟩ := bounded_read width pre (packRow width row++suffix) backing hb
  have hs : (readRow width (packRow width row++suffix)).isSome=true := by
    rw [row_isSome]
    simp [packRow_length]
  have ht : (packRow width row++suffix).take (4*width)=packRow width row :=
    List.take_left' (packRow_length width row)
  exact ⟨r,hr,by simpa only [ht] using hf hs⟩

end NearCubicWires.RepairOrdinary.RecoveryCertificateRow
