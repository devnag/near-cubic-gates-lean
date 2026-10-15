import Proof.Amplification.RecoveryRowFieldsRun

/-! The four physically retained row fields equal the selected parser's
kind, code, count and payload, including the exact next source cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowFields
open LocalBitMultitape RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (width : Nat) (bits : List Bool) (i : Fin 4) :=
  (bits.drop (i.val*width)).take width
def parsed (width : Nat) (bits : List Bool) : Row :=
  ⟨value (words width bits 0),value (words width bits 1),
    value (words width bits 2),value (words width bits 3)⟩

theorem readRow_full (width : Nat) (bits : List Bool) (hw : 4*width ≤ bits.length) :
    readRow width bits=some (parsed width bits,bits.drop (4*width)) := by
  have h0 : width ≤ bits.length := by omega
  have h1 : width ≤ (bits.drop width).length := by rw [List.length_drop]; omega
  have h2 : width ≤ ((bits.drop width).drop width).length := by simp only [List.length_drop]; omega
  have h3 : width ≤ (((bits.drop width).drop width).drop width).length := by simp only [List.length_drop]; omega
  simp only [readRow,readField,if_pos h0]
  dsimp only [Bind.bind,Option.bind]
  rw [if_pos h1]
  dsimp only [Bind.bind,Option.bind]
  rw [if_pos h2]
  dsimp only [Bind.bind,Option.bind]
  rw [if_pos h3]
  dsimp only [Bind.bind,Option.bind]
  apply congrArg some
  apply Prod.ext
  · simp [parsed,words,List.drop_drop,Nat.succ_mul,Nat.add_assoc]
  · simp only [List.drop_drop]
    congr 1
    omega

theorem afterReads_width (d : Data) (start count : Nat) (bits : List Bool) :
    (afterReads d start count bits).width=d.width := by
  induction count generalizing d start bits with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem afterReads_source (d : Data) (start count : Nat) (bits : List Bool) :
    (afterReads d start count bits).source=d.source := by
  induction count generalizing d start bits with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem afterReads_valid (d : Data) (start count : Nat) (bits : List Bool) (hd : d.Valid) :
    (afterReads d start count bits).Valid := by
  induction count generalizing d start bits with
  | zero => exact hd
  | succ count ih => exact ih _ _ _ (after_valid d _ _ hd (List.length_take_le _ _))

theorem four_fields (d : Data) (bits : List Bool) (i : Fin 4) :
    (afterReads d 0 4 bits).fields i=frame (words d.width bits i) := by
  fin_cases i <;> simp [afterReads,index,Data.after,words,List.drop_drop,Nat.succ_mul,Nat.add_assoc]

theorem afterReads_pos (d : Data) (start count : Nat) (bits : List Bool)
    (hw : count*d.width ≤ bits.length) :
    (afterReads d start count bits).pos=d.pos+2*(count*d.width) := by
  induction count generalizing d start bits with
  | zero => simp [afterReads]
  | succ count ih =>
    have hfirst : d.width ≤ bits.length := by rw [Nat.succ_mul] at hw; omega
    have hrest : count*(d.after (index start) (bits.take d.width)).width ≤ (bits.drop d.width).length := by
      change count*d.width ≤ (bits.drop d.width).length
      rw [List.length_drop,Nat.succ_mul] at *
      omega
    rw [afterReads,ih _ _ _ hrest]
    simp only [Data.after,List.length_take,Nat.min_eq_left hfirst,Nat.succ_mul]
    omega

theorem row_value_run (d : Data) (pre bits : List Bool) (row : Row) (tail : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length) (hd : d.Valid)
    (hread : readRow d.width bits=some (row,tail)) :
    ∃ r,runFrom machine (budget d.width) (d.cfg machine.start)=some r ∧
      r.steps ≤ budget d.width ∧
      ∃ out : Data,r.final=terminal out ∧ out.Valid ∧ out.source=d.source ∧
        out.width=d.width ∧ out.pos=d.pos+8*d.width ∧ out.valid=true ∧
        out.fields 0=frame (words d.width bits 0) ∧
        out.fields 1=frame (words d.width bits 1) ∧
        out.fields 2=frame (words d.width bits 2) ∧
        out.fields 3=frame (words d.width bits 3) ∧
        row=parsed d.width bits ∧ tail=bits.drop (4*d.width) := by
  have hsome : (readRow d.width bits).isSome=true := by simp [hread]
  have hw : 4*d.width ≤ bits.length := by
    rw [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at hsome
    exact hsome
  have he : (row,tail)=(parsed d.width bits,bits.drop (4*d.width)) :=
    Option.some.inj (hread.symm.trans (readRow_full d.width bits hw))
  obtain ⟨r,hr,hbound,_,_,hfinal⟩ := row_run d pre bits hs hp hd
  refine ⟨r,hr,hbound,{afterReads d 0 4 bits with valid:=true},hfinal hsome,
    afterReads_valid d 0 4 bits hd,afterReads_source d 0 4 bits,
    afterReads_width d 0 4 bits,?_,rfl,four_fields d bits 0,four_fields d bits 1,
    four_fields d bits 2,four_fields d bits 3,congrArg Prod.fst he,congrArg Prod.snd he⟩
  change (afterReads d 0 4 bits).pos=d.pos+8*d.width
  rw [afterReads_pos d 0 4 bits hw]
  omega

end NearCubicWires.RepairOrdinary.RecoveryRowFields
