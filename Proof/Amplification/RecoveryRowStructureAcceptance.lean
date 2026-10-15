import Proof.Amplification.RecoveryRowStructureRun

/-! The streamed structural dispatch computes the original balanced-row
predicate on every parsed row. Checked prior rows are needed only for the
first-match/semantic-row correspondence already isolated in check_eq. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RecoveryRowLookupTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dataRow (d : Data) : Row := ⟨value d.kind,value d.code,value d.count,value d.state.bits⟩

theorem front_success_flags (d : Data) (h : (frontOutput d).valid=true) (i : Fin 3) :
    (frontOutput d).flags i=decide (value d.kind=i.val) := by
  have hp : (Nat.unpair (value d.code)).1=value d.kind ∧ value d.kind≤2 := by
    rw [front_output_answer,front_answer] at h
    exact of_decide_eq_true h
  have he : (prepared d).flags 0=true := by rw [prepared_flag]; simp [hp.1]
  unfold frontOutput
  rw [he]
  change (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags i=_
  rw [classified_flags,(code_values d).1,hp.1]

theorem check_front (rows : List Row) (row : Row) (h : check rows row=true) :
    (Nat.unpair row.code).1=row.kind ∧ row.kind≤2 := by
  unfold check at h
  by_cases h0 : row.kind=0
  · simp only [h0,if_pos,Bool.and_eq_true,beq_iff_eq] at h
    rw [h0,h.1]
    decide
  · simp only [if_neg h0] at h
    by_cases h1 : row.kind=1
    · simp only [h1,if_pos,Bool.and_eq_true,beq_iff_eq] at h
      exact ⟨(congrArg Prod.fst h.1).trans h1.symm,by omega⟩
    · simp only [if_neg h1] at h
      by_cases h2 : row.kind=2
      · simp only [if_pos h2] at h
        unfold childrenCheck at h
        split at h
        next _ _ _ _ =>
          simp only [Bool.and_eq_true,beq_iff_eq] at h
          exact ⟨h.1.trans h2.symm,by omega⟩
        next => contradiction
      · simp [h2] at h

theorem structure_answer (x : Children) (bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    (structureOutput x bits).base.valid=check rows (dataRow x.base) := by
  cases ha : (frontOutput x.base).valid
  · have hf : check rows (dataRow x.base)=false := by
      cases hh : check rows (dataRow x.base) with
      | false => rfl
      | true =>
        have hgood := check_front rows (dataRow x.base) hh
        have ht : (frontOutput x.base).valid=true := by
          rw [front_output_answer,front_answer]
          exact decide_eq_true hgood
        rw [ha] at ht
        contradiction
    simp only [structureOutput,ha,Bool.false_eq_true,if_false]
    exact ha.trans hf.symm
  · have hflags := front_success_flags x.base ha
    have htag : (Nat.unpair (value x.base.code)).1=value x.base.kind ∧ value x.base.kind≤2 := by
      have h := ha
      rw [front_output_answer,front_answer] at h
      exact of_decide_eq_true h
    by_cases h0 : value x.base.kind=0
    · have hf0 : (frontOutput x.base).flags 0=true := by rw [hflags 0]; simp [h0]
      simp only [structureOutput,ha,if_true,hf0]
      change decide (value (frontOutput x.base).code=0 ∧ value (frontOutput x.base).count=0)=check rows (dataRow x.base)
      rw [(front_retained x.base).2.1,(front_retained x.base).2.2.1]
      simp [check,dataRow,h0]
      rfl
    · by_cases h1 : value x.base.kind=1
      · have hf0 : (frontOutput x.base).flags 0=false := by rw [hflags 0]; simp [h0]
        have hf1 : (frontOutput x.base).flags 1=true := by rw [hflags 1]; simp [h1]
        simp only [structureOutput,ha,if_true,hf0,Bool.false_eq_true,if_false,hf1]
        change decide (value (pairWord x.base)=value (frontOutput x.base).state.bits ∧
          value (frontOutput x.base).count=1)=check rows (dataRow x.base)
        rw [(front_retained x.base).2.2.2.1,(front_retained x.base).2.2.1,pairWord,(code_values x.base).2]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq,check,dataRow,if_neg h0,if_pos h1,Bool.and_eq_true,beq_iff_eq]
        have ht : (Nat.unpair (value x.base.code)).1=1 := htag.1.trans h1
        constructor
        · intro h
          exact ⟨Prod.ext ht h.1,h.2⟩
        · intro h
          exact ⟨congrArg Prod.snd h.1,h.2⟩
      · have h2 : value x.base.kind=2 := by omega
        have hf0 : (frontOutput x.base).flags 0=false := by rw [hflags 0]; simp [h0]
        have hf1 : (frontOutput x.base).flags 1=false := by rw [hflags 1]; simp [h1]
        simp only [structureOutput,ha,if_true,hf0,hf1,Bool.false_eq_true,if_false]
        rw [children_output_answer (structureFront x) (pairWord x.base) bits rows rest hp]
        change pairAnswer rows (value (frontOutput x.base).count) (pairWord x.base)=check rows (dataRow x.base)
        rw [(front_retained x.base).2.2.1]
        have he : pairAnswer rows (value x.base.count) (pairWord x.base)=childrenCheck rows (dataRow x.base) :=
          pairAnswer_eq_childrenCheck rows (dataRow x.base) (pairWord x.base) (code_values x.base).2 (htag.1.trans h2)
        rw [he]
        simp only [check,dataRow,if_neg h0,if_neg h1,if_pos h2]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
