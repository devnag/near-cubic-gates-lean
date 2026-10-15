import Proof.Amplification.RecoveryCertificateCountWitness

/-! The bounded physical table scanner returns the exact shared finite
valuation value, with rejection characterized on every serialized suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem reject_ne_success (s : Nat) : RepeatMachine.phaseCode s 4≠RepeatMachine.phaseCode s 3 := by
  intro h
  have he := (RepeatMachine.code s).injective h
  cases he

theorem result_acceptance (total : Nat) (x : Cursor)
    (final : Configuration 9 (Fintype.card (RepeatMachine.Control (Fintype.card (RecoveryCalls.Control sizes)))))
    (h : RepeatMachine.Result source total (RepeatMachine.iterate next total x) final) :
    final.control=RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3 ↔
      (readMany (readEntry x.data.width) total x.rest).isSome=true := by
  rw [←iterate_accepts]
  cases ha : (RepeatMachine.iterate next total x).1 with
  | false =>
    simp only [RepeatMachine.Result,ha,Bool.false_eq_true,↓reduceIte] at h
    rw [h]
    simp only [Bool.false_eq_true,iff_false]
    exact reject_ne_success _
  | true =>
    simp only [RepeatMachine.Result,ha,↓reduceIte] at h
    rw [h]
    exact iff_of_true rfl rfl

theorem result_lookup (total : Nat) (x : Cursor) (table : FiniteValuation.Table) (rest : List Bool)
    (hparse : readMany (readEntry x.data.width) total x.rest=some (table,rest))
    (hfound : x.data.found=false) (hvalue : x.data.value=false)
    (final : Configuration 9 (Fintype.card (RepeatMachine.Control (Fintype.card (RecoveryCalls.Control sizes)))))
    (h : RepeatMachine.Result source total (RepeatMachine.iterate next total x) final) :
    final.heads 5=0 ∧ final.tapes 5=[FiniteValuation.lookup table (value x.data.index)] := by
  have ha : (RepeatMachine.iterate next total x).1=true := by rw [iterate_accepts,hparse]; rfl
  simp only [RepeatMachine.Result,ha,↓reduceIte] at h
  rw [h]
  refine ⟨rfl,?_⟩
  change [(RepeatMachine.iterate next total x).2.data.value]=_
  have hv := congrArg Prod.snd (iterate_accumulator total x table rest hparse)
  rw [fold_selected] at hv
  simp only [accumulator,hfound,hvalue,Bool.false_eq_true,↓reduceIte,lookupOr_false] at hv
  exact congrArg List.singleton hv

theorem lookup_run (width total : Nat) (x : Cursor) (hx : Inv width x)
    (hfound : x.data.found=false) (hvalue : x.data.value=false) :
    ∃ r,runFrom machine (total*(budget width+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(budget width+3)+3 ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final ∧
      (r.final.control=RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3 ↔
        (readMany (readEntry x.data.width) total x.rest).isSome=true) ∧
      ∀ table rest,readMany (readEntry x.data.width) total x.rest=some (table,rest) →
        r.final.heads 5=0 ∧ r.final.tapes 5=[FiniteValuation.lookup table (value x.data.index)] := by
  obtain ⟨r,hr,ht,hf⟩ := table_run width total x hx
  exact ⟨r,hr,ht,hf,result_acceptance total x r.final hf,
    fun table rest hp=>result_lookup total x table rest hp hfound hvalue r.final hf⟩

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
