import Proof.CaseAnalysis.RowsGateNativeBudget
import Proof.CaseAnalysis.RowsGateRawBounds

/-! Total cold gate-component execution, including every malformed codec
exit. The SAME parser and append worker retain both actual list counts for
the final source-arity guard; they are never recomputed from a declaration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateRawRun
open LocalBitMultitape RadixSemantics CanonicalBinary CloseoutWitness RecoveryRootRound
open CloseoutRowsGateCold CloseoutRowsGateColdStages CloseoutRowsGateSupport
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Components (bits : List Bool) (weights : List ℤ) (threshold : ℤ) (members : List Bool) : Prop :=
  CompetitorWitnessTriple.structural bits ∧
    decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some weights ∧
    decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some threshold ∧
    decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some members
def ExistsComponents (bits : List Bool) := ∃ weights threshold members,Components bits weights threshold members
def budget (bits : List Bool) := CloseoutRowsGateFields.budget bits+1+1000*(bits.length+2)^2+1
def Produced (compressed : Bool) (bits : List Bool) (weights : List ℤ) (threshold : ℤ)
    (members : List Bool) (out : Fin 1035 → List Bool) : Prop :=
  out 1033=frame (CloseoutRowsGateNative.word compressed (CloseoutRowsGateDecisionMeaning.fields weights)
    members (signSource bits) threshold.natAbs) ∧
  out 1018=[validity (CloseoutRowsGateDecisionMeaning.fields weights) members true weights.length] ∧
  out 368=CompareMachine.word weights.length ∧ out 861=CompareMachine.word members.length

theorem guard_iff (bits : List Bool) (fields : Fin 998 → List Bool) (hf : FieldMeaning bits fields) :
    guard (fun i => readTapeBit (install oldSlots (input bits) fields i) 0)=true ↔ ExistsComponents bits := by
  have old (i : Fin 998) : install oldSlots (input bits) fields (oldSlots i)=fields i :=
    install_slot _ old_injective _ _ _
  change (readTapeBit (install oldSlots (input bits) fields (oldSlots 147)) 0 &&
    readTapeBit (install oldSlots (input bits) fields (oldSlots 367)) 0 &&
    readTapeBit (install oldSlots (input bits) fields (oldSlots 819)) 0 &&
    readTapeBit (install oldSlots (input bits) fields (oldSlots 996)) 0)=true ↔ _
  rw [old,old,old,old,Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1]
  constructor
  · rintro ⟨⟨⟨hs,hw⟩,ht⟩,hm⟩
    obtain ⟨weights,hw⟩ := Option.isSome_iff_exists.mp hw
    obtain ⟨threshold,ht⟩ := Option.isSome_iff_exists.mp ht
    obtain ⟨members,hm⟩ := Option.isSome_iff_exists.mp hm
    exact ⟨weights,threshold,members,hs,hw,ht,hm⟩
  · rintro ⟨weights,threshold,members,hs,hw,ht,hm⟩
    exact ⟨⟨⟨hs,by rw [hw];rfl⟩,by rw [ht];rfl⟩,by rw [hm];rfl⟩

theorem positive (compressed : Bool) (bits : List Bool) (fields : Fin 998 → List Bool)
    (hf : ClockJoin.ReadyRun fieldStage.2.val (CloseoutRowsGateFields.budget bits)
      (CloseoutRowsGateFields.input bits) fields) (meaning : FieldMeaning bits fields)
    (weights : List ℤ) (threshold : ℤ) (members : List Bool) (hc : Components bits weights threshold members) :
    ∃ out,ClockJoin.ReadyRun (actualMachine compressed) (budget bits) (input bits) out ∧
      Produced compressed bits weights threshold members out := by
  obtain ⟨hs,hw,ht,hm⟩ := hc
  have keepMeaning := meaning
  obtain ⟨_,_,_,_,sign,payload,_,_,count,weightFields,_,supportFields⟩ := meaning
  let fs := CloseoutRowsGateDecisionMeaning.fields weights
  have flen : fs.length=weights.length := List.length_map _
  have hwb : ∀ field∈fs,field.2.length ≤ bits.length+2 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.fields_bound _ weights hw
  have hwc : fs.length ≤ bits.length+1 := by
    simpa only [fs,CloseoutRowsGateDecisionMeaning.fields,List.length_map,CloseoutRowsGateFields.field_length]
      using CloseoutRowsGateRawBounds.list_count _ weights hw
  have hmc : members.length ≤ bits.length+1 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.members_count _ members hm
  have htc : threshold.natAbs.bits.length ≤ bits.length+1 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.integer_bits _ threshold ht
  let bank := install oldSlots (input bits) fields
  have firstReady := hf.focus oldSlots old_injective (input bits)
    (by intro i;simp only [CloseoutRowsGateCold.input,oldSlots,Fin.addCases_left])
  have old (i : Fin 998) : bank (oldSlots i)=fields i := install_slot _ old_injective _ _ _
  obtain ⟨native,nr,nt,nflag,ncount⟩ := CloseoutRowsGateColdStages.native_run compressed fs members
    (signSource bits) threshold.natAbs (bits.length+2) hwb
  have hi : ∀ i,bank (slots i)=CloseoutRowsGateNative.framedInput fs members (signSource bits) threshold.natAbs i := by
    intro i
    rw [native_input]
    refine Fin.addCases (m := 5) (n := 37) (fun j => ?_) (fun j => ?_) i
    · simp only [slots,Fin.addCases_left,old]
      fin_cases j
      · exact (weightFields _ hw).1.trans (CloseoutRowsGateRawBounds.fields_word weights).symm
      · change fields 368=CompareMachine.word fs.length
        rw [flen];exact (weightFields _ hw).2
      · exact supportFields _ hm
      · exact sign
      · exact payload.trans (congrArg frame (CloseoutRowsGateFieldsMeaning.threshold_payload _ _ ht))
    · simp only [slots,Fin.addCases_right]
      exact fresh fields j
  have lastReady := nr.focus slots slots_injective bank hi
  have allReady := CloseoutRowsGateColdPair.joined actualFirst (actualLast compressed) guard
    _ _ (input bits) bank (install slots bank native) firstReady lastReady
    ((guard_iff bits fields keepMeaning).mpr ⟨weights,threshold,members,hs,hw,ht,hm⟩)
  have htime := CloseoutRowsGateNativeBudget.framed_bound compressed fs members (signSource bits)
    threshold.natAbs bits.length hwc hmc htc hwb
  rw [flen] at nflag ncount
  refine ⟨install slots bank native,ClockJoin.enlarge _ _ (budget bits) _ _ allReady
    (by unfold budget;omega),?_,?_,?_,?_⟩
  · exact (install_slot _ slots_injective _ _ 40).trans nt
  · exact (install_slot _ slots_injective _ _ 25).trans nflag
  · exact (install_slot _ slots_injective _ _ 1).trans ncount
  · rw [install_other _ _ _ _ (by decide)]
    change bank (oldSlots 861)=_
    rw [old,count,(CloseoutRowsBooleanVector.checks_of_typed members _ (encodeBoolList_of_decode hm).symm).2]

theorem allraw (compressed : Bool) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (actualMachine compressed) (budget bits) (input bits) out ∧
    ((∃ weights threshold members,Components bits weights threshold members ∧
        Produced compressed bits weights threshold members out) ∨
      (out 1018=[] ∧ ¬ExistsComponents bits)) := by
  obtain ⟨fields,hf,meaning⟩ := CloseoutRowsGateColdStages.field_run bits
  by_cases hc : ExistsComponents bits
  · obtain ⟨weights,threshold,members,hc⟩ := hc
    obtain ⟨out,hr,ho⟩ := positive compressed bits fields hf meaning weights threshold members hc
    exact ⟨out,hr,Or.inl ⟨weights,threshold,members,hc,ho⟩⟩
  · let bank := install oldSlots (input bits) fields
    have firstReady := hf.focus oldSlots old_injective (input bits)
      (by intro i;simp only [CloseoutRowsGateCold.input,oldSlots,Fin.addCases_left])
    have hguard : guard (fun i => readTapeBit (bank i) 0)=false := by
      apply Bool.eq_false_iff.mpr
      exact fun hg => hc ((guard_iff bits fields meaning).mp hg)
    have stopped := CloseoutRowsGateColdPair.rejected actualFirst (actualLast compressed) guard
      _ (input bits) bank firstReady hguard
    refine ⟨bank,ClockJoin.enlarge _ _ (budget bits) _ _ stopped (by unfold budget;omega),Or.inr ⟨?_,hc⟩⟩
    exact fresh fields (20 : Fin 37)

theorem budget_bound (bits : List Bool) : budget bits ≤ 4000000000000000000001002*(bits.length+2)^26 := by
  have hf := CloseoutRowsGateFields.budget_bound bits
  have h2 : (bits.length+2)^2 ≤ (bits.length+2)^26 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1 ≤ (bits.length+2)^26 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateRawRun
