import Proof.MachineModel.ClosureRadixFamily
import Proof.MachineModel.NativeWidth
import Proof.MachineModel.NativeAllocation
import Proof.MachineModel.NativeMeasured
import Proof.MachineModel.NativeMaster
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.CaseAnalysis.RowsSourceMeaning
import Proof.MachineModel.BankFields
import Proof.MachineModel.BankMetadata
import Proof.MachineModel.BankCountLayout
import Proof.MachineModel.BankCountFields
import Proof.MachineModel.BankConsumer
import Proof.MachineModel.BankOptional
import Proof.MachineModel.BankCountNative
import Proof.MachineModel.BankCountConsumer
import Proof.MachineModel.BankCountRaw
import Proof.MachineModel.BankCountState
import Proof.MachineModel.BankCountInputs
import Proof.MachineModel.BankCountPositive
import Proof.MachineModel.BankCountZero
import Proof.MachineModel.BankCountBranch
import Proof.MachineModel.BankCountOptional
import Proof.MachineModel.NativeTemplate
import Proof.MachineModel.NativeTemplateReads
import Proof.MachineModel.NativeTemplateTail
import Proof.MachineModel.NativeMasterBounds
import Proof.MachineModel.NativeTemplateExact
import Proof.MachineModel.NativeBankInputs
import Proof.CaseAnalysis.RowsEstimatorBankCountZeroRetained
import Proof.CaseAnalysis.RowsEstimatorBankCountPositiveRetained
import Proof.CaseAnalysis.RowsEstimatorBankCountOptionalRetained
import Proof.CaseAnalysis.RowsEstimatorBankCycleFields
import Proof.CaseAnalysis.RowsEstimatorBankCycle
import Proof.MachineModel.NativeRound
import Proof.MachineModel.NativeState
import Proof.MachineModel.NativeFamily

/-! The complete measured-cache run produces the final p=base+Q word and
signed-field driver, retaining every shared cache/dimension field. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeWidth
open NearCubicWires.ExtIncidence.NativeWidth
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ):=P1CompactRowTupleFixedCapacity.width gs Q+Q

theorem width_guards {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ) :
    Q ≤ width gs Q ∧ P1CompactRowTupleFixedCapacity.width gs Q ≤ width gs Q:=by
  unfold width;omega

end NearCubicWires.ExtIncidence.P1CompactNativeWidth

/-! The same measured native cache supplies p and the exact coefficient
allocation F. No width or capacity word is an input to this whole run. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeAllocation
open NearCubicWires.ExtIncidence.NativeAllocation
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ):=
  P1CompactRowCommonBounds.capacity gs (gs.length*Q) (P1CompactNativeWidth.width gs Q)

end NearCubicWires.ExtIncidence.P1CompactNativeAllocation

/-! One measured cache supplies the actual p, F, and full preparation C.
Only the mode's short w and Q are additional inputs to this whole run. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMeasured
open NearCubicWires.ExtIncidence.NativeMeasured
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ):=
  P1CompactCloseoutRowsPreparationBounds.capacity n (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) w gs.length Q

end NearCubicWires.ExtIncidence.P1CompactNativeMeasured

/-! All fifteen distinct source words for native initialization are outputs
of one fixed ordinary run over the same measured cache. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMaster
open NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields : Fin 15→Fin 149:=![0,15,27,3,31,57,86,135,4,146,139,143,88,53,141]

theorem fields_injective : Function.Injective fields:=by decide

def words {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) : Fin 15→List Bool:=
  ![exactListWord gs,List.replicate (P1Radix.bits gs) true,
    List.replicate (RowCachedCoordinateBounds.inner (P1Radix.bits gs)) true,
    UnaryTemplate.tape n,
    List.replicate (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) true,
    CompareMachine.word (P1CompactNativeWidth.width gs Q+1),List.replicate (P1CompactNativeAllocation.capacity gs Q) true,
    CompareMachine.word (n+1),UnaryTemplate.tape gs.length,frame (SignedSortKey.binary w 0),
    CompareMachine.word w,CompareMachine.word 1,List.replicate w true,
    List.replicate (P1CompactNativeWidth.width gs Q) true,CompareMachine.word Q]

end NearCubicWires.ExtIncidence.P1CompactNativeMaster

/-! The complete executed outer loop uses the same strict paper load as
the signed cuts. This bounds the actual driver and loop, not an assumed
original-source packet generator or the narrower internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyBudget
open NearCubicWires.RepairOrdinary.CloseoutRowsFamilyBudget
open CloseoutRowsSourceDigits P1CompactCloseoutRowsSourceLoad P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (N Q C : ℕ) :
    P1CompactCloseoutRowsFamilyLoop.budget N Q C=N*oneCost Q C+N+3 := by
  unfold P1CompactCloseoutRowsFamilyLoop.budget P1CompactCloseoutRowsPacketOptional.cost oneCost
  ring

theorem bank_bound (S R K s N : ℕ) (hQ : K+1 ≤ S) (hload : K+R ≤ s) (hN : N ≤ 2^K) :
    CloseoutRowsCapacityDriver.budget S R+
        P1CompactCloseoutRowsFamilyLoop.budget N (K+1) (4096*S^4*2^R)  ≤ 
      4000000*2^s*(S+1)^5*(R+1) := by
  have hb:=P1CompactCloseoutRowsSourceLoad.bank_bound S R K s hQ hload
  have hm:=Nat.mul_le_mul_right (oneCost (K+1) (4096*S^4*2^R)) hN
  have hpow : 2^K ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have hS : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have hp : 1 ≤ 2^s := Nat.one_le_two_pow
  have htail : 2^s ≤ 2^s*(S+1)^5*(R+1) := by
    calc
      _ = 2^s*1*1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) (by omega)
  rw [budget_eq]
  nlinarith

theorem source_bank_bound {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (K s S : ℕ) (hQ : K+1 ≤ S) (hbank : ps.length ≤ 2^K)
    (hload : 200*load K (degree ps) B ≤ s) :
    CloseoutRowsCapacityDriver.budget S (width ps*(K+2))+
        P1CompactCloseoutRowsFamilyLoop.budget (bank ps).length (K+1)
          (4096*S^4*2^(width ps*(K+2)))  ≤ 
      4000000*2^s*(S+1)^5*(width ps*(K+2)+1) := by
  apply bank_bound S _ K s _ hQ
  · have h:=digit_margin ps K s hload
    omega
  · simpa only [bank,List.length_map] using hbank

theorem packet_length {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length ≤ 2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity n p F w gs.length Q
    (P1CompactCloseoutRowsPacketOptional.packet gs p F Q w C rows).length ≤ 110*(2*C+1)+1 := by
  dsimp only
  by_cases he : rows=[]
  · simp [P1CompactCloseoutRowsPacketOptional.packet,he]
  · have hb:=P1CompactCloseoutRowsPacketIndependent.packet_length (capacity n p F w gs.length Q)
      (P1CompactCloseoutRowsPacketPolynomial.data gs p F Q w (capacity n p F w gs.length Q) rows [])
      (P1CompactCloseoutRowsPacketPolynomial.data_bound gs p F Q w rows [] hl hw hF)
    simpa only [P1CompactCloseoutRowsPacketOptional.packet,he,↓reduceIte,List.length_cons] using Nat.add_le_add_right hb 1

theorem stream_length {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w : ℕ) (bank : List (List (List Bool)))
    (hl : ∀ rows∈bank,∀ row∈rows,row.length=gs.length)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity n p F w gs.length Q
    (P1CompactCloseoutRowsFamilyLoop.stream gs p F Q w C bank).length ≤ bank.length*(110*(2*C+1)+1) := by
  dsimp only
  induction bank with
  | nil => simp [P1CompactCloseoutRowsFamilyLoop.stream]
  | cons rows bank ih =>
    have hb:=packet_length gs p F Q w rows (hl rows (by simp)) (hw rows (by simp)) hF
    have ht:=ih (fun rs hrs=>hl rs (by simp [hrs])) (fun rs hrs=>hw rs (by simp [hrs]))
    simp only [P1CompactCloseoutRowsFamilyLoop.stream,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyBudget

/-! The actual canonical support becomes the existing native incidence ABI.
Only repeated variables inside one conjunction are collapsed; distinct
monomial occurrences, including equal resulting masks, remain separate. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceMeaning
open NearCubicWires.RepairOrdinary.CloseoutRowsSourceMeaning
open SupplierPrinter CloseoutRowsSourceDigits P1CompactCloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem positions_mem (bits : List Bool) (j i : ℕ) :
    i∈RowMaskMeaning.positions j bits ↔
      ∃ k : Fin bits.length,i=j+k.val ∧ bits.get k=true := by
  induction bits generalizing j with
  | nil => simp [RowMaskMeaning.positions]
  | cons b bs ih =>
    have ha (k : ℕ) : j+1+k=j+(k+1) := by omega
    cases b <;> simp [RowMaskMeaning.positions,ih,Fin.exists_fin_succ,ha]

theorem mask_one_mem {B : ℕ} (f : Fin B→Bool) (i : Fin B) :
    i∈P1CompactRowTupleCommonEquation.one B (List.ofFn f) ↔ f i=true := by
  have hlen : (List.ofFn f).length ≤ B := by simp
  rw [P1CompactRowTupleCommonEquation.one,dif_pos hlen]
  have hv:=RowMaskMeaning.typed_values B 0 (List.ofFn f) (by simp)
  have he : i∈RowMaskMeaning.typed B 0 (List.ofFn f) (by simp) ↔
      i.val∈RowMaskMeaning.positions 0 (List.ofFn f) := by
    rw [←hv]
    constructor
    · intro hi; exact List.mem_map.mpr ⟨i,hi,rfl⟩
    · intro hi
      obtain ⟨k,hk,hki⟩ := List.mem_map.mp hi
      exact (Fin.ext hki) ▸ hk
  rw [he,positions_mem]
  constructor
  · rintro ⟨k,hk,hf⟩
    have hik : k.val=i.val := by omega
    have he : (⟨k.val,by simpa using k.isLt⟩ : Fin B)=i := Fin.ext hik
    simpa only [List.get_eq_getElem,List.getElem_ofFn,he] using hf
  · intro hf
    refine ⟨⟨i.val,by simp⟩,by simp,?_⟩
    simpa using hf

theorem mask_all {B : ℕ} (m : List (Fin B)) (f : Fin B→Bool) :
    (P1CompactRowTupleCommonEquation.one B (List.ofFn (fun i=>decide (i∈m)))).all f=m.all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,mask_one_mem,decide_eq_true_eq]

theorem monomial_value {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    {R C : Type} (holds : Equation l r→R→C→Bool)
    (m : List (Fin gs.length)) (row : R) (column : C) :
    exactMonomialValue holds
      (monomial gs (List.ofFn (fun i=>decide (i∈m)))) row column=
      exactMonomialValue (fun i=>holds (coordinates (P1CompactRowCachedEquation.equation gs[i.val]))) m row column := by
  simp only [exactMonomialValue,monomial,P1CompactRowCachedEquation.equations,List.all_map]
  exact mask_all m _

theorem polynomial_value {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (P : MvPolynomial (Fin gs.length) (ZMod 2))
    {R C : Type} (holds : Equation l r→R→C→Bool) (row : R) (column : C) :
    exactPolynomialValue holds (polynomial gs (rows P)) row column=
      decide (MvPolynomial.aeval
        (fun i=>((holds (coordinates (P1CompactRowCachedEquation.equation gs[i.val])) row column).toNat : ZMod 2)) P=1) := by
  rw [←exactPolynomialValue_compiled
    (fun i=>holds (coordinates (P1CompactRowCachedEquation.equation gs[i.val]))) P row column]
  unfold exactPolynomialValue polynomialOccurrenceCount
  congr 2
  simp only [polynomial,rows,List.map_map,Function.comp_def,monomial_value]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceMeaning

/-! Exact existing native-bank projections consumed by the physical incidence
dock. These are field identities, not producers for the remaining metadata. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankFields
open NearCubicWires.ExtIncidence.BankFields
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).heads=
      P1CompactCloseoutRowsBankFields.heads out :=
  P1CompactCloseoutRowsBankFields.polynomial_heads gs p F Q w C rows out

theorem table {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 36=
      ZeroPadding.pad C rows.flatten := by
  change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0 rows.flatten))=_
  rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]

theorem template {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 38=
      ZeroPadding.pad C (UnaryTemplate.tape gs.length) := by
  change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0 (UnaryTemplate.tape gs.length)))=_
  rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]

theorem driver {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 104=List.replicate C true := by
  change ZeroPadding.pad C (List.replicate C true)=_
  simp [ZeroPadding.pad]

theorem log {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 105=List.replicate (C+1) false := by
  change ZeroPadding.pad (C+1) (List.replicate (C+1) false)=_
  simp [ZeroPadding.pad]

theorem table_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w : ℕ)
    (ms : List (List (Fin gs.length))) (hM : ms.length ≤ 2^w) :
    (rawRows ms).flatten.length ≤ P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q := by
  have hc:=P1CompactCloseoutRowsPreparationFits.cursor_fits n p F w gs.length Q ms.length 1 hM (by omega)
  rw [Padded.raw_rows_length]
  unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
  nlinarith

end NearCubicWires.ExtIncidence.P1CompactBankFields

/-! The actual incidence table and two copies of its last row index are the
only row-dependent native inputs. Common false backing erases the dependence
of the two scratch extents on the number of monomial occurrences. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankMetadata
open NearCubicWires.ExtIncidence.BankMetadata
open LocalBitMultitape RepairOrdinary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem last_index {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 52=
      ZeroPadding.pad C (frame (SignedSortKey.binary w (rows.length-1))) ∧
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 107=
      ZeroPadding.pad C (frame (SignedSortKey.binary w (rows.length-1))) := by
  constructor
  · change ZeroPadding.pad C (ZeroPadding.pad C _) = _
    exact MatrixBucketRootPower.pad_pad C C _ le_rfl
  · rfl

theorem cursor_other {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 48)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47) :
    P1CompactRowTupleCursorLayout.data gs 0 p F w M 1 rows [] out 0 [] i=
      P1CompactRowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i := by
  revert h36 h43 h47
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · intro _ _ _
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left]
  · intro h36 h43 h47
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_right]
    fin_cases j <;> simp_all

theorem raw_other {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 103)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47) (h52 : i.val≠52) :
    (P1CompactCloseoutRowsLoopLayout.rawInput gs p F w 0 rows out).tapes i=
      (P1CompactCloseoutRowsLoopLayout.rawInput gs p F w 0 [] out).tapes i := by
  revert h36 h43 h47 h52
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · refine Fin.addCases (m:=48) (n:=1) (fun c=>?_) (fun c=>?_) b
      · intro h36 h43 h47 _
        have hn : ((c.castAdd 1).castAdd 40 : Fin 89)≠48 := by
          intro he
          have hv : c.val=48:=congrArg (fun x : Fin 89=>x.val) he
          exact Nat.ne_of_lt c.isLt hv
        simp only [P1CompactCloseoutRowsLoopLayout.rawInput,P1CompactCloseoutRowsComputedCuts.input,
          Fin.addCases_left,Function.update_of_ne hn,P1CompactCloseoutRowsComputedCuts.body,
          P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,P1CompactCloseoutRowsEnumeratedCuts.core]
        apply congrArg
        exact cursor_other gs p F w rows.length rows out c h36 h43 h47
      · intro _ _ _ _
        simp only [P1CompactCloseoutRowsLoopLayout.rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
        fin_cases c
        change Function.update (P1CompactCloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 rows out).tapes (48 : Fin 89) [] 48=
          Function.update (P1CompactCloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes (48 : Fin 89) [] 48
        simp only [Function.update_self]
    · intro _ _ _ h52
      have hn : (b.natAdd 49 : Fin 89)≠48 := by
        intro he
        have hv : 49+b.val=48:=congrArg (fun x : Fin 89=>x.val) he
        omega
      simp only [P1CompactCloseoutRowsLoopLayout.rawInput,P1CompactCloseoutRowsComputedCuts.input,
        Fin.addCases_left,Function.update_of_ne hn,P1CompactCloseoutRowsComputedCuts.body,
        P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
      have h3 : b≠3 := by intro he;subst b;exact h52 rfl
      simp only [P1CompactRowTupleEnumeratedEquations.extra,h3,↓reduceIte]
  · intro _ _ _ _
    simp only [P1CompactCloseoutRowsLoopLayout.rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]

theorem other {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 113)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47)
    (h52 : i.val≠52) (h107 : i.val≠107) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes i := by
  apply congrArg (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C i))
  simp only [P1CompactCloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    P1CompactCloseoutRowsDegreeLoop.entry]
  revert h36 h43 h47 h52 h107
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
    · intro h36 h43 h47 h52 _
      simp only [Fin.addCases_left,P1CompactCloseoutRowsLoopLayout.inputTapes]
      apply congrArg
      exact raw_other gs p F w rows out b h36 h43 h47 h52
    · intro _ _ _ _ h107
      simp only [Fin.addCases_left,P1CompactCloseoutRowsLoopLayout.inputTapes,Fin.addCases_right,
        P1CompactCloseoutRowsLoopLayout.extra,P1CompactCloseoutRowsLoopLayout.templates]
      fin_cases b <;> simp_all [Fin.addCases]
  · intro _ _ _ _ _
    simp only [Fin.addCases_right]

theorem false_backing (C k : ℕ) (hk : k≤C) :
    ZeroPadding.pad C (List.replicate k false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hk]

theorem scratch {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 43=List.replicate C false ∧
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 47=List.replicate C false := by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q
  have b43:=P1CompactCloseoutRowsBankCapacity.raw_bound gs p F Q w 0 rows out hl hw (Nat.zero_le Q) hF 43 (by decide)
  have b47:=P1CompactCloseoutRowsBankCapacity.raw_bound gs p F Q w 0 rows out hl hw (Nat.zero_le Q) hF 47 (by decide)
  change (ZeroPadding.pad 0 (List.replicate (RowMaskLookupReusable.capacity gs.length w rows.length) false)).length≤C at b43
  change (ZeroPadding.pad 0 (List.replicate (RowTupleCursorReady.capacity gs.length w rows.length 1) false)).length≤C at b47
  rw [ZeroPadding.pad_zero,List.length_replicate] at b43 b47
  constructor
  · change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (List.replicate (RowMaskLookupReusable.capacity gs.length w rows.length) false)))=_
    rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
    exact false_backing C _ b43
  · change ZeroPadding.pad C (ZeroPadding.pad C (ZeroPadding.pad 0
      (List.replicate (RowTupleCursorReady.capacity gs.length w rows.length 1) false)))=_
    rw [ZeroPadding.pad_zero,MatrixBucketRootPower.pad_pad C C _ le_rfl]
    exact false_backing C _ b47

theorem row_independent {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (i : Fin 113) (h36 : i≠36) (h52 : i≠52) (h107 : i≠107) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes i := by
  dsimp only
  by_cases h43 : i=43
  · subst i
    exact (scratch gs p F Q w rows out hl hw hF).1.trans
      (scratch gs p F Q w [] out (by simp) (by simp) hF).1.symm
  by_cases h47 : i=47
  · subst i
    exact (scratch gs p F Q w rows out hl hw hF).2.trans
      (scratch gs p F Q w [] out (by simp) (by simp) hF).2.symm
  exact other gs p F Q w _ rows out i
    (fun h=>h36 (Fin.ext h)) (fun h=>h43 (Fin.ext h)) (fun h=>h47 (Fin.ext h))
    (fun h=>h52 (Fin.ext h)) (fun h=>h107 (Fin.ext h))

end NearCubicWires.ExtIncidence.P1CompactBankMetadata

/-! Dock the actual count converter into the existing native bank. Shared
ports are count115, width109, fields52/107 and driver104/log105. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 18→Fin 128:=
  ![115,116,117,118,119,120,121,122,123,124,109,52,125,126,127,107,104,105]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots CountIndexClean.machine
def changed (A : Fin 128→List Bool) (C w M : ℕ):=
  Function.update (Function.update (Function.update A 115 (List.replicate C false))
    52 (ZeroPadding.pad C (frame (binary w (M-1)))))
    107 (ZeroPadding.pad C (frame (binary w (M-1))))

theorem count_run (C w M : ℕ) (hM : 0<M) (hw : M<2^w)
    (hC : CountIndex.budget w M+1≤C) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (slots j)=0)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w M j) :
    ∃ r,runFrom machine (CountIndexClean.budget C w M) ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=H ∧
      r.final.tapes=install slots A (CountIndexClean.output C w M) ∧
      r.steps≤CountIndexClean.budget C w M :=
  (CountIndexClean.ready C w M hM hw hC).focus_at slots slots_injective H A ha hh

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Exact field replacement by the count-conversion run: private scratch is
restored, and only count115 and the two native index words change. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_same (C w M : ℕ) (j : Fin 18) (h0 : j≠0) (h11 : j≠11) (h15 : j≠15) :
    CountIndexClean.output C w M j=CountIndexCopy.input C w M j := by
  fin_cases j <;> simp_all [CountIndexClean.output,CountIndexCopy.input,CountIndexCopy.extra,
    CountIndex.padded,CountIndex.input,Fin.addCases,ZeroPadding.pad]

theorem replaced (A : Fin 128→List Bool) (C w M : ℕ)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w M j) :
    install slots A (CountIndexClean.output C w M)=changed A C w M := by
  apply HierarchyAllocation.install_eq slots slots_injective
  · intro j
    by_cases h0 : j=0
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    by_cases h11 : j=11
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    by_cases h15 : j=15
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    have n115 : slots j≠115:=by
      intro he
      exact h0 (slots_injective (show slots j=slots 0 from he))
    have n52 : slots j≠52:=by
      intro he
      exact h11 (slots_injective (show slots j=slots 11 from he))
    have n107 : slots j≠107:=by
      intro he
      exact h15 (slots_injective (show slots j=slots 15 from he))
    simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]
    exact (ha j).trans (output_same C w M j h0 h11 h15).symm
  · intro i hi
    have n115 : i≠115:=Ne.symm (hi 0)
    have n52 : i≠52:=Ne.symm (hi 11)
    have n107 : i≠107:=Ne.symm (hi 15)
    simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Physical raw incidence production, paid cursor return, and the EXISTING
polynomial consumer. All other native fields are explicit caller-produced
inputs. The separate zero-polynomial branch is not supplied here. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankConsumer
open NearCubicWires.ExtIncidence.BankConsumer
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 116 := i.castAdd 3
theorem old_injective : Function.Injective old := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 116=>k.val) h)
theorem old_ne (i : Fin 113) (k : Fin 116) (hk : 113 ≤ k.val) : old i≠k := by
  intro he
  have hv:=congrArg Fin.val he
  change i.val=k.val at hv
  omega

noncomputable def consumer:=RecoveryFocus.machine old P1CompactCloseoutRowsBankPolynomial.machine
noncomputable def machine:=Composition.machine BankExecution.machine consumer
def budget (B C Q : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+P1CompactCloseoutRowsBankPolynomial.budget Q C

theorem count_bound (n p F w B Q M : ℕ) (hM : M ≤ 2^w) :
    M ≤ P1CompactCloseoutRowsPreparationBounds.capacity n p F w B Q := by
  have hc:=P1CompactCloseoutRowsPreparationFits.cursor_fits n p F w B Q M 1 hM (by omega)
  unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
  nlinarith

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hM : 0 < ms.length) (hw : ms.length < 2^w) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 116 → ℕ) (A : Fin 116 → List Bool)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hother : ∀ i,i≠36 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) (rawRows ms) out).tapes i)
    (hext : H 113=pre.length ∧ H 114=0 ∧ H 115=0)
    (hsource : A 113=pre++stream (rawIndices ms)++tail)
    (hblank : A 36=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hscratch : A 114=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hcount : A 115=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom machine (budget gs.length C Q (rawIndices ms)) ⟨machine.start,H,A⟩=some result ∧
      result.steps ≤ budget gs.length C Q (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=ZeroPadding.pad C (List.replicate ms.length true) := by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  let pos:=pre.length+(stream (rawIndices ms)).length
  let nextH:=BankExecution.changedHeads H pos 0 0
  let nextA:=BankExecution.changedTapes A C (rawRows ms).flatten ms.length
  have hB:gs.length ≤ C:=by
    have hs:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
    unfold P1CompactCloseoutRowsPreparationBounds.scale at hs
    dsimp only [C]
    omega
  have hh:∀ j,H (BankExecution.slots j)=Padded.heads pre.length 0 0 j:=by
    intro j;fin_cases j
    · exact hext.1
    · exact hheads 38
    · exact hext.2.1
    · exact hheads 36
    · exact hext.2.2
  have ht:∀ j,A (BankExecution.slots j)=Padded.tapes C gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j:=by
    intro j;fin_cases j
    · exact hsource
    · exact (hother 38 (by decide)).trans (P1CompactBankFields.template gs p F Q w C (rawRows ms) out)
    · exact hscratch
    · change A 36=ZeroPadding.pad C []
      simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hblank
    · change A 115=ZeroPadding.pad C []
      simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hcount
  have first:=BankExecution.raw_run ms C hB pre tail H A hh ht
    (P1CompactBankFields.table_bound gs p F Q w ms hw.le) (count_bound (l+r) p F w gs.length Q ms.length hw.le)
    (hheads 104) (hheads 105)
    ((hother 104 (by decide)).trans (P1CompactBankFields.driver gs p F Q w C (rawRows ms) out))
    ((hother 105 (by decide)).trans (P1CompactBankFields.log gs p F Q w C (rawRows ms) out))
  have length_rows:(rawRows ms).length=ms.length:=by simp only [rawRows,List.length_map]
  have row_length:∀ row∈rawRows ms,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  obtain ⟨base,hbase,bh,bo,bc,bs⟩:=P1CompactCloseoutRowsBankPolynomial.polynomial_run gs p F Q w (rawRows ms) out
    row_length (by simpa only [length_rows] using hM) (by simpa only [length_rows] using hw) hQp hp hF
  have bankH:∀ i,nextH (old i)=(P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C (rawRows ms) out).heads i:=by
    intro i
    rw [P1CompactBankFields.heads]
    by_cases h36:i=36
    · subst i;simp [nextH,BankExecution.changedHeads,old,P1CompactCloseoutRowsBankFields.heads,P1CompactCloseoutRowsBankFields.raised]
    · have n36:old i≠36:=by intro he;exact h36 (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simpa only [nextH,BankExecution.changedHeads,Function.update_of_ne (old_ne i 115 (by decide)),
        Function.update_of_ne n36,Function.update_of_ne (old_ne i 113 (by decide))] using hheads i
  have bankT:∀ i,nextA (old i)=(P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C (rawRows ms) out).tapes i:=by
    intro i
    by_cases h36:i=36
    · subst i
      change BankExecution.changedTapes A C (rawRows ms).flatten ms.length 36=_
      rw [BankExecution.changedTapes,Function.update_of_ne (by decide : (36 : Fin 116)≠115),Function.update_self]
      exact (P1CompactBankFields.table gs p F Q w C (rawRows ms) out).symm
    · have n36:old i≠36:=by intro he;exact h36 (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simpa only [nextA,BankExecution.changedTapes,Function.update_of_ne (old_ne i 115 (by decide)),
        Function.update_of_ne n36] using hother i h36
  obtain ⟨last,hl,_lf,ls,lh,lt,keep⟩:=RecoveryFocus.dock old old_injective
    P1CompactCloseoutRowsBankPolynomial.machine _ nextH nextA _ bankH bankT base hbase
  obtain ⟨result,hr,rh,rt,rs⟩:=PCPOuter.exact_then first last hl
  refine ⟨result,hr,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rs,ls]
    exact Nat.add_le_add_left bs _
  · intro i;rw [rh,lh,bh]
  · intro i;rw [rt,lt,CloseoutRowsBankPorts.erased_store C _ base.final.tapes bo bc]
  · rw [rh,(keep 113 (fun i=>old_ne i 113 (by decide))).1]
    simp only [nextH,BankExecution.changedHeads,Function.update_of_ne (by decide : (113 : Fin 116)≠115),
      Function.update_of_ne (by decide : (113 : Fin 116)≠36),Function.update_self,pos]
  · rw [rt,(keep 113 (fun i=>old_ne i 113 (by decide))).2]
    simp only [nextA,BankExecution.changedTapes,Function.update_of_ne (by decide : (113 : Fin 116)≠115),
      Function.update_of_ne (by decide : (113 : Fin 116)≠36)]
  · rw [rh,(keep 115 (fun i=>old_ne i 115 (by decide))).1]
    exact Function.update_self _ _ _
  · rw [rt,(keep 115 (fun i=>old_ne i 115 (by decide))).2]
    exact Function.update_self _ _ _

end NearCubicWires.ExtIncidence.P1CompactBankConsumer

/-! One actual raw stream runs through the positive or empty bank entry.
The caller supplies the existing native ports; no separate marker, count pass
or serialized polynomial packet is required. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankOptional
open NearCubicWires.ExtIncidence.BankOptional
open LocalBitMultitape RepairOrdinary P1CompactBankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def budget (B C Q : ℕ) (ms : List (List ℕ)):=
  max (P1CompactBankConsumer.budget B C Q ms) (BankZero.budget B C)+2

theorem entry_size {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl:∀ row∈rows,row.length=gs.length) (hw:rows.length ≤ 2^w)
    (hF:P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 113) (hi:i≠31) (hlog:i≠105) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    ((P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i).length ≤ C:=by
  dsimp only
  change (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities _ i)
    ((P1CompactCloseoutRowsPolynomial.input gs p F Q w _ rows out).tapes i)).length ≤ _
  rw [ZeroPadding.pad_length]
  refine max_le (by simp [P1CompactCloseoutRowsBankCapacity.capacities,hi,hlog]) ?_
  exact P1CompactCloseoutRowsBankCapacity.loop_bound _ gs 0 p F Q w 0 rows out hl hw (Nat.zero_le _) hF i hi hlog

theorem entry_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 31=out:=by
  change ZeroPadding.pad 0 (P1CompactCloseoutRowsLoopLayout.inputTapes gs p F w 0 C rows out 31)=out
  rw [ZeroPadding.pad_zero]
  exact (P1CompactCloseoutRowsPolynomial.output_fields gs p F w 0 C rows out).1

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hw:ms.length < 2^w) (hQp:Q ≤ p)
    (hp:P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF:P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (hheads:∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hother:∀ i,i≠36 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) (rawRows ms) out).tapes i)
    (hext:H 113=pre.length ∧ H 114=0 ∧ H 115=0)
    (hsource:A 113=pre++stream (rawIndices ms)++tail)
    (hblank:A 36=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hscratch:A 114=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hcount:A 115=List.replicate (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom BankBranch.machine (budget gs.length C Q (rawIndices ms))
      ⟨BankBranch.machine.start,H,A⟩=some result ∧
      result.steps ≤ budget gs.length C Q (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=ZeroPadding.pad C (List.replicate ms.length true):=by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  have marker:readTapeBit (A 113) (H 113)=decide (0 < ms.length):=by
    rw [hsource,hext.1,BankBranch.stream_marker]
    simp only [rawIndices,List.length_map]
  by_cases hempty:ms=[]
  · subst ms
    have hB:gs.length ≤ C:=by
      have h:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
      unfold P1CompactCloseoutRowsPreparationBounds.scale at h
      dsimp only [C];omega
    have hh:∀ j,H (BankExecution.slots j)=Padded.heads pre.length 0 0 j:=by
      intro j;fin_cases j
      · exact hext.1
      · exact hheads 38
      · exact hext.2.1
      · exact hheads 36
      · exact hext.2.2
    have ht:∀ j,A (BankExecution.slots j)=Padded.tapes C gs.length (pre++[false]++tail) [] 0 j:=by
      intro j;fin_cases j
      · exact hsource
      · exact (hother 38 (by decide)).trans (P1CompactBankFields.template gs p F Q w C [] out)
      · exact hscratch
      · change A 36=ZeroPadding.pad C []
        simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hblank
      · change A 115=ZeroPadding.pad C (List.replicate 0 true)
        simpa only [List.replicate_zero,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hcount
    have hsize:∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C:=by
      intro i hi hlog
      by_cases h36:i=36
      · subst i;rw [show old 36=(36 : Fin 116) from rfl,hblank,List.length_replicate]
      · rw [hother i h36]
        exact entry_size gs p F Q w [] out (by simp) (by simp) hF i hi hlog
    obtain ⟨base,hbase,_,bh,bt,bs,ba,bch,bct⟩:=BankZero.zero_run gs.length C hB out pre tail H A hh ht
      hheads hsize ((hother 31 (by decide)).trans (entry_out gs p F Q w C [] out))
      ((hother 104 (by decide)).trans (P1CompactBankFields.driver gs p F Q w C [] out))
      ((hother 105 (by decide)).trans (P1CompactBankFields.log gs p F Q w C [] out))
    obtain ⟨z,hz,zs,zh,zt⟩:=BankBranch.dispatch_run P1CompactBankConsumer.machine BankZero.machine 2 (Or.inr rfl)
      _ H A base (by rw [marker];rfl) hbase
    have hb:BankZero.budget gs.length C+2 ≤ budget gs.length C Q (rawIndices (B:=gs.length) []):=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    have more:=runFrom_moreFuel BankBranch.machine _
      (budget gs.length C Q (rawIndices (B:=gs.length) [])-(BankZero.budget gs.length C+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨z,more,zs.trans hb,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zh,zt,rawRows,rawIndices,List.map_nil,P1CompactCloseoutRowsPacketOptional.cuts_nil,
      List.flatMap_nil,List.append_nil,stream_nil,List.length_singleton,List.length_nil,
      List.replicate_zero,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    · exact bh
    · exact bt
    · exact bs
    · exact ba
    · exact bch
    · exact bct
  · obtain ⟨base,hbase,_,bh,bt,bs,ba,bch,bct⟩:=P1CompactBankConsumer.polynomial_run gs ms p F Q w out pre tail
      (List.length_pos_iff.mpr hempty) hw hQp hp hF H A hheads hother hext hsource hblank hscratch hcount
    obtain ⟨z,hz,zs,zh,zt⟩:=BankBranch.dispatch_run P1CompactBankConsumer.machine BankZero.machine 1 (Or.inl rfl)
      _ H A base (by rw [marker,if_pos (by simpa using List.length_pos_iff.mpr hempty)]) hbase
    have hb:P1CompactBankConsumer.budget gs.length C Q (rawIndices ms)+2 ≤ budget gs.length C Q (rawIndices ms):=
      Nat.add_le_add_right (Nat.le_max_left _ _) 2
    have more:=runFrom_moreFuel BankBranch.machine _
      (budget gs.length C Q (rawIndices ms)-(P1CompactBankConsumer.budget gs.length C Q (rawIndices ms)+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨z,more,zs.trans hb,by rw [zh];exact bh,by rw [zt];exact bt,
      by rw [zh];exact bs,by rw [zt];exact ba,by rw [zh];exact bch,by rw [zt];exact bct⟩

end
end NearCubicWires.ExtIncidence.P1CompactBankOptional

/-! Discharge the native worker's row-dependent input from the actual table
and counted index. Every other native input is the same empty-row template. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 128:=i.castAdd 15
theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)

theorem width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 109=
      ZeroPadding.pad C (List.replicate w true):=rfl

theorem native_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (A : Fin 128→List Bool)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q) [] out).tapes i)
    (ht : A 36=ZeroPadding.pad (P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q) rows.flatten) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    ∀ i,changed A C w rows.length (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i := by
  dsimp only
  intro i
  by_cases h52 : i=52
  · subst i
    change ZeroPadding.pad _ (frame (RepairOrdinary.SignedSortKey.binary w (rows.length-1)))=_
    exact (P1CompactBankMetadata.last_index gs p F Q w _ rows out).1.symm
  by_cases h107 : i=107
  · subst i
    change ZeroPadding.pad _ (frame (RepairOrdinary.SignedSortKey.binary w (rows.length-1)))=_
    exact (P1CompactBankMetadata.last_index gs p F Q w _ rows out).2.symm
  have n52 : old i≠52:=fun h=>h52 (Fin.ext (congrArg (fun x : Fin 128=>x.val) h))
  have n107 : old i≠107:=fun h=>h107 (Fin.ext (congrArg (fun x : Fin 128=>x.val) h))
  have n115 : old i≠115:=by
    intro h
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) h
    have hi:=i.isLt
    omega
  simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]
  by_cases h36 : i=36
  · subst i
    exact ht.trans (P1CompactBankFields.table gs p F Q w _ rows out).symm
  exact (hbase i h36 h52 h107).trans
    (P1CompactBankMetadata.row_independent gs p F Q w rows out hl hw hF i h36 h52 h107).symm

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Execute count metadata and the original polynomial worker on the same
actual incidence table. No last-index word is supplied to this consumer. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def consumer:=RecoveryFocus.machine old P1CompactCloseoutRowsBankPolynomial.machine
noncomputable def counted:=Composition.machine machine consumer
def budget (C Q w M : ℕ):=CountIndexClean.budget C w M+1+P1CompactCloseoutRowsBankPolynomial.budget Q C

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (p F Q w : ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length) (hw : rows.length<2^w)
    (hQ : 1≤Q) (hQp : Q≤p) (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (slots j)=0)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w rows.length j)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (ht : A 36=ZeroPadding.pad (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) rows.flatten) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom counted (budget C Q w rows.length) ⟨counted.start,H,A⟩=some result ∧
      result.steps≤budget C Q w rows.length ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      (∀ i,(∀ j,old j≠i) → result.final.heads i=H i ∧
        result.final.tapes i=changed A C w rows.length i) := by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  obtain ⟨a,ar,ah,atape,ast⟩:=count_run C w rows.length hM hw
    (CountIndex.fits (l+r) p F w gs.length Q rows.length hQ hw.le) H A hh ha
  have at' : a.final.tapes=changed A C w rows.length:=atape.trans (replaced A C w rows.length ha)
  obtain ⟨b,br,bh,bo,bc,bst⟩:=P1CompactCloseoutRowsBankPolynomial.polynomial_run gs p F Q w rows out hl hM hw hQp hp hF
  have nh : ∀ i,H (old i)=(P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out).heads i:=by
    intro i
    rw [P1CompactBankFields.heads]
    exact hheads i
  have nt:=native_tapes gs p F Q w rows out hl hw.le hF A hbase ht
  obtain ⟨last,lastRun,_lf,_ls,lh,lt,keep⟩:=RecoveryFocus.dock old old_injective
    P1CompactCloseoutRowsBankPolynomial.machine _ H (changed A C w rows.length) _ nh nt b br
  have restart : Composition.restart a.final consumer.start=
      ⟨consumer.start,H,changed A C w rows.length⟩:=by
    apply configuration_ext
    · rfl
    · exact ah
    · exact at'
  change runFrom consumer (P1CompactCloseoutRowsBankPolynomial.budget Q C)
    ⟨consumer.start,H,changed A C w rows.length⟩=some last at lastRun
  rw [←restart] at lastRun
  have whole:=Composition.run_join machine consumer _ _ _ a last ar lastRun
  let result:=Composition.joinedReceipt a last
  refine ⟨result,whole,runFrom_steps_le counted _ _ result whole,?_,?_,?_⟩
  · intro i
    exact (lh i).trans (congrFun bh i)
  · intro i
    exact (lt i).trans (congrFun (CloseoutRowsBankPorts.erased_store C _ b.final.tapes bo bc) i)
  · intro i hi
    exact keep i hi

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The original incidence printer runs in the count-metadata bank. Its
actual count and table are retained; the twelve new private tapes are idle. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawOld (i : Fin 116) : Fin 128:=i.castAdd 12
theorem rawOld_injective : Function.Injective rawOld:=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
noncomputable def raw:=RecoveryFocus.machine rawOld BankExecution.machine
noncomputable def afterHeads (H : Fin 128→ℕ) (pos : ℕ):=
  dockH rawOld H (BankExecution.changedHeads (H ∘ rawOld) pos 0 0)
noncomputable def afterTapes (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ):=
  install rawOld A (BankExecution.changedTapes (A ∘ rawOld) C table M)

theorem raw_run {B : ℕ} (ms : List (List (Fin B))) (C : ℕ) (hB : B≤C)
    (pre tail : List Bool) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (rawOld (BankExecution.slots j))=
      Padded.tapes C B (pre++stream (rawIndices ms)++tail) [] 0 j)
    (hsize : (rawRows ms).flatten.length≤C) (hcount : ms.length≤C)
    (hdh : H 104=0) (hlh : H 105=0)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false) :
    Step raw (BankExecution.budget B C (rawIndices ms)) H A
      (afterHeads H (pre.length+(stream (rawIndices ms)).length))
      (afterTapes A C (rawRows ms).flatten ms.length) := by
  have base:=BankExecution.raw_run ms C hB pre tail (H ∘ rawOld) (A ∘ rawOld)
    hh ht hsize hcount hdh hlh hd hl
  obtain ⟨b,br,bh,bt,bs⟩:=base
  exact (Step.of_run br bh bt).dock rawOld rawOld_injective H A
    (by intro i;rfl) (by intro i;rfl)

theorem after_heads_old (H : Fin 128→ℕ) (pos : ℕ) (i : Fin 116) :
    afterHeads H pos (rawOld i)=BankExecution.changedHeads (H ∘ rawOld) pos 0 0 i:=
  dockH_slot rawOld rawOld_injective H _ i
theorem after_tapes_old (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ) (i : Fin 116) :
    afterTapes A C table M (rawOld i)=BankExecution.changedTapes (A ∘ rawOld) C table M i:=
  install_slot rawOld rawOld_injective A _ i
theorem rawOld_avoids (i : Fin 128) (hi : 116 ≤ i.val) : ∀ j,rawOld j≠i:=by
  intro j he
  have hv : j.val=i.val:=congrArg (fun x : Fin 128=>x.val) he
  have hj:=j.isLt
  omega
theorem after_heads_extra (H : Fin 128→ℕ) (pos : ℕ) (i : Fin 128) (hi : 116 ≤ i.val) :
    afterHeads H pos i=H i:=dockH_other rawOld H _ i (rawOld_avoids i hi)
theorem after_tapes_extra (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ)
    (i : Fin 128) (hi : 116 ≤ i.val) : afterTapes A C table M i=A i:=
  install_other rawOld A _ i (rawOld_avoids i hi)

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Exact ambient state after the original raw incidence pass. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_tapes_eq (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ) :
    afterTapes A C table M=Function.update (Function.update A 36 (ZeroPadding.pad C table))
      115 (ZeroPadding.pad C (List.replicate M true)):=by
  funext i
  by_cases inside : ∃ j,rawOld j=i
  · obtain ⟨j,rfl⟩:=inside
    rw [after_tapes_old]
    simp only [BankExecution.changedTapes,Function.update_apply,Function.comp_apply,
      rawOld,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have outside : ∀ j,rawOld j≠i:=by simpa only [not_exists] using inside
    have n36 : i≠36:=Ne.symm (outside 36)
    have n115 : i≠115:=Ne.symm (outside 115)
    rw [afterTapes,install_other rawOld A _ i outside,
      Function.update_of_ne n115,Function.update_of_ne n36]

theorem after_heads_eq (H : Fin 128→ℕ) (pos : ℕ) :
    afterHeads H pos=Function.update (Function.update (Function.update H 113 pos) 36 0) 115 0:=by
  funext i
  by_cases inside : ∃ j,rawOld j=i
  · obtain ⟨j,rfl⟩:=inside
    rw [after_heads_old]
    simp only [BankExecution.changedHeads,Function.update_apply,Function.comp_apply,
      rawOld,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have outside : ∀ j,rawOld j≠i:=by simpa only [not_exists] using inside
    have n113 : i≠113:=Ne.symm (outside 113)
    have n36 : i≠36:=Ne.symm (outside 36)
    have n115 : i≠115:=Ne.symm (outside 115)
    rw [afterHeads,dockH_other rawOld H _ i outside,
      Function.update_of_ne n115,Function.update_of_ne n36,Function.update_of_ne n113]

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The raw pass physically supplies the converter count and preserves the
empty native template, the same width and every private scratch field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counted_inputs (A : Fin 128→List Bool) (C w M : ℕ) (table : List Bool)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w 0 j) :
    ∀ j,afterTapes A C table M (slots j)=CountIndexCopy.input C w M j:=by
  intro j
  rw [after_tapes_eq]
  fin_cases j
  · rfl
  all_goals simp only [slots,Function.update_apply]
  all_goals exact ha _

theorem counted_heads (H : Fin 128→ℕ) (pos : ℕ) (hh : ∀ j,H (slots j)=0) :
    ∀ j,afterHeads H pos (slots j)=0:=by
  intro j
  rw [after_heads_eq]
  fin_cases j
  · rfl
  all_goals simp only [slots,Function.update_apply]
  all_goals exact hh _

theorem native_heads (H : Fin 128→ℕ) (pos : ℕ) (out : List Bool)
    (hh : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i) :
    ∀ i,afterHeads H pos (old i)=P1CompactCloseoutRowsBankFields.heads out i:=by
  intro i
  rw [after_heads_eq]
  have n115 : old i≠115:=by
    intro he
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  have n113 : old i≠113:=by
    intro he
    have hv : i.val=113:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  rw [Function.update_of_ne n115]
  by_cases h36 : i=36
  · subst i;rfl
  · have n36 : old i≠36:=fun he=>h36 (Fin.ext (congrArg (fun x : Fin 128=>x.val) he))
    rw [Function.update_of_ne n36,Function.update_of_ne n113]
    exact hh i

theorem native_other (A : Fin 128→List Bool) (C M : ℕ) (table : List Bool)
    (i : Fin 113) (hi : i≠36) : afterTapes A C table M (old i)=A (old i):=by
  rw [after_tapes_eq]
  have n115 : old i≠115:=by
    intro he
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  have n36 : old i≠36:=fun he=>hi (Fin.ext (congrArg (fun x : Fin 128=>x.val) he))
  rw [Function.update_of_ne n115,Function.update_of_ne n36]

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positive:=Composition.machine raw counted
def positiveBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+budget C Q w ms.length

theorem positive_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hM : 0 < ms.length) (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (hcH : ∀ j,H (slots j)=0)
    (hcA : ∀ j,A (slots j)=CountIndexCopy.input
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w 0 j)
    (hrH : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (hrA : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom positive (positiveBudget gs.length C Q w (rawIndices ms))
      ⟨positive.start,H,A⟩=some result ∧
      result.steps≤positiveBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false :=by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  let pos:=pre.length+(stream (rawIndices ms)).length
  have hB : gs.length≤C:=by
    have hs:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
    unfold P1CompactCloseoutRowsPreparationBounds.scale at hs
    dsimp only [C];omega
  have first:=raw_run ms C hB pre tail H A hrH hrA
    (P1CompactBankFields.table_bound gs p F Q w ms hw.le)
    (P1CompactBankConsumer.count_bound (l+r) p F w gs.length Q ms.length hw.le)
    (hheads 104) (hheads 105)
    ((hbase 104 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.driver gs p F Q w C [] out))
    ((hbase 105 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.log gs p F Q w C [] out))
  have hl : ∀ row∈rawRows ms,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  have hlen : (rawRows ms).length=ms.length:=by simp only [rawRows,List.length_map]
  obtain ⟨last,lastRun,_ls,lh,lt,keep⟩:=polynomial_run gs (rawRows ms) p F Q w out hl
    (by simpa only [hlen] using hM) (by simpa only [hlen] using hw) hQ hQp hp hF
    (afterHeads H pos) (afterTapes A C (rawRows ms).flatten ms.length)
    (counted_heads H pos hcH)
    (by simpa only [hlen] using counted_inputs A C w ms.length (rawRows ms).flatten hcA)
    (native_heads H pos out hheads)
    (by intro i h36 h52 h107
        exact (native_other A C ms.length (rawRows ms).flatten i h36).trans (hbase i h36 h52 h107))
    (by rw [after_tapes_eq];rfl)
  have time : (rawRows ms).length=(rawIndices ms).length:=by simp only [rawRows,rawIndices,List.length_map]
  rw [time] at lastRun
  obtain ⟨result,rr,rh,rt,rs⟩:=first.seq (Step.of_run lastRun rfl rfl)
  have outside (i : Fin 128) (hi : 113 ≤ i.val) : ∀ j,old j≠i:=by
    intro j he
    have hv : j.val=i.val:=congrArg (fun x : Fin 128=>x.val) he
    have hj:=j.isLt;omega
  refine ⟨result,rr,rs,?_,?_,?_,?_,?_,?_⟩
  · intro i;rw [rh];exact lh i
  · intro i;rw [rt];exact lt i
  · rw [rh,(keep 113 (outside 113 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 113 (outside 113 (by decide))).2]
    simp only [changed,Function.update_of_ne (by decide : (113 : Fin 128)≠107),
      Function.update_of_ne (by decide : (113 : Fin 128)≠52),
      Function.update_of_ne (by decide : (113 : Fin 128)≠115),after_tapes_eq,
      Function.update_of_ne (by decide : (113 : Fin 128)≠36)]
  · rw [rh,(keep 115 (outside 115 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 115 (outside 115 (by decide))).2];rfl

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def zero:=RecoveryFocus.machine rawOld BankZero.machine

theorem zero_run (B C : ℕ) (hB : B≤C) (out pre tail : List Bool)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes C B (pre++[false]++tail) [] 0 j)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length≤C)
    (ho : A 31=out) (hd : A 104=List.replicate C true)
    (hl : A 105=List.replicate (C+1) false) :
    ∃ result,runFrom zero (BankZero.budget B C) ⟨zero.start,H,A⟩=some result ∧
      result.steps≤BankZero.budget B C ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads out i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C out i) ∧
      result.final.heads 113=pre.length+1 ∧ result.final.tapes 113=A 113 ∧
      result.final.heads 115=0 ∧ result.final.tapes 115=List.replicate C false:=by
  obtain ⟨base,hb,_bs,bh,bt,bpos,bsource,bcount,bzero⟩:=BankZero.zero_run B C hB out pre tail
    (H ∘ rawOld) (A ∘ rawOld) hh ht hheads hsize ho hd hl
  obtain ⟨result,hr,_rf,_rs,rh,rt,_keep⟩:=RecoveryFocus.dock rawOld rawOld_injective BankZero.machine
    _ H A _ (fun _=>rfl) (fun _=>rfl) base hb
  refine ⟨result,hr,runFrom_steps_le zero _ _ _ hr,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (rh (P1CompactBankConsumer.old i)).trans (bh i)
  · intro i
    exact (rt (P1CompactBankConsumer.old i)).trans (bt i)
  · exact (rh 113).trans bpos
  · exact (rt 113).trans bsource
  · exact (rh 115).trans bcount
  · exact (rt 115).trans bzero

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Dispatch on the original raw stream marker in the same count bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def idle : Machine 128 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def dispatch {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t):=
  CloseoutWitness.HeaderSwitch.machine idle yes no (fun _=>true) (fun cells=>cells 113)
def optional:=dispatch positive zero

theorem dispatch_run {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t)
    (j : Fin 3) (hj : j=1 ∨ j=2) (fuel : ℕ) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (base : ExecutionReceipt 128 (CloseoutWitness.HeaderSwitch.sizes 1 s t j))
    (hbit : j=if readTapeBit (A 113) (H 113) then 1 else 2)
    (hr : runFrom (CloseoutWitness.HeaderSwitch.programs idle yes no j) fuel
      ⟨(CloseoutWitness.HeaderSwitch.programs idle yes no j).start,H,A⟩=some base) :
    ∃ actual,runFrom (dispatch yes no) (fuel+2)
      ⟨(dispatch yes no).start,H,A⟩=some actual ∧
      actual.steps≤fuel+2 ∧ actual.final.heads=base.final.heads ∧
      actual.final.tapes=base.final.tapes:=by
  let prior : ExecutionReceipt 128 1:=⟨⟨0,H,A⟩,0,(⟨0,H,A⟩ : Configuration 128 1).tapeCells⟩
  have hp : runFrom idle 0 ⟨idle.start,H,A⟩=some prior:=rfl
  simpa only [dispatch,Nat.zero_add,Nat.add_comm 1 fuel,Nat.add_assoc,Nat.reduceAdd] using
    CloseoutWitness.HeaderSwitch.accepted idle yes no (fun _=>true) (fun cells=>cells 113)
      j hj 0 fuel H A prior base hp hr rfl hbit

end
end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def optionalBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  max (positiveBudget B C Q w ms) (BankZero.budget B C)+2

theorem optional_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (hcH : ∀ j,H (slots j)=0)
    (hcA : ∀ j,A (slots j)=CountIndexCopy.input
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w 0 j)
    (hrH : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (hrA : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom optional (optionalBudget gs.length C Q w (rawIndices ms))
      ⟨optional.start,H,A⟩=some result ∧
      result.steps≤optionalBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false:=by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  have marker : readTapeBit (A 113) (H 113)=decide (0 < ms.length):=by
    have ha : A 113=pre++stream (rawIndices ms)++tail:=hrA 0
    have hh : H 113=pre.length:=hrH 0
    rw [ha,hh,BankBranch.stream_marker]
    simp only [rawIndices,List.length_map]
  by_cases empty : ms=[]
  · subst ms
    have hB : gs.length ≤ C:=by
      have hs:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
      unfold P1CompactCloseoutRowsPreparationBounds.scale at hs
      dsimp only [C];omega
    have hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C:=by
      intro i hi hlog
      by_cases h36 : i=36
      · subst i
        have ha : A (old 36)=ZeroPadding.pad C []:=hrA 3
        rw [ha];simp [ZeroPadding.pad]
      by_cases h52 : i=52
      · subst i
        have ha : A (old 52)=ZeroPadding.pad C []:=hcA 11
        rw [ha];simp [ZeroPadding.pad]
      by_cases h107 : i=107
      · subst i
        have ha : A (old 107)=List.replicate C false:=hcA 15
        rw [ha,List.length_replicate]
      rw [hbase i h36 h52 h107]
      exact P1CompactBankOptional.entry_size gs p F Q w [] out (by simp) (by simp) hF i hi hlog
    obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct⟩:=zero_run gs.length C hB out pre tail H A hrH hrA hheads hsize
      ((hbase 31 (by decide) (by decide) (by decide)).trans (P1CompactBankOptional.entry_out gs p F Q w C [] out))
      ((hbase 104 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.driver gs p F Q w C [] out))
      ((hbase 105 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.log gs p F Q w C [] out))
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 2 (Or.inr rfl) _ H A base (by rw [marker];rfl) hb
    have bound : BankZero.budget gs.length C+2 ≤ optionalBudget gs.length C Q w (rawIndices (B:=gs.length) []):=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices (B:=gs.length) [])-(BankZero.budget gs.length C+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨z,more,zs.trans bound,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zh,zt,rawRows,rawIndices,List.map_nil,P1CompactCloseoutRowsPacketOptional.cuts_nil,
      List.flatMap_nil,List.append_nil,stream_nil,List.length_singleton]
    · exact bh
    · exact bt
    · exact bp
    · exact ba
    · exact bch
    · exact bct
  · obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct⟩:=positive_run gs ms p F Q w out pre tail
      (List.length_pos_iff.mpr empty) hw hQ hQp hp hF H A hheads hbase hcH hcA hrH hrA
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 1 (Or.inl rfl) _ H A base
      (by rw [marker,if_pos (by simpa using List.length_pos_iff.mpr empty)]) hb
    have bound : positiveBudget gs.length C Q w (rawIndices ms)+2 ≤ optionalBudget gs.length C Q w (rawIndices ms):=
      Nat.add_le_add_right (Nat.le_max_left _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices ms)-(positiveBudget gs.length C Q w (rawIndices ms)+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    exact ⟨z,more,zs.trans bound,by rw [zh];exact bh,by rw [zt];exact bt,
      by rw [zh];exact bp,by rw [zt];exact ba,by rw [zh];exact bch,by rw [zt];exact bct⟩

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The fifteen measured source words are exactly the static native inputs.
Only the table and counted last-index fields remain for incidence to fill. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def select (i : Fin 113) : Option (Fin 15):=match i.val with
  | 0 => some 0
  | 9 => some 1
  | 13 => some 2
  | 18 => some 3
  | 21 => some 4
  | 29 => some 5
  | 33 => some 6
  | 35 => some 7
  | 38 => some 8
  | 39 => some 9
  | 40 => some 9
  | 45 => some 10
  | 46 => some 11
  | 51 => some 10
  | 61 => some 11
  | 66 => some 12
  | 90 => some 13
  | 106 => some 10
  | 108 => some 11
  | 109 => some 12
  | 111 => some 13
  | 112 => some 14
  | _ => none

def payload {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (i : Fin 113):=
  NativeFanout.word select (P1CompactNativeMaster.words gs Q w) i

private theorem read_false_ExtIncidence_NativeTemplate (z k : ℕ) : readTapeBit (List.replicate z false) k=false:=by
  simp [readTapeBit,List.getD]
private theorem read_empty_ExtIncidence_NativeTemplate (k : ℕ) : readTapeBit [] k=false:=rfl

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (out : List Bool) :
    (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes=
      fun i=>ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C i)
        (Fin.addCases (m:=112) (n:=1) (motive:=fun _=>List Bool)
          (P1CompactCloseoutRowsLoopLayout.inputTapes gs p F w 0 C [] out) (fun _=>CompareMachine.word Q) i):=rfl

theorem core_read {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (out : List Bool) (i : Fin 48) (pos : ℕ) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes (i.castAdd 65)) pos=
      readTapeBit (P1CompactRowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i) pos:=by
  change readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
    (((i.castAdd 55).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left]
  simp only [P1CompactCloseoutRowsLoopLayout.inputTapes,Fin.addCases_left]
  change readTapeBit (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C (i.castAdd 65))
    (ZeroPadding.pad (CloseoutRowsDegreeReset.caps C (i.castAdd 55))
      ((P1CompactCloseoutRowsLoopLayout.rawInput gs p F w 0 [] out).tapes ((i.castAdd 41).castAdd 14)))) pos=_
  simp only [P1CompactCloseoutRowsLoopLayout.rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
  change readTapeBit (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C (i.castAdd 65))
    (ZeroPadding.pad (CloseoutRowsDegreeReset.caps C (i.castAdd 55))
      (Function.update (P1CompactCloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes 48 []
        (i.castAdd 41)))) pos=_
  have hn : (i.castAdd 41 : Fin 89)≠48:=by
    intro h;have hv:=congrArg (fun x : Fin 89=>x.val) h;have hi:=i.isLt
    simp only [Fin.val_castAdd] at hv;omega
  rw [ZeroPadding.read_pad,ZeroPadding.read_pad,Function.update_of_ne hn]
  change readTapeBit ((P1CompactCloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes
    ((i.castAdd 1).castAdd 40)) pos=_
  simp only [P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,
    TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsEnumeratedCuts.core]
  change readTapeBit (ZeroPadding.pad (P1CompactRowTupleCursorBody.padding F i)
    (P1CompactRowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i)) pos=_
  exact ZeroPadding.read_pad _ _ _

end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Native input correspondence is proved through small tape projections;
no concrete ordinary controller is expanded by the field simplifier. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem read_false_ExtIncidence_NativeTemplateReads (z k : ℕ) : readTapeBit (List.replicate z false) k=false:=by
  simp [readTapeBit,List.getD]
private theorem read_empty_ExtIncidence_NativeTemplateReads (k : ℕ) : readTapeBit [] k=false:=rfl

theorem reads_core {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w C : ℕ)
    (out : List Bool) (i : Fin 48) (pos : ℕ) (h31 : (i.castAdd 65 : Fin 113)≠31) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes (i.castAdd 65)) pos=
      readTapeBit (payload gs Q w (i.castAdd 65)) pos:=by
  rw [core_read]
  fin_cases i <;> try contradiction
  all_goals simp [P1CompactRowTupleCursorLayout.data,P1CompactRowCommonReusable.data,Fin.addCases,
    payload,select,NativeFanout.word,P1CompactNativeMaster.words,P1CompactRowOccurrenceLoop.word,
    UnaryTemplate.tape,CompareMachine.word,read_false_ExtIncidence_NativeTemplateReads,read_empty_ExtIncidence_NativeTemplateReads]
  all_goals first | exact read_false_ExtIncidence_NativeTemplateReads 2 pos | exact read_false_ExtIncidence_NativeTemplateReads 1 pos

theorem enum_read {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w C : ℕ)
    (out : List Bool) (i : Fin 40) (pos : ℕ) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
      ((i.natAdd 49).castAdd 24)) pos=
      readTapeBit (P1CompactRowTupleEnumeratedEquations.extra w 1 0 i) pos:=by
  change readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
    ((((i.natAdd 49).castAdd 14).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left,P1CompactCloseoutRowsLoopLayout.inputTapes]
  simp only [Fin.addCases_left,ZeroPadding.read_pad,P1CompactCloseoutRowsLoopLayout.rawInput,
    P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
  have hn : (i.natAdd 49 : Fin 89)≠48:=by
    intro h;have hv:=congrArg (fun x : Fin 89=>x.val) h
    simp only [Fin.val_natAdd] at hv;omega
  rw [Function.update_of_ne hn]
  simp only [P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,
    TapeEmbedding.config,Fin.addCases_right]
  rfl

theorem reads_enum {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w C : ℕ)
    (out : List Bool) (i : Fin 40) (pos : ℕ) (h52 : ((i.natAdd 49).castAdd 24 : Fin 113)≠52) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes ((i.natAdd 49).castAdd 24)) pos=
      readTapeBit (payload gs Q w ((i.natAdd 49).castAdd 24)) pos:=by
  rw [enum_read]
  fin_cases i <;> try contradiction
  all_goals simp [P1CompactRowTupleEnumeratedEquations.extra,payload,select,NativeFanout.word,
    P1CompactNativeMaster.words,read_empty_ExtIncidence_NativeTemplateReads]

end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Remaining coefficient/template ports complete the exact static payload. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem read_false_ExtIncidence_NativeTemplateTail (z k : ℕ) : readTapeBit (List.replicate z false) k=false:=by
  simp [readTapeBit,List.getD]
private theorem read_empty_ExtIncidence_NativeTemplateTail (k : ℕ) : readTapeBit [] k=false:=rfl

theorem reads_coefficient {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w C : ℕ)
    (out : List Bool) (i : Fin 14) (pos : ℕ) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes ((i.natAdd 89).castAdd 10)) pos=
      readTapeBit (payload gs Q w ((i.natAdd 89).castAdd 10)) pos:=by
  change readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes (((i.natAdd 89).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left,P1CompactCloseoutRowsLoopLayout.inputTapes]
  simp only [ZeroPadding.read_pad,P1CompactCloseoutRowsLoopLayout.rawInput,
    P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input,payload,select,NativeFanout.word,
    P1CompactNativeMaster.words,read_empty_ExtIncidence_NativeTemplateTail]

theorem reads_tail {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w C : ℕ)
    (out : List Bool) (i : Fin 10) (pos : ℕ)
    (h104 : (i.natAdd 103 : Fin 113)≠104) (h105 : (i.natAdd 103 : Fin 113)≠105)
    (h107 : (i.natAdd 103 : Fin 113)≠107) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes (i.natAdd 103)) pos=
      readTapeBit (payload gs Q w (i.natAdd 103)) pos:=by
  fin_cases i <;> try contradiction
  all_goals simp [entry_tapes,P1CompactCloseoutRowsLoopLayout.inputTapes,P1CompactCloseoutRowsLoopLayout.extra,
    P1CompactCloseoutRowsLoopLayout.templates,Fin.addCases,ZeroPadding.read_pad,payload,select,
    NativeFanout.word,P1CompactNativeMaster.words,read_false_ExtIncidence_NativeTemplateTail,read_empty_ExtIncidence_NativeTemplateTail]

theorem reads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w C : ℕ)
    (out : List Bool) (i : Fin 113) (pos : ℕ)
    (h31 : i≠31) (h52 : i≠52) (h104 : i≠104) (h105 : i≠105) (h107 : i≠107) :
    readTapeBit ((P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes i) pos=
      readTapeBit (payload gs Q w i) pos:=by
  revert h31 h52 h104 h105 h107
  refine Fin.addCases (m:=103) (n:=10) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=89) (n:=14) (fun b=>?_) (fun b=>?_) a
    · refine Fin.addCases (m:=49) (n:=40) (fun c=>?_) (fun c=>?_) b
      · refine Fin.addCases (m:=48) (n:=1) (fun d=>?_) (fun d=>?_) c
        · intro h31 _ _ _ _;exact reads_core gs Q w C out d pos h31
        · intro _ _ _ _ _;fin_cases d
          change readTapeBit (ZeroPadding.pad C (ZeroPadding.pad C [])) pos=readTapeBit [] pos
          rw [ZeroPadding.read_pad,ZeroPadding.read_pad]
      · intro _ h52 _ _ _;exact reads_enum gs Q w C out c pos h52
    · intro _ _ _ _ _;exact reads_coefficient gs Q w C out b pos
  · intro _ _ h104 h105 h107;exact reads_tail gs Q w C out a pos h104 h105 h107

end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Every distributed metadata word fits the actual measured native C.
The coefficient width, mode width and original arity remain distinct. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMaster
open NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem words_fit {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (i : Fin 15) :
    (words gs Q w i).length ≤ P1CompactNativeMeasured.capacity gs Q w:=by
  obtain ⟨hc,hi,ho⟩:=P1CompactCloseoutRowsBankFields.cache_bounds gs (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) Q le_rfl
  have small:=P1CompactCloseoutRowsPreparationInput.small_fits n (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) w gs.length Q
  unfold P1CompactCloseoutRowsPreparationBounds.scale at small
  change (words gs Q w i).length ≤ P1CompactCloseoutRowsPreparationBounds.capacity n
    (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) w gs.length Q
  have hw : P1Radix.bits gs ≤
      RowCachedCoordinateBounds.inner (P1Radix.bits gs):=by
    unfold RowCachedCoordinateBounds.inner;omega
  fin_cases i <;> simp [words,UnaryTemplate.tape,CompareMachine.word,frame_length,SignedSortKey.binary_length]
  all_goals omega

end NearCubicWires.ExtIncidence.P1CompactNativeMaster

/-! Observed bits and the proved common extent identify the exact native
input lists, so false backing never becomes a prepared-word assumption. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem exact_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (out : List Bool) (i : Fin 113)
    (h31 : i≠31) (h52 : i≠52) (h104 : i≠104) (h105 : i≠105) (h107 : i≠107) :
    let C:=P1CompactNativeMeasured.capacity gs Q w
    (P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes i=
        ZeroPadding.pad C (payload gs Q w i):=by
  dsimp only
  let C:=P1CompactNativeMeasured.capacity gs Q w
  let E:=(P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) Q w C [] out).tapes i
  have size : E.length ≤ C:=P1CompactBankOptional.entry_size gs (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) Q w [] out (by simp) (by simp) le_rfl i h31 h105
  have len : E.length=C:=by
    apply Nat.le_antisymm size
    change C ≤ (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C i) _).length
    rw [ZeroPadding.pad_length]
    simp only [P1CompactCloseoutRowsBankCapacity.capacities,h31,h105,↓reduceIte]
    exact Nat.le_max_left _ _
  have fit : (payload gs Q w i).length ≤ C:=by
    unfold payload NativeFanout.word
    cases h : select i with
    | none => simp
    | some j => exact P1CompactNativeMaster.words_fit gs Q w j
  have bits : readTapeBit E=readTapeBit (payload gs Q w i):=by
    funext pos;exact reads gs Q w C out i pos h31 h52 h104 h105 h107
  have same : RecoveryBoundedTapeCopy.copied E C=E:=by
    simpa only [len] using CloseoutRowsMetadataCopy.copied_self E
  change E=ZeroPadding.pad C (payload gs Q w i)
  rw [←same]
  have copied_same : RecoveryBoundedTapeCopy.copied E C=RecoveryBoundedTapeCopy.copied (payload gs Q w i) C:=by simp only [RecoveryBoundedTapeCopy.copied,bits]
  rw [copied_same]
  exact CloseoutRowsMetadataCopy.copied_pad _ C fit

end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! The physically initialized bank supplies all native, count-conversion
and raw-incidence inputs, without an input row count or last-index word. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeBankInputs
open NearCubicWires.ExtIncidence.NativeBankInputs
open LocalBitMultitape RepairOrdinary NativeInitializedPorts NativeFanoutLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem base {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (source out : List Bool) (i : Fin 113) (h52 : i≠52) (h107 : i≠107) :
    word (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w) source out (P1CompactBankCount.old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
        (P1CompactNativeAllocation.capacity gs Q) Q w (P1CompactNativeMeasured.capacity gs Q w) [] out).tapes i:=by
  by_cases h31 : i=31
  · subst i;exact (P1CompactBankOptional.entry_out gs _ _ Q w _ [] out).symm
  by_cases h104 : i=104
  · subst i;exact (P1CompactBankFields.driver gs _ _ Q w _ [] out).symm
  by_cases h105 : i=105
  · subst i;exact (P1CompactBankFields.log gs _ _ Q w _ [] out).symm
  have n31 : P1CompactBankCount.old i≠31:=by intro h;apply h31;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n104 : P1CompactBankCount.old i≠104:=by intro h;apply h104;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n105 : P1CompactBankCount.old i≠105:=by intro h;apply h105;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n113 : P1CompactBankCount.old i≠113:=by
    intro h;have hv:=congrArg (fun x : Fin 128=>x.val) h;have hi:=i.isLt
    simp only [P1CompactBankCount.old,Fin.val_castAdd] at hv;omega
  simp only [word,if_neg n31,if_neg n104,if_neg n105,if_neg n113]
  change ZeroPadding.pad (P1CompactNativeMeasured.capacity gs Q w) (P1CompactNativeTemplate.payload gs Q w i)=_
  exact (P1CompactNativeTemplate.exact_input gs Q w out i h31 h52 h104 h105 h107).symm

theorem count_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (source out : List Bool) (j : Fin 18) :
    word (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w) source out (P1CompactBankCount.slots j)=
      CountIndexCopy.input (P1CompactNativeMeasured.capacity gs Q w) w 0 j:=by
  fin_cases j <;> simp [word,selection,P1CompactNativeMaster.words,P1CompactBankCount.slots,CountIndexCopy.input,
    CountIndex.padded,CountIndex.input,CountIndexCopy.extra,Fin.addCases,ZeroPadding.pad]

theorem raw_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (source out : List Bool) (j : Fin 5) :
    word (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w) source out
      (P1CompactBankCount.rawOld (BankExecution.slots j))=
        Padded.tapes (P1CompactNativeMeasured.capacity gs Q w) gs.length source [] 0 j:=by
  fin_cases j <;> simp [word,selection,P1CompactNativeMaster.words,P1CompactBankCount.rawOld,BankExecution.slots,
    Padded.tapes,ZeroPadding.pad]

end NearCubicWires.ExtIncidence.P1CompactNativeBankInputs

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_retained_run (B C : ℕ) (hB : B≤C) (out pre tail : List Bool)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes C B (pre++[false]++tail) [] 0 j)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length≤C)
    (ho : A 31=out) (hd : A 104=List.replicate C true)
    (hl : A 105=List.replicate (C+1) false) :
    ∃ result,runFrom zero (BankZero.budget B C) ⟨zero.start,H,A⟩=some result ∧
      result.steps≤BankZero.budget B C ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads out i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C out i) ∧
      result.final.heads 113=pre.length+1 ∧ result.final.tapes 113=A 113 ∧
      result.final.heads 115=0 ∧ result.final.tapes 115=List.replicate C false ∧
      (∀ i : Fin 128,i.val=114 ∨ 116 ≤ i.val → result.final.heads i=H i ∧ result.final.tapes i=A i):=by
  obtain ⟨base,hb,_bs,bh,bt,bpos,bsource,bcount,bzero,b114H,b114A⟩:=BankZero.zero_retained_run B C hB out pre tail
    (H ∘ rawOld) (A ∘ rawOld) hh ht hheads hsize ho hd hl
  obtain ⟨result,hr,_rf,_rs,rh,rt,keep⟩:=RecoveryFocus.dock rawOld rawOld_injective BankZero.machine
    _ H A _ (fun _=>rfl) (fun _=>rfl) base hb
  refine ⟨result,hr,runFrom_steps_le zero _ _ _ hr,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (rh (P1CompactBankConsumer.old i)).trans (bh i)
  · intro i
    exact (rt (P1CompactBankConsumer.old i)).trans (bt i)
  · exact (rh 113).trans bpos
  · exact (rt 113).trans bsource
  · exact (rh 115).trans bcount
  · exact (rt 115).trans bzero

  · intro i hi
    rcases hi with hi|hi
    · have he : i=114:=Fin.ext hi
      subst i
      exact ⟨(rh 114).trans b114H,(rt 114).trans b114A⟩
    · exact keep i (rawOld_avoids i hi)

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem positive_retained_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hM : 0 < ms.length) (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (hcH : ∀ j,H (slots j)=0)
    (hcA : ∀ j,A (slots j)=CountIndexCopy.input
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w 0 j)
    (hrH : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (hrA : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom positive (positiveBudget gs.length C Q w (rawIndices ms))
      ⟨positive.start,H,A⟩=some result ∧
      result.steps≤positiveBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false ∧
      (∀ i : Fin 128,i.val=114 ∨ 116 ≤ i.val → result.final.heads i=H i ∧ result.final.tapes i=A i) :=by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  let pos:=pre.length+(stream (rawIndices ms)).length
  have hB : gs.length≤C:=by
    have hs:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
    unfold P1CompactCloseoutRowsPreparationBounds.scale at hs
    dsimp only [C];omega
  have first:=raw_run ms C hB pre tail H A hrH hrA
    (P1CompactBankFields.table_bound gs p F Q w ms hw.le)
    (P1CompactBankConsumer.count_bound (l+r) p F w gs.length Q ms.length hw.le)
    (hheads 104) (hheads 105)
    ((hbase 104 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.driver gs p F Q w C [] out))
    ((hbase 105 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.log gs p F Q w C [] out))
  have hl : ∀ row∈rawRows ms,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  have hlen : (rawRows ms).length=ms.length:=by simp only [rawRows,List.length_map]
  obtain ⟨last,lastRun,_ls,lh,lt,keep⟩:=polynomial_run gs (rawRows ms) p F Q w out hl
    (by simpa only [hlen] using hM) (by simpa only [hlen] using hw) hQ hQp hp hF
    (afterHeads H pos) (afterTapes A C (rawRows ms).flatten ms.length)
    (counted_heads H pos hcH)
    (by simpa only [hlen] using counted_inputs A C w ms.length (rawRows ms).flatten hcA)
    (native_heads H pos out hheads)
    (by intro i h36 h52 h107
        exact (native_other A C ms.length (rawRows ms).flatten i h36).trans (hbase i h36 h52 h107))
    (by rw [after_tapes_eq];rfl)
  have time : (rawRows ms).length=(rawIndices ms).length:=by simp only [rawRows,rawIndices,List.length_map]
  rw [time] at lastRun
  obtain ⟨result,rr,rh,rt,rs⟩:=first.seq (Step.of_run lastRun rfl rfl)
  have outside (i : Fin 128) (hi : 113 ≤ i.val) : ∀ j,old j≠i:=by
    intro j he
    have hv : j.val=i.val:=congrArg (fun x : Fin 128=>x.val) he
    have hj:=j.isLt;omega
  refine ⟨result,rr,rs,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;rw [rh];exact lh i
  · intro i;rw [rt];exact lt i
  · rw [rh,(keep 113 (outside 113 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 113 (outside 113 (by decide))).2]
    simp only [changed,Function.update_of_ne (by decide : (113 : Fin 128)≠107),
      Function.update_of_ne (by decide : (113 : Fin 128)≠52),
      Function.update_of_ne (by decide : (113 : Fin 128)≠115),after_tapes_eq,
      Function.update_of_ne (by decide : (113 : Fin 128)≠36)]
  · rw [rh,(keep 115 (outside 115 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 115 (outside 115 (by decide))).2];rfl

  · intro i hi
    have hlo : 113 ≤ i.val:=by omega
    have n36 : i≠36:=by intro he;subst i;rcases hi with hi|hi <;>simp at hi
    have n52 : i≠52:=by intro he;subst i;rcases hi with hi|hi <;>simp at hi
    have n107 : i≠107:=by intro he;subst i;rcases hi with hi|hi <;>simp at hi
    have n113 : i≠113:=by intro he;subst i;rcases hi with hi|hi <;>simp at hi
    have n115 : i≠115:=by intro he;subst i;rcases hi with hi|hi <;>simp at hi
    constructor
    · rw [rh,(keep i (outside i hlo)).1,after_heads_eq]
      simp only [Function.update_of_ne n115,Function.update_of_ne n36,Function.update_of_ne n113]
    · rw [rt,(keep i (outside i hlo)).2]
      simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115,
        after_tapes_eq,Function.update_of_ne n36]

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem optional_retained_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (p F Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hheads : ∀ i,H (old i)=P1CompactCloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w
        (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (hcH : ∀ j,H (slots j)=0)
    (hcA : ∀ j,A (slots j)=CountIndexCopy.input
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w 0 j)
    (hrH : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (hrA : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j) :
    let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom optional (optionalBudget gs.length C Q w (rawIndices ms))
      ⟨optional.start,H,A⟩=some result ∧
      result.steps≤optionalBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false ∧
      (∀ i : Fin 128,i.val=114 ∨ 116 ≤ i.val → result.final.heads i=H i ∧ result.final.tapes i=A i):=by
  dsimp only
  let C:=P1CompactCloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  have marker : readTapeBit (A 113) (H 113)=decide (0 < ms.length):=by
    have ha : A 113=pre++stream (rawIndices ms)++tail:=hrA 0
    have hh : H 113=pre.length:=hrH 0
    rw [ha,hh,BankBranch.stream_marker]
    simp only [rawIndices,List.length_map]
  by_cases empty : ms=[]
  · subst ms
    have hB : gs.length ≤ C:=by
      have hs:=P1CompactCloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
      unfold P1CompactCloseoutRowsPreparationBounds.scale at hs
      dsimp only [C];omega
    have hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C:=by
      intro i hi hlog
      by_cases h36 : i=36
      · subst i
        have ha : A (old 36)=ZeroPadding.pad C []:=hrA 3
        rw [ha];simp [ZeroPadding.pad]
      by_cases h52 : i=52
      · subst i
        have ha : A (old 52)=ZeroPadding.pad C []:=hcA 11
        rw [ha];simp [ZeroPadding.pad]
      by_cases h107 : i=107
      · subst i
        have ha : A (old 107)=List.replicate C false:=hcA 15
        rw [ha,List.length_replicate]
      rw [hbase i h36 h52 h107]
      exact P1CompactBankOptional.entry_size gs p F Q w [] out (by simp) (by simp) hF i hi hlog
    obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct,bkeep⟩:=zero_retained_run gs.length C hB out pre tail H A hrH hrA hheads hsize
      ((hbase 31 (by decide) (by decide) (by decide)).trans (P1CompactBankOptional.entry_out gs p F Q w C [] out))
      ((hbase 104 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.driver gs p F Q w C [] out))
      ((hbase 105 (by decide) (by decide) (by decide)).trans (P1CompactBankFields.log gs p F Q w C [] out))
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 2 (Or.inr rfl) _ H A base (by rw [marker];rfl) hb
    have bound : BankZero.budget gs.length C+2 ≤ optionalBudget gs.length C Q w (rawIndices (B:=gs.length) []):=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices (B:=gs.length) [])-(BankZero.budget gs.length C+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨z,more,zs.trans bound,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zh,zt,rawRows,rawIndices,List.map_nil,P1CompactCloseoutRowsPacketOptional.cuts_nil,
      List.flatMap_nil,List.append_nil,stream_nil,List.length_singleton]
    · exact bh
    · exact bt
    · exact bp
    · exact ba
    · exact bch
    · exact bct
    · exact bkeep
  · obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct,bkeep⟩:=positive_retained_run gs ms p F Q w out pre tail
      (List.length_pos_iff.mpr empty) hw hQ hQp hp hF H A hheads hbase hcH hcA hrH hrA
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 1 (Or.inl rfl) _ H A base
      (by rw [marker,if_pos (by simpa using List.length_pos_iff.mpr empty)]) hb
    have bound : positiveBudget gs.length C Q w (rawIndices ms)+2 ≤ optionalBudget gs.length C Q w (rawIndices ms):=
      Nat.add_le_add_right (Nat.le_max_left _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices ms)-(positiveBudget gs.length C Q w (rawIndices ms)+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    exact ⟨z,more,zs.trans bound,by rw [zh];exact bh,by rw [zt];exact bt,
      by rw [zh];exact bp,by rw [zt];exact ba,by rw [zh];exact bch,by rw [zt];exact bct,by intro i hi;rw [zh,zt];exact bkeep i hi⟩

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The completed optional worker has the literal all-blank reload bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle
open NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_heads (pos : ℕ) (out : List Bool) (i : Fin 113) :
    CloseoutRowsBankClear.zeroHeads out i=NativeInitialize.extraH pos out (P1CompactBankCount.old i) := by
  fin_cases i <;> rfl

theorem native_word (C : ℕ) (source out : List Bool) (i : Fin 113) :
    CloseoutRowsBankClear.blank C out i=
      NativeInitializedPorts.word (fun _ : Fin 15=>[]) C source out (P1CompactBankCount.old i) := by
  fin_cases i <;>simp [CloseoutRowsBankClear.blank,NativeInitializedPorts.word,P1CompactBankCount.old,selection,ZeroPadding.pad]

theorem unused (data : Fin 15→List Bool) (C pos : ℕ) (source out : List Bool) (i : Fin 128)
    (hi : i.val=114 ∨ 116 ≤ i.val) :
    NativeBankPosition.heads pos out i=0 ∧ NativeInitialize.extraH pos out i=0 ∧
      NativeInitializedPorts.word data C source out i=List.replicate C false := by
  fin_cases i <;>simp_all [NativeBankPosition.heads,NativeBankPosition.raised,NativeInitialize.extraH,
    NativeInitializedPorts.word,selection,ZeroPadding.pad]

theorem cleared (data : Fin 15→List Bool) (C pos next : ℕ) (source out word : List Bool)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ i,H (P1CompactBankCount.old i)=CloseoutRowsBankClear.zeroHeads word i)
    (ha : ∀ i,A (P1CompactBankCount.old i)=CloseoutRowsBankClear.blank C word i)
    (sh : H 113=next) (sa : A 113=source) (ch : H 115=0) (ca : A 115=List.replicate C false)
    (keep : ∀ i : Fin 128,i.val=114 ∨ 116 ≤ i.val →
      H i=NativeBankPosition.heads pos out i ∧ A i=NativeInitializedPorts.word data C source out i)
    (i : Fin 128) : H i=NativeInitialize.extraH next word i ∧
      A i=NativeInitializedPorts.word (fun _ : Fin 15=>[]) C source word i := by
  by_cases hi : i.val<113
  · let j : Fin 113:=⟨i.val,hi⟩
    have he : P1CompactBankCount.old j=i:=Fin.ext rfl
    rw [←he]
    exact ⟨(hh j).trans (native_heads next word j),(ha j).trans (native_word C source word j)⟩
  · by_cases h113 : i=113
    · subst i;exact ⟨sh,sa⟩
    by_cases h115 : i=115
    · subst i
      simpa [NativeInitialize.extraH,NativeInitializedPorts.word,selection,ZeroPadding.pad] using And.intro ch ca
    have hn113 : i.val≠113:=fun he=>h113 (Fin.ext he)
    have hn115 : i.val≠115:=fun he=>h115 (Fin.ext he)
    have hother : i.val=114 ∨ 116 ≤ i.val:=by omega
    have first:=unused data C pos source out i hother
    have last:=unused (fun _ : Fin 15=>[]) C next source word i hother
    exact ⟨(keep i hother).1.trans (first.1.trans last.2.1.symm),
      (keep i hother).2.trans (first.2.2.trans last.2.2.symm)⟩

end NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle

/-! One actual reusable native call preserves every ambient port outside its bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle
open NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last:=RecoveryFocus.machine bank P1CompactBankCount.optional
noncomputable def machine:=Composition.machine NativeBankPosition.machine last
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (ms : List (List ℕ)):=
  1+1+P1CompactBankCount.optionalBudget gs.length (P1CompactNativeMeasured.capacity gs Q w) Q w ms

theorem direction_outside (i : Fin 277) (hi : ∀ j,bank j≠i) : NativeBankPosition.directions i=.stay := by
  simp only [NativeBankPosition.directions,Ne.symm (hi 15),Ne.symm (hi 18),Ne.symm (hi 24),
    Ne.symm (hi 35),Ne.symm (hi 37),Ne.symm (hi 38),Ne.symm (hi 45),Ne.symm (hi 46),Ne.symm (hi 112),
    or_self,ite_false]

theorem cycle_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (hh : ∀ i,H (bank i)=NativeInitialize.extraH pre.length out i)
    (ha : ∀ i,A (bank i)=NativeInitializedPorts.word (P1CompactNativeMaster.words gs Q w)
      (P1CompactNativeMeasured.capacity gs Q w) (pre++stream (rawIndices ms)++tail) out i) :
    let C:=P1CompactNativeMeasured.capacity gs Q w
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (P1CompactNativeWidth.width gs Q))
    ∃ H' A',Step machine (budget gs Q w (rawIndices ms)) H A H' A' ∧
      (∀ i,H' (bank i)=NativeInitialize.extraH (pre.length+(stream (rawIndices ms)).length) word i ∧
        A' (bank i)=NativeInitializedPorts.word (fun _ : Fin 15=>[]) C
          (pre++stream (rawIndices ms)++tail) word i) ∧
      (∀ j,(∀ i,bank i≠j) → H' j=H j ∧ A' j=A j) := by
  dsimp only
  let source:=pre++stream (rawIndices ms)++tail
  let C:=P1CompactNativeMeasured.capacity gs Q w
  let J : Fin 277→ℕ:=fun i=>(NativeBankPosition.directions i).apply (H i)
  obtain ⟨position,hposition,pfinal,_⟩:=DecompositionCountPosition.move_run NativeBankPosition.directions H A
  have moved : Step NativeBankPosition.machine 1 H A J A:=
    Step.of_run hposition (congrArg Configuration.heads pfinal) (congrArg Configuration.tapes pfinal)
  have jh (i : Fin 128) : J (bank i)=NativeBankPosition.heads pre.length out i:=
    NativeBankPosition.heads_bank H pre.length out hh i
  have hQp : Q ≤ P1CompactNativeWidth.width gs Q:=by unfold P1CompactNativeWidth.width;omega
  have hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ P1CompactNativeWidth.width gs Q:=by unfold P1CompactNativeWidth.width;omega
  obtain ⟨result,rr,_rs,nh,nt,sp,st,ch,ct,keep⟩:=P1CompactBankCount.optional_retained_run gs ms (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) Q w out pre tail hw hQ hQp hp le_rfl (J ∘ bank) (A ∘ bank)
    (by intro i;exact (jh (P1CompactBankCount.old i)).trans (NativeBankPosition.native_heads pre.length out i))
    (by intro i _h36 h52 h107;exact (ha (P1CompactBankCount.old i)).trans (P1CompactNativeBankInputs.base gs Q w source out i h52 h107))
    (by intro j;exact (jh (P1CompactBankCount.slots j)).trans (NativeBankPosition.count_heads pre.length out j))
    (by intro j;exact (ha (P1CompactBankCount.slots j)).trans (P1CompactNativeBankInputs.count_input gs Q w source out j))
    (by intro j;exact (jh (P1CompactBankCount.rawOld (BankExecution.slots j))).trans (NativeBankPosition.raw_heads pre.length out j))
    (by intro j;exact (ha (P1CompactBankCount.rawOld (BankExecution.slots j))).trans (P1CompactNativeBankInputs.raw_input gs Q w source out j))
  have focused:=(Step.of_run rr rfl rfl).dock bank bank_injective J A (fun _=>rfl) (fun _=>rfl)
  have whole:=moved.seq focused
  let Hout:=dockH bank J result.final.heads
  let Aout:=install bank A result.final.tapes
  have oh (i : Fin 128) : Hout (bank i)=result.final.heads i:=dockH_slot bank bank_injective J _ i
  have ot (i : Fin 128) : Aout (bank i)=result.final.tapes i:=install_slot bank bank_injective A _ i
  have field:=cleared (P1CompactNativeMaster.words gs Q w) C pre.length (pre.length+(stream (rawIndices ms)).length)
    source out _ result.final.heads result.final.tapes nh nt sp (st.trans (ha 113)) ch ct
    (fun i hi=>⟨(keep i hi).1.trans (jh i),(keep i hi).2.trans (ha i)⟩)
  refine ⟨Hout,Aout,whole,?_,?_⟩
  · intro i
    exact ⟨(oh i).trans (field i).1,(ot i).trans (field i).2⟩
  · intro j hj
    refine ⟨?_,install_other bank A result.final.tapes j hj⟩
    rw [show Hout j=J j from dockH_other bank J result.final.heads j hj]
    dsimp [J]
    rw [direction_outside j hj]
    rfl

end NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle

/-! The actual polynomial worker and one retained-metadata reload return
the reusable entry bank, ready for the next original raw polynomial. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeRound
open NearCubicWires.ExtIncidence.NativeRound
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bank_source_ne (i : Fin 128) (j : Fin 15) : bank i≠sources j:=by
  have hs : P1CompactNativeMaster.fields j≠133:=by revert j;decide
  intro h
  have hv:=congrArg (fun a : Fin 277=>a.val) h
  simp only [bank,sources] at hv
  split_ifs at hv with hi
  · apply hs;apply Fin.ext;exact hv.symm
  · simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hb:=(P1CompactNativeMaster.fields j).isLt
    omega

noncomputable def machine:=Composition.machine P1CompactEstimatorBankCycle.machine NativeFanoutLayout.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (ms : List (List ℕ)):=
  P1CompactEstimatorBankCycle.budget gs Q w ms+1+(2*P1CompactNativeMeasured.capacity gs Q w+4)

theorem round_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (hh : ∀ i,H (bank i)=extraH pre.length out i)
    (ha : ∀ i,A (bank i)=word (P1CompactNativeMaster.words gs Q w)
      (P1CompactNativeMeasured.capacity gs Q w) (pre++stream (rawIndices ms)++tail) out i)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=P1CompactNativeMaster.words gs Q w j) :
    let appended:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (P1CompactNativeWidth.width gs Q))
    ∃ H' A',Step machine (budget gs Q w (rawIndices ms)) H A H' A' ∧
      (∀ i,H' (bank i)=extraH (pre.length+(stream (rawIndices ms)).length) appended i ∧
        A' (bank i)=word (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
          (pre++stream (rawIndices ms)++tail) appended i) ∧
      (∀ j,(∀ i,bank i≠j) → H' j=H j ∧ A' j=A j):=by
  dsimp only
  obtain ⟨J,B,run,fields,keep⟩:=P1CompactEstimatorBankCycle.cycle_run gs ms Q w out pre tail hw hQ H A hh ha
  have jh (j) : J (sources j)=0:=(keep (sources j) (fun i=>bank_source_ne i j)).1.trans (mh j)
  have ba (j) : B (sources j)=P1CompactNativeMaster.words gs Q w j:=
    (keep (sources j) (fun i=>bank_source_ne i j)).2.trans (ma j)
  obtain ⟨D,reload,df,_ds,dk⟩:=NativeReload.reload_retained_run (P1CompactNativeMaster.words gs Q w)
    (P1CompactNativeMeasured.capacity gs Q w) _ _ _ (P1CompactNativeMaster.words_fit gs Q w) J B jh ba
    (fun i=>(fields i).1) (fun i=>(fields i).2)
  refine ⟨J,D,run.seq reload,fun i=>⟨(fields i).1,df i⟩,?_⟩
  intro j hj
  exact ⟨(keep j hj).1,(dk j hj).trans (keep j hj).2⟩

end NearCubicWires.ExtIncidence.P1CompactNativeRound

/-! Canonical reusable states change only the source and append positions.
Every other ambient tape is the same actual initialized workspace. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeState
open NearCubicWires.ExtIncidence.NativeState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def heads (H : Fin 277→ℕ) (pos : ℕ) (out : List Bool):=
  dockH bank H (extraH pos out)
noncomputable def tapes (A : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool):=install bank A (word data C source out)

theorem heads_eq (H J : Fin 277→ℕ) (pos : ℕ) (out : List Bool)
    (hb : ∀ i,J (bank i)=extraH pos out i) (ho : ∀ j,(∀ i,bank i≠j) → J j=H j) :
    J=heads H pos out:=by
  classical
  funext j
  by_cases hit : ∃ i,bank i=j
  · obtain ⟨i,rfl⟩:=hit
    exact (hb i).trans (dockH_slot bank bank_injective H _ i).symm
  · have hn : ∀ i,bank i≠j:=by intro i hi;exact hit ⟨i,hi⟩
    exact (ho j hn).trans (dockH_other bank H _ j hn).symm

theorem tapes_eq (A B : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool)
    (hb : ∀ i,B (bank i)=word data C source out i) (ho : ∀ j,(∀ i,bank i≠j) → B j=A j) :
    B=tapes A data C source out:=by
  classical
  funext j
  by_cases hit : ∃ i,bank i=j
  · obtain ⟨i,rfl⟩:=hit
    exact (hb i).trans (install_slot bank bank_injective A _ i).symm
  · have hn : ∀ i,bank i≠j:=by intro i hi;exact hit ⟨i,hi⟩
    exact (ho j hn).trans (install_other bank A _ j hn).symm

theorem round_step {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=P1CompactNativeMaster.words gs Q w j) :
    let source:=pre++stream (rawIndices ms)++tail
    let data:=P1CompactNativeMaster.words gs Q w
    let C:=P1CompactNativeMeasured.capacity gs Q w
    let appended:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
      (MatrixScoreBatch.cutWord (P1CompactNativeWidth.width gs Q))
    Step P1CompactNativeRound.machine (P1CompactNativeRound.budget gs Q w (rawIndices ms))
      (heads H pre.length out) (tapes A data C source out)
      (heads H (pre.length+(stream (rawIndices ms)).length) appended) (tapes A data C source appended):=by
  dsimp only
  obtain ⟨J,B,run,fields,keep⟩:=P1CompactNativeRound.round_run gs ms Q w out pre tail hw hQ
    (heads H pre.length out) (tapes A _ _ _ out)
    (fun i=>dockH_slot bank bank_injective H _ i) (fun i=>install_slot bank bank_injective A _ i)
    (by intro j;exact (dockH_other bank H _ (sources j) (fun i=>P1CompactNativeRound.bank_source_ne i j)).trans (mh j))
    (by intro j;exact (install_other bank A _ (sources j) (fun i=>P1CompactNativeRound.bank_source_ne i j)).trans (ma j))
  exact run.congr
    (heads_eq H J _ _ (fun i=>(fields i).1) (fun j hj=>(keep j hj).1.trans (dockH_other bank H _ j hj)))
    (tapes_eq A B _ _ _ _ (fun i=>(fields i).2) (fun j hj=>(keep j hj).2.trans (install_other bank A _ j hj)))

end NearCubicWires.ExtIncidence.P1CompactNativeState

/-! The original raw polynomial family executes with one retained native
bank and one literal outer driver, including empty polynomials/families. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeFamily
open NearCubicWires.ExtIncidence.NativeFamily
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawWord {B : ℕ} (ms : List (List (Fin B))):=stream (rawIndices ms)
def emit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ)
    (ms : List (List (Fin gs.length))):=
  (P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
    (MatrixScoreBatch.cutWord (P1CompactNativeWidth.width gs Q))
def cost {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) :
    List (List (List (Fin gs.length)))→ℕ
  | []=>0
  | ms::ps=>max (P1CompactNativeRound.budget gs Q w (rawIndices ms)) (cost gs Q w ps)

theorem member_cost {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (ms : List (List (Fin gs.length))) (hm : ms∈ps) :
    P1CompactNativeRound.budget gs Q w (rawIndices ms) ≤ cost gs Q w ps:=by
  induction ps with
  | nil=>simp at hm
  | cons p ps ih=>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact (ih hm).trans (Nat.le_max_right _ _)

noncomputable def machine:=P1CompactCloseoutRowsDegreeLoop.machine P1CompactNativeRound.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))):=ps.length*(cost gs Q w ps+3)+3
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (pre tail : List Bool)
    (H : Fin 277→ℕ) (A : Fin 277→List Bool) (j : ℕ) (out : List Bool):=
    (⟨P1CompactNativeRound.machine.start,
      P1CompactNativeState.heads H (pre.length+((ps.take j).flatMap rawWord).length) out,
      P1CompactNativeState.tapes A (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
        (pre++ps.flatMap rawWord++tail) out⟩ : Configuration 277 _)

theorem family_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length))))
    (hmask : ∀ ms∈ps, P1MaskDegree gs (rawRows ms)) (out pre tail : List Bool)
    (hw : ∀ ms∈ps,ms.length < 2^w) (hQ : 1 ≤ Q) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (mh : ∀ j,H (sources j)=0) (ma : ∀ j,A (sources j)=P1CompactNativeMaster.words gs Q w j) :
    ∃ actual,runFrom machine (budget gs Q w ps)
      (RepeatMachine.cfg 0 (entry gs Q w ps pre tail H A 0 out) ps.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry gs Q w ps pre tail H A ps.length (out++ps.flatMap (emit gs Q w))) ps.length 1 ∧
      actual.steps ≤ budget gs Q w ps:=by
  let packet:=fun j=>ps.getD j []
  let output:=fun j=>emit gs Q w (packet j)
  have supplier : ∀ j<ps.length,∀ acc,∃ actual,
      runFrom P1CompactNativeRound.machine (cost gs Q w ps) (entry gs Q w ps pre tail H A j acc)=some actual ∧
      actual.final.heads=(entry gs Q w ps pre tail H A (j+1) (acc++output j)).heads ∧
      actual.final.tapes=(entry gs Q w ps pre tail H A (j+1) (acc++output j)).tapes ∧
      actual.steps ≤ cost gs Q w ps:=by
    intro j hj acc
    have hm : packet j∈ps:=by
      dsimp only [packet]
      rw [List.getD_eq_getElem ps [] hj]
      exact List.getElem_mem hj
    let before:=pre++(ps.take j).flatMap rawWord
    let after:=(ps.drop (j+1)).flatMap rawWord++tail
    have hs : before++rawWord (packet j)++after=pre++ps.flatMap rawWord++tail:=by
      rw [P1CompactCloseoutRowsFamilyLoop.split_word ps [] rawWord j hj]
      simp only [before,after,packet,List.append_assoc]
    have hp : before.length=pre.length+((ps.take j).flatMap rawWord).length:=List.length_append
    have hn : before.length+(rawWord (packet j)).length=
        pre.length+((ps.take (j+1)).flatMap rawWord).length:=by
      dsimp only [packet]
      rw [P1CompactCloseoutRowsFamilyLoop.next_word ps [] rawWord j hj,hp]
      omega
    letI := hmask (packet j) hm
    have run:=P1CompactNativeState.round_step gs (packet j) Q w acc before after (hw _ hm) hQ H A mh ma
    dsimp only at run
    change Step P1CompactNativeRound.machine _ (P1CompactNativeState.heads H before.length acc)
      (P1CompactNativeState.tapes A _ _ (before++rawWord (packet j)++after) acc)
      (P1CompactNativeState.heads H (before.length+(rawWord (packet j)).length) (acc++output j))
      (P1CompactNativeState.tapes A _ _ (before++rawWord (packet j)++after) (acc++output j)) at run
    rw [hs,hn,hp] at run
    exact run.enlarge (member_cost gs Q w ps (packet j) hm)
  obtain ⟨actual,run,final,bound⟩:=P1CompactCloseoutRowsDegreeLoop.loop_run P1CompactNativeRound.machine
    (entry gs Q w ps pre tail H A) output (cost gs Q w ps) ps.length
    (by intro j hj acc;rfl) supplier out
  have he : (List.range ps.length).flatMap output=ps.flatMap (emit gs Q w):=
    P1CompactCloseoutRowsFamilyLoop.flatMap_index ps [] (emit gs Q w)
  rw [he] at final
  exact ⟨actual,run,final,bound⟩

end NearCubicWires.ExtIncidence.P1CompactNativeFamily

namespace NearCubicWires.ExtIncidence
theorem p1CompactNativeFamily_machine_unchanged :
    P1CompactNativeFamily.machine = NativeFamily.machine := rfl
end NearCubicWires.ExtIncidence
