import Proof.CaseAnalysis.RowsGateNativePrefix
import Proof.CaseAnalysis.RowsGateSupportAppend
import Proof.CaseAnalysis.RowsStrictNative
import Proof.PCP.PCPPNativeFrame

/-! One request cursor joins the paid arity, the same supported weights,
and the actual strict threshold. Work banks are disjoint; only their input
ports and the live output cursor are exposed to the enclosing proof. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
open LocalBitMultitape RepairRepresentation CloseoutRowsGateSupport
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportSlots : Fin 6 → Fin 38 := ![0,24,23,2,25,1]
def strictSlots (i : Fin 15) : Fin 38 :=
  if i.val=0 then 4 else if i.val=10 then 3 else if h14 : i.val=14 then 23
  else if hs : i.val < 10 then ⟨i.val+25,by omega⟩ else ⟨i.val+24,by omega⟩
theorem support_injective : Function.Injective supportSlots := by decide
theorem strict_injective : Function.Injective strictSlots := by decide
theorem strict_fresh (i : Fin 15) (h0 : i.val≠0) (h10 : i.val≠10) (h14 : i.val≠14) :
    26 ≤ (strictSlots i).val := by
  unfold strictSlots
  split_ifs <;> simp <;> omega
def fieldsInput (fields : List (Bool×List Bool)) (membership source : List Bool) (n : ℕ) :
    Fin 5 → List Bool :=
  ![fields.flatMap fieldWord,CompareMachine.word fields.length,frame membership,source,frame n.bits]
def input (fields : List (Bool×List Bool)) (membership source : List Bool) (n : ℕ) :
    Fin 38 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (24+14) => List Bool)
    (CloseoutRowsGateNativePrefix.input (fieldsInput fields membership source n)) (fun _ => [])
noncomputable def prefixMachine (compressed : Bool) :=
  TapeEmbedding.machine 14 (CloseoutRowsGateNativePrefix.machine compressed)
noncomputable def support (compressed : Bool) := RecoveryFocus.machine supportSlots (preparedMachine compressed)
noncomputable def first (compressed : Bool) := Composition.machine (prefixMachine compressed) (support compressed)
noncomputable def strict := RecoveryFocus.machine strictSlots CloseoutRowsStrictNative.machine
noncomputable def machine (compressed : Bool) := Composition.machine (first compressed) strict
def arity (compressed : Bool) (fields : List (Bool×List Bool)) (membership : List Bool) :=
  CloseoutRowsGateNativePrefix.arity compressed fields.length membership
def weights (compressed : Bool) (fields : List (Bool×List Bool)) (membership : List Bool) :=
  (List.range fields.length).flatMap (emission compressed fields membership)
def word (compressed : Bool) (fields : List (Bool×List Bool)) (membership source : List Bool) (n : ℕ) :=
  natWord (arity compressed fields membership)++weights compressed fields membership++
    CloseoutRowsStrictNative.produced source n
def budget (compressed : Bool) (fields : List (Bool×List Bool)) (membership : List Bool) (n w : ℕ) :=
  CloseoutRowsGateNativePrefix.budget compressed fields.length membership+1+
    preparedBudget w fields.length+1+CloseoutRowsStrictNative.budget n

theorem strict_entry_heads (source out : List Bool) (n : ℕ) (i : Fin 15) :
    (CloseoutRowsStrictNative.entry source n [] out).heads i=if i.val=14 then out.length else 0 := by
  fin_cases i <;> rfl
theorem strict_entry_tapes (source out : List Bool) (n : ℕ) (i : Fin 15) :
    (CloseoutRowsStrictNative.entry source n [] out).tapes i=
      if i.val=0 then frame n.bits else if i.val=10 then source else if i.val=14 then out else [] := by
  fin_cases i <;> rfl

theorem strict_forward : CursorRestore.NoLeft CloseoutRowsStrictNative.machine 14 := by
  apply CursorRestore.composition_forward
  · exact EquationRowRaw.embedded_extra_forward CloseoutRowsStrictThreshold.machine (1 : Fin 2)
  · apply CursorRestore.focus_forward CloseoutRowsStrictNative.slots CloseoutRowsStrictNative.slots_injective
      CloseoutRowsSignedAppend.machine 3
    apply CursorRestore.composition_forward
    · intro q bits a ha
      fin_cases q <;> simp [CloseoutRowsSignedAppend.sign] at ha <;> cases ha <;> simp
    · exact CursorRestore.focus_forward CloseoutRowsSignedAppend.copySlots
        CloseoutRowsSignedAppend.copy_injective CloseoutWitness.NativeAppend.machine 2
        EquationRowRaw.header_field_forward

theorem output_forward (compressed : Bool) : CursorRestore.NoLeft (machine compressed) 23 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 14 (CloseoutRowsGateNativePrefix.machine compressed) 23
        (CloseoutRowsGateNativePrefix.output_forward compressed))
      (CursorRestore.focus_forward supportSlots support_injective _ 2 (append_forward compressed)))
    (CursorRestore.focus_forward strictSlots strict_injective _ 14 strict_forward)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
