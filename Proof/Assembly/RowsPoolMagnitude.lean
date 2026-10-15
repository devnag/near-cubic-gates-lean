import Proof.Assembly.RowsPoolWeightLoop
import Proof.Supplier.RowPowerBlockMeaning
import Proof.MachineModel.OrdinaryMatrixScoreWeightLayout

/-! The original native signed-field worker supplies both scalar parts of a
weight. Its output heads are returned before the live-negative accumulator;
the source cursor alone remains advanced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMagnitude
open LocalBitMultitape RecoveryExecution RepairRepresentation SignedSortKey
open ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 12) := decide (i≠0)
def caps (C : ℕ) (i : Fin 12) := if i=0 ∨ i=9 then 0 else C
noncomputable def machine := MaskedReset.machine RowPowerNative.machine selected
def budget (z : ℤ) (w : ℕ) := 2*RowPowerNativeReset.rawTime z w+2
def heads (pos : ℕ) : Fin 13→ℕ := fun i=>if i=0 then pos else 0
def input (source : List Bool) (w C : ℕ) : Fin 13→List Bool :=
  fun i=>if i=0 then source else if i=9 then List.replicate w true else List.replicate C false
noncomputable def output (source : List Bool) (pos w C : ℕ) (z : ℤ) : Fin 13→List Bool :=
  Fin.addCases (m:=12) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i)
      ((RowPowerNative.output source pos w (binary (natBitLength z.natAbs) z.natAbs)
        (decide (z<0)) [] []).tapes i))
    (fun _ : Fin 1=>List.replicate C false)

theorem native_run (pre tail : List Bool) (w C : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) :
    Step machine (budget z w) (heads pre.length)
      (input (pre++intWord z++tail) w C)
      (heads (pre.length+(intWord z).length))
      (output (pre++intWord z++tail) (pre.length+(intWord z).length) w C z) := by
  obtain ⟨r,hr,rf,_⟩:=RowPowerNative.field_run pre tail [] [] z w
  have first:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have padded:=first.pad (caps C)
  have all:=padded.mask (cap:=C) selected (by
    intro i hi
    have hn : i≠0:=of_decide_eq_true hi
    fin_cases i <;> first | contradiction | rfl) (by
      unfold RowPowerNativeReset.rawTime at hC
      omega)
  apply all.congr_in ?_ ?_ |>.congr ?_ rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;>
      simp [input,RowPowerNative.extraTapes,
        DecompositionNativeMagnitude.input,TapeEmbedding.config,Composition.leftConfig,
        Fin.addCases,ZeroPadding.pad,caps]
  · funext i
    fin_cases i <;>
      simp [heads,selected,RowPowerNative.output_heads,Fin.addCases]

theorem source (source : List Bool) (pos w C : ℕ) (z : ℤ) :
    output source pos w C z 0=source := by
  change ZeroPadding.pad 0 ((RowPowerNative.output source pos w
    (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) [] []).tapes 0)=_
  rw [RowPowerNativeReusable.raw_output_live _ _ _ _ _ _ 0 (by simp)]
  simp [ZeroPadding.pad]

theorem width (source : List Bool) (pos w C : ℕ) (z : ℤ) :
    output source pos w C z 9=List.replicate w true := by
  change ZeroPadding.pad 0 ((RowPowerNative.output source pos w
    (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) [] []).tapes 9)=_
  rw [RowPowerNativeReusable.raw_output_live _ _ _ _ _ _ 9 (by simp)]
  simp [ZeroPadding.pad]

theorem parts (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (hw : natBitLength z.natAbs≤w) :
    output source pos w C z 10=MatrixScoreWeight.scalar C w z.toNat ∧
    output source pos w C z 11=MatrixScoreWeight.scalar C w (-z).toNat := by
  have hb:=RowPowerNativeReusable.block_binary w z hw
  constructor
  · change ZeroPadding.pad C ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) [] []).tapes 10)=_
    rw [RowPowerNativeReusable.raw_output_live _ _ _ _ _ _ 10 (by simp)]
    change ZeroPadding.pad C (Streaming.marks (RowPowerNativeReusable.block w z false)++[false])=_
    rw [hb.1]
    apply congrArg (ZeroPadding.pad C)
    simpa only [List.append_nil,show RepairOrdinary.frame []=[false] from rfl] using
      (Streaming.frame_append (binary w z.toNat) []).symm
  · change ZeroPadding.pad C ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) [] []).tapes 11)=_
    rw [RowPowerNativeReusable.raw_output_live _ _ _ _ _ _ 11 (by simp)]
    change ZeroPadding.pad C (Streaming.marks (RowPowerNativeReusable.block w z true)++[false])=_
    rw [hb.2]
    apply congrArg (ZeroPadding.pad C)
    simpa only [List.append_nil,show RepairOrdinary.frame []=[false] from rfl] using
      (Streaming.frame_append (binary w (-z).toNat) []).symm

theorem support (pre tail : List Bool) (w C : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) (i : Fin 13) (hi : i≠0 ∧ i≠9) :
    (output (pre++intWord z++tail) (pre.length+(intWord z).length) w C z i).length≤C := by
  obtain ⟨r,hr,rf,rs⟩:=RowPowerNative.field_run pre tail [] [] z w
  have localSupport (j : Fin 12) (hj : j≠0 ∧ j≠9) : (r.final.tapes j).length≤C := by
    have hh : (RowPowerNative.entry (pre++intWord z++tail) pre.length w [] []).heads j=0 := by
      fin_cases j <;> first | exact False.elim (hj.1 rfl) | rfl
    have ht : (RowPowerNative.entry (pre++intWord z++tail) pre.length w [] []).tapes j=[] := by
      fin_cases j <;> first | exact False.elim (hj.1 rfl) | exact False.elim (hj.2 rfl) | rfl
    have h:=PCPSerializerReuse.tape_support _ _ _ r hr j 0 0
      (by rw [hh]) (by rw [ht];simp)
    rw [rs] at h
    unfold RowPowerNativeReset.rawTime at hC
    omega
  revert hi
  refine Fin.addCases (m:=12) (n:=1) (fun j=>?_) (fun j=>?_) i
  · intro hi
    have hj : j≠0 ∧ j≠9 := by
      constructor
      · intro h;apply hi.1;subst j;rfl
      · intro h;apply hi.2;subst j;rfl
    simp only [output,Fin.addCases_left]
    rw [caps,if_neg (by tauto),ZeroPadding.pad_length]
    apply max_le le_rfl
    rw [←rf]
    exact localSupport j hj
  · intro _
    simp only [output,Fin.addCases_right,List.length_replicate]
    exact le_rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMagnitude
