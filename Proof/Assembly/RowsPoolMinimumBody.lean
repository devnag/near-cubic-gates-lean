import Proof.Assembly.RowsPoolMinimumMeaning

/-! One actual original weight is read, conditionally accumulated, and its
workspace erased. The capacity premise concerns the scalar reader only;
it never requires a C-cell sweep to fit within C steps. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance : Machine 20 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun _ _=>some ⟨1,fun _=>none,fun i=>if i=13 then .right else .stay⟩
noncomputable def readAdd:=Composition.machine reader choice
noncomputable def advanced:=Composition.machine readAdd advance
noncomputable def body:=Composition.machine advanced erase
def bodyBudget (z : ℤ) (w C : ℕ):=12*natBitLength z.natAbs+16*w+2*C+47
def uniformBudget (w C : ℕ):=28*w+2*C+47

theorem advance_run (A : Fin 20→List Bool) (pos mpos : ℕ) :
    Step advance 1 (heads pos mpos) A (heads pos (mpos+1)) A:=by
  have h:step advance ⟨0,heads pos mpos,A⟩=some ⟨1,heads pos (mpos+1),A⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem body_run (pre tail mpre mtail : List Bool) (z : ℤ) (live : Bool) (w C a : ℕ)
    (hw : natBitLength z.natAbs≤w) (hc : 8*w+12≤C) (hf : (-z).toNat+a<2^w) :
    Step body (bodyBudget z w C) (heads pre.length mpre.length)
      (data (pre++intWord z++tail) (mpre++live::mtail) w C a)
      (heads (pre.length+(intWord z).length) (mpre.length+1))
      (data (pre++intWord z++tail) (mpre++live::mtail) w C
        (a+if live then (-z).toNat else 0)):=by
  have hC:RowPowerNativeReset.rawTime z w+1≤C:=by
    unfold RowPowerNativeReset.rawTime
    omega
  let source:=pre++intWord z++tail
  let mask:=mpre++live::mtail
  let pos:=pre.length+(intWord z).length
  let A:=parsed source mask pos w C a z
  let B:=added C w (-z).toNat a live A
  have read:=read_run pre tail mask mpre.length w C a z hC
  have add:=choice_run C w (-z).toNat a (heads pos mpre.length) A live (by omega) hf
    (by intro j;fin_cases j <;> rfl)
    (parsed_input source mask pos w C a z hw)
    (Streaming.read_append mpre mtail live)
  have joined:=read.seq add |>.seq (advance_run B pos mpre.length)
  have eraseCall:=clear_run C (heads pos (mpre.length+1)) B
    (by intro j;fin_cases j <;> rfl)
    (added_support C w (-z).toNat a live A (by omega)
      (parsed_support pre tail mask w C a z hC))
    (by
      change added C w (-z).toNat a live A 18=_
      rw [added_other C w (-z).toNat a live A 18 (by intro j;fin_cases j <;> decide)]
      rfl)
    (by
      change added C w (-z).toNat a live A 19=_
      rw [added_other C w (-z).toNat a live A 19 (by intro j;fin_cases j <;> decide)]
      rfl)
  have complete:=joined.seq eraseCall
  have ht:((CloseoutRowsPoolMagnitude.budget z w+1+budget w)+1+1)+1+(2*C+4)=bodyBudget z w C:=by
    unfold CloseoutRowsPoolMagnitude.budget RowPowerNativeReset.rawTime budget bodyBudget
    omega
  rw [ht] at complete
  exact complete.congr rfl (cleared_added source mask pos w C a z live)

theorem body_bound (z : ℤ) (w C : ℕ) (hw : natBitLength z.natAbs≤w) :
    bodyBudget z w C≤uniformBudget w C:=by
  unfold bodyBudget uniformBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
