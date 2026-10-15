import Proof.CaseAnalysis.RowsOriginalWriterReady
import Proof.CaseAnalysis.RowsEstimatorSubstitutionAppend
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead

/-! Actual constant metadata for one of the finitely many paper templates.
The coefficient prefix is the consumer's width-three rational record. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMetadata
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution CloseoutRowsEstimator CloseoutRowsOriginalTemplates
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rho (r : Row):=CloseoutRowsEstimatorCoefficients.Product.record 3 r.rho
def count (r : Row):=CompareMachine.word r.factors.length
def parity (r : Row) : List Bool:=[r.parity.isSome,decide (r.parity=some 1)]
def data (C : ℕ) (a b c : List Bool) : Fin 4→List Bool:=
  ![ZeroPadding.pad C a,ZeroPadding.pad C b,ZeroPadding.pad C c,List.replicate C false]
def heads (a b : ℕ) : Fin 4→ℕ:=![a,b,0,0]
def rhoSlots : Fin 1→Fin 4:=fun _=>0
def countSlots : Fin 2→Fin 4:=![1,3]
def paritySlots : Fin 2→Fin 4:=![2,3]
noncomputable def writeRho (r : Row):=RecoveryFocus.machine rhoSlots (HierarchyFixedWord.raw (rho r))
noncomputable def writeCount (r : Row):=RecoveryFocus.machine countSlots (HierarchyFixedWord.machine (count r))
noncomputable def writeParity (r : Row):=RecoveryFocus.machine paritySlots (HierarchyFixedWord.machine (parity r))
def advance : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.stay,.right,.stay,.stay]⟩ else none
noncomputable def machine (r : Row):=Composition.machine
  (Composition.machine (Composition.machine (writeRho r) (writeCount r)) (writeParity r)) advance
def budget (r : Row):=(rho r).length+1+(2*(count r).length+2)+1+(2*(parity r).length+2)+1+1

theorem raw_run (bits : List Bool) (C : ℕ) :
    Step (HierarchyFixedWord.raw bits) bits.length (fun _=>0) (fun _=>List.replicate C false)
      (fun _=>bits.length) (fun _=>ZeroPadding.pad C bits) := by
  obtain ⟨r,hr,rf,_⟩:=(HierarchyFixedWord.write_prefix bits 0 bits.length (by omega)).run
    (by simp [HierarchyFixedWord.raw,HierarchyFixedWord.cfg])
  have raw:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa only [HierarchyFixedWord.cfg,List.take_zero,List.take_length,
    show ZeroPadding.pad C ([] : List Bool)=List.replicate C false from rfl] using raw.pad (fun _=>C)

theorem fixed_run (bits : List Bool) (C : ℕ) (hc : bits.length≤C) :
    Step (HierarchyFixedWord.machine bits) (2*bits.length+2) (fun _=>0) (fun _=>List.replicate C false)
      (fun _=>0) (![ZeroPadding.pad C bits,List.replicate C false] : Fin 2→List Bool) := by
  have raw:=(Step.of_ready (HierarchyFixedWord.word_ready bits)).pad (fun _=>C)
  apply (raw.congr_in rfl ?_).congr rfl ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i
    · rfl
    · exact SubstitutionErase.false_pad bits.length C hc

theorem run (r : Row) (C : ℕ) (hc : (count r).length≤C) (hp : 2≤C) :
    Step (machine r) (budget r) (heads 0 0) (data C [] [] [])
      (heads (rho r).length 1) (data C (rho r) (count r) (parity r)) := by
  have first : Step (writeRho r) (rho r).length (heads 0 0) (data C [] [] [])
      (heads (rho r).length 0) (data C (rho r) [] []) := by
    refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (raw_run (rho r) C) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))
  have second : Step (writeCount r) (2*(count r).length+2) (heads (rho r).length 0) (data C (rho r) [] [])
      (heads (rho r).length 0) (data C (rho r) (count r) []) := by
    refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (fixed_run (count r) C hc) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))
  have third : Step (writeParity r) (2*(parity r).length+2) (heads (rho r).length 0) (data C (rho r) (count r) [])
      (heads (rho r).length 0) (data C (rho r) (count r) (parity r)) := by
    refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (fixed_run (parity r) C hp) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))
  have hs : step advance ⟨0,heads (rho r).length 0,data C (rho r) (count r) (parity r)⟩=
      some ⟨1,heads (rho r).length 1,data C (rho r) (count r) (parity r)⟩ := by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  obtain ⟨last,hl,lf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ((first.seq second).seq third).seq (Step.of_run hl (congrArg Configuration.heads lf) (congrArg Configuration.tapes lf))

theorem rho_length (r : Row) : (rho r).length=17 := CloseoutRowsEstimatorCoefficients.Product.record_length 3 r.rho

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMetadata
