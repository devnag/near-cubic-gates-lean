import Proof.CaseAnalysis.RowsOriginalMetadata
import Proof.CaseAnalysis.RowsOriginalBounds

/-! One concrete template writer, unit initializer, original-term product
loop, and metadata writer compose into a single ordinary program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsOriginalTemplates
open CloseoutRowsRawAtomSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (C : ℕ) (indices : Fin 2→ℕ) (metadata : Fin 4→List Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=4) (n:=4) (motive:=fun _=>List Bool)
    ![ZeroPadding.pad C (List.replicate (indices 0) true),ZeroPadding.pad C (List.replicate (indices 1) true),
      List.replicate C false,List.replicate C false] metadata
def heads (pos a b : ℕ) : Fin 18→ℕ:=Fin.addCases (m:=10) (n:=8) (motive:=fun _=>ℕ)
  (SubstitutionFactor.heads pos)
  (Fin.addCases (m:=4) (n:=4) (motive:=fun _=>ℕ) (fun _=>0) (CloseoutRowsOriginalMetadata.heads a b))
def data (C : ℕ) (indices : Fin 2→ℕ) (source cache acc : List Bool) (metadata : Fin 4→List Bool) : Fin 18→List Bool:=
  Fin.addCases (m:=10) (n:=8) (motive:=fun _=>List Bool)
    (SubstitutionFactor.data C (ZeroPadding.pad C source) cache [] acc []) (extra C indices metadata)
def writerSlots : Fin 5→Fin 18:=![10,11,0,12,13]
def unitSlots : Fin 2→Fin 18:=![3,8]
def metaSlots (i : Fin 4) : Fin 18:=⟨i.val+14,by omega⟩
noncomputable def writer (r : Row):=RecoveryFocus.machine writerSlots (CloseoutRowsOriginalWriter.readyMachine r.factors)
noncomputable def unit:=RecoveryFocus.machine unitSlots SubstitutionAppend.unitMachine
noncomputable def inner:=TapeEmbedding.machine 8 CloseoutRowsOriginalMonomial.machine
noncomputable def metadata (r : Row):=RecoveryFocus.machine metaSlots (CloseoutRowsOriginalMetadata.machine r)
noncomputable def machine (r : Row):=Composition.machine (Composition.machine (Composition.machine (writer r) unit) inner) (metadata r)
def budget (r : Row) (R : ℕ) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ)
    (valid : CloseoutRowsOriginalMonomial.Valid cs (r.factors.map indices)):=
  (2*CloseoutRowsOriginalWriter.budget indices r.factors+2)+1+8+1+
    CloseoutRowsOriginalMonomial.budget R cs (r.factors.map indices) valid [[]]+1+CloseoutRowsOriginalMetadata.budget r

theorem run (r : Row) (C R B : ℕ) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ)
    (valid : CloseoutRowsOriginalMonomial.Valid cs (r.factors.map indices))
    (hb : ∀ side,indices side≤B) (hl : r.factors.length≤4) (hw : 8*B+37≤C)
    (hc : CloseoutRowsOriginalCache.capacity cs≤C)
    (hf : CloseoutRowsOriginalMonomial.Fits C R cs (r.factors.map indices) valid [[]]) :
    Step (machine r) (budget r R cs indices valid) (heads 0 0 0)
      (data C indices [] (cacheWord cs) [] (CloseoutRowsOriginalMetadata.data C [] [] []))
      (heads ((r.factors.map indices).flatMap ExtIncidence.block).length 17 1)
      (data C indices (CloseoutRowsOriginalWriter.indicesWord indices r.factors) (cacheWord cs)
        (ExtIncidence.stream (CloseoutRowsOriginalMonomial.value cs (r.factors.map indices) valid [[]]))
        (CloseoutRowsOriginalMetadata.data C (CloseoutRowsOriginalMetadata.rho r)
          (CloseoutRowsOriginalMetadata.count r) (CloseoutRowsOriginalMetadata.parity r))) := by
  let source:=CloseoutRowsOriginalWriter.indicesWord indices r.factors
  let cold:=CloseoutRowsOriginalMetadata.data C [] [] []
  have first : Step (writer r) (2*CloseoutRowsOriginalWriter.budget indices r.factors+2)
      (heads 0 0 0) (data C indices [] (cacheWord cs) [] cold)
      (heads 0 0 0) (data C indices source (cacheWord cs) [] cold) := by
    refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _
      (CloseoutRowsOriginalWriter.ready_run C B indices r.factors hb hl hw) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 2 rfl))
  have second : Step unit 8 (heads 0 0 0) (data C indices source (cacheWord cs) [] cold)
      (heads 0 0 0) (data C indices source (cacheWord cs) (ExtIncidence.stream [[]]) cold) := by
    refine SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _
      (SubstitutionAppend.unit_run C (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl))
  have raw:=CloseoutRowsOriginalMonomial.run C R cs (r.factors.map indices) valid [] [] [[]] hc hf
  have padded:=raw.pad (fun i=>if i=0 then C else 0)
  have third : Step inner (CloseoutRowsOriginalMonomial.budget R cs (r.factors.map indices) valid [[]])
      (heads 0 0 0) (data C indices source (cacheWord cs) (ExtIncidence.stream [[]]) cold)
      (heads ((r.factors.map indices).flatMap ExtIncidence.block).length 0 0)
      (data C indices source (cacheWord cs)
        (ExtIncidence.stream (CloseoutRowsOriginalMonomial.value cs (r.factors.map indices) valid [[]])) cold) := by
    have lifted:=padded.embed (fun _ : Fin 8=>0) (extra C indices cold)
    apply (lifted.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i
    all_goals simp [heads,data,source,CloseoutRowsOriginalWriter.indicesWord,SubstitutionFactor.heads,
      SubstitutionFactor.data,Fin.addCases,CloseoutRowsOriginalMetadata.heads,ZeroPadding.pad_zero]
  have fourth : Step (metadata r) (CloseoutRowsOriginalMetadata.budget r)
      (heads ((r.factors.map indices).flatMap ExtIncidence.block).length 0 0)
      (data C indices source (cacheWord cs)
        (ExtIncidence.stream (CloseoutRowsOriginalMonomial.value cs (r.factors.map indices) valid [[]])) cold)
      (heads ((r.factors.map indices).flatMap ExtIncidence.block).length (CloseoutRowsOriginalMetadata.rho r).length 1)
      (data C indices source (cacheWord cs)
        (ExtIncidence.stream (CloseoutRowsOriginalMonomial.value cs (r.factors.map indices) valid [[]]))
        (CloseoutRowsOriginalMetadata.data C (CloseoutRowsOriginalMetadata.rho r)
          (CloseoutRowsOriginalMetadata.count r) (CloseoutRowsOriginalMetadata.parity r))) := by
    refine SubstitutionDock.run _ _ (by intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h;dsimp [metaSlots] at hv;omega)
      _ _ _ _ _ _ _ _ (CloseoutRowsOriginalMetadata.run r C (by
        simp only [CloseoutRowsOriginalMetadata.count,RepairSource.VerifierDecoding.CompareMachine.word,List.length_cons,List.length_replicate];omega) (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
    | (intro j;fin_cases j <;>rfl)
    | (intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl))
  have whole:=((first.seq second).seq third).seq fourth
  exact whole.congr (by rw [CloseoutRowsOriginalMetadata.rho_length]) rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer
