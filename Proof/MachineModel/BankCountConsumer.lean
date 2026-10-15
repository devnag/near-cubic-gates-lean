import Proof.MachineModel.BankCountNative
import Proof.MachineModel.CountIndexBudget

/-! Execute count metadata and the original polynomial worker on the same
actual incidence table. No last-index word is supplied to this consumer. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def consumer:=RecoveryFocus.machine old CloseoutRowsBankPolynomial.machine
noncomputable def counted:=Composition.machine machine consumer
def budget (C Q w M : ℕ):=CountIndexClean.budget C w M+1+CloseoutRowsBankPolynomial.budget Q C

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (rows : List (List Bool)) (p F Q w : ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length) (hw : rows.length<2^w)
    (hQ : 1≤Q) (hQp : Q≤p) (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (slots j)=0)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input
      (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w rows.length j)
    (hheads : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w
        (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (ht : A 36=ZeroPadding.pad (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) rows.flatten) :
    let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom counted (budget C Q w rows.length) ⟨counted.start,H,A⟩=some result ∧
      result.steps≤budget C Q w rows.length ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      (∀ i,(∀ j,old j≠i) → result.final.heads i=H i ∧
        result.final.tapes i=changed A C w rows.length i) := by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  obtain ⟨a,ar,ah,atape,ast⟩:=count_run C w rows.length hM hw
    (CountIndex.fits (l+r) p F w gs.length Q rows.length hQ hw.le) H A hh ha
  have at' : a.final.tapes=changed A C w rows.length:=atape.trans (replaced A C w rows.length ha)
  obtain ⟨b,br,bh,bo,bc,bst⟩:=CloseoutRowsBankPolynomial.polynomial_run gs p F Q w rows out hl hM hw hQp hp hF
  have nh : ∀ i,H (old i)=(CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).heads i:=by
    intro i
    rw [BankFields.heads]
    exact hheads i
  have nt:=native_tapes gs p F Q w rows out hl hw.le hF A hbase ht
  obtain ⟨last,lastRun,_lf,_ls,lh,lt,keep⟩:=RecoveryFocus.dock old old_injective
    CloseoutRowsBankPolynomial.machine _ H (changed A C w rows.length) _ nh nt b br
  have restart : Composition.restart a.final consumer.start=
      ⟨consumer.start,H,changed A C w rows.length⟩:=by
    apply configuration_ext
    · rfl
    · exact ah
    · exact at'
  change runFrom consumer (CloseoutRowsBankPolynomial.budget Q C)
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

end NearCubicWires.ExtIncidence.BankCount
