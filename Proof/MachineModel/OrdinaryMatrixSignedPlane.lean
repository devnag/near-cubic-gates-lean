import Proof.MachineModel.OrdinaryMatrixMaskSemantics

/-! The actual retained-mask AND pass now supplies the exact signed left
Boolean plane used by the corrected Williams request. The original left
plane and mask are returned at head zero for the following plane call. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedPlane
open LocalBitMultitape MatrixScoreBatch SupplierPrinter
open MatrixMaskSemantics (mask cell)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def row (r : Request) (i : Fin r.U) := List.ofFn (fun inner : Fin r.Capacity =>
  LeftPlaneCell.coefficientBit false (padSignedInner (Capacity := r.Capacity) (MatrixBucketLeftPlane.left r) i inner) 0)
noncomputable def rows (r : Request) := List.ofFn (row r)
noncomputable def plane (r : Request) (negative : Bool) (t : ℕ) :=
  WilliamsLoaderForms.rowMajorBitMatrix (fun i j => LeftPlaneCell.coefficientBit negative (signedLeft r i j) t)

theorem row_length (r : Request) (i : Fin r.U) : (row r i).length=r.Capacity := by simp [row]
theorem rows_length (r : Request) : (rows r).length=r.U := by simp [rows]
theorem rows_flatten (r : Request) : (rows r).flatten=MatrixBucketLeftPlane.plane r := rfl

theorem row_values (r : Request) (negative : Bool) (t : ℕ) (i : Fin r.U) :
    MatrixMaskAndRow.values ((mask r negative t).zip (row r i))=
      List.ofFn (fun inner : Fin r.Capacity => LeftPlaneCell.coefficientBit negative (signedLeft r i inner) t) := by
  apply List.ext_getElem
  · simp [MatrixMaskAndRow.values,MatrixMaskSemantics.mask_length,row_length]
  · intro j hj hk
    have hjc : j<r.Capacity := by simpa using hk
    have hm : j<(mask r negative t).length := by rw [MatrixMaskSemantics.mask_length]; exact hjc
    have hr := MatrixMaskSemantics.mask_read r negative t ⟨j,hjc⟩
    simp only [readTapeBit,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hm,Option.getD_some] at hr
    simp only [MatrixMaskAndRow.values,List.getElem_map,List.getElem_zip,List.getElem_ofFn,row]
    rw [hr,MatrixMaskSemantics.signed_cell]
    exact Bool.and_comm _ _

theorem output_eq (r : Request) (negative : Bool) (t : ℕ) :
    MatrixMaskAndLoop.output (mask r negative t) (rows r)=plane r negative t := by
  simp only [MatrixMaskAndLoop.output,rows,List.flatMap_def,List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => MatrixMaskAndRow.values ((mask r negative t).zip (row r i)))).flatten=_
  apply congrArg List.flatten
  exact congrArg List.ofFn (funext (row_values r negative t))

noncomputable def input (r : Request) (negative : Bool) (t : ℕ) := MatrixMaskAndPass.input (mask r negative t) (rows r)
def budget (r : Request) := MatrixMaskAndPass.budget r.Capacity r.U

theorem plane_run (r : Request) (negative : Bool) (t : ℕ) : ∃ actual,
    runFrom MatrixMaskAndPass.machine (budget r) (input r negative t)=some actual ∧
    (∀ i : Fin 5,actual.final.tapes (i.castAdd 1)=
      (![UnaryTemplate.tape r.Capacity,mask r negative t,MatrixBucketLeftPlane.plane r,plane r negative t,
        UnaryTemplate.tape r.U] : Fin 5 → List Bool) i) ∧
    (∀ i : Fin 5,actual.final.heads (i.castAdd 1)=(![1,0,0,0,1] : Fin 5 → ℕ) i) ∧
    actual.final.heads 5=0 ∧
    (∃ n,actual.final.tapes 5=List.replicate n false ∧ n≤MatrixMaskAndLoop.nativeBudget r.Capacity r.U) ∧
    actual.steps≤budget r := by
  have hwidth : ∀ bits ∈ rows r,bits.length=(mask r negative t).length := by
    intro bits hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [row_length,MatrixMaskSemantics.mask_length]
  obtain ⟨actual,ha,af,ah,al,az,as⟩ := MatrixMaskAndPass.pass_run (mask r negative t) (rows r) hwidth
  rw [MatrixMaskSemantics.mask_length,rows_length] at ha az as
  refine ⟨actual,ha,?_,ah,al,az,as⟩
  intro i
  rw [af,MatrixMaskSemantics.mask_length,rows_length,rows_flatten,output_eq]

end NearCubicWires.RepairOrdinary.MatrixSignedPlane
