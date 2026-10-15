import Proof.Hierarchy.CompetitorOddRowSliceDock

/-! Exact original row-major projection. Selecting the lower half of each
row is zeroing the last little-endian right coordinate; coefficients and
count values are unchanged. This is the existing raw fixed-Q codec. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open SourceInterfaces WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstColumn {u : ℕ} (he : u/2+u/2=u) (j : Fin (u/2)) : Fin u :=
  Fin.cast he (j.castAdd (u/2))
def lastColumn {u : ℕ} (he : u/2+u/2=u) (j : Fin (u/2)) : Fin u :=
  Fin.cast he (j.natAdd (u/2))
def matrixRows {u : ℕ} (q : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) : List Row :=
  List.ofFn (fun i : Fin u =>
    ((List.ofFn (fun j => f i (firstColumn he j))).flatMap (binary q),
     (List.ofFn (fun j => f i (lastColumn he j))).flatMap (binary q)))

theorem columns_split {u : ℕ} (he : u/2+u/2=u) (f : Fin u → ℕ) :
    List.ofFn f=List.ofFn (fun j => f (firstColumn he j))++List.ofFn (fun j => f (lastColumn he j)) := by
  rw [List.ofFn_congr he.symm f,List.ofFn_add]
  rfl

theorem source_matrix_rows {u : ℕ} (q : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) :
    sourceRows (matrixRows q f he)=(rowMajorNatMatrix f).flatMap (binary q) := by
  unfold sourceRows matrixRows rowMajorNatMatrix
  simp only [List.flatMap_def,List.map_flatten,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_def,rowWord]
  rw [columns_split he,List.map_append,List.flatten_append]
  simp only [List.map_ofFn,Function.comp_def]

theorem selected_matrix_rows {u : ℕ} (q : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) :
    selectedRows (matrixRows q f he)=(rowMajorNatMatrix (fun i j => f i (firstColumn he j))).flatMap (binary q) := by
  simp [selectedRows,matrixRows,rowMajorNatMatrix,List.flatMap_def,List.flatten_flatten,Function.comp_def]

theorem matrix_rows_valid {u : ℕ} (q : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) :
    ∀ row∈matrixRows q f he,rowValid (halfBytes u q) row := by
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  constructor <;> simp [halfBytes,List.length_flatMap,binary_length,Function.comp_def,Nat.mul_comm]

theorem selected_cardinality {u : ℕ} (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) :
    (rowMajorNatMatrix (fun i j => f i (firstColumn he j))).length=u*(u/2) ∧
      2*(rowMajorNatMatrix (fun i j => f i (firstColumn he j))).length=u*u := by
  rw [rowMajorNatMatrix_length]
  constructor
  · rfl
  · nlinarith

/-- Exact flat Fin order, hence the original row-major count stream can be
    consumed without a representation change. -/
theorem flat_matrix_values {u v : ℕ} (f : Fin u → Fin v → ℕ) :
    List.ofFn (fun i : Fin (u*v) => f i.divNat i.modNat)=rowMajorNatMatrix f := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  have hv : 0<v := by have := column.isLt; omega
  have hd : (row.val*v+column.val)/v=row.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hv,Nat.div_eq_of_lt column.isLt,Nat.zero_add]
  have hm : (row.val*v+column.val)%v=column.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt column.isLt]
  simp [Fin.divNat,Fin.modNat,hd,hm]

theorem power_even (d : ℕ) (hd : 1≤d) : (2^d)/2+(2^d)/2=2^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hd
  simp [pow_add]
  omega

/-- Within the d-bit range the last bit is zero precisely on the first
    half. The lower coordinates keep their original natural index. -/
theorem zero_last_iff (d column : ℕ) (hd : 1≤d) (hc : column<2^d) :
    column.testBit (d-1)=false ↔ column<(2^d)/2 := by
  have hp : 2^d=2*2^(d-1) := by
    conv_lhs => rw [show d=(d-1)+1 by omega,pow_succ]
    omega
  have hhalf : (2^d)/2=2^(d-1) := by rw [hp]; omega
  rw [hhalf]
  constructor
  · intro hz
    have hdiv : column/2^(d-1)<2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
    have hn : column/2^(d-1)≠1 := by
      intro he
      rw [Nat.testBit_eq_decide_div_mod_eq,he] at hz
      contradiction
    have he : column/2^(d-1)=0 := (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hdiv)).resolve_right hn
    exact (Nat.div_eq_zero_iff).mp he |>.resolve_left (by positivity)
  · exact Nat.testBit_lt_two_pow

theorem first_column_zero_last (d : ℕ) (hd : 1≤d) (j : Fin ((2^d)/2)) :
    (firstColumn (power_even d hd) j).val.testBit (d-1)=false := by
  apply (zero_last_iff d _ hd (firstColumn (power_even d hd) j).isLt).mpr
  exact j.isLt

/-- The native actual pass consumes the original full count stream and
    emits the selected counts with their exact original values and order. -/
theorem matrix_dock_run {u : ℕ} (q pos : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u)
    (suffix : List Bool) (ambient : Fin 86 → List Bool)
    (hsource : ambient 45=(rowMajorNatMatrix f).flatMap (binary q)++suffix)
    (hq : ambient 35=List.replicate q true) :
    ∃ r,runFrom CompetitorOddRowSliceDock.machine (CompetitorOddRowSliceDock.budget u q)
      (CompetitorOddRowSliceDock.cfg CompetitorOddRowSliceDock.machine.start pos 1
        (CompetitorOddRowSliceDock.input ambient u))=some r ∧
      r.steps≤256*(u*u+1)*(q+1) ∧ r.final.heads=CompetitorOddRowSliceDock.heads pos 1 ∧
      r.final.tapes 88=(rowMajorNatMatrix (fun i j => f i (firstColumn he j))).flatMap (binary q) ∧
      r.final.tapes 86=UnaryTemplate.tape u ∧
      (∀ i : Fin 86,r.final.tapes (i.castAdd 20)=ambient i) := by
  have hn : (matrixRows q f he).length=u := by simp [matrixRows]
  obtain ⟨r,hr,hs,hh,ht,hu,hkeep⟩ := CompetitorOddRowSliceDock.dock_run q pos (matrixRows q f he) suffix ambient
    (by rw [source_matrix_rows]; exact hsource) hq (by rw [hn]; exact matrix_rows_valid q f he)
  rw [hn] at hr hs hu
  refine ⟨r,hr,hs.trans (CompetitorOddRowSliceDock.budget_bound u q),hh,?_,hu,hkeep⟩
  rw [ht,selected_matrix_rows]

end NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
