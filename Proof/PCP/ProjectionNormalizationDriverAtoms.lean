import Proof.PCP.ProjectionNormalizationClauses
import Proof.Hierarchy.HierarchyBinaryPower

/-! Restored-counter endpoints used by the actual dimension-driver chain.
The padding of the difference sentinel is retained at its next consumer. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DriverAtoms
open LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun Counter.machine (Counter.budget n) (Counter.input n) out ∧
      out 0=List.replicate n true ∧ out 2=CompareMachine.word n := by
  obtain ⟨r,hr,h0,h2,hh,hs⟩ := Counter.counter_run n
  exact ⟨r.final.tapes,⟨r,hr,rfl,hh,hs.le⟩,h0,h2⟩

theorem difference_run (n m : ℕ) (hm : m ≤ n) : ∃ out,
    ClockJoin.ReadyRun Difference.machine (2*n+8) (Difference.input n m) out ∧
      out 0=CompareMachine.word n ∧ out 1=CompareMachine.word m ∧ out 2=UnaryTemplate.tape (n-m) := by
  obtain ⟨r,hr,h0,h1,h2,hh,hs⟩ := Difference.difference_run n m hm
  exact ⟨r.final.tapes,⟨r,hr,rfl,hh,hs.le⟩,h0,h1,h2⟩

def productBudget (d e : ℕ) := 2*(d*(2*e+3)+4)+2
theorem product_run (d e : ℕ) : ∃ out,
    ClockJoin.ReadyRun Product.reset (productBudget d e) (Product.input d e) out ∧
      out 0=List.replicate d true ∧ out 1=CompareMachine.word e ∧ out 2=CompareMachine.word (d*e) := by
  obtain ⟨base,hbase,hout,hbs⟩ := Product.raw_run d e
  obtain ⟨r,hr,ht,_,hh,hs,_⟩ := Rewind.Workspace.reset_workspace Product.raw _ _ base hbase 0
  refine ⟨r.final.tapes,⟨r,?_,rfl,hh,?_⟩,?_,?_,?_⟩
  · simpa [hbs,Product.reset,productBudget,Product.input] using hr
  · dsimp only [productBudget]
    omega
  · exact (ht 0).trans (by rw [hout]; rfl)
  · exact (ht 1).trans (by rw [hout]; rfl)
  · exact (ht 2).trans (by rw [hout]; rfl)

def templateInput (d e : ℕ) : Fin 4 → List Bool := ![List.replicate d true,UnaryTemplate.tape e,[],[]]
def templateCap (e : ℕ) : Fin 4 → ℕ := fun i => if i=1 then e+2 else 0
theorem template_product_run (d e : ℕ) : ∃ out,
    ClockJoin.ReadyRun Product.reset (productBudget d e) (templateInput d e) out ∧
      out 0=List.replicate d true ∧ out 1=UnaryTemplate.tape e ∧ out 2=CompareMachine.word (d*e) := by
  obtain ⟨baseOut,⟨base,hb,hbt,hbh,hbs⟩,h0,h1,h2⟩ := product_run d e
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config Product.reset (templateCap e) _ _ base hb
  have he : ZeroPadding.config (templateCap e) (initialConfiguration Product.reset (Product.input d e))=
      initialConfiguration Product.reset (templateInput d e) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;>
        simp [ZeroPadding.config,templateCap,initialConfiguration,Product.input,Product.input3,templateInput,Fin.addCases,Difference.padded_word]
  rw [he] at hr
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,hs.le.trans hbs⟩,?_,?_,?_⟩
  · intro i; simpa only [hf,ZeroPadding.config] using hbh i
  · simpa [hf,ZeroPadding.config,templateCap,hbt] using h0
  · simp [hf,ZeroPadding.config,templateCap,hbt,h1,Difference.padded_word]
  · simpa [hf,ZeroPadding.config,templateCap,hbt] using h2

end NearCubicWires.RepairSource.ProjectionNormalization.DriverAtoms
