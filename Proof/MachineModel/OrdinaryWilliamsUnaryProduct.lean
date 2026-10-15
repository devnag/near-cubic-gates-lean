import Proof.MachineModel.OrdinaryWilliamsMetadataReset

/-! Exact ordinary multiplication using the sentinel-terminated factor
produced by the metadata pass. The source multiplier's actual replay and
rewind are retained, including the physical product allocation. -/
namespace NearCubicWires.RepairOrdinary.WilliamsUnaryProduct
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (d e : ℕ) := 2*(d*(2*e+3)+2)+2
def scratch (d e : ℕ) := d*(2*e+3)+2
def input (d e : ℕ) : Fin 4 → List Bool :=
  ![List.replicate d true,UnaryTemplate.tape e,[],[]]
def output (d e : ℕ) : Fin 4 → List Bool :=
  ![List.replicate d true,UnaryTemplate.tape e,List.replicate (d*e) true,List.replicate (scratch d e) false]
def capacity (e : ℕ) : Fin 4 → ℕ := ![0,e+2,0,0]

theorem product_ready (d e : ℕ) : ReadyRun ClockUnaryProduct.machine (budget d e) (input d e) (output d e) := by
  obtain ⟨base,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run d e
  obtain ⟨r,hp,hf,hsteps,_⟩ := ZeroPadding.run_config ClockUnaryProduct.machine (capacity e) _ _ base hr
  have hin : ZeroPadding.config (capacity e)
      (initialConfiguration ClockUnaryProduct.machine
        (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
          ![List.replicate d true,false::List.replicate e true,[]] (fun _ : Fin 1 => []))) =
      initialConfiguration ClockUnaryProduct.machine (input d e) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,initialConfiguration,input,
        Fin.addCases,ZeroPadding.pad,UnaryTemplate.tape]
  rw [hin] at hp
  refine ⟨r,hp,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,output,h0,h1,h2,h3,
      ZeroPadding.pad,UnaryTemplate.tape,scratch]
  · intro i; rw [hf]; exact hh i

end NearCubicWires.RepairOrdinary.WilliamsUnaryProduct
