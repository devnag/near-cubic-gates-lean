import Proof.CaseAnalysis.RowsPolynomial

/-! The complete polynomial program starts its added scratch suffixes
blank. Reverse zero-padding simulation preserves every transition and the
actual output bytes. Only the true C driver remains a required native field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsColdScratch
open LocalBitMultitape CloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraCaps (C : ℕ) : Fin 9→ℕ :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>ℕ) ![C,0,C+1] (fun _=>0)
def capacities (C : ℕ) : Fin 113→ℕ :=
  Fin.addCases (m:=112) (n:=1) (motive:=fun _=>ℕ)
    (Fin.addCases (m:=103) (n:=9) (motive:=fun _=>ℕ) (CloseoutRowsDegreeReset.caps C) (extraCaps C))
    (fun _=>0)
def coldExtra (p w M C : ℕ) : Fin 9→List Bool :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>List Bool)
    ![[],List.replicate C true,[]] (templates p w M 0)
noncomputable def coldTapes {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (rawInput gs p F w 0 rows out).tapes (coldExtra p w rows.length C)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  RepeatMachine.cfg 0
    (⟨CloseoutRowsPolynomial.body.start,inputHeads gs p F w 0 rows out,coldTapes gs p F w C rows out⟩ :
      Configuration 112 _) Q 1

theorem padded_input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    ZeroPadding.config (capacities C) (input gs p F Q w C rows out)=
      CloseoutRowsPolynomial.input gs p F Q w C rows out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
    · simp only [ZeroPadding.config,input,CloseoutRowsPolynomial.input,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,Fin.addCases_left,CloseoutRowsDegreeLoop.entry]
      refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
      · simp only [capacities,coldTapes,inputTapes,Fin.addCases_left]
      · fin_cases b <;> simp [capacities,extraCaps,coldTapes,coldExtra,inputTapes,extra,
          Fin.addCases,ZeroPadding.pad]
    · fin_cases a
      exact ZeroPadding.pad_zero _

theorem from_receipt {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C fuel : ℕ) (rows : List (List Bool)) (out : List Bool)
    (source : ExecutionReceipt 113 _)
    (hr : runFrom CloseoutRowsPolynomial.machine fuel
      (CloseoutRowsPolynomial.input gs p F Q w C rows out)=some source) :
    ∃ actual,runFrom CloseoutRowsPolynomial.machine fuel (input gs p F Q w C rows out)=some actual ∧
      actual.final.heads=source.final.heads ∧
      actual.final.tapes 31=source.final.tapes 31 ∧
      actual.final.tapes 112=source.final.tapes 112 ∧
      actual.steps=source.steps ∧ actual.peakTapeCells ≤ source.peakTapeCells := by
  rw [←padded_input gs p F Q w C rows out] at hr
  obtain ⟨actual,ha,hf,hs,hp⟩ := ZeroPadding.run_unpad CloseoutRowsPolynomial.machine
    (capacities C) fuel (input gs p F Q w C rows out) source hr
  refine ⟨actual,ha,?_,?_,?_,hs,hp⟩
  · have hh := congrArg Configuration.heads hf
    exact hh
  · have h := congrArg (fun c=>c.tapes 31) hf
    change ZeroPadding.pad 0 (actual.final.tapes 31)=source.final.tapes 31 at h
    simpa only [ZeroPadding.pad_zero] using h
  · have h := congrArg (fun c=>c.tapes 112) hf
    change ZeroPadding.pad 0 (actual.final.tapes 112)=source.final.tapes 112 at h
    simpa only [ZeroPadding.pad_zero] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsColdScratch
