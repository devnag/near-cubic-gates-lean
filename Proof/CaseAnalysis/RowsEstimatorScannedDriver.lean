import Proof.CaseAnalysis.RowsEstimatorDriverRun

/-! The paid scanner's actual d,p,G,C ports feed the fixed driver directly.
Every one of the original70 words is retained; no scalar copy or count pass
is inserted before the driver arithmetic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) := 70+DriverLayout.tapes a
noncomputable def source (a : WilliamsAlgorithm) : Fin 4 → Fin (tapes a) :=
  ![(0 : Fin 70).castAdd _,(17 : Fin 70).castAdd _,(34 : Fin 70).castAdd _,(68 : Fin 70).castAdd _]
noncomputable def slots (a : WilliamsAlgorithm) : Fin (DriverLayout.tapes a) → Fin (tapes a) :=
  DriverPorts.slots 70 (source a) (by rfl)
noncomputable def machine (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) (DriverLayout.machine a)
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) : Fin (tapes a) → List Bool :=
  Fin.addCases (Scanned.output row C) (fun _ : Fin (DriverLayout.tapes a) => [])
noncomputable def driver (a : WilliamsAlgorithm) := slots a (DriverLayout.output a)

theorem ready (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine a) (DriverLayout.budget a row.d row.p row.cuts.length C) (input a row C) out ∧
      (∀ i : Fin 70,out (i.castAdd (DriverLayout.tapes a))=Scanned.output row C i) ∧
      out (driver a)=List.replicate (Driver.value a row.d row.p row.cuts.length C) true := by
  obtain ⟨localOut,hl,hkeep,hvalue⟩ := DriverLayout.ready a row.d row.p row.cuts.length C
  obtain ⟨out,hr,hk,_hf,hv⟩ := DriverPorts.run 70 (source a) (by rfl)
    (by
      intro i j he
      have hv := congrArg (fun z : Fin (tapes a) => z.val) he
      fin_cases i <;> fin_cases j <;> simp [source] at hv ⊢)
    (by intro i;fin_cases i <;> dsimp [source] <;> omega)
    (DriverLayout.machine a) (DriverLayout.budget a row.d row.p row.cuts.length C)
    (input a row C) (DriverLayout.input a row.d row.p row.cuts.length C) localOut hl
    (by
      intro i
      by_cases h0 : i.val=0
      · have he : i=⟨0,by dsimp [DriverLayout.tapes];omega⟩ := Fin.ext h0
        rw [he]
        exact (Scanned.scalar_words row C).1
      · by_cases h1 : i.val=1
        · have he : i=⟨1,by dsimp [DriverLayout.tapes];omega⟩ := Fin.ext h1
          rw [he]
          exact (Scanned.scalar_words row C).2.1
        · by_cases h2 : i.val=2
          · have he : i=⟨2,by dsimp [DriverLayout.tapes];omega⟩ := Fin.ext h2
            rw [he]
            exact (Scanned.scalar_words row C).2.2.1
          · by_cases h3 : i.val=3
            · have he : i=⟨3,by dsimp [DriverLayout.tapes];omega⟩ := Fin.ext h3
              rw [he]
              rfl
            · have hi : ¬i.val<4 := by omega
              simp [hi,DriverLayout.input,h0,h1,h2,h3])
    hkeep
    (by
      intro i hi
      let j : Fin (DriverLayout.tapes a) := ⟨i.val-70,by have h := i.isLt;dsimp [tapes] at h;omega⟩
      have he : i=j.natAdd 70 := Fin.ext (by dsimp [j];omega)
      rw [he]
      simp only [input,Fin.addCases_right])
  refine ⟨out,hr,?_,?_⟩
  · intro i
    exact (hk (i.castAdd _) (by exact i.isLt)).trans (by simp only [input,Fin.addCases_left])
  · exact (hv (DriverLayout.output a)).trans hvalue

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
