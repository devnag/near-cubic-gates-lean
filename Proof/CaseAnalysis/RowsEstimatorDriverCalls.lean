import Proof.CaseAnalysis.RowsEstimatorDriverLayout

/-! Each call in the fixed reset-driver graph executes an original unary
worker, retaining every earlier word and exposing only its physical result. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem run0 (a : WilliamsAlgorithm) (r s : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source0 a 0)=List.replicate r true)
    (hs1 : A (source0 a 1)=List.replicate s true)
    (hf : ∀ i,4 ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program0 a) (2*(r+s)+6) A out ∧
      (∀ i,i.val<4 → out i=A i) ∧
      (∀ i,8 ≤ i.val → out i=[]) ∧
      out ⟨6,by dsimp [tapes];omega⟩=List.replicate (r+s) true := by
  let localOut := ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false]
  have hl := ClockUnarySum.sum_ready r s
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (4) (source0 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l he;fin_cases i <;> fin_cases l <;> simp [source0] at he ⊢)
    (by intro i;fin_cases i <;> dsimp [source0] <;> omega)
    (ClockUnarySum.machine) (2*(r+s)+6) A (![List.replicate r true,List.replicate s true,[],[]]) localOut hl
    (by intro i;fin_cases i <;> simp [source0] at hs0 hs1 ⊢ <;> assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots0 a ((2 : Fin 4))=⟨6,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (4)+(2)=6
    omega
  have hval : localOut ((2 : Fin 4))=List.replicate (r+s) true := by rfl
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by omega)
  · have h := hv ((2 : Fin 4))
    change out (slots0 a ((2 : Fin 4)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run1 (a : WilliamsAlgorithm) (r s : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source1 a 0)=List.replicate r true)
    (hs1 : A (source1 a 1)=List.replicate s true)
    (hf : ∀ i,8 ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program1 a) (2*(r+s)+6) A out ∧
      (∀ i,i.val<8 → out i=A i) ∧
      (∀ i,12 ≤ i.val → out i=[]) ∧
      out ⟨10,by dsimp [tapes];omega⟩=List.replicate (r+s) true := by
  let localOut := ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false]
  have hl := ClockUnarySum.sum_ready r s
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (8) (source1 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l he;fin_cases i <;> fin_cases l <;> simp [source1] at he ⊢)
    (by intro i;fin_cases i <;> dsimp [source1] <;> omega)
    (ClockUnarySum.machine) (2*(r+s)+6) A (![List.replicate r true,List.replicate s true,[],[]]) localOut hl
    (by intro i;fin_cases i <;> simp [source1] at hs0 hs1 ⊢ <;> assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots1 a ((2 : Fin 4))=⟨10,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (8)+(2)=10
    omega
  have hval : localOut ((2 : Fin 4))=List.replicate (r+s) true := by rfl
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by omega)
  · have h := hv ((2 : Fin 4))
    change out (slots1 a ((2 : Fin 4)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run2 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source2 a 0)=List.replicate n true)
    (hf : ∀ i,12 ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program2 a) (DriverPower.budget 1 64 n) A out ∧
      (∀ i,i.val<12 → out i=A i) ∧
      (∀ i,28 ≤ i.val → out i=[]) ∧
      out ⟨17,by dsimp [tapes];omega⟩=List.replicate (64*(n+1)^1) true := by
  obtain ⟨localOut,hl,hkeep,hvalue⟩ := DriverPower.ready 1 64 n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (12) (source2 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source2];omega)
    (DriverPower.machine 1 64) (DriverPower.budget 1 64 n) A (DimensionPolynomial.input 1 n) localOut hl
    (by
      intro i
      by_cases hi : i.val=0
      · have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext hi
        rw [he]
        exact hs0
      · have hn : ¬i.val<1 := by omega
        simp [hn,DimensionPolynomial.input,hi])
    (by
      intro i hi
      have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext (show i.val=0 from by omega)
      rw [he]
      exact hkeep) hf
  have hp : slots2 a (DriverPower.valueSlot 1)=⟨17,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (12)+(5)=17
    omega
  have hval : localOut (DriverPower.valueSlot 1)=List.replicate (64*(n+1)^1) true := by exact hvalue
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (12)+(16) ≤ _;omega)
  · have h := hv (DriverPower.valueSlot 1)
    change out (slots2 a (DriverPower.valueSlot 1))=_ at h
    rw [hp,hval] at h
    exact h

theorem run3 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source3 a 0)=List.replicate n true)
    (hf : ∀ i,28 ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program3 a) (DriverPower.budget 3 2000000 n) A out ∧
      (∀ i,i.val<28 → out i=A i) ∧
      (∀ i,48 ≤ i.val → out i=[]) ∧
      out ⟨37,by dsimp [tapes];omega⟩=List.replicate (2000000*(n+1)^3) true := by
  obtain ⟨localOut,hl,hkeep,hvalue⟩ := DriverPower.ready 3 2000000 n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (28) (source3 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source3];omega)
    (DriverPower.machine 3 2000000) (DriverPower.budget 3 2000000 n) A (DimensionPolynomial.input 3 n) localOut hl
    (by
      intro i
      by_cases hi : i.val=0
      · have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext hi
        rw [he]
        exact hs0
      · have hn : ¬i.val<1 := by omega
        simp [hn,DimensionPolynomial.input,hi])
    (by
      intro i hi
      have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext (show i.val=0 from by omega)
      rw [he]
      exact hkeep) hf
  have hp : slots3 a (DriverPower.valueSlot 3)=⟨37,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (28)+(9)=37
    omega
  have hval : localOut (DriverPower.valueSlot 3)=List.replicate (2000000*(n+1)^3) true := by exact hvalue
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (28)+(20) ≤ _;omega)
  · have h := hv (DriverPower.valueSlot 3)
    change out (slots3 a (DriverPower.valueSlot 3))=_ at h
    rw [hp,hval] at h
    exact h

theorem run4 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source4 a 0)=List.replicate n true)
    (hf : ∀ i,48 ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program4 a) (DriverPower.budget (e a) (Driver.tableCoefficient a) n) A out ∧
      (∀ i,i.val<48 → out i=A i) ∧
      (∀ i,62+2*e a ≤ i.val → out i=[]) ∧
      out ⟨51+2*e a,by dsimp [tapes];omega⟩=List.replicate ((Driver.tableCoefficient a)*(n+1)^(e a)) true := by
  obtain ⟨localOut,hl,hkeep,hvalue⟩ := DriverPower.ready (e a) (Driver.tableCoefficient a) n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (48) (source4 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source4];omega)
    (DriverPower.machine (e a) (Driver.tableCoefficient a)) (DriverPower.budget (e a) (Driver.tableCoefficient a) n) A (DimensionPolynomial.input (e a) n) localOut hl
    (by
      intro i
      by_cases hi : i.val=0
      · have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext hi
        rw [he]
        exact hs0
      · have hn : ¬i.val<1 := by omega
        simp [hn,DimensionPolynomial.input,hi])
    (by
      intro i hi
      have he : i=⟨0,by dsimp [DimensionPolynomial.tapes];omega⟩ := Fin.ext (show i.val=0 from by omega)
      rw [he]
      exact hkeep) hf
  have hp : slots4 a (DriverPower.valueSlot (e a))=⟨51+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    have hz : 1+2*e a≠0 := by omega
    have hn : ¬(2+(1+2*e a)<1) := by omega
    simp only [slots4,DriverPorts.slots,DriverPower.valueSlot,DimensionPolynomial.powerSlots,DimensionPower.valueSlot,Fin.val_mk,hz,if_false,hn,dite_false]
    omega
  have hval : localOut (DriverPower.valueSlot (e a))=List.replicate ((Driver.tableCoefficient a)*(n+1)^(e a)) true := by exact hvalue
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (48)+(14+2*e a) ≤ _;omega)
  · have h := hv (DriverPower.valueSlot (e a))
    change out (slots4 a (DriverPower.valueSlot (e a)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run5 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source5 a 0)=List.replicate n true)
    (hf : ∀ i,62+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program5 a) (CompetitorCrossRequestHeaders.powerBudget n) A out ∧
      (∀ i,i.val<62+2*e a → out i=A i) ∧
      (∀ i,77+2*e a ≤ i.val → out i=[]) ∧
      out ⟨75+2*e a,by dsimp [tapes];omega⟩=UnaryTemplate.tape (2^n) := by
  obtain ⟨localOut,hl,hkeep,_hwidth,hvalue⟩ := CompetitorCrossRequestHeaders.power_run n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (62+2*e a) (source5 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source5];omega)
    (CompetitorCrossRequestHeaders.powerMachine) (CompetitorCrossRequestHeaders.powerBudget n) A (CompetitorCrossRequestHeaders.powerInput n) localOut hl
    (by intro i;fin_cases i <;> simp [CompetitorCrossRequestHeaders.powerInput,MatrixScorePower.input,Fin.addCases,source5] at hs0 ⊢;assumption)
    (by
      intro i hi
      have he : i=0 := Fin.ext (show i.val=0 from by omega)
      rw [he]
      exact hkeep) hf
  have hp : slots5 a ((13 : Fin 15))=⟨75+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (62+2*e a)+(13)=75+2*e a
    omega
  have hval : localOut ((13 : Fin 15))=UnaryTemplate.tape (2^n) := by exact hvalue
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (62+2*e a)+(15) ≤ _;omega)
  · have h := hv ((13 : Fin 15))
    change out (slots5 a ((13 : Fin 15)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run6 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source6 a 0)=UnaryTemplate.tape n)
    (hf : ∀ i,77+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program6 a) (DimensionPower.cost 1 n 2) A out ∧
      (∀ i,i.val<77+2*e a → out i=A i) ∧
      (∀ i,84+2*e a ≤ i.val → out i=[]) ∧
      out ⟨82+2*e a,by dsimp [tapes];omega⟩=List.replicate (n^2) true := by
  obtain ⟨localOut,hl,hkeep,hvalue⟩ := DimensionPower.power_run 2 1 n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (77+2*e a) (source6 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source6];omega)
    (DimensionPower.machine 2 1) (DimensionPower.cost 1 n 2) A (DimensionPower.input 2 n) localOut hl
    (by intro i;fin_cases i <;> simp [DimensionPower.input,source6] at hs0 ⊢;assumption)
    (by
      intro i hi
      have he : i=⟨0,by decide⟩ := Fin.ext (show i.val=0 from by omega)
      rw [he]
      exact hkeep) hf
  have hp : slots6 a (DimensionPower.valueSlot 2 2 le_rfl)=⟨82+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (77+2*e a)+(5)=82+2*e a
    omega
  have hval : localOut (DimensionPower.valueSlot 2 2 le_rfl)=List.replicate (n^2) true := by simpa only [one_mul] using hvalue
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (77+2*e a)+(7) ≤ _;omega)
  · have h := hv (DimensionPower.valueSlot 2 2 le_rfl)
    change out (slots6 a (DimensionPower.valueSlot 2 2 le_rfl))=_ at h
    rw [hp,hval] at h
    exact h

theorem run7 (a : WilliamsAlgorithm) (n : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source7 a 0)=List.replicate n true)
    (hf : ∀ i,84+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program7 a) (2*n+8) A out ∧
      (∀ i,i.val<84+2*e a → out i=A i) ∧
      (∀ i,87+2*e a ≤ i.val → out i=[]) ∧
      out ⟨85+2*e a,by dsimp [tapes];omega⟩=UnaryTemplate.tape n := by
  let localOut := DimensionTemplate.output false n
  have hl := DimensionTemplate.ready false n
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (84+2*e a) (source7 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l _;exact Subsingleton.elim i l)
    (by intro i;fin_cases i;dsimp [source7];omega)
    (DimensionTemplate.machine false) (2*n+8) A (DimensionTemplate.input n) localOut hl
    (by intro i;fin_cases i <;> simp [DimensionTemplate.input,source7] at hs0 ⊢;assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots7 a ((1 : Fin 3))=⟨85+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (84+2*e a)+(1)=85+2*e a
    omega
  have hval : localOut ((1 : Fin 3))=UnaryTemplate.tape n := by simp [localOut,DimensionTemplate.output]
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by change (84+2*e a)+(3) ≤ _;omega)
  · have h := hv ((1 : Fin 3))
    change out (slots7 a ((1 : Fin 3)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run8 (a : WilliamsAlgorithm) (r s : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source8 a 0)=List.replicate r true)
    (hs1 : A (source8 a 1)=UnaryTemplate.tape s)
    (hf : ∀ i,87+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program8 a) (WilliamsUnaryProduct.budget r s) A out ∧
      (∀ i,i.val<87+2*e a → out i=A i) ∧
      (∀ i,91+2*e a ≤ i.val → out i=[]) ∧
      out ⟨89+2*e a,by dsimp [tapes];omega⟩=List.replicate (r*s) true := by
  let localOut := WilliamsUnaryProduct.output r s
  have hl : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget r s) (WilliamsUnaryProduct.input r s) localOut := by
    obtain ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready r s
    exact ⟨r,hr,ht,hh,hs.le⟩
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (87+2*e a) (source8 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l he;fin_cases i <;> fin_cases l <;> simp [source8] at he ⊢)
    (by intro i;fin_cases i <;> dsimp [source8] <;> omega)
    (ClockUnaryProduct.machine) (WilliamsUnaryProduct.budget r s) A (WilliamsUnaryProduct.input r s) localOut hl
    (by intro i;fin_cases i <;> simp [WilliamsUnaryProduct.input,source8] at hs0 hs1 ⊢ <;> assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots8 a ((2 : Fin 4))=⟨89+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (87+2*e a)+(2)=89+2*e a
    omega
  have hval : localOut ((2 : Fin 4))=List.replicate (r*s) true := by rfl
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by omega)
  · have h := hv ((2 : Fin 4))
    change out (slots8 a ((2 : Fin 4)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run9 (a : WilliamsAlgorithm) (r s : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source9 a 0)=List.replicate r true)
    (hs1 : A (source9 a 1)=List.replicate s true)
    (hf : ∀ i,91+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program9 a) (2*(r+s)+6) A out ∧
      (∀ i,i.val<91+2*e a → out i=A i) ∧
      (∀ i,95+2*e a ≤ i.val → out i=[]) ∧
      out ⟨93+2*e a,by dsimp [tapes];omega⟩=List.replicate (r+s) true := by
  let localOut := ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false]
  have hl := ClockUnarySum.sum_ready r s
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (91+2*e a) (source9 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l he;fin_cases i <;> fin_cases l <;> simp [source9] at he ⊢)
    (by intro i;fin_cases i <;> dsimp [source9] <;> omega)
    (ClockUnarySum.machine) (2*(r+s)+6) A (![List.replicate r true,List.replicate s true,[],[]]) localOut hl
    (by intro i;fin_cases i <;> simp [source9] at hs0 hs1 ⊢ <;> assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots9 a ((2 : Fin 4))=⟨93+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (91+2*e a)+(2)=93+2*e a
    omega
  have hval : localOut ((2 : Fin 4))=List.replicate (r+s) true := by rfl
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by omega)
  · have h := hv ((2 : Fin 4))
    change out (slots9 a ((2 : Fin 4)))=_ at h
    rw [hp,hval] at h
    exact h

theorem run10 (a : WilliamsAlgorithm) (r s : ℕ) (A : Fin (tapes a) → List Bool)
    (hs0 : A (source10 a 0)=List.replicate r true)
    (hs1 : A (source10 a 1)=List.replicate s true)
    (hf : ∀ i,95+2*e a ≤ i.val → A i=[]) : ∃ out,
    ClockJoin.ReadyRun (program10 a) (2*(r+s)+6) A out ∧
      (∀ i,i.val<95+2*e a → out i=A i) ∧
      (∀ i,99+2*e a ≤ i.val → out i=[]) ∧
      out ⟨97+2*e a,by dsimp [tapes];omega⟩=List.replicate (r+s) true := by
  let localOut := ![List.replicate r true,List.replicate s true,List.replicate (r+s) true,List.replicate (r+s+2) false]
  have hl := ClockUnarySum.sum_ready r s
  obtain ⟨out,hr,hk,hfresh,hv⟩ := DriverPorts.run (95+2*e a) (source10 a)
    (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
    (by intro i l he;fin_cases i <;> fin_cases l <;> simp [source10] at he ⊢)
    (by intro i;fin_cases i <;> dsimp [source10] <;> omega)
    (ClockUnarySum.machine) (2*(r+s)+6) A (![List.replicate r true,List.replicate s true,[],[]]) localOut hl
    (by intro i;fin_cases i <;> simp [source10] at hs0 hs1 ⊢ <;> assumption)
    (by intro i hi;fin_cases i <;> first | rfl | (simp at hi)) hf
  have hp : slots10 a ((2 : Fin 4))=⟨97+2*e a,by dsimp [tapes];omega⟩ := by
    apply Fin.ext
    change (95+2*e a)+(2)=97+2*e a
    omega
  have hval : localOut ((2 : Fin 4))=List.replicate (r+s) true := by rfl
  refine ⟨out,hr,hk,?_,?_⟩
  · intro i hi
    exact hfresh i (by omega)
  · have h := hv ((2 : Fin 4))
    change out (slots10 a ((2 : Fin 4)))=_ at h
    rw [hp,hval] at h
    exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
