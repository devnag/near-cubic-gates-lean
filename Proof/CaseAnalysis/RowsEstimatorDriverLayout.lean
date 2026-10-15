import Proof.CaseAnalysis.RowsEstimatorDriverPorts
import Proof.CaseAnalysis.RowsEstimatorDriverBounds
import Proof.Hierarchy.CompetitorCrossRequestHeaders
import Proof.MachineModel.ClockUnarySum

/-! Fixed physical call graph for the estimator reset driver.
All constants depend only on the Williams algorithm; d,p,G,C are tape inputs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev e (a : WilliamsAlgorithm) := CompetitorCrossScheduler.exponent a
noncomputable def tapes (a : WilliamsAlgorithm) := 99+2*e a
noncomputable def input (a : WilliamsAlgorithm) (d p G C : ℕ) : Fin (tapes a) → List Bool :=
  fun i => if i.val=0 then List.replicate d true else if i.val=1 then List.replicate p true
    else if i.val=2 then List.replicate G true else if i.val=3 then List.replicate C true else []

noncomputable def source0 (a : WilliamsAlgorithm) : Fin 2 → Fin (tapes a) := ![⟨0,by dsimp [tapes];omega⟩,⟨1,by dsimp [tapes];omega⟩]
noncomputable def slots0 (a : WilliamsAlgorithm) : Fin (4) → Fin (tapes a) :=
  DriverPorts.slots (4) (source0 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program0 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots0 a) (ClockUnarySum.machine)

noncomputable def source1 (a : WilliamsAlgorithm) : Fin 2 → Fin (tapes a) := ![⟨6,by dsimp [tapes];omega⟩,⟨2,by dsimp [tapes];omega⟩]
noncomputable def slots1 (a : WilliamsAlgorithm) : Fin (4) → Fin (tapes a) :=
  DriverPorts.slots (8) (source1 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program1 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots1 a) (ClockUnarySum.machine)

noncomputable def source2 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨3,by dsimp [tapes];omega⟩]
noncomputable def slots2 (a : WilliamsAlgorithm) : Fin (DimensionPolynomial.tapes 1) → Fin (tapes a) :=
  DriverPorts.slots (12) (source2 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program2 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots2 a) (DriverPower.machine 1 64)

noncomputable def source3 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨10,by dsimp [tapes];omega⟩]
noncomputable def slots3 (a : WilliamsAlgorithm) : Fin (DimensionPolynomial.tapes 3) → Fin (tapes a) :=
  DriverPorts.slots (28) (source3 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program3 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots3 a) (DriverPower.machine 3 2000000)

noncomputable def source4 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨6,by dsimp [tapes];omega⟩]
noncomputable def slots4 (a : WilliamsAlgorithm) : Fin (DimensionPolynomial.tapes (e a)) → Fin (tapes a) :=
  DriverPorts.slots (48) (source4 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program4 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots4 a) (DriverPower.machine (e a) (Driver.tableCoefficient a))

noncomputable def source5 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨0,by dsimp [tapes];omega⟩]
noncomputable def slots5 (a : WilliamsAlgorithm) : Fin (15) → Fin (tapes a) :=
  DriverPorts.slots (62+2*e a) (source5 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program5 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots5 a) (CompetitorCrossRequestHeaders.powerMachine)

noncomputable def source6 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨75+2*e a,by dsimp [tapes];omega⟩]
noncomputable def slots6 (a : WilliamsAlgorithm) : Fin (DimensionPower.tapes 2) → Fin (tapes a) :=
  DriverPorts.slots (77+2*e a) (source6 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program6 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots6 a) (DimensionPower.machine 2 1)

noncomputable def source7 (a : WilliamsAlgorithm) : Fin 1 → Fin (tapes a) := ![⟨51+2*e a,by dsimp [tapes];omega⟩]
noncomputable def slots7 (a : WilliamsAlgorithm) : Fin (3) → Fin (tapes a) :=
  DriverPorts.slots (84+2*e a) (source7 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program7 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots7 a) (DimensionTemplate.machine false)

noncomputable def source8 (a : WilliamsAlgorithm) : Fin 2 → Fin (tapes a) := ![⟨82+2*e a,by dsimp [tapes];omega⟩,⟨85+2*e a,by dsimp [tapes];omega⟩]
noncomputable def slots8 (a : WilliamsAlgorithm) : Fin (4) → Fin (tapes a) :=
  DriverPorts.slots (87+2*e a) (source8 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program8 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots8 a) (ClockUnaryProduct.machine)

noncomputable def source9 (a : WilliamsAlgorithm) : Fin 2 → Fin (tapes a) := ![⟨17,by dsimp [tapes];omega⟩,⟨37,by dsimp [tapes];omega⟩]
noncomputable def slots9 (a : WilliamsAlgorithm) : Fin (4) → Fin (tapes a) :=
  DriverPorts.slots (91+2*e a) (source9 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program9 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots9 a) (ClockUnarySum.machine)

noncomputable def source10 (a : WilliamsAlgorithm) : Fin 2 → Fin (tapes a) := ![⟨93+2*e a,by dsimp [tapes];omega⟩,⟨89+2*e a,by dsimp [tapes];omega⟩]
noncomputable def slots10 (a : WilliamsAlgorithm) : Fin (4) → Fin (tapes a) :=
  DriverPorts.slots (95+2*e a) (source10 a) (by dsimp [tapes,DimensionPolynomial.tapes,DimensionPower.tapes];omega)
noncomputable def program10 (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots10 a) (ClockUnarySum.machine)
noncomputable def prefix1 (a : WilliamsAlgorithm) := Composition.machine (program0 a) (program1 a)
noncomputable def prefix2 (a : WilliamsAlgorithm) := Composition.machine (prefix1 a) (program2 a)
noncomputable def prefix3 (a : WilliamsAlgorithm) := Composition.machine (prefix2 a) (program3 a)
noncomputable def prefix4 (a : WilliamsAlgorithm) := Composition.machine (prefix3 a) (program4 a)
noncomputable def prefix5 (a : WilliamsAlgorithm) := Composition.machine (prefix4 a) (program5 a)
noncomputable def prefix6 (a : WilliamsAlgorithm) := Composition.machine (prefix5 a) (program6 a)
noncomputable def prefix7 (a : WilliamsAlgorithm) := Composition.machine (prefix6 a) (program7 a)
noncomputable def prefix8 (a : WilliamsAlgorithm) := Composition.machine (prefix7 a) (program8 a)
noncomputable def prefix9 (a : WilliamsAlgorithm) := Composition.machine (prefix8 a) (program9 a)
noncomputable def prefix10 (a : WilliamsAlgorithm) := Composition.machine (prefix9 a) (program10 a)
noncomputable def machine (a : WilliamsAlgorithm) := prefix10 a
noncomputable def output (a : WilliamsAlgorithm) : Fin (tapes a) := ⟨97+2*e a,by dsimp [tapes];omega⟩

noncomputable def budget (a : WilliamsAlgorithm) (d p G C : ℕ) :=
  let S := d+p
  let M := S+G
  let Ct := 64*(C+1)
  let Mt := 2000000*(M+1)^3
  let Tp := Driver.tableCoefficient a*(S+1)^(e a)
  let U := 2^d
  let T := U^2*Tp
  ((((((((((2*S+6)+1+(2*M+6))+1+DriverPower.budget 1 64 C)+1+
    DriverPower.budget 3 2000000 M)+1+DriverPower.budget (e a) (Driver.tableCoefficient a) S)+1+
    CompetitorCrossRequestHeaders.powerBudget d)+1+DimensionPower.cost 1 U 2)+1+
    (2*Tp+8))+1+WilliamsUnaryProduct.budget (U^2) Tp)+1+(2*(Ct+Mt)+6))+1+
    (2*(Ct+Mt+T)+6)
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
