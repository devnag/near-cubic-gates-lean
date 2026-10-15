import Proof.CaseAnalysis.RowsTouchingCoordinateLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem vector9 {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b6 : α)
    (i : Fin 9) (h0:i=0→b0=a0) (h1:i=1→b1=a1) (h2:i=2→b2=a2) (h3:i=3→b3=a3) (h6:i=6→b6=a6):
    (![b0,b1,b2,b3,a4,a5,b6,a7,a8] : Fin 9→α) i=(![a0,a1,a2,a3,a4,a5,a6,a7,a8] : Fin 9→α) i:=by
  fin_cases i <;> simp_all

theorem vector15 {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 b2 b9 b10 b11 b14 : α)
    (i : Fin 15) (h2:i=2→b2=a2) (h9:i=9→b9=a9) (h10:i=10→b10=a10)
    (h11:i=11→b11=a11) (h14:i=14→b14=a14):
    (![a0,a1,b2,a3,a4,a5,a6,a7,a8,b9,b10,b11,a12,a13,b14] : Fin 15→α) i=
      (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14] : Fin 15→α) i:=by
  fin_cases i <;> simp_all

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
