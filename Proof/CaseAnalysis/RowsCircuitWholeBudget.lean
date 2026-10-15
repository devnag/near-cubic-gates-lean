import Proof.CaseAnalysis.RowsCircuitCapacity

/-! The complete cold circuit has one paid linear-in-capacity bound.
Actual list multiplicity is included; policy caps are read-only operands. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWholeBudget
open LocalBitMultitape RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (C N : ℕ):=1000*(N+2)*(C+1)

theorem amount_bound (threshold : Bool) (D n : ℕ) :
    CloseoutRowsCircuitArithmeticDock.amount threshold D n ≤ D+n+2:=by
  cases threshold
  · exact Nat.div_le_self _ _
  · exact (Nat.div_le_self _ _).trans (by omega)

theorem arithmetic_bound (threshold : Bool) (D n : ℕ) :
    CloseoutRowsCircuitArithmeticDock.budget threshold D n ≤ 24*(D+n)+58:=by
  cases threshold
  · change CloseoutRowsCircuitSymmetricDescription.budget D n ≤ _
    rw [CloseoutRowsCircuitDescriptionMeaning.symmetric_budget]
    omega
  · change CloseoutRowsCircuitThresholdDescription.budget D n ≤ _
    have h:=CloseoutRowsCircuitDescriptionMeaning.threshold_budget D n
    omega

theorem body_bound (threshold : Bool) (C retained D n wire L W : ℕ) (top : List Bool)
    (hheader : EquationHeaderAppend.budget retained+1 ≤ C) (htop : 2*top.length+1 ≤ C)
    (hc : 32*(D+n+wire+3) ≤ C) :
    CloseoutRowsCircuitBody.budget threshold C retained top D n wire L W ≤
      n*(12*C+33)+40*C+203:=by
  have ha:=arithmetic_bound threshold D n
  have hm:=amount_bound threshold D n
  have md:=Nat.min_le_left (CloseoutRowsCircuitArithmeticDock.amount threshold D n) L
  have mw:=Nat.min_le_left wire W
  unfold CloseoutRowsCircuitBody.budget CloseoutRowsCircuitPreparedRun.budget
    CloseoutRowsCircuitNativePrepare.budget CloseoutRowsCircuitNativePrefix.budget
    CloseoutRowsCircuitCountHeader.budget CloseoutRowsCircuitTraversalCaps.budget
    CloseoutRowsCircuitBottomReturned.budget CloseoutRowsCircuitBottomLoop.budget
    CloseoutRowsCircuitResourceRun.budget CloseoutRowsCircuitCaps.budget RawCompare.budget
  omega

theorem symmetric_cold_bound (C : ℕ) (bits : List Bool)
    (hp : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C)
    (ht : CloseoutRowsCircuitSymTop.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+1 ≤ C) :
    CloseoutRowsCircuitColdSymmetric.budget C bits ≤ 14*C+40:=by
  unfold CloseoutRowsCircuitColdSymmetric.budget CloseoutRowsCircuitColdEntry.budget
    CloseoutRowsCircuitSymmetricTop.budget
  omega

theorem threshold_cold_bound (C : ℕ) (bits : List Bool)
    (hp : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C)
    (ht : 2*CloseoutRowsGateMeasured.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+4 ≤ C) :
    CloseoutRowsCircuitColdThreshold.budget C bits ≤ 14*C+40:=by
  unfold CloseoutRowsCircuitColdThreshold.budget CloseoutRowsCircuitColdEntry.budget
    CloseoutRowsCircuitThresholdTop.budget
  omega

theorem joined_bound (C N n cold body : ℕ) (hn : n ≤ N+1)
    (hc : cold ≤ 14*C+40) (hb : body ≤ n*(12*C+33)+40*C+203) :
    cold+1+body+1 ≤ budget C N:=by
  have hm:=Nat.mul_le_mul_right (12*C+33) hn
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWholeBudget
