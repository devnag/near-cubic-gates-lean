import Proof.MachineModel.ClockUnarySum
import Proof.Amplification.RecoveryEraseConstant

/-! Fixed tape plan for the actual full dyadic U clock. Only c and k index
finite program descriptions; N indexes receipt statements and prepared data. -/
namespace NearCubicWires.RepairOrdinary.ClockWordLayout
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def exponent (k c N : ℕ) : ℕ := ClockEnvelope.exponent k c N
def product (c N : ℕ) : ℕ := c*ClockEnvelope.logWidth N
def firstSum (c N : ℕ) : ℕ := ClockDyadicLedger.exponent N+product c N

def pack (stage k c N a b : ℕ) : Fin 22 → List Bool :=
  ![List.replicate (ClockDyadicLedger.exponent N) true,
    false::List.replicate (PCPResourceLedger.ell N) true,
    if 1≤ stage then frame (List.replicate (PCPResourceLedger.ell N) true) else [],
    if 1≤ stage then frame (ClockBinary.word (PCPResourceLedger.ell N)) else [],
    if 1≤ stage then List.replicate a false else [],
    if 1≤ stage then List.replicate b false else [],
    if 1≤ stage then false::List.replicate (ClockEnvelope.logWidth N) true else [],
    if 2≤ stage then List.replicate c true else [],
    if 2≤ stage then List.replicate c false else [],
    if 3≤ stage then List.replicate k true else [],
    if 3≤ stage then List.replicate k false else [],
    if 4≤ stage then List.replicate (product c N) true else [],
    if 4≤ stage then List.replicate (c*(2*ClockEnvelope.logWidth N+3)+2) false else [],
    if 5≤ stage then List.replicate (firstSum c N) true else [],
    if 5≤ stage then List.replicate (firstSum c N+2) false else [],
    if 6≤ stage then List.replicate (exponent k c N) true else [],
    if 6≤ stage then List.replicate (exponent k c N+2) false else [],
    if 7≤ stage then frame (List.replicate (exponent k c N) false++[true]) else [],
    if 7≤ stage then List.replicate (exponent k c N+3) true else [],
    if 7≤ stage then List.replicate (2*(exponent k c N+3)) true else [],
    if 7≤ stage then List.replicate (2*(exponent k c N+3)+2) true else [],
    if 7≤ stage then List.replicate (2*exponent k c N+10) false else []]

def logLayout : Fin 22 ≃ Fin 22 where
  toFun := ![1,2,3,4,5,6,0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
  invFun := ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def coefficientLayout : Fin 22 ≃ Fin 22 where
  toFun := ![7,8,0,1,2,3,4,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21]
  invFun := ![2,3,4,5,6,7,8,0,1,9,10,11,12,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def offsetLayout : Fin 22 ≃ Fin 22 where
  toFun := ![9,10,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16,17,18,19,20,21]
  invFun := ![2,3,4,5,6,7,8,9,10,0,1,11,12,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def productLayout : Fin 22 ≃ Fin 22 where
  toFun := ![7,6,11,12,0,1,2,3,4,5,8,9,10,13,14,15,16,17,18,19,20,21]
  invFun := ![4,5,6,7,8,9,1,0,10,11,12,2,3,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def firstSumLayout : Fin 22 ≃ Fin 22 where
  toFun := ![0,11,13,14,1,2,3,4,5,6,7,8,9,10,12,15,16,17,18,19,20,21]
  invFun := ![0,4,5,6,7,8,9,10,11,12,13,1,14,2,3,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def secondSumLayout : Fin 22 ≃ Fin 22 where
  toFun := ![13,9,15,16,0,1,2,3,4,5,6,7,8,10,11,12,14,17,18,19,20,21]
  invFun := ![4,5,6,7,8,9,10,11,12,1,13,14,15,0,16,2,3,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fieldLayout : Fin 22 ≃ Fin 22 where
  toFun := ![15,17,18,19,20,21,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16]
  invFun := ![6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0,21,1,2,3,4,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def logPhase : Machine 22 29 := ClockJoin.lifted (e:=16) logLayout ClockLogLog.machine
def coefficientPhase (c : ℕ) : Machine 22 (c+3) :=
  ClockJoin.lifted (e:=20) coefficientLayout (RecoveryEraseConstant.resetMachine c)
def offsetPhase (k : ℕ) : Machine 22 (k+3) :=
  ClockJoin.lifted (e:=20) offsetLayout (RecoveryEraseConstant.resetMachine k)
def productPhase : Machine 22 7 := ClockJoin.lifted (e:=18) productLayout ClockUnaryProduct.machine
def firstSumPhase : Machine 22 5 := ClockJoin.lifted (e:=18) firstSumLayout ClockUnarySum.machine
def secondSumPhase : Machine 22 5 := ClockJoin.lifted (e:=18) secondSumLayout ClockUnarySum.machine
def fieldPhase : Machine 22 14 := ClockJoin.lifted (e:=16) fieldLayout ClockFields.machine

def logCost (N : ℕ) := 8*(PCPResourceLedger.ell N)^2+34*PCPResourceLedger.ell N+15
def productCost (c N : ℕ) := 2*(c*(2*ClockEnvelope.logWidth N+3)+2)+2
def firstSumCost (c N : ℕ) := 2*firstSum c N+6
def secondSumCost (k c N : ℕ) := 2*exponent k c N+6
def fieldCost (k c N : ℕ) := 4*exponent k c N+22

def states (k c : ℕ) := 29+(c+3)+(k+3)+7+5+5+14
def machine (k c : ℕ) : Machine 22 (states k c) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine logPhase (coefficientPhase c)) (offsetPhase k))
    productPhase) firstSumPhase) secondSumPhase) fieldPhase

def budget (k c N : ℕ) := logCost N+1+(2*c+2)+1+(2*k+2)+1+productCost c N+
  1+firstSumCost c N+1+secondSumCost k c N+1+fieldCost k c N

theorem budget_bound (k c N : ℕ) : budget k c N≤200*(c+k+1)*(PCPResourceLedger.q N)^2 := by
  let q := PCPResourceLedger.q N
  have hq : 1≤q := by simp [q,PCPResourceLedger.q]
  have he : PCPResourceLedger.ell N≤q := by simp [q,PCPResourceLedger.q]
  have hq2 : q≤q^2 := by nlinarith
  have he2 : (PCPResourceLedger.ell N)^2≤q^2 := Nat.pow_le_pow_left he 2
  have hlog : ClockEnvelope.logWidth N≤PCPResourceLedger.ell N :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have hprod : c*ClockEnvelope.logWidth N≤c*q^2 :=
    Nat.mul_le_mul_left c (hlog.trans (he.trans hq2))
  have hc : c≤c*q^2 := by nlinarith
  have hk : k≤k*q^2 := by nlinarith
  have hr := (ClockDyadicLedger.width_bounds N).2
  change ClockDyadicLedger.exponent N+3≤3*q^2 at hr
  dsimp only [budget,logCost,productCost,firstSumCost,secondSumCost,fieldCost,
    firstSum,product,exponent,ClockEnvelope.exponent]
  change _≤200*(c+k+1)*q^2
  nlinarith

end NearCubicWires.RepairOrdinary.ClockWordLayout
