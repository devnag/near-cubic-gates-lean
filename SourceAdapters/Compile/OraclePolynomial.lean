import SourceAdapters.Compile.OracleCircuitBounds

/-!
proof of `thm:short-pcp-ours`, Step 4: global polynomial size, with program-dependent coefficient
chosen before the request. Unary seed length and charged fuel both contribute
to the request measure; no bounded input family is used in this estimate.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource
set_option autoImplicit false

def transitionCoefficient (t s : ℕ) := s*(2^t*5000*(t+1)+2)+1
def stateCoefficient (t s : ℕ) := s+19*t+2
def circuitCoefficient (t s : ℕ) :=
  stateCoefficient t s+200+stateCoefficient t s*transitionCoefficient t s+3*s+8

theorem transitionBodyBound_scale (t width cap m : ℕ) (hm : 1 ≤ m)
    (hw : width ≤ 6*m) (hc : cap ≤ m) :
    transitionBodyBound t width cap  ≤  4000*(t+1)*m^3 := by
  have hm2 : m ≤ m^2 := by nlinarith
  have hm3 : m^2 ≤ m^3 := by nlinarith
  have hm13 : m ≤ m^3 := hm2.trans hm3
  have h13 : 1 ≤ m^3 := hm.trans hm13
  have ha : localActionBound width  ≤  171*m^2 := by
    have h1 : width+1 ≤ 7*m := by omega
    have h2 : 3*width+3 ≤ 21*m := by omega
    have hp := Nat.mul_le_mul h1 h2
    unfold localActionBound
    nlinarith
  have hq : queryActionBound width  ≤  1176*m^2 := by
    have h1 : 4*width+6 ≤ 30*m := by omega
    have h2 : 6*width+3 ≤ 39*m := by omega
    have hp := Nat.mul_le_mul h1 h2
    unfold queryActionBound
    nlinarith
  have hl : localGuardBound t width cap  ≤  (20*t+7)*m := by
    have h1 : 3*width+2 ≤ 20*m := by omega
    have hp := Nat.mul_le_mul_left t h1
    unfold localGuardBound
    nlinarith
  have hg : queryGuardBound width cap  ≤  2492*m^3 := by
    have h1 : cap+1 ≤ 2*m := by omega
    have h2 : 3*width+2 ≤ 20*m := by omega
    have hp := Nat.mul_le_mul h1 h2
    have h3 : 2*((cap+1)*(3*width+2)+1)+1 ≤ 83*m^2 := by nlinarith
    have h4 : 4*width+6 ≤ 30*m := by omega
    have hprod := Nat.mul_le_mul h4 h3
    unfold queryGuardBound
    nlinarith
  have ha3 := ha.trans (Nat.mul_le_mul_left 171 hm3)
  have hq3 := hq.trans (Nat.mul_le_mul_left 1176 hm3)
  have hl3 := hl.trans (Nat.mul_le_mul_left (20*t+7) hm13)
  unfold transitionBodyBound
  nlinarith

theorem clockTransitionBound_scale (t s width cap m : ℕ) (hm : 1 ≤ m)
    (hw : width ≤ 6*m) (hc : cap ≤ m) :
    clockTransitionBound t s width cap  ≤  transitionCoefficient t s*m^3 := by
  have hb := transitionBodyBound_scale t width cap m hm hw hc
  have hm3 : m ≤ m^3 := by nlinarith [Nat.mul_self_le_mul_self hm]
  have h13 : 1 ≤ m^3 := hm.trans hm3
  have hrow : t*(2*width+3)+2+transitionBodyBound t width cap+2  ≤  5000*(t+1)*m^3 := by
    have h1 : 2*width+3 ≤ 15*m := by omega
    have h2 := Nat.mul_le_mul_left t (h1.trans (Nat.mul_le_mul_left 15 hm3))
    nlinarith
  have hpow := Nat.mul_le_mul_left (2^t) hrow
  have hs := Nat.mul_le_mul_left s (show
    2^t*(t*(2*width+3)+2+transitionBodyBound t width cap+2)+2  ≤ 
      (2^t*5000*(t+1)+2)*m^3 by nlinarith)
  unfold clockTransitionBound transitionCoefficient
  nlinarith

theorem clockBits_scale (p : OrdinaryOracleProgram) (width cap m : ℕ) (hm : 1 ≤ m)
    (hw : width ≤ 6*m) (hc : cap ≤ m) :
    clockBits p width cap  ≤  stateCoefficient p.base.tapeCount p.base.stateCount*m := by
  have h := Nat.mul_le_mul_left (3*p.base.tapeCount) hw
  have ht := Nat.mul_le_mul_left p.base.tapeCount hm
  have hs := Nat.mul_le_mul_left p.base.stateCount hm
  unfold clockBits windowBits stateCoefficient
  nlinarith

theorem clockRoundBound_scale (p : OrdinaryOracleProgram) (width cap arity m : ℕ)
    (hm : 1 ≤ m) (hw : width ≤ 6*m) (hc : cap ≤ m) (ha : arity ≤ m) :
    clockRoundBound p width cap arity  ≤ 
      (200+stateCoefficient p.base.tapeCount p.base.stateCount*
        transitionCoefficient p.base.tapeCount p.base.stateCount)*m^4 := by
  have hm2 : 1 ≤ m^2 := by nlinarith
  have hm34 : m^3 ≤ m^4 := by
    calc
      m^3 = m^3*1 := by omega
      _ ≤ m^3*m := Nat.mul_le_mul_left _ hm
      _ = m^4 := by ring
  have hm4 : 1 ≤ m^4 := by nlinarith
  have hquery : arity*(width*(4*width+9)+1)+1 ≤ 200*m^4 := by
    have h1 : 4*width+9 ≤ 33*m := by omega
    have hp := Nat.mul_le_mul hw h1
    have h2 : width*(4*width+9)+1 ≤ 199*m^2 := by nlinarith
    have h3 := Nat.mul_le_mul ha h2
    nlinarith
  have hb := clockBits_scale p width cap m hm hw hc
  have ht := clockTransitionBound_scale p.base.tapeCount p.base.stateCount width cap m hm hw hc
  have hprod := Nat.mul_le_mul hb ht
  unfold clockRoundBound
  nlinarith

theorem requestCircuitBound_polynomial (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    requestCircuitBound p r  ≤  circuitCoefficient p.base.tapeCount p.base.stateCount*r.measure^5 := by
  have hm : 1 ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  have hw := requestWidth_bound r
  have hc : r.fuel ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  have ha : r.ell ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  have hb := clockBits_scale p (requestWidth r) r.fuel r.measure hm hw hc
  have hr := clockRoundBound_scale p (requestWidth r) r.fuel r.ell r.measure hm hw hc ha
  have hp := Nat.mul_le_mul hc hr
  have hm15 : r.measure ≤ r.measure^5 := by
    exact Nat.le_self_pow (by omega) r.measure
  have h15 : 1 ≤ r.measure^5 := hm.trans hm15
  have hb5 := hb.trans (Nat.mul_le_mul_left (stateCoefficient p.base.tapeCount p.base.stateCount) hm15)
  have hs := Nat.mul_le_mul_left (3*p.base.stateCount+7) h15
  unfold requestCircuitBound circuitCoefficient
  nlinarith

end NearCubicGates.Adapters.Compile.OracleExecution

namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires.RepairSource OracleExecution
set_option autoImplicit false

theorem requestCircuit_size_polynomial (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestCircuit p r).size  ≤  circuitCoefficient p.base.tapeCount p.base.stateCount*r.measure^5 :=
  (requestCircuit_size p r).trans (requestCircuitBound_polynomial p r)

end NearCubicGates.Adapters.Compile.OracleExpressions
