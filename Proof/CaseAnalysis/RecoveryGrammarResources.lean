import Proof.CaseAnalysis.RecoveryGrammarRoom

/-! The original grammar uses the same coarse C/D/L reservations and row
backing as the original verifier rows. This supplies the complete Room value;
physical production of these resources remains in the cold compiler. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarResources
open RecoveryBoundedGrammarCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def backing (W S : ℕ) := 32*S+10000000000*(W+1)^6+64

private theorem scaled (W c e : ℕ) (hc : c≤10000000000) (he : e≤6) :
    c*(W+1)^e≤10000000000*(W+1)^6 :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he)

private theorem reserve (W S t : ℕ) (ht : t≤10000000000*(W+1)^6) :
    S+t+3≤backing W S := by unfold backing;omega

theorem unary_log (limit W : ℕ) (hl : limit≤W) :
    RecoveryBoundedNativeUnaryJoin.budget limit (16384*(W+1)^2)≤
      8388608*(W+1)^3 := by
  have h:=RecoveryBoundedUnaryReuse.budget_cubic limit W hl
  have hp : 0<(W+1)^3 := by positivity
  unfold RecoveryBoundedUnaryReuse.budget at h
  omega

theorem fold_cubic (conjunction : Bool) (count W : ℕ) (hc : count≤W) :
    RecoveryBoundedGrammarFold.budget conjunction count (16384*(W+1)^2)≤
      600000*(W+1)^3 := by
  have hb : (RecoveryBoundedGrammarFold.bits conjunction).length≤100 := by
    cases conjunction <;> decide
  have hm:=Nat.mul_le_mul_right (24*(16384*(W+1)^2)+67) hc
  unfold RecoveryBoundedGrammarFold.budget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

theorem room (W S : ℕ) (hS : 1≤S) :
    Room W (16384*(W+1)^2) (8388608*(W+1)^3)
      (268435600*(W+1)^4) S (backing W S) (backing W S) := by
  have hC:=reserve W S _ (scaled W 16384 2 (by omega) (by omega))
  have hD:=reserve W S _ (scaled W 8388608 3 (by omega) (by omega))
  have hL:=reserve W S _ (scaled W 268435600 4 (by omega) (by omega))
  have hW : 2*W+2≤16384*(W+1)^2 := by nlinarith [Nat.zero_le (W^2)]
  refine ⟨rfl,by omega,by omega,by omega,by omega,hS,by omega,?_,
    fun limit hl=>unary_log limit W hl,le_rfl,?_,?_,?_,?_⟩
  · have hp : 4*(16384*(W+1)^2)+10*W+20≤70000*(W+1)^2 := by
      nlinarith [Nat.zero_le (W^2)]
    have h:=reserve W S _ (hp.trans (scaled W 70000 2 (by omega) (by omega)))
    omega
  · intro limit hl
    have h:=RecoveryBoundedUnaryReuse.budget_cubic limit W hl
    have hr:=reserve W S _ (scaled W 8388610 3 (by omega) (by omega))
    omega
  · intro upper hu
    have h:=RecoveryBoundedAddressFinish.reset_budget_quartic upper W hu
    have hr:=reserve W S _ (scaled W 268435802 4 (by omega) (by omega))
    change S+(2*RecoveryBoundedAddressFinish.budget upper W+2)+3≤backing W S
    omega
  · intro conjunction count hc
    have h:=fold_cubic conjunction count W hc
    have hr:=reserve W S _ (scaled W 600000 3 (by omega) (by omega))
    omega
  · have hp : W*(2*W+1)≤3*(W+1)^2 := by nlinarith [Nat.zero_le (W^2)]
    have h:=reserve W S _ (hp.trans (scaled W 3 2 (by omega) (by omega)))
    omega

end NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarResources
