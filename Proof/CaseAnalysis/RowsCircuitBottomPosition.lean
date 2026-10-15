import Proof.CaseAnalysis.RowsCircuitReturnHeads

/-! One paid move positions the original membership frame and the actual
bottom-count template. The threshold top already retains the latter at one. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 1703:=![1692,624]
def worker (threshold : Bool) : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,![.right,if threshold then .stay else .right]⟩ else none
noncomputable def machine (threshold : Bool):=RecoveryFocus.machine slots (worker threshold)
def heads (threshold : Bool) : Fin 2 → ℕ:=![0,if threshold then 1 else 0]
def output (H : Fin 1703 → ℕ):=Function.update (Function.update H 1692 1) 624 1

theorem position_run (threshold : Bool) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hm : H 1692=0) (hc : H 624=if threshold then 1 else 0) :
    PCPOuter.Exact (machine threshold) 1 H A (output H) A:=by
  let input:Configuration 2 2:=⟨0,heads threshold,fun i=>A (slots i)⟩
  let final:Configuration 2 2:=⟨1,fun _=>1,fun i=>A (slots i)⟩
  have hs:step (worker threshold) input=some final:=by
    apply congrArg some;apply configuration_ext
    · rfl
    · funext i;cases threshold <;> fin_cases i <;> rfl
    · rfl
  obtain ⟨base,hb,bf,bs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots (by decide) (worker threshold) 1 H A input
    (by intro i;fin_cases i;exact hm;exact hc) (by intro i;rfl) base hb
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · funext i
    by_cases h624:i=624
    · subst i;rw [output,Function.update_self]
      change r.final.heads (slots 1)=1
      rw [rh,bf]
    by_cases h1692:i=1692
    · subst i;rw [output,Function.update_of_ne (by decide : (1692 : Fin 1703)≠624),Function.update_self]
      change r.final.heads (slots 0)=1
      rw [rh,bf]
    rw [output,Function.update_of_ne h624,Function.update_of_ne h1692]
    exact (keep i (by intro j;fin_cases j;exact Ne.symm h1692;exact Ne.symm h624)).1
  · funext i
    by_cases hit:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hit;rw [rt,bf]
    · exact (keep i (by simpa only [not_exists] using hit)).2

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition
