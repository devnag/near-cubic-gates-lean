import Proof.CaseAnalysis.CommonPortBank

/-! Fresh worker banks inherit only their explicitly shared input fields.
No allocated work or restored inactive cursor is supplied by this layout. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPortBank
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem input_bank {m n t : ℕ} (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (ambient : Fin t→List Bool) (input : Fin n→List Bool)
    (fields : ∀ j,ambient (shared j)=input (localPort j))
    (blank : ∀ i,(∀ j,localPort j≠i) → input i=[]) (i : Fin n) :
    Fin.addCases (m:=t) (n:=n) (motive:=fun _=>List Bool) ambient (fun _=>[])
      (slot localPort shared i)=input i:=by
  cases hp : RecoveryFocus.pick localPort i with
  | none =>
    have hi : ∀ j,localPort j≠i:=by
      intro j he
      have hex : ∃ j,localPort j=i:=⟨j,he⟩
      simp only [RecoveryFocus.pick,dif_pos hex] at hp
      contradiction
    simp only [slot,hp,Fin.addCases_right,blank i hi]
  | some j =>
    have he:=RecoveryFocus.slot_of_pick localPort hp
    simp only [slot,hp,Fin.addCases_left]
    exact (fields j).trans (congrArg input he)

theorem heads_bank {m n t : ℕ} (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (heads : Fin t→ℕ) (fields : ∀ j,heads (shared j)=0) (i : Fin n) :
    Fin.addCases (m:=t) (n:=n) (motive:=fun _=>ℕ) heads (fun _=>0)
      (slot localPort shared i)=0:=by
  cases hp : RecoveryFocus.pick localPort i with
  | none =>simp only [slot,hp,Fin.addCases_right]
  | some j =>simpa only [slot,hp,Fin.addCases_left] using fields j

end
end NearCubicWires.RepairSource.CloseoutCommonPortBank
