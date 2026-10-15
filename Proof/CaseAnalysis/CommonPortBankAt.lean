import Proof.CaseAnalysis.CommonPortBankInput

/-! Pointwise cold-input matching in an ambient bank. This form keeps
concrete worker tape counts out of nested Fin.addCases elaboration. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPortBank
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem input_at {m n t : ℕ} (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (ambient : Fin (t+n)→List Bool) (input : Fin n→List Bool)
    (fields : ∀ j,ambient ((shared j).castAdd n)=input (localPort j))
    (fresh : ∀ i : Fin n,ambient (i.natAdd t)=[])
    (blank : ∀ i,(∀ j,localPort j≠i) → input i=[]) (i : Fin n) :
    ambient (slot localPort shared i)=input i:=by
  cases hp : RecoveryFocus.pick localPort i with
  | none =>
    have hi : ∀ j,localPort j≠i:=by
      intro j he
      have hex : ∃ j,localPort j=i:=⟨j,he⟩
      simp only [RecoveryFocus.pick,dif_pos hex] at hp
      contradiction
    simp only [slot,hp,fresh,blank i hi]
  | some j =>
    have he:=RecoveryFocus.slot_of_pick localPort hp
    simp only [slot,hp]
    exact (fields j).trans (congrArg input he)

end
end NearCubicWires.RepairSource.CloseoutCommonPortBank
