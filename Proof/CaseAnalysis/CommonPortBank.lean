import Proof.Amplification.RecoveryReadyCalls

/-! The common dispatcher shares only explicitly selected physical ports.
Every other worker tape occupies a fresh bank. This is static finite wiring;
the existing focus theorem transports the actual transitions and their cost. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPortBank
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {m n t : ℕ}

def slot (localPort : Fin m→Fin n) (shared : Fin m→Fin t) (i : Fin n) : Fin (t+n):=
  match RecoveryFocus.pick localPort i with
  | some j => (shared j).castAdd n
  | none => i.natAdd t

theorem shared_slot (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (hi : Function.Injective localPort) (j : Fin m) :
    slot localPort shared (localPort j)=(shared j).castAdd n:=by
  simp only [slot,RecoveryFocus.pick_slot localPort hi]

theorem fresh_slot (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (i : Fin n) (hi : ∀ j,localPort j≠i) : slot localPort shared i=i.natAdd t:=by
  have hn : RecoveryFocus.pick localPort i=none:=by
    cases h : RecoveryFocus.pick localPort i with
    | none => rfl
    | some j => exact False.elim (hi j (RecoveryFocus.slot_of_pick localPort h))
  simp only [slot,hn]

theorem injective (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (hs : Function.Injective shared) : Function.Injective (slot localPort shared):=by
  intro i j he
  cases hi : RecoveryFocus.pick localPort i with
  | none =>
    cases hj : RecoveryFocus.pick localPort j with
    | none =>
      have hv:=congrArg Fin.val he
      simp only [slot,hi,hj,Fin.val_natAdd] at hv
      exact Fin.ext (by omega)
    | some b =>
      have hv:=congrArg Fin.val he
      have hb:=(shared b).isLt
      simp only [slot,hi,hj,Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
  | some a =>
    cases hj : RecoveryFocus.pick localPort j with
    | none =>
      have hv:=congrArg Fin.val he
      have ha:=(shared a).isLt
      simp only [slot,hi,hj,Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    | some b =>
      have hab : shared a=shared b:=by
        apply Fin.ext
        simpa only [slot,hi,hj,Fin.val_castAdd] using congrArg Fin.val he
      exact (RecoveryFocus.slot_of_pick localPort hi).symm.trans
        ((congrArg localPort (hs hab)).trans (RecoveryFocus.slot_of_pick localPort hj))

theorem outside (localPort : Fin m→Fin n) (shared : Fin m→Fin t)
    (i : Fin t) (hi : ∀ j,shared j≠i) (j : Fin n) :
    slot localPort shared j≠i.castAdd n:=by
  intro he
  cases hj : RecoveryFocus.pick localPort j with
  | none =>
    have hv:=congrArg Fin.val he
    have hb:=i.isLt
    simp only [slot,hj,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  | some a =>
    apply hi a
    apply Fin.ext
    simpa only [slot,hj,Fin.val_castAdd] using congrArg Fin.val he

end
end NearCubicWires.RepairSource.CloseoutCommonPortBank
