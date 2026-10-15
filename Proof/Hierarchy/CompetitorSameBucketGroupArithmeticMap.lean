import Proof.Hierarchy.CompetitorSameBucketGroupArithmeticFields

/-! Concrete finite tape maps, with inverse picks checked once before the
arithmetic run is specialized to the full data endpoint. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmeticMap
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addSlots : Fin 5 → Fin 11 := ![2,5,6,7,8]
def eraseSlots : Fin 8 → Fin 11 := ![2,3,4,6,7,8,9,10]
theorem add_injective : Function.Injective addSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide

theorem add_pick (i : Fin 11) : RecoveryFocus.pick addSlots i=
    (![none,none,some 0,none,none,some 1,some 2,some 3,some 4,none,none] : Fin 11 → Option (Fin 5)) i := by
  fin_cases i
  · decide
  · decide
  · exact RecoveryFocus.pick_slot addSlots add_injective 0
  · decide
  · decide
  · exact RecoveryFocus.pick_slot addSlots add_injective 1
  · exact RecoveryFocus.pick_slot addSlots add_injective 2
  · exact RecoveryFocus.pick_slot addSlots add_injective 3
  · exact RecoveryFocus.pick_slot addSlots add_injective 4
  · decide
  · decide

theorem erase_pick (i : Fin 11) : RecoveryFocus.pick eraseSlots i=
    (![none,none,some 0,some 1,some 2,none,some 3,some 4,some 5,some 6,some 7] : Fin 11 → Option (Fin 8)) i := by
  fin_cases i
  · decide
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 4
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 5
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 6
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 7

theorem install_add (u v x f z a b raw log : List Bool) :
    install addSlots ![u,v,x,f,z,a,z,z,z,raw,log] ![x,b,b,z,z]=
      ![u,v,x,f,z,b,b,z,z,raw,log] := by
  funext i
  fin_cases i <;> simp [install,add_pick]

theorem install_clear (u v a z raw log : List Bool) (scratch : Fin 6 → List Bool) :
    install eraseSlots ![u,v,scratch 0,scratch 1,scratch 2,a,scratch 3,scratch 4,scratch 5,raw,log]
      (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool) (fun _=>z) (fun _=>raw)) (fun _=>log))=
      ![u,v,z,z,z,a,z,z,z,raw,log] := by
  funext i
  fin_cases i <;> simp [install,erase_pick,Fin.addCases]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmeticMap
