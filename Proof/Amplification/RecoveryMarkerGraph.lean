import Proof.Amplification.RecoveryMarkerAtomSemantics

/-! One fixed marker recognizer replays the original outer code. It checks
the leading empty clause, payload singleton, optional signed two-literal
prefix clause, and exact outer tail. Its retained fields feed the flat or
nested table checker after this executed classification. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev loadStates := stateCount loadMachine
noncomputable abbrev emptyStates := stateCount emptyMachine
noncomputable abbrev atomStates (which : Fin 3) := stateCount (RecoveryMarkerAtom.machine which)
noncomputable abbrev outerStates := stateCount outerMachine
noncomputable def sizes : Fin 11→Nat :=
  ![2,loadStates,emptyStates,loadStates,atomStates 0,loadStates,atomStates 1,atomStates 2,outerStates,2,2]
noncomputable def programs : (j : Fin 11)→Machine 57 (sizes j)
  | ⟨0,_⟩=>RecoveryMarkerFlags.answerMachine false
  | ⟨1,_⟩=>loadMachine
  | ⟨2,_⟩=>emptyMachine
  | ⟨3,_⟩=>loadMachine
  | ⟨4,_⟩=>RecoveryMarkerAtom.machine 0
  | ⟨5,_⟩=>loadMachine
  | ⟨6,_⟩=>RecoveryMarkerAtom.machine 1
  | ⟨7,_⟩=>RecoveryMarkerAtom.machine 2
  | ⟨8,_⟩=>outerMachine
  | ⟨9,_⟩=>RecoveryMarkerFlags.answerMachine true
  | ⟨10,_⟩=>RecoveryMarkerFlags.answerMachine false
  | ⟨n+11,h⟩=>False.elim (by omega)
noncomputable def next (j : Fin 11) (_ : Fin (sizes j)) (bits : Fin 57→Bool) : Option (Fin 11) :=
  ![some 1,some (if bits 52 then 2 else 10),some (if bits 23 then 10 else 3),
    some (if bits 52 then 4 else 10),some (if bits 28 then 5 else 10),
    some (if bits 52 then 6 else 9),some (if bits 28 then 7 else 10),
    some (if bits 28 then 8 else 10),some (if bits 52 then 10 else 9),none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def prefixOutput (x : State) : State :=
  let y := RecoveryMarkerAtom.output 1 x
  if y.inner.present then
    let z := RecoveryMarkerAtom.output 2 y
    if z.inner.present then
      let t := outerStep z
      RecoveryMarkerFlags.answered t (!t.outer.flag)
    else RecoveryMarkerFlags.answered z false
  else RecoveryMarkerFlags.answered y false
def thirdOutput (x : State) : State :=
  let y := loaded x
  if y.outer.flag then prefixOutput y else RecoveryMarkerFlags.answered y true
def payloadOutput (x : State) : State :=
  let y := loaded x
  if y.outer.flag then
    let z := RecoveryMarkerAtom.output 0 y
    if z.inner.present then thirdOutput z else RecoveryMarkerFlags.answered z false
  else RecoveryMarkerFlags.answered y false
def output (x : State) : State :=
  let y := loaded (RecoveryMarkerFlags.answered x false)
  if y.outer.flag then
    let z := emptyStep y
    if z.inner.data.flag then RecoveryMarkerFlags.answered z false else payloadOutput z
  else RecoveryMarkerFlags.answered y false

def prefixBudget (width : Nat) := 4194304*(width+1)^2
def thirdBudget (width : Nat) := 8388608*(width+1)^2
def payloadBudget (width : Nat) := 16777216*(width+1)^2
def budget (width : Nat) := 33554432*(width+1)^2

theorem prefix_valid (x : State) (hx : x.Valid) : (prefixOutput x).Valid := by
  have hy := RecoveryMarkerAtom.output_valid 1 x hx
  have hz := RecoveryMarkerAtom.output_valid 2 _ hy
  have ht := outer_valid _ hz
  dsimp only [prefixOutput]
  split
  · split
    · exact ht
    · exact hz
  · exact hy

theorem prefix_width (x : State) : (prefixOutput x).width=x.width := by
  have hy := RecoveryMarkerAtom.output_width 1 x
  have hz := (RecoveryMarkerAtom.output_width 2 (RecoveryMarkerAtom.output 1 x)).trans hy
  dsimp only [prefixOutput]
  split
  · split <;> exact hz
  · exact hy

end NearCubicWires.RepairOrdinary.RecoveryMarker
