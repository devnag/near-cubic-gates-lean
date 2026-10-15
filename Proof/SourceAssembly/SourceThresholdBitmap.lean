import Proof.SourceAssembly.SourceThresholdHeader

/- Cache the actual retained systematic bitmap after the counted scan; its
paid rewind uses only the already-produced local C driver. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdBitmap
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

def rewindSlots : Fin 3→Fin 7:=![0,2,6]
def cacheSlots : Fin 5→Fin 7:=![0,3,4,1,5]
def first:=RecoveryFocus.machine rewindSlots (SourceAssemblyClear.rewind 1)
def last:=RecoveryFocus.machine cacheSlots Bitmap.machine
def machine:=Composition.machine first last
def heads (q : Nat) : Fin 7→Nat:=![q,1,0,0,0,0,0]
def readyHeads : Fin 7→Nat:=![0,1,0,0,0,0,0]
def input (Q q : Nat) (bits : List Bool) (i : Fin 7):=
  if i=0 then ZeroPadding.pad Q bits else if i=1 then CompareMachine.word q else
  if i=2 then List.replicate (Capacity.value q) true else []
def middle (Q q : Nat) (bits : List Bool) (i : Fin 7):=
  if i=6 then List.replicate (Capacity.value q) false else input Q q bits i
def result (Q q : Nat) (bits : List Bool) (k : Nat) (i : Fin 7):=
  if i=3 then frame (weights bits) else if i=4 then frame bits else
  if i=5 then List.replicate k false else middle Q q bits i
def budget (q : Nat):=2*Capacity.value q+42*q+17

theorem rewind_run (Q q : Nat) (bits : List Bool) :
    Step first (2*Capacity.value q+2) (heads q) (input Q q bits) readyHeads (middle Q q bits) := by
  have hC:q≤Capacity.value q:=by unfold Capacity.value;nlinarith [Nat.zero_le (q*q)]
  have raw:=SourceAssemblyClear.raw_rewind (![ZeroPadding.pad Q bits]) (![q])
    (Capacity.value q) (by intro i;fin_cases i;exact hC)
  refine CloseoutRowsEstimator.SubstitutionDock.run _ rewindSlots (by decide) _ _ _ _ _ _ _ _ raw ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl
  · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | rfl

theorem run (Q q : Nat) (bits : List Bool) (hlen : bits.length=q) :
    ∃ k, k≤21*q+6 ∧Step machine (budget q) (heads q) (input Q q bits) readyHeads (result Q q bits k) := by
  obtain ⟨k,hk,hb⟩:=Bitmap.cache_run bits (List.replicate (Q-bits.length) false)
  rw [hlen] at hk hb
  have lastStep : Step last (42*q+14) readyHeads (middle Q q bits) readyHeads (result Q q bits k) := by
    refine CloseoutRowsEstimator.SubstitutionDock.run _ cacheSlots (by decide) _ _ _ _ _ _ _ _ hb ?_ ?_ ?_ ?_ ?_ ?_
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>first | rfl | exact congrArg (fun xs=>bits++xs) (by rw [hlen])
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>first | rfl | exact congrArg (fun xs=>bits++xs) (by rw [hlen])
    · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) | rfl
    · intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) | rfl
  exact ⟨k,hk,((rewind_run Q q bits).seq lastStep).enlarge (by unfold budget;omega)⟩

end
end SourceAssemblyThresholdBitmap
