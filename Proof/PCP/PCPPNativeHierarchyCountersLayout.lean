import Proof.PCP.PCPPNativeCounters
import Proof.PCP.PCPPNativeHierarchyReady

/-! Literal original hierarchy fields dock directly into the paid metadata
and mass scans. All counter workspace is physically fresh. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def base (k : ℕ) := PCPPNativeHierarchy.tapes source k
def tapes (k : ℕ) := base source k+75
def sourcePorts (k : ℕ) : Fin 6 → Fin (base source k) :=
  ![PCPPNativeHierarchy.loadSlots source k 2,
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.old source k (HierarchyStreams.bitsQ source k)),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 46),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 29),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 25),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 38)]
def sourceValues (k : ℕ) : Fin 6 → ℕ :=
  ![2,4+(HierarchyStreams.bitsQ source k).val,4+HierarchyStreams.base source k+46,
    4+HierarchyStreams.base source k+29,4+HierarchyStreams.base source k+25,4+HierarchyStreams.base source k+38]
theorem source_values (k : ℕ) (i : Fin 6) : (sourcePorts source k i).val=sourceValues source k i := by
  have hp : 0<(HierarchyStreams.bitsQ source k).val := HierarchyStreams.slot_positive source k _
  fin_cases i <;>
    simp [sourcePorts,sourceValues,PCPPNativeHierarchy.hierarchySlots,PCPPNativeHierarchy.loadSlots,
      HierarchyStreams.old,HierarchyStreams.slots,Nat.ne_of_gt hp,Nat.add_assoc]

def slots (k : ℕ) (i : Fin 75) : Fin (tapes source k) :=
  if i=0 then (sourcePorts source k 0).castAdd 75
  else if i=40 then (sourcePorts source k 1).castAdd 75
  else if i=47 then (sourcePorts source k 2).castAdd 75
  else if i=52 then (sourcePorts source k 3).castAdd 75
  else if i=54 then (sourcePorts source k 4).castAdd 75
  else if i=57 then (sourcePorts source k 5).castAdd 75
  else i.natAdd (base source k)
theorem slots_injective (k : ℕ) : Function.Injective (slots source k) := by
  intro a b he
  have hbits := (HierarchyStreams.bitsQ source k).isLt
  have hp : 0<(HierarchyStreams.bitsQ source k).val := HierarchyStreams.slot_positive source k _
  have hv := congrArg Fin.val he
  have hb : base source k=4+(HierarchyStreams.base source k+48) := rfl
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd,source_values] at hv
  all_goals try simp [sourceValues] at hv
  all_goals (subst_vars; first | rfl | exact Fin.ext (by omega))

def first (k CH Cpad : ℕ) (code : List Bool) :=
  TapeEmbedding.machine 75 (PCPPNativeHierarchy.machine source k CH Cpad code)
def second (k : ℕ) := RecoveryFocus.machine (slots source k) PCPPNativeColdCounters.machine
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (first source k CH Cpad code) (second source k)
def input (k : ℕ) (a oracle : List Bool) : Fin (tapes source k) → List Bool :=
  Fin.addCases (m:=base source k) (n:=75) (motive:=fun _=>List Bool)
    (PCPPNativeHierarchy.input source k a oracle) (fun _=>[])

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
