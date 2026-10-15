import Proof.SourceAssembly.SourceClear

/- The paid cleanup is consumed by the actual MaskSeedCode.Ready boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyRefill
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open FixedLivePackets PacketProduction
open MaskedFamilySource
open SourceAssemblyClear (join)
noncomputable section

def prepend {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U s : Nat}
    (c : MaskSeedCode mask packet U) (p : Machine U s) : MaskSeedCode mask packet U :=
  { c with prefixStates := _, lead := Composition.machine p c.lead }

theorem prepend_ready {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U s : Nat}
    (c : MaskSeedCode mask packet U) (p : Machine U s) (r : Request) (n fuel : Nat)
    (H₀ H H' : Fin U → Nat) (A₀ A A' : Fin U → List Bool)
    (before : Step p n H₀ A₀ H A) (rest : c.Ready r fuel H H' A A') :
    (prepend c p).Ready r (n+1+fuel) H₀ H' A₀ A' := by
  obtain ⟨mR,mH,mA,pR,pH,pA,leadFuel,suffixFuel,tailFuel,lead,suffix,tail,bound⟩ := rest
  refine ⟨mR,mH,mA,pR,pH,pA,n+1+leadFuel,suffixFuel,tailFuel,
    before.seq lead,suffix,tail,?_⟩
  omega

def recycled {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U t : Nat}
    (c : MaskSeedCode mask packet U) (slots : Fin (t+1+1) → Fin U) :=
  prepend c (RecoveryFocus.machine slots (SourceAssemblyClear.machine t))

/-- A next request, including a smaller request or the terminal tag, starts on
the same fixed backing after an actual paid erase.  Ambient immutable tapes
and their heads are preserved, since only the supplied scratch slots are focused.
The Ready premise concerns the next paid loader, not resident packet outputs. -/
theorem recycled_ready {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U t : Nat}
    (c : MaskSeedCode mask packet U) (slots : Fin (t+1+1) → Fin U)
    (hs : Function.Injective slots) (r : Request) (fuel C : Nat)
    (ambientH H' : Fin U → Nat) (ambientA A' : Fin U → List Bool)
    (dirty : Fin t → List Bool) (heads : Fin t → Nat)
    (hH : ∀ i, heads i≤C) (hA : ∀ i, (dirty i).length≤C)
    (next : c.Ready r fuel (dockH slots ambientH (fun _ => 0)) H'
      (install slots ambientA (join (fun _ : Fin t => List.replicate C false)
        (List.replicate C true) (List.replicate (C+1) false))) A') :
    (recycled c slots).Ready r (4*C+8+fuel)
      (dockH slots ambientH (join heads 0 0)) H'
      (install slots ambientA (join dirty (List.replicate C true)
        (List.replicate (C+1) false))) A' := by
  have clear := (SourceAssemblyClear.clear_run dirty heads C hH hA).focus
    slots hs ambientH ambientA
  simpa only [recycled,show 4*C+7+1+fuel=4*C+8+fuel by omega] using
    prepend_ready c _ r (4*C+7) fuel _ _ H' _ _ A' clear next

end
end SourceAssemblyRefill
