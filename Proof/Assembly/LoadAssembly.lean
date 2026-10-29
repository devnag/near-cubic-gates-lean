import Proof.Assembly.Fetch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource.VerifierDecoding RecoveryRootRound
namespace FetchRecipes
open CloseoutRowsTupleSeek
open IndexFetchProgram

/-- Only the immediate parent composition. Prefix, fetch correctness and tail
remain explicit inputs; this constructs none of their words or runs. -/
theorem assembleLoad (correct : Correct) {U ps qs : Nat}
 (prefixProgram : Machine U ps) (tail : Machine U qs)
 (slots : Fin 31 → Fin U) (hi : Function.Injective slots)
 (ts : List TermSlices) (js : List (Fin ts.length)) (C D : Nat)
 (hC : ∀ t∈ts,t.cost+1≤C) (hD : ∀ i,(familyWords ts i).length≤D)
 (hfour : js.length≤4) (hindex : (tupleWord js).length≤C)
 (pos : Fin 3 → Nat) (hpos : ∀ i,pos i≤D)
 (caps : Fin 31 → Nat) (ambientH : Fin U → Nat) (ambientT : Fin U → List Bool)
 (hin hout : Fin U → Nat) (tin tout : Fin U → List Bool)
 (prefixCost tailCost loadCost : Nat)
 (hp : Step prefixProgram prefixCost hin tin
  (dockH slots ambientH (entryH pos))
  (install slots ambientT (fun i=>ZeroPadding.pad (caps i) (entryT ts js C D i))))
 (ht : Step tail tailCost
  (dockH slots ambientH (exitH ts js))
  (install slots ambientT (fun i=>ZeroPadding.pad (caps i) (exitT ts js C D i)))
  hout tout)
 (hb : prefixCost+1+(cost ts js C D+1+tailCost)≤loadCost) :
 Step (Composition.machine prefixProgram
  (Composition.machine (RecoveryFocus.machine slots IndexFetchProgram.machine) tail))
  loadCost hin tin hout tout := by
 have hf : Step IndexFetchProgram.machine (cost ts js C D)
   (entryH pos) (fun i=>ZeroPadding.pad (caps i) (entryT ts js C D i))
   (exitH ts js) (fun i=>ZeroPadding.pad (caps i) (exitT ts js C D i)) :=
  (correct ts js C D hC hD hfour hindex pos hpos).pad caps
 have focused : Step (RecoveryFocus.machine slots IndexFetchProgram.machine)
   (cost ts js C D)
   (dockH slots ambientH (entryH pos))
   (install slots ambientT (fun i=>ZeroPadding.pad (caps i) (entryT ts js C D i)))
   (dockH slots ambientH (exitH ts js))
   (install slots ambientT (fun i=>ZeroPadding.pad (caps i) (exitT ts js C D i))) :=
  hf.focus slots hi ambientH ambientT
 exact (hp.seq (focused.seq ht)).enlarge hb
end FetchRecipes
