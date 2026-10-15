import Proof.PCP.PCPPNativeCompactNodes

/-! The whole node emitter consumes exactly the physically measured
counter outputs. Its native header arity copy remains disjoint. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 363) : Fin 438 :=
  if i=0 then 45 else if i=1 then 32 else if i=2 then 48 else if i=18 then 71
  else if i=19 then 53 else if i=20 then 58 else if i=95 then 0 else if i=96 then 52
  else if i=291 then 57 else i.natAdd 75
theorem slots_injective : Function.Injective slots := by decide
def nodeInput (bits query clause : List Bool) (R Q s M Lq Lc : ℕ) (i : Fin 363) : List Bool :=
  if i=0 then List.replicate Q true else if i=1 then List.replicate s true
  else if i=2 then List.replicate M true else if i=18 then List.replicate R true
  else if i=19 then List.replicate Lq true else if i=20 then List.replicate Lc true
  else if i=95 then bits else if i=96 then query else if i=291 then clause else []
theorem node_input (bits query clause : List Bool) (R Q s M Lq Lc : ℕ) :
    PCPPNativeClauseOracle.input (PCPPNativeQueryConjunction.input bits query R Q s M Lq Lc) clause=
      nodeInput bits query clause R Q s M Lq Lc := by
  funext i
  fin_cases i <;> rfl
noncomputable def first := TapeEmbedding.machine 363 PCPPNativeColdCounters.machine
noncomputable def second := RecoveryFocus.machine slots PCPPNativeClauseOracle.machine
noncomputable def machine := Composition.machine first second
def input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) : Fin 438 → List Bool :=
  Fin.addCases (m:=75) (n:=363) (motive:=fun _=>List Bool) (PCPPNativeColdCounters.input oracle p R Q) (fun _=>[])
def heads : Fin 438 → ℕ := Fin.addCases (m:=75) (n:=363) (motive:=fun _=>ℕ) PCPPNativeColdCounters.heads (fun _=>0)
noncomputable def entry (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) :=
  (⟨machine.start,heads,input oracle p R Q⟩ : Configuration 438 _)
def budget {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :=
  PCPPNativeColdCounters.budget p R Q oracle.size+1+
    PCPPNativeClauseOracle.budget oracle Q (Codec.clauses p).length
      (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length

end NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
