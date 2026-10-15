import Proof.Amplification.RecoveryTseitinClauseAppend

/-! The original free-input Tseitin node clauses, as six finite control
plans over three retained variable references. Every equivalence direction
and duplicate literal remains in the original clause order. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Plan where
  signs : Fin 3→Bool
  sources : Fin 3→Fin 3
def unary (positive : Bool) : Plan := ⟨fun _=>positive,fun _=>0⟩
def implication (positive : Bool) (source : Fin 3) : Plan :=
  ⟨![positive,!positive,!positive],![0,source,source]⟩
def same (positive : Bool) : Plan := ⟨fun _=>positive,![0,1,1]⟩
def binary (positive : Bool) : Plan := ⟨![positive,!positive,!positive],![0,1,2]⟩
def plans : Fin 6→List Plan :=
  ![[unary false],[unary true],[implication false 1,implication true 1],
    [same false,same true],[implication false 1,implication false 2,binary true],
    [implication true 1,implication true 2,binary false]]
def kind {n : Nat} : BooleanNode n→Fin 6
  | .const b=>if b then 1 else 0
  | .input _=>2
  | .not _=>3
  | .and _ _=>4
  | .or _ _=>5
def references {n : Nat} (index : Nat) : BooleanNode n→Fin 3→Nat
  | .const _=>![circuitInputGateVariable n index,0,0]
  | .input i=>![circuitInputGateVariable n index,i.val,0]
  | .not i=>![circuitInputGateVariable n index,circuitInputGateVariable n i,0]
  | .and i j=>![circuitInputGateVariable n index,circuitInputGateVariable n i,circuitInputGateVariable n j]
  | .or i j=>![circuitInputGateVariable n index,circuitInputGateVariable n i,circuitInputGateVariable n j]
def indices (refs : Fin 3→Nat) (p : Plan) : Fin 3→Nat := fun k=>refs (p.sources k)
def clause (refs : Fin 3→Nat) (p : Plan) := RecoveryTseitin.clause (Prepare.literals p.signs (indices refs p))
def formula (refs : Fin 3→Nat) (ps : List Plan) := ps.map (clause refs)

theorem original_node {n : Nat} (index : Nat) (node : BooleanNode n) :
    formula (references index node) (plans (kind node))=circuitInputNodeClauses index node := by
  cases node with
  | const b=>cases b <;> rfl
  | input i=>rfl
  | not i=>rfl
  | and i j=>rfl
  | or i j=>rfl
theorem original_assertion (index : Nat) : clause (fun _=>index) (unary true)=positiveUnit index := rfl

def emitted (refs : Fin 3→Nat) : List Plan→List Bool
  | []=>[]
  | p::ps=>RepairOrdinary.frame (Encodable.encode (clause refs p)).bits++emitted refs ps
theorem emitted_formula (refs : Fin 3→Nat) (ps : List Plan) :
    emitted refs ps=RecoveryFormulaPayload.input (formula refs ps) := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    simp only [emitted,ih,RecoveryFormulaPayload.input,RecoveryFormulaPayload.fields,formula,
      List.map_cons,ProjectionNormalization.FieldList.stream,List.flatten_cons]

end NearCubicWires.RepairSource.RecoveryTseitinNode
