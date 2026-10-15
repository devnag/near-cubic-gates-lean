import Proof.PCP.PCPPNativeOracleSkip

/-! The actual oracle-size driver skips the original list of native
three-field nodes, preserving the descriptor and restoring its driver. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleSkip
open LocalBitMultitape PCPPQueryField RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream {r : ℕ} (nodes : List (BooleanNode r)) := nodes.flatMap PCPPRequestNodeSchema.native
def savedNodes {r : ℕ} (nodes : List (BooleanNode r)) (backing : List Bool) := nodes.foldl (fun old v => savedNode v old) backing
noncomputable def machine := RepeatMachine.machine node (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (store (s := 12) 0 source pos backing out) total driver

theorem remaining {r : ℕ} (pre : List Bool) (nodes : List (BooleanNode r))
    (tail backing out : List Bool) (total pos : ℕ) (hn : pos+nodes.length=total) :
    Timed machine ((stream nodes).length+10*nodes.length+total+3)
      (cfg 0 (pre++stream nodes++tail) pre.length backing out total (pos+1))
      (cfg 3 (pre++stream nodes++tail) (pre.length+(stream nodes).length)
        (savedNodes nodes backing) out total 1) := by
  induction nodes generalizing pre backing pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa only [machine,cfg,stream,savedNodes,List.flatMap_nil,List.foldl_nil,List.append_nil,
      List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      using RepeatMachine.exhaust node (fun _ _ => true) (store (s := 12) 0 (pre++tail) pre.length backing out) total
  | cons v nodes ih =>
    obtain ⟨body,hbody,bf,bs⟩ := node_run v pre (stream nodes++tail) backing out
    have hstep := RepeatMachine.iteration node (fun _ _ => true)
      (store (s := 12) 0 (pre++PCPPRequestNodeSchema.native v++(stream nodes++tail)) pre.length backing out)
      total pos body rfl (by simp only [List.length_cons] at hn; omega) hbody
    rw [bf,bs] at hstep
    have htail := ih (pre++PCPPRequestNodeSchema.native v) (savedNode v backing) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hsource : (pre++PCPPRequestNodeSchema.native v)++stream nodes++tail=
        pre++PCPPRequestNodeSchema.native v++(stream nodes++tail) := by simp only [List.append_assoc]
    have hmid : cfg 0 (pre++PCPPRequestNodeSchema.native v++(stream nodes++tail))
        (pre.length+(PCPPRequestNodeSchema.native v).length) (savedNode v backing) out total (pos+2)=
      cfg 0 ((pre++PCPPRequestNodeSchema.native v)++stream nodes++tail)
        (pre++PCPPRequestNodeSchema.native v).length (savedNode v backing) out total ((pos+1)+1) := by
      rw [hsource,List.length_append]
    change Timed machine ((PCPPRequestNodeSchema.native v).length+8+2)
      (cfg 0 (pre++PCPPRequestNodeSchema.native v++(stream nodes++tail)) pre.length backing out total (pos+1))
      (cfg 0 (pre++PCPPRequestNodeSchema.native v++(stream nodes++tail))
        (pre.length+(PCPPRequestNodeSchema.native v).length) (savedNode v backing) out total (pos+2)) at hstep
    rw [hmid] at hstep
    have hall := hstep.trans htail
    have ht : (PCPPRequestNodeSchema.native v).length+8+2+
        ((stream nodes).length+10*nodes.length+total+3)=
        (stream (v::nodes)).length+10*(v::nodes).length+total+3 := by
      simp only [stream,List.flatMap_cons,List.length_append,List.length_cons]
      omega
    rw [ht] at hall
    simpa only [stream,List.flatMap_cons,List.append_assoc,List.length_append,
      savedNodes,List.foldl_cons,Nat.add_assoc] using hall

theorem nodes_run {r : ℕ} (pre : List Bool) (nodes : List (BooleanNode r))
    (tail backing out : List Bool) : ∃ result,
    runFrom machine ((stream nodes).length+11*nodes.length+3)
      (cfg 0 (pre++stream nodes++tail) pre.length backing out nodes.length 1)=some result ∧
    result.final=cfg 3 (pre++stream nodes++tail) (pre.length+(stream nodes).length)
      (savedNodes nodes backing) out nodes.length 1 ∧
    result.steps=(stream nodes).length+11*nodes.length+3 := by
  have h := remaining pre nodes tail backing out nodes.length 0 (by omega)
  have ht : (stream nodes).length+10*nodes.length+nodes.length+3=(stream nodes).length+11*nodes.length+3 := by omega
  rw [ht] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairOrdinary.PCPPNativeOracleSkip
