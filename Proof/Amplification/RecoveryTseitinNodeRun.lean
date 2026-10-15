import Proof.Amplification.RecoveryTseitinNodePlans

/-! Execute every clause of a fixed Tseitin node plan using the shared
reusable clause kernel. Runtime references stay on the three retained tapes. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF TseitinCNF RecoveryTseitinClauseAppend
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stop : Machine 241 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
private def stateCount {s : Nat} (_ : Machine 241 s) := s
noncomputable def states : List Plan→Nat
  | []=>1
  | p::ps=>stateCount (emitMachine p.signs p.sources)+states ps
noncomputable def machine : (ps : List Plan)→Machine 241 (states ps)
  | []=>stop
  | p::ps=>Composition.machine (emitMachine p.signs p.sources) (machine ps)
def sourceSlot (i : Fin 3) : Fin 239 := ⟨i.val,by have hi:=i.isLt; omega⟩

theorem plans_run (ps : List Plan) (cap : Nat) (refs : Fin 3→Nat)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hc : ∀ p∈ps,RecoveryTseitin.capacity (Prepare.literals p.signs (indices refs p))≤cap)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate (cap+1) false)
    (hi : ∀ j,ambient (sourceSlot j)=RepairOrdinary.frame (refs j).bits++padding j) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (machine ps) (ps.length*(20*cap+5))
        ⟨(machine ps).start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++emitted refs ps).length ∧
      r.final.tapes=input after (out++emitted refs ps) cap ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate cap true ∧ after 4=List.replicate (cap+1) false ∧
      Bounded cap after ∧ r.steps≤ps.length*(20*cap+5) := by
  induction ps generalizing ambient out with
  | nil=>
    obtain ⟨r,hr,hf,hs⟩ := (Timed.refl stop
      (⟨stop.start,heads out.length,input ambient out cap⟩ : Configuration 241 1)).run (by rfl)
    exact ⟨ambient,r,by simpa only [machine,states,List.length_nil,Nat.zero_mul] using hr,
      by rw [hf]; simp [emitted],by rw [hf]; simp [emitted],
      by intros; rfl,hd,hl,hb,by simpa only [List.length_nil,Nat.zero_mul] using hs.le⟩
  | cons p ps ih=>
    obtain ⟨middle,first,hf,fh,ft,fkeep,fd,fl,fb,fs⟩ :=
      emit_run cap (cap+1) p.signs p.sources (indices refs p) ambient
        (fun j=>padding (p.sources j)) out (hc p (by simp)) hb hd hl (Nat.le_refl _) (by
          intro j
          exact hi (p.sources j))
    obtain ⟨after,last,hr,rh,rt,rkeep,rd,rl,rb,rs⟩ := ih middle
      (out++RepairOrdinary.frame (Encodable.encode (clause refs p)).bits)
      (by intro q hq; exact hc q (by simp [hq])) fb fd fl (by
        intro j
        exact (fkeep (sourceSlot j) j.isLt).trans (hi j))
    have he : Composition.restart first.final (machine ps).start=
        (⟨(machine ps).start,
          heads (out++RepairOrdinary.frame (Encodable.encode (clause refs p)).bits).length,
          input middle (out++RepairOrdinary.frame (Encodable.encode (clause refs p)).bits) cap⟩ :
          Configuration 241 (states ps)) := by
      apply configuration_ext
      · rfl
      · exact fh
      · exact ft
    rw [←he] at hr
    have hwhole := Composition.run_join (emitMachine p.signs p.sources) (machine ps) _ _ _ first last hf hr
    have htime : (20*cap+4)+1+ps.length*(20*cap+5)=(p::ps).length*(20*cap+5) := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    rw [htime] at hwhole
    refine ⟨after,_,hwhole,?_,?_,?_,rd,rl,rb,?_⟩
    · change last.final.heads=_
      simpa only [emitted,List.append_assoc] using rh
    · change last.final.tapes=_
      simpa only [emitted,List.append_assoc] using rt
    · intro i hi
      exact (rkeep i hi).trans (fkeep i hi)
    · change first.steps+1+last.steps≤_
      rw [←htime]
      omega

theorem node_run {n : Nat} (index : Nat) (node : BooleanNode n) (cap : Nat)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hc : ∀ p∈plans (kind node),RecoveryTseitin.capacity
      (Prepare.literals p.signs (indices (references index node) p))≤cap)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate (cap+1) false)
    (hi : ∀ j,ambient (sourceSlot j)=RepairOrdinary.frame (references index node j).bits++padding j) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (machine (plans (kind node))) ((plans (kind node)).length*(20*cap+5))
        ⟨(machine (plans (kind node))).start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node)).length ∧
      r.final.tapes=input after (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node)) cap ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate cap true ∧ after 4=List.replicate (cap+1) false ∧
      Bounded cap after ∧ r.steps≤(plans (kind node)).length*(20*cap+5) := by
  have h:=plans_run (plans (kind node)) cap (references index node) ambient padding out hc hb hd hl hi
  simpa only [emitted_formula,original_node] using h

end NearCubicWires.RepairSource.RecoveryTseitinNode
