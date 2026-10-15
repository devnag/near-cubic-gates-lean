import Proof.PCP.PCPPQueryClauseCached
import Proof.PCP.PCPSerializerTapeSupport

/-! Paid head restoration for the SAME cached clause object. Allocated
scratch and native result padding remain explicit for repeated callers. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseReset
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (j : Fin 16) := decide (j≠13 ∧ j≠14)
def caps (C : ℕ) (j : Fin 17) := if 0<j.val ∧ j.val<13 ∨ j=15 ∨ j=16 then C else 0
noncomputable def machine := MaskedReset.machine PCPPQueryClause.machine selected
noncomputable def entry (source : List Bool) (arity index C : ℕ) :=
  ZeroPadding.config (caps C) (Rewind.recording (PCPPQueryClause.entry source arity index) 0)

theorem initial_head (source : List Bool) (arity index : ℕ) (j : Fin 16)
    (hj : selected j=true) : (PCPPQueryClause.entry source arity index).heads j=0 := by
  have he : j≠13 ∧ j≠14 := of_decide_eq_true hj
  change (if j=13 ∨ j=14 then 1 else 0)=0
  simp only [he.1,he.2,or_self,if_false]

theorem initial_work (source : List Bool) (arity index : ℕ) (j : Fin 16)
    (hj : 0<j.val ∧ j.val<13 ∨ j=15) :
    (PCPPQueryClause.entry source arity index).heads j=0 ∧
      (PCPPQueryClause.entry source arity index).tapes j=[] := by
  have h0 : j≠0 := by intro h; subst j; rcases hj with hj|hj <;> simp at hj
  have h13 : j≠13 := by intro h; subst j; rcases hj with hj|hj <;> simp at hj
  have h14 : j≠14 := by intro h; subst j; rcases hj with hj|hj <;> simp at hj
  constructor
  · exact initial_head source arity index j (by simp [selected,h13,h14])
  · change (if j=0 then source else if j=13 then UnaryTemplate.tape arity
      else if j=14 then UnaryTemplate.tape index else [])=[]
    simp only [h0,h13,h14,if_false]

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin (2^p.clauseBits)) (C : ℕ) (hC : PCPPQueryClause.queryBudget r p i+1 ≤ C) :
    ∃ receipt,runFrom machine (2*PCPPQueryClause.queryBudget r p i+2)
      (entry (pcppOutput r p) r.arity i.val C)=some receipt ∧
      receipt.steps≤2*PCPPQueryClause.queryBudget r p i+2 ∧
      receipt.final.tapes 0=pcppOutput r p ∧
      receipt.final.tapes 13=UnaryTemplate.tape r.arity ∧
      receipt.final.tapes 14=UnaryTemplate.tape i.val ∧
      receipt.final.tapes 15=ZeroPadding.pad C
        (natListWord [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]) ∧
      (∀ j,receipt.final.heads j=if j=13 ∨ j=14 then 1 else 0) ∧
      (∀ j : Fin 17,0<j.val ∧ j.val<13 ∨ j=15 ∨ j=16 → (receipt.final.tapes j).length ≤ C) := by
  obtain ⟨raw,hr,hs,hout,hsource,harity,hh13,hindex,hh14⟩ :=
    PCPPQueryClause.lookup_retained_run r p i
  have hp := (prefix_of_run PCPPQueryClause.machine _ _ raw hr).1
  have hhead : ∀ j,selected j=true → raw.final.heads j ≤ raw.steps := by
    intro j hj
    have h := SelectiveReset.prefix_head hp j
    rw [initial_head _ _ _ j hj,Nat.zero_add] at h
    exact h
  have hsmall (j : Fin 16) (hj : 0<j.val ∧ j.val<13 ∨ j=15) :
      (raw.final.tapes j).length ≤ C := by
    have hz := initial_work (pcppOutput r p) r.arity i.val j hj
    have h := PCPSerializerReuse.tape_support PCPPQueryClause.machine _ _ raw hr j 0 0
      (by rw [hz.1]) (by rw [hz.2]; simp)
    simp only [Nat.zero_add,max_eq_right (Nat.zero_le _)] at h
    omega
  obtain ⟨reset,hreset,rf,rs,_⟩ :=
    MaskedReset.reset_run PCPPQueryClause.machine selected _ _ raw hr hhead
  obtain ⟨result,hresult,ff,fs,_⟩ := ZeroPadding.run_config machine (caps C) _ _ reset hreset
  have htime : 2*raw.steps+2 ≤ 2*PCPPQueryClause.queryBudget r p i+2 := by omega
  have more := runFrom_moreFuel machine (2*raw.steps+2)
    ((2*PCPPQueryClause.queryBudget r p i+2)-(2*raw.steps+2)) _ result hresult
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨result,more,(fs.trans rs).le.trans htime,?_,?_,?_,?_,?_,?_⟩
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 0)=pcppOutput r p
    rw [ZeroPadding.pad_zero,hsource]
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 13)=UnaryTemplate.tape r.arity
    rw [ZeroPadding.pad_zero,harity]
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 14)=UnaryTemplate.tape i.val
    rw [ZeroPadding.pad_zero,hindex]
  · rw [ff,rf]
    change ZeroPadding.pad C (raw.final.tapes 15)=_
    rw [hout]
  · intro j
    rw [ff,rf]
    fin_cases j <;> simp [ZeroPadding.config,SelectiveReset.finished,Rewind.config,
      Fin.addCases,selected,hh13,hh14]
  · intro j hj
    rw [ff,rf]
    rcases hj with hj|rfl|rfl
    · let k : Fin 16 := ⟨j.val,by omega⟩
      have he : j=k.castAdd 1 := Fin.ext rfl
      rw [he]
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
      change (ZeroPadding.pad (caps C (k.castAdd 1)) (raw.final.tapes k)).length ≤ C
      have hc : caps C (k.castAdd 1)=C := by simp [caps,k,hj]
      rw [hc,ZeroPadding.pad_length]
      exact max_le le_rfl (hsmall k (Or.inl hj))
    · change (ZeroPadding.pad C (raw.final.tapes 15)).length ≤ C
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl (hsmall 15 (Or.inr rfl))
    · change (ZeroPadding.pad C (List.replicate raw.steps false)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact max_le le_rfl (by omega)

end NearCubicWires.RepairOrdinary.PCPPQueryClauseReset
