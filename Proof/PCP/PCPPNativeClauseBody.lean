import Proof.PCP.PCPPNativeClauseBodyLayout

/-! One original compact clause is read and appended as its three native DAG
nodes. The live source/output cursors and actual base/accumulator survive. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseBody
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def references (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n : ℕ) :=
  fun i=>PCPPNativeClauseReusable.reference (indices i) stride (signs i) p n

theorem read_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C base accumulator : ℕ) (out : List Bool)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C) :
    ∃ r,runFrom first (PCPPNativeClauseTriple.budget bits indices signs stride p n C)
      (entry first (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length stride p n C base accumulator (fun _=>0) out)=some r ∧
      r.final.heads=heads (pre++PCPPNativeClauseTriple.fields bits).length out ∧
      r.final.tapes=data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C base accumulator
        (references indices signs stride p n) out ∧
      r.steps≤PCPPNativeClauseTriple.budget bits indices signs stride p n C := by
  obtain ⟨a,ha,ah,atapes,asteps⟩:=PCPPNativeClauseTriple.triple_run pre tail bits indices signs stride p n C hv hC
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock tripleSlots triple_injective
    PCPPNativeClauseTriple.machine _ (heads pre.length out)
    (data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C base accumulator (fun _=>0) out) _
    (fun j=>(triple_input (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length stride p n C base accumulator (fun _=>0) out j).1)
    (fun j=>(triple_input (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length stride p n C base accumulator (fun _=>0) out j).2) a ha
  refine ⟨r,hr,?_,?_,rs.le.trans asteps⟩
  · funext i
    by_cases hi : i.val<25
    · let j : Fin 25:=⟨i.val,hi⟩
      have he : tripleSlots j=i:=Fin.ext rfl
      rw [←he,rh,ah]
      exact (triple_input (pre++PCPPNativeClauseTriple.fields bits++tail)
        (pre++PCPPNativeClauseTriple.fields bits).length stride p n C base accumulator
        (references indices signs stride p n) out j).1.symm
    · rw [(keep i (by intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt; change j.val=i.val at hv; omega)).1]
      have hn : i≠13:=by intro h; subst i; exact hi (by decide)
      simp only [heads,hn,ite_false]
  · funext i
    by_cases hi : i.val<25
    · let j : Fin 25:=⟨i.val,hi⟩
      have he : tripleSlots j=i:=Fin.ext rfl
      rw [←he,rt,atapes]
      exact (triple_input (pre++PCPPNativeClauseTriple.fields bits++tail)
        (pre++PCPPNativeClauseTriple.fields bits).length stride p n C base accumulator
        (references indices signs stride p n) out j).2.symm
    · rw [(keep i (by intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt; change j.val=i.val at hv; omega)).2]
      simp only [data,dif_neg hi]

theorem append_run (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool)
    (hC : PCPPNativeClauseBank.Capacity (PCPPNativeClauseBank.values base accumulator refs) C) :
    ∃ r,runFrom last (PCPPNativeClauseBank.budget (PCPPNativeClauseBank.values base accumulator refs) C)
      (entry last source pos stride p n C base accumulator refs out)=some r ∧
      r.final.heads=heads pos (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator refs)) ∧
      r.final.tapes=data source stride p n C base accumulator refs
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator refs)) ∧
      r.steps≤PCPPNativeClauseBank.budget (PCPPNativeClauseBank.values base accumulator refs) C := by
  obtain ⟨a,ha,asteps,ah,atapes⟩:=PCPPNativeClauseBank.block_run _ C out hC
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock blockSlots block_injective
    PCPPNativeClauseBank.machine _ (heads pos out) (data source stride p n C base accumulator refs out) _
    (fun j=>(block_input source pos stride p n C base accumulator refs out j).1)
    (fun j=>(block_input source pos stride p n C base accumulator refs out j).2) a ha
  refine ⟨r,hr,?_,?_,rs.le.trans asteps⟩
  · funext i
    by_cases hi : ∃ j,blockSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh,ah]
      exact (block_input source pos stride p n C base accumulator refs
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator refs)) j).1.symm
    · rw [(keep i (by intro j h; exact hi ⟨j,h⟩)).1]
      have h47 : i≠47:=by intro h; exact hi ⟨20,h.symm⟩
      simp only [heads,h47,ite_false]
  · funext i
    by_cases hi : ∃ j,blockSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt,atapes]
      exact (block_input source pos stride p n C base accumulator refs
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator refs)) j).2.symm
    · rw [(keep i (by intro j h; exact hi ⟨j,h⟩)).2]
      have h47 : i≠47:=by intro h; exact hi ⟨20,h.symm⟩
      simp only [data,h47,ite_false]

def budget (bits : Fin 3→List Bool) (indices : Fin 3→ℕ) (signs : Fin 3→Bool)
    (stride p n C base accumulator : ℕ) :=
  PCPPNativeClauseTriple.budget bits indices signs stride p n C+1+
    PCPPNativeClauseBank.budget (PCPPNativeClauseBank.values base accumulator (references indices signs stride p n)) C

theorem body_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C base accumulator : ℕ) (out : List Bool)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C)
    (hB : PCPPNativeClauseBank.Capacity
      (PCPPNativeClauseBank.values base accumulator (references indices signs stride p n)) C) :
    ∃ r,runFrom machine (budget bits indices signs stride p n C base accumulator)
      (entry machine (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length stride p n C base accumulator (fun _=>0) out)=some r ∧
      r.final.heads=heads (pre++PCPPNativeClauseTriple.fields bits).length
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (references indices signs stride p n))) ∧
      r.final.tapes=data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C base accumulator
        (references indices signs stride p n)
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (references indices signs stride p n))) ∧
      r.steps≤budget bits indices signs stride p n C base accumulator := by
  obtain ⟨a,ha,ah,atapes,asteps⟩:=read_run pre tail bits indices signs stride p n C base accumulator out hv hC
  obtain ⟨b,hb,bh,bt,bsteps⟩:=append_run _ (pre++PCPPNativeClauseTriple.fields bits).length
    stride p n C base accumulator (references indices signs stride p n) out hB
  have he : Composition.restart a.final last.start=entry last
      (pre++PCPPNativeClauseTriple.fields bits++tail) (pre++PCPPNativeClauseTriple.fields bits).length
      stride p n C base accumulator (references indices signs stride p n) out :=
    configuration_ext rfl ah atapes
  rw [←he] at hb
  exact ⟨Composition.joinedReceipt a b,Composition.run_join first last _ _ _ a b ha hb,bh,bt,
    by change a.steps+1+b.steps≤_; unfold budget; omega⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseBody
