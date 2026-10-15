import Proof.PCP.PCPPNativeClauseFullStages

/-! A whole reusable original-clause iteration. The source/output cursors
advance, the actual two DAG counters advance, and all temporary references
return to the same paid zero bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def Run {s : ℕ} (m : Machine 51 s) (fuel : ℕ)
    (h0 h1 : Fin 51→ℕ) (d0 d1 : Fin 51→List Bool) : Prop :=
  ∃ r,runFrom m fuel ⟨m.start,h0,d0⟩=some r ∧
    r.final.heads=h1 ∧ r.final.tapes=d1 ∧ r.steps≤fuel

private theorem join {s t : ℕ} (a : Machine 51 s) (b : Machine 51 t)
    (fa fb : ℕ) (h0 h1 h2 : Fin 51→ℕ) (d0 d1 d2 : Fin 51→List Bool)
    (ha : Run a fa h0 h1 d0 d1) (hb : Run b fb h1 h2 d1 d2) :
    Run (Composition.machine a b) (fa+1+fb) h0 h2 d0 d2 := by
  obtain ⟨ra,ar,ah,atapes,as⟩:=ha
  obtain ⟨rb,br,bh,bt,bs⟩:=hb
  have he : Composition.restart ra.final b.start=⟨b.start,h1,d1⟩:=configuration_ext rfl ah atapes
  rw [←he] at br
  exact ⟨Composition.joinedReceipt ra rb,Composition.run_join a b fa fb _ ra rb ar br,bh,bt,
    by change ra.steps+1+rb.steps≤fa+1+fb; omega⟩

def budget (bits : Fin 3→List Bool) (indices : Fin 3→ℕ) (signs : Fin 3→Bool)
    (stride p n C base accumulator : ℕ) :=
  PCPPNativeClauseBody.budget bits indices signs stride p n C base accumulator+1+(6*base+20)+1+(2*C+4)

theorem body_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C base accumulator : ℕ) (out : List Bool)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C)
    (hB : PCPPNativeClauseBank.Capacity
      (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n)) C)
    (hr : ∀ i,PCPPNativeClauseBody.references indices signs stride p n i≤C)
    (ha : accumulator≤base) (hc : base+3≤C) :
    ∃ r,runFrom machine (budget bits indices signs stride p n C base accumulator)
      (entry machine (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length
        stride p n C base accumulator 0 (fun _=>0) out)=some r ∧
      r.final.heads=PCPPNativeClauseBody.heads (pre++PCPPNativeClauseTriple.fields bits).length
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.final.tapes=data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C (base+3) (base+2) 0 (fun _=>0)
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.steps≤budget bits indices signs stride p n C base accumulator := by
  let source:=pre++PCPPNativeClauseTriple.fields bits++tail
  let refs:=PCPPNativeClauseBody.references indices signs stride p n
  let output:=out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator refs)
  let pos:=(pre++PCPPNativeClauseTriple.fields bits).length
  have a:=padded_run pre tail bits indices signs stride p n C base accumulator out hv hC hB
  have b:=counter_run source pos stride p n C base accumulator refs output ha hc
  have c:=erase_run source pos stride p n C (base+3) (base+2) (base+3) refs output hc hr
  have ab:=join PCPPNativeClauseBody.machine counter _ _ _ _ _ _ _ _ a b
  exact join beforeErase erase _ _ _ _ _ _ _ _ ab c

theorem budget_bound (bits : Fin 3→List Bool) (indices : Fin 3→ℕ) (signs : Fin 3→Bool)
    (stride p n C base accumulator : ℕ)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C)
    (hB : PCPPNativeClauseBank.Capacity
      (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n)) C)
    (hr : ∀ i,PCPPNativeClauseBody.references indices signs stride p n i≤C)
    (hc : base+3≤C) : budget bits indices signs stride p n C base accumulator≤48*C+128 := by
  have each (i : Fin 3) : PCPPNativeClauseReusable.budget (bits i) (indices i) stride (signs i) p n C≤5*C+9 := by
    have hf:=hC i
    have hh:=hr i
    change PCPPNativeClauseReusable.reference (indices i) stride (signs i) p n≤C at hh
    unfold PCPPNativeClauseReusable.budget PCPPNativeClauseReusable.prefixBudget
    omega
  have h0:=each 0; have h1:=each 1; have h2:=each 2
  have hb:=PCPPNativeClauseBank.budget_bound _ C hB
  unfold budget PCPPNativeClauseBody.budget PCPPNativeClauseTriple.budget
  omega

theorem uniform_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C base accumulator : ℕ) (out : List Bool)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C)
    (hB : PCPPNativeClauseBank.Capacity
      (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n)) C)
    (hr : ∀ i,PCPPNativeClauseBody.references indices signs stride p n i≤C)
    (ha : accumulator≤base) (hc : base+3≤C) :
    ∃ r,runFrom machine (48*C+128)
      (entry machine (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length
        stride p n C base accumulator 0 (fun _=>0) out)=some r ∧
      r.final.heads=PCPPNativeClauseBody.heads (pre++PCPPNativeClauseTriple.fields bits).length
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.final.tapes=data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C (base+3) (base+2) 0 (fun _=>0)
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.steps≤48*C+128 := by
  obtain ⟨r,run,heads,tapes,steps⟩:=body_run pre tail bits indices signs stride p n C base accumulator out hv hC hB hr ha hc
  have hb:=budget_bound bits indices signs stride p n C base accumulator hC hB hr hc
  have more:=runFrom_moreFuel machine _ (48*C+128-budget bits indices signs stride p n C base accumulator) _ r run
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,heads,tapes,steps.trans hb⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
