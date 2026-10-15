import Proof.PCP.PCPOuterPrepare

/-! Literal four-field outer balanced serialization from physical framed
sources and blank work. This invokes the cold traversal exactly once. -/
namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape RecoveryExecution PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem exact_then {t a b fp fq : ℕ} {p : Machine t a} {q : Machine t b}
    {h h' : Fin t → ℕ} {d d' : Fin t → List Bool}
    (hp : Exact p fp h d h' d') (r : ExecutionReceipt t b)
    (hq : runFrom q fq ⟨q.start,h',d'⟩=some r) :
    ∃ s,runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,h,d⟩=some s ∧
      s.final.heads=r.final.heads ∧ s.final.tapes=r.final.tapes ∧ s.steps=fp+1+r.steps := by
  obtain ⟨base,hb,bh,bt,bs⟩ := hp
  have hc : Composition.restart base.final q.start=⟨q.start,h',d'⟩ := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [←hc] at hq
  refine ⟨Composition.joinedReceipt base r,Composition.run_join p q fp fq _ base r hb hq,rfl,rfl,?_⟩
  change base.steps+1+r.steps=fp+1+r.steps
  omega

noncomputable def serializer := RecoveryFocus.machine bank PCPTraversal.machine
noncomputable def machine := Composition.machine preparation serializer
noncomputable def entry (a b c d sa sb sc sd : List Bool) :=
  (⟨machine.start,fun _ => 0,input a b c d sa sb sc sd⟩ : Configuration 133 _)
def budget (S : ℕ) := 4*S+28+PCPTraversal.budget (2*S+4)

theorem fields_mass (a b c d : List Bool) : mass (fields a b c d)=2*size a b c d+4 := by
  simp [mass,fields,size]
  omega

theorem outer_run (a b c d sa sb sc sd : List Bool) :
    ∃ r,runFrom machine (budget (size a b c d)) (entry a b c d sa sb sc sd)=some r ∧
      r.final.tapes 82=(PCPTraversal.code (fields a b c d)).bits ∧
      r.final.heads 82=0 ∧
      r.final.tapes 81=ZeroPadding.pad (PCPPairReusable.capacity (2*size a b c d+4))
        (frame (PCPTraversal.code (fields a b c d)).bits) ∧
      (∀ i : Fin 4,r.final.tapes (i.castAdd 129)=input a b c d sa sb sc sd (i.castAdd 129)) ∧
      r.steps≤budget (size a b c d) := by
  have hp := preparation_run a b c d sa sb sc sd
  obtain ⟨base,hb,b77,b78,_b0,_b2,bh,other,bs⟩ := PCPTraversal.focused_run bank bank_injective
    [] (fields a b c d) [] (preparedHeads a b c d) (preparedTapes a b c d sa sb sc sd)
    (prepared_heads a b c d)
    (by intro j; simpa only [List.nil_append,List.append_nil,fields,List.length_cons,List.length_nil]
          using prepared_tapes a b c d sa sb sc sd j)
  obtain ⟨r,hr,rh,rt,rs⟩ := exact_then hp base hb
  have hc : (4*size a b c d+27)+1+PCPTraversal.budget (mass (fields a b c d))=
      budget (size a b c d) := by rw [fields_mass]; unfold budget; omega
  rw [hc] at hr
  refine ⟨r,hr,?_,?_,?_,?_,?_⟩
  · rw [rt]
    exact b78
  · rw [rh]
    have hh := bh 78
    simpa [bank,PCPTraversal.coldHeads,PCPSerializerCountEntry.finalHeads,
      PCPTraversal.heads] using hh
  · rw [rt,←fields_mass]
    exact b77
  · intro i
    have hi : ∀ j,bank j≠i.castAdd 129 := by
      intro j he
      have hv := congrArg Fin.val he
      simp only [bank,Fin.val_castAdd] at hv
      omega
    rw [rt,(other (i.castAdd 129) hi).1]
    fin_cases i <;> rfl
  · rw [rs]
    rw [fields_mass] at bs
    unfold budget
    omega

theorem budget_polynomial (S : ℕ) : budget S≤1000000000000000000000*(S+1)^12 := by
  have hs : S+1≤(S+1)^12 := by
    calc
      _=(S+1)^1 := by simp
      _≤_ := pow_le_pow_right₀ (by omega) (by omega)
  have hb : 2*S+5≤5*(S+1) := by omega
  have hp : (2*S+5)^12≤(5*(S+1))^12 := Nat.pow_le_pow_left hb 12
  have hm := Nat.mul_le_mul_left 1000000000000 hp
  rw [mul_pow] at hm
  norm_num at hm
  unfold budget PCPTraversal.budget
  have he : 2*S+4+1=2*S+5 := by omega
  rw [he]
  omega

theorem polynomial_run (a b c d sa sb sc sd : List Bool) :
    ∃ r,runFrom machine (1000000000000000000000*(size a b c d+1)^12)
      (entry a b c d sa sb sc sd)=some r ∧
      r.final.tapes 82=(PCPTraversal.code (fields a b c d)).bits ∧ r.final.heads 82=0 ∧
      r.steps≤1000000000000000000000*(size a b c d+1)^12 := by
  obtain ⟨r,hr,ht,hh,_hf,_hi,hs⟩ := outer_run a b c d sa sb sc sd
  have hb := budget_polynomial (size a b c d)
  have more := runFrom_moreFuel machine (budget (size a b c d))
    (1000000000000000000000*(size a b c d+1)^12-budget (size a b c d)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,ht,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.PCPOuter
