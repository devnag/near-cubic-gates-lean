import Proof.CaseAnalysis.RecoveryClauseForward

/-! Reuse the paid literal reset, then append the original true seed.
Its cleared cells already provide the existing reverse fold's workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
open RecoveryBoundedNativeUnaryPhase (trueBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (j : Fin 71) : Fin 73:=j.castAdd 2
theorem old_injective : Function.Injective old := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 73=>k.val) he
noncomputable def reset:=RecoveryFocus.machine old (RecoveryBoundedLiteralReset.machine false)
noncomputable def cleared (A : Fin 73→List Bool) (C : ℕ):=
  install old A (RecoveryBoundedLiteralReset.output (A∘old) false C)
def writeSlot : Fin 1→Fin 73:=fun _=>20
noncomputable def seed:=RecoveryFocus.machine writeSlot (HierarchyFixedWord.raw trueBits)
def heads (H : Fin 73→ℕ) (out : List Bool):=Function.update H 20 out.length
def written (A : Fin 73→List Bool) (out : List Bool):=Function.update A 20 out
noncomputable def prepare:=Composition.machine reset seed
def prepareBudget (C : ℕ):=2*C+4+1+trueBits.length

theorem reset_run (H : Fin 73→ℕ) (A : Fin 73→List Bool) (node left right W C L : ℕ)
    (out pre source refs : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) node left right C L out pre source refs)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom reset (2*C+4) ⟨reset.start,H,A⟩=some r ∧ r.steps ≤ 2*C+4 ∧
      r.final.heads=H ∧ r.final.tapes=cleared A C := by
  have hw : W ≤ C:=PCPPNativeClauseCapacity.width_le_capacity W C hC
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedLiteralReset.reset_run false (H∘old) (A∘old) C
    (RecoveryBoundedClauseState.reset_heads h false) (h.restoreA 3) (h.restoreA 4)
    (RecoveryBoundedClauseState.reset_bounds h false (hl.trans hw) (hr.trans hw))
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock old old_injective (RecoveryBoundedLiteralReset.machine false) _ H A
    ⟨(RecoveryBoundedLiteralReset.machine false).start,H∘old,A∘old⟩ (by intro j;rfl) (by intro j;rfl) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,old j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      rfl
    · exact (rkeep i (by intro j he;exact hi ⟨j,he⟩)).1
  · have he : cleared A C=r.final.tapes := by
      apply HierarchyWidth.install_eq old old_injective
      · intro j;rw [rt j,pt]
      · intro i hi;exact (rkeep i hi).2
    exact he.symm

theorem seed_run (H : Fin 73→ℕ) (A : Fin 73→List Bool) (out : List Bool)
    (hH : H 20=out.length) (hA : A 20=out) :
    ∃ r,runFrom seed trueBits.length ⟨seed.start,H,A⟩=some r ∧ r.steps=trueBits.length ∧
      r.final.heads=heads H (out++trueBits) ∧ r.final.tapes=written A (out++trueBits) := by
  obtain ⟨p,pr,pf,ps⟩:=RepairSource.ProjectionNormalization.Constants.write_run trueBits out
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock writeSlot (by decide) (HierarchyFixedWord.raw trueBits) _ H A
    (RepairSource.ProjectionNormalization.Constants.cfg trueBits out 0 (by omega))
    (by intro j;simpa only [writeSlot,RepairSource.ProjectionNormalization.Constants.cfg,Nat.add_zero] using hH)
    (by intro j;simpa only [writeSlot,RepairSource.ProjectionNormalization.Constants.cfg,List.take_zero,List.append_nil] using hA) p pr
  refine ⟨r,rr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · subst i
      change r.final.heads (writeSlot 0)=_
      rw [rh 0,pf]
      change out.length+trueBits.length=(out++trueBits).length
      simp only [List.length_append]
    · rw [(rkeep i (by intro j;exact Ne.symm hi)).1]
      exact (Function.update_of_ne hi _ _).symm
  · funext i
    by_cases hi : i=20
    · subst i
      change r.final.tapes (writeSlot 0)=_
      rw [rt 0,pf]
      change out++trueBits.take trueBits.length=out++trueBits
      rw [List.take_length]
    · rw [(rkeep i (by intro j;exact Ne.symm hi)).2]
      exact (Function.update_of_ne hi _ _).symm

theorem cleared_old (A : Fin 73→List Bool) (C : ℕ) (j : Fin 71) :
    cleared A C (old j)=RecoveryBoundedLiteralReset.output (A∘old) false C j :=
  install_slot old old_injective _ _ j
theorem cleared_other (A : Fin 73→List Bool) (C : ℕ) (i : Fin 73) (hi : ∀ j,old j≠i) :
    cleared A C i=A i :=install_other old _ _ _ hi
theorem cleared_graph (A : Fin 73→List Bool) (C : ℕ) : cleared A C 20=A 20 := by
  change cleared A C (old 20)=A 20
  rw [cleared_old]
  exact install_other _ _ _ _ (by decide)

theorem prepare_run (H : Fin 73→ℕ) (A : Fin 73→List Bool) (node left right W C L : ℕ)
    (out pre source refs : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) node left right C L out pre source refs)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom prepare (prepareBudget C) ⟨prepare.start,H,A⟩=some r ∧ r.steps ≤ prepareBudget C ∧
      r.final.heads=heads H (out++trueBits) ∧ r.final.tapes=written (cleared A C) (out++trueBits) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=reset_run H A node left right W C L out pre source refs h hl hr hC
  have hg : A 20=out := by
    have ha:=h.gateA 20
    change A 20=ZeroPadding.pad 0 out at ha
    simpa only [ZeroPadding.pad_zero] using ha
  obtain ⟨q,qr,qs,qh,qt⟩:=seed_run H (cleared A C) out (h.gateH 20) (by rw [cleared_graph];exact hg)
  have qr' : runFrom seed trueBits.length (restart p.final seed.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join reset seed _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ prepareBudget C
  unfold prepareBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
