import Proof.CaseAnalysis.WitnessSupportDock
import Proof.Amplification.RecoveryFocusDock

/-! An actual extended worker runs below an unchanged ambient bank. The
added public tape stays last; old bank fields retain their original indices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields {t e : ℕ} {α : Type} (base : Fin t→α) (extra : Fin e→α) (last : α) : Fin (t+e+1)→α:=
  lift (Fin.addCases (m:=t) (n:=e) base extra) last
noncomputable def machine {t e s : ℕ} (p : Machine (t+1) s) : Machine (t+e+1) s:=
  RecoveryFocus.machine (slots (Fin.castAdd e)) p

theorem field_local {t e : ℕ} {α : Type} (base : Fin t→α) (extra : Fin e→α) (last : α)
    (i : Fin (t+1)) : fields base extra last (slots (Fin.castAdd e) i)=lift base last i:=
  local_fields (Fin.castAdd e) _ base last (fun i=>Fin.addCases_left i) i

theorem field_outside {t e : ℕ} (i : Fin e) :
    ∀ j,slots (Fin.castAdd e) j≠(i.natAdd t).castAdd 1:=by
  apply outside (Fin.castAdd e) (i.natAdd t)
  intro j h
  have hv:=congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem run {t e s : ℕ} (p : Machine (t+1) s) (fuel : ℕ) (control : Fin s)
    (h h' : Fin t→ℕ) (d d' : Fin t→List Bool) (eh : Fin e→ℕ) (ed : Fin e→List Bool)
    (sh sh' : ℕ) (st st' : List Bool) (base : ExecutionReceipt (t+1) s)
    (hr : runFrom p fuel ⟨control,lift h sh,lift d st⟩=some base)
    (bh : base.final.heads=lift h' sh') (bt : base.final.tapes=lift d' st') :
    ∃ r,runFrom (machine (e:=e) p) fuel ⟨control,fields h eh sh,fields d ed st⟩=some r ∧
      r.steps=base.steps ∧ r.final.heads=fields h' eh sh' ∧ r.final.tapes=fields d' ed st':=by
  obtain ⟨r,run,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock (slots (Fin.castAdd e))
    (injective (Fin.castAdd e) (Fin.castAdd_injective t e)) p fuel (fields h eh sh) (fields d ed st)
    ⟨control,lift h sh,lift d st⟩ (field_local h eh sh) (field_local d ed st) base hr
  refine ⟨r,run,rs,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=t+e) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=e) ?_ ?_ j
      · intro k
        have q:=rh (k.castAdd 1)
        rw [slots_old,bh] at q
        simpa only [lift,fields,Fin.addCases_left] using q
      · intro k
        simpa only [fields,lift,Fin.addCases_left,Fin.addCases_right] using (keep _ (field_outside k)).1
    · intro j
      have q:=rh (j.natAdd t)
      rw [slots_new,bh] at q
      simpa only [lift,fields,Fin.addCases_right] using q
  · funext i
    refine Fin.addCases (m:=t+e) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=t) (n:=e) ?_ ?_ j
      · intro k
        have q:=rt (k.castAdd 1)
        rw [slots_old,bt] at q
        simpa only [lift,fields,Fin.addCases_left] using q
      · intro k
        simpa only [fields,lift,Fin.addCases_left,Fin.addCases_right] using (keep _ (field_outside k)).2
    · intro j
      have q:=rt (j.natAdd t)
      rw [slots_new,bt] at q
      simpa only [lift,fields,Fin.addCases_right] using q

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
