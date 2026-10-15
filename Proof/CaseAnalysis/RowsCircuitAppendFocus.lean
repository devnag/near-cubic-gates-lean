import Proof.CaseAnalysis.RowsCircuitBottomLoad

/-! The three circuit append consumers change one global output coordinate.
This local projection proof keeps their large ambient banks opaque. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAppend
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem one_change {t u : ℕ} {α : Type} (slots : Fin t→Fin u) (j : Fin t)
    (before after : Fin u→α) (value : α)
    (target : after (slots j)=value)
    (selected : ∀ k,k≠j → after (slots k)=before (slots k))
    (outside : ∀ i,(∀ k,slots k≠i) → after i=before i) :
    after=Function.update before (slots j) value := by
  apply Function.eq_update_iff.mpr
  refine ⟨target,?_⟩
  intro i hi
  by_cases hp : ∃ k,slots k=i
  · obtain ⟨k,rfl⟩:=hp
    exact selected k (by intro h;subst k;exact hi rfl)
  · exact outside i (by intro k h;exact hp ⟨k,h⟩)

theorem focused_one {t u s : ℕ} (p : Machine t s) (slots : Fin t→Fin u)
    (hinj : Function.Injective slots) (j : Fin t) (fuel : ℕ) (c : Configuration t s)
    (base : ExecutionReceipt t s) (hr : runFrom p fuel c=some base) (hc : c.control=p.start)
    (hh : ∀ i,i≠j → base.final.heads i=c.heads i)
    (ht : ∀ i,i≠j → base.final.tapes i=c.tapes i)
    (heads : Fin u→ℕ) (tapes : Fin u→List Bool)
    (ih : ∀ i,heads (slots i)=c.heads i) (it : ∀ i,tapes (slots i)=c.tapes i) : ∃ r,
    runFrom (RecoveryFocus.machine slots p) fuel ⟨p.start,heads,tapes⟩=some r ∧
      r.final.heads=Function.update heads (slots j) (base.final.heads j) ∧
      r.final.tapes=Function.update tapes (slots j) (base.final.tapes j) ∧ r.steps=base.steps := by
  obtain ⟨r,rr,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots hinj p fuel heads tapes c ih it base hr
  rw [hc] at rr
  refine ⟨r,rr,one_change slots j heads r.final.heads _ (rh j) ?_ ?_,
    one_change slots j tapes r.final.tapes _ (rt j) ?_ ?_,rs⟩
  · intro i hi;exact (rh i).trans ((hh i hi).trans (ih i).symm)
  · intro i hi;exact (keep i hi).1
  · intro i hi;exact (rt i).trans ((ht i hi).trans (it i).symm)
  · intro i hi;exact (keep i hi).2

theorem frame_focus {u : ℕ} (slots : Fin 3→Fin u) (hinj : Function.Injective slots)
    (cap : ℕ) (bits out : List Bool) (hc : 2*bits.length+1 ≤ cap)
    (heads : Fin u→ℕ) (tapes : Fin u→List Bool)
    (hh : ∀ i,heads (slots i)=(frameCfg 0 cap bits out).heads i)
    (ht : ∀ i,tapes (slots i)=(frameCfg 0 cap bits out).tapes i) :
    PCPOuter.Exact (RecoveryFocus.machine slots CompetitorFrameAppend.machine) (4*bits.length+3)
      heads tapes (Function.update heads (slots 1) (out++frame bits).length)
      (Function.update tapes (slots 1) (out++frame bits)) := by
  obtain ⟨base,hb,bf,bs⟩:=frame_run cap bits out hc
  obtain ⟨r,hr,rh,rt,rs⟩:=focused_one CompetitorFrameAppend.machine slots hinj 1 _ _ base hb rfl
    (by intro i hi;rw [bf];fin_cases i <;> first | rfl | exact False.elim (hi rfl))
    (by intro i hi;rw [bf];fin_cases i <;> first | rfl | exact False.elim (hi rfl)) heads tapes hh ht
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [bf] at rh;exact rh
  · rw [bf] at rt;exact rt

theorem unary_focus {u : ℕ} (slots : Fin 4→Fin u) (hinj : Function.Injective slots)
    (cap a b : ℕ) (out : List Bool) (hc : a+b+2 ≤ cap)
    (heads : Fin u→ℕ) (tapes : Fin u→List Bool)
    (hh : ∀ i,heads (slots i)=(unaryCfg 0 cap a b out).heads i)
    (ht : ∀ i,tapes (slots i)=(unaryCfg 0 cap a b out).tapes i) :
    PCPOuter.Exact (RecoveryFocus.machine slots unary) (2*(a+b)+6)
      heads tapes (Function.update heads (slots 2) (out++List.replicate (a+b) true).length)
      (Function.update tapes (slots 2) (out++List.replicate (a+b) true)) := by
  obtain ⟨base,hb,bf,bs⟩:=unary_run cap a b out hc
  obtain ⟨r,hr,rh,rt,rs⟩:=focused_one unary slots hinj 2 _ _ base hb rfl
    (by intro i hi;rw [bf];fin_cases i <;> first | rfl | exact False.elim (hi rfl))
    (by intro i hi;rw [bf];fin_cases i <;> first | rfl | exact False.elim (hi rfl)) heads tapes hh ht
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [bf] at rh;exact rh
  · rw [bf] at rt;exact rt

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAppend
