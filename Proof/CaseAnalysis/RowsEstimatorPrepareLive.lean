import Proof.CaseAnalysis.RowsEstimatorPrepareRun

/-! Preserve the growing scalar cursor while paying the two preparation passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def live (p : Program) (A : Fin (tapes p) → List Bool) (out : List Bool) :=
  Function.update A (spare p) out
noncomputable def heads (p : Program) (out : List Bool) : Fin (tapes p) → ℕ :=
  fun i=>if i=spare p then out.length else 0

theorem install_update {t u : ℕ} (slot : Fin t → Fin u) (A : Fin u → List Bool)
    (B : Fin t → List Bool) (i : Fin u) (out : List Bool) (hi : ∀ j,slot j≠i) :
    install slot (Function.update A i out) B=Function.update (install slot A B) i out := by
  classical
  funext k
  by_cases hk : k=i
  · subst k
    rw [install_other _ _ _ _ hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hk]
    cases hp : RecoveryFocus.pick slot k
    · simp only [install,hp,Function.update_of_ne hk]
    · simp only [install,hp]

theorem focus_live {t s : ℕ} (p : Program) (worker : Machine t s) (n : ℕ)
    (slot : Fin t → Fin (tapes p)) (hi : Function.Injective slot) (avoid : ∀ j,slot j≠spare p)
    (input output : Fin t → List Bool) (A : Fin (tapes p) → List Bool) (out : List Bool)
    (hr : ReadyRun worker n input output) (ha : ∀ j,A (slot j)=input j) : ∃ r,
    runFrom (RecoveryFocus.machine slot worker) n ⟨worker.start,heads p out,live p A out⟩=some r ∧
      r.final.heads=heads p out ∧
      r.final.tapes=live p (install slot A output) out ∧ r.steps=n := by
  obtain ⟨r,rr,rh,rt,rs⟩:=hr.focus_at slot hi (heads p out) (live p A out)
    (by intro j;simpa only [live,Function.update_of_ne (avoid j)] using ha j)
    (by intro j;simp only [heads,avoid j,ite_false])
  refine ⟨r,rr,rh,?_,rs⟩
  exact rt.trans (install_update slot A output (spare p) out avoid)

theorem pad_live (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) : ∃ r,
    runFrom (pad p) (2*D+4) ⟨(pad p).start,heads p out,live p (data p A D 0 fields) out⟩=some r ∧
      r.final.heads=heads p out ∧
      r.final.tapes=live p (data p (WarmReuse.padded p D A) D (D+1) fields) out ∧ r.steps=2*D+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=focus_live p (Pad.machine (WholePrefix.tapes p-2)) _
    (padSlots p) (pad_injective p) (pad_avoids p _ (Or.inr (Or.inr (Or.inl rfl))))
    _ _ (data p A D 0 fields) out (Pad.ready (owned p A) D) (pad_input p A D fields)
  rw [pad_output] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem copy_live (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool)
    (ha : ∀ i,A (WarmFields.slots p i)=List.replicate D false) (hd : ∀ i,(fields i).length ≤ D) : ∃ r,
    runFrom (copy p) (2*D+4) ⟨(copy p).start,heads p out,live p (data p A D (D+1) fields) out⟩=some r ∧
      r.final.heads=heads p out ∧
      r.final.tapes=live p (data p (install (WarmFields.slots p) A
        (fun i=>ZeroPadding.pad D (fields i))) D (D+1) fields) out ∧ r.steps=2*D+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=focus_live p (MetadataBatch.machine 7) _
    (copySlots p) (copy_injective p) (copy_avoids_spare p)
    _ _ (data p A D (D+1) fields) out (MetadataBatch.ready fields D hd) (copy_input p A D fields ha)
  rw [copy_output] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem live_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p) :
    let p:=CompetitorCrossScheduler.producer a
    let D:=Driver.value a row.d row.p row.cuts.length C
    let fields:=WarmFields.words row Q q denominator select
    ∃ r,runFrom (machine p) (4*D+9)
      (Composition.leftConfig _ ⟨(pad p).start,heads p out,live p (data p (WarmFields.bare p row C) D 0 fields) out⟩)=some r ∧
      r.final.heads=heads p out ∧
      r.final.tapes=live p (data p (WarmReuse.padded p D (Warm.input p row C Q q denominator select)) D (D+1) fields) out ∧
      r.steps=4*D+9 := by
  dsimp only
  let p:=CompetitorCrossScheduler.producer a
  let D:=Driver.value a row.d row.p row.cuts.length C
  let fields:=WarmFields.words row Q q denominator select
  obtain ⟨x,hx,xh,xt,xs⟩:=pad_live p (WarmFields.bare p row C) D fields out
  obtain ⟨y,hy,yh,yt,ys⟩:=copy_live p (WarmReuse.padded p D (WarmFields.bare p row C)) D fields out
    (WarmFields.padded_field p row C D) (WarmFields.bounded a row C Q q denominator select hC hQ)
  rw [WarmFields.padded_installed] at yt
  have he : Composition.restart x.final (copy p).start=
      ⟨(copy p).start,heads p out,live p (data p (WarmReuse.padded p D (WarmFields.bare p row C)) D (D+1) fields) out⟩ := by
    apply configuration_ext
    · rfl
    · exact xh
    · exact xt
  rw [←he] at hy
  have hr:=Composition.run_join (pad p) (copy p) _ _ _ x y hx hy
  have hn : 2*D+4+1+(2*D+4)=4*D+9:=by omega
  rw [hn] at hr
  exact ⟨Composition.joinedReceipt x y,hr,yh,yt,by change x.steps+1+y.steps=4*D+9;omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
