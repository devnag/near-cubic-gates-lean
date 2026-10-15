import Proof.PCP.PCPTraversalFocused
import Proof.MachineModel.OrdinaryMaskedReset

/-! Four literal field copies for the final balanced PCP record. Every
handoff is a paid ordinary transition; suffixes on the four sources remain. -/
namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Exact {t s : ℕ} (p : Machine t s) (cost : ℕ)
    (h : Fin t → ℕ) (d : Fin t → List Bool) (hh : Fin t → ℕ) (dd : Fin t → List Bool) : Prop :=
  ∃ r,runFrom p cost ⟨p.start,h,d⟩=some r ∧ r.final.heads=hh ∧ r.final.tapes=dd ∧ r.steps=cost

theorem exact_join {t a b x y : ℕ} {p : Machine t a} {q : Machine t b}
    {h h' h'' : Fin t → ℕ} {d d' d'' : Fin t → List Bool}
    (hp : Exact p x h d h' d') (hq : Exact q y h' d' h'' d'') :
    Exact (Composition.machine p q) (x+1+y) h d h'' d'' := by
  obtain ⟨r,hr,rh,rt,rs⟩ := hp
  obtain ⟨s,hs,sh,st,ss⟩ := hq
  have hc : Composition.restart r.final q.start=⟨q.start,h',d'⟩ := by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [←hc] at hs
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q x y _ r s hr hs,sh,st,?_⟩
  change r.steps+1+s.steps=x+1+y
  omega

theorem focused_existing {t u s : ℕ} (slot : Fin t → Fin u)
    (h : Fin u → ℕ) (d : Fin u → List Bool) (c : Configuration t s)
    (hh : ∀ i,h (slot i)=c.heads i) (ht : ∀ i,d (slot i)=c.tapes i) :
    RecoveryFocus.config slot h d c=⟨c.control,h,d⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp only [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simpa only [RecoveryFocus.config,hp] using (hh j).symm.trans (congrArg h he)
  · exact install_existing slot d c.tapes ht

theorem install_two {u : ℕ} {α : Type} (s t : Fin u) (hne : s≠t)
    (ambient : Fin u → α) (a b : α) :
    (fun i => match RecoveryFocus.pick ![s,t] i with
      | some j => (![a,b] : Fin 2 → α) j | none => ambient i)=
      Function.update (Function.update ambient s a) t b := by
  classical
  have inj : Function.Injective (![s,t] : Fin 2 → Fin u) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  funext i
  by_cases hs : i=s
  · subst i
    have hp : RecoveryFocus.pick ![s,t] s=some 0 := RecoveryFocus.pick_slot _ inj 0
    rw [hp]
    simp [Function.update_of_ne hne]
  · by_cases ht : i=t
    · subst i
      have hp : RecoveryFocus.pick ![s,t] t=some 1 := RecoveryFocus.pick_slot _ inj 1
      rw [hp]
      simp
    · have hp : RecoveryFocus.pick ![s,t] i=none := by
        unfold RecoveryFocus.pick
        exact dif_neg (by rintro ⟨j,hj⟩; fin_cases j <;> simp_all)
      simp [hp,hs,ht]

noncomputable def copy {t : ℕ} (s o : Fin t) := RecoveryFocus.machine ![s,o] Field.machine
def copiedHeads {t : ℕ} (s o : Fin t) (bits out : List Bool) (h : Fin t → ℕ) :=
  Function.update (Function.update h s (2*bits.length+1)) o (out++frame bits).length

theorem copy_run {t : ℕ} (s o : Fin t) (hne : s≠o)
    (bits suffix out : List Bool) (h : Fin t → ℕ) (d : Fin t → List Bool)
    (hs : h s=0) (ho : h o=out.length) (ds : d s=frame bits++suffix) (dto : d o=out) :
    Exact (copy s o) (2*bits.length+1) h d (copiedHeads s o bits out h)
      (Function.update d o (out++frame bits)) := by
  classical
  have inj : Function.Injective (![s,o] : Fin 2 → Fin t) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨base,hb,bf,bs⟩ := Field.copy_run [] bits suffix out
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config ![s,o] inj Field.machine h d _ _ base hb
  rw [focused_existing ![s,o] h d _
    (by intro i; fin_cases i <;> simpa [Field.cfg] using (by assumption))
    (by intro i; fin_cases i <;> simpa [Field.cfg] using (by assumption))] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i
    by_cases his : i=s
    · subst i
      have hp : RecoveryFocus.pick ![s,o] s=some 0 := RecoveryFocus.pick_slot _ inj 0
      simp [RecoveryFocus.config,hp,Field.cfg,copiedHeads,hne]
    by_cases hio : i=o
    · subst i
      have hp : RecoveryFocus.pick ![s,o] o=some 1 := RecoveryFocus.pick_slot _ inj 1
      simp [RecoveryFocus.config,hp,Field.cfg,copiedHeads]
    have hp : RecoveryFocus.pick ![s,o] i=none := by
      unfold RecoveryFocus.pick
      exact dif_neg (by rintro ⟨j,hj⟩; fin_cases j <;> simp_all)
    simp [RecoveryFocus.config,hp,copiedHeads,his,hio]
  · rw [rf,bf]
    funext i
    by_cases his : i=s
    · subst i
      have hp : RecoveryFocus.pick ![s,o] s=some 0 := RecoveryFocus.pick_slot _ inj 0
      simp [RecoveryFocus.config,hp,Field.cfg,hne,ds]
    by_cases hio : i=o
    · subst i
      have hp : RecoveryFocus.pick ![s,o] o=some 1 := RecoveryFocus.pick_slot _ inj 1
      simp [RecoveryFocus.config,hp,Field.cfg]
    have hp : RecoveryFocus.pick ![s,o] i=none := by
      unfold RecoveryFocus.pick
      exact dif_neg (by rintro ⟨j,hj⟩; fin_cases j <;> simp_all)
    simp [RecoveryFocus.config,hp,hio]

end NearCubicWires.RepairOrdinary.PCPOuter
