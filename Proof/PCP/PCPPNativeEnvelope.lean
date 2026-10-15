import Proof.PCP.PCPPNativeCount

/-! The native caller physically combines retained dimensions and measured
query/clause byte masses into the SAME W used by the capacity bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeEnvelope
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def value (R Q N stride Lq Lc : ℕ) := ((R+Q)+(N+stride))+((Lq+Lc)+4)
def slots0 : Fin 2 → Fin 20 := ![6,7]
def slots1 : Fin 4 → Fin 20 := ![0,1,8,9]
def slots2 : Fin 4 → Fin 20 := ![2,3,10,11]
def slots3 : Fin 4 → Fin 20 := ![4,5,12,13]
def slots4 : Fin 4 → Fin 20 := ![8,10,14,15]
def slots5 : Fin 4 → Fin 20 := ![12,6,16,17]
def slots6 : Fin 4 → Fin 20 := ![14,16,18,19]
def data (R Q N stride Lq Lc phase : ℕ) : Fin 20 → List Bool :=
  ![List.replicate R true,
    List.replicate Q true,
    List.replicate N true,
    List.replicate stride true,
    List.replicate Lq true,
    List.replicate Lc true,
    if 1≤phase then List.replicate 4 true else [],
    if 1≤phase then List.replicate 4 false else [],
    if 2≤phase then List.replicate (R+Q) true else [],
    if 2≤phase then List.replicate ((R+Q)+2) false else [],
    if 3≤phase then List.replicate (N+stride) true else [],
    if 3≤phase then List.replicate ((N+stride)+2) false else [],
    if 4≤phase then List.replicate (Lq+Lc) true else [],
    if 4≤phase then List.replicate ((Lq+Lc)+2) false else [],
    if 5≤phase then List.replicate ((R+Q)+(N+stride)) true else [],
    if 5≤phase then List.replicate (((R+Q)+(N+stride))+2) false else [],
    if 6≤phase then List.replicate ((Lq+Lc)+4) true else [],
    if 6≤phase then List.replicate (((Lq+Lc)+4)+2) false else [],
    if 7≤phase then List.replicate (value R Q N stride Lq Lc) true else [],
    if 7≤phase then List.replicate ((value R Q N stride Lq Lc)+2) false else []]
noncomputable def program0 := RecoveryFocus.machine slots0 (HierarchyFixedWord.machine (List.replicate 4 true))
noncomputable def program1 := RecoveryFocus.machine slots1 ClockUnarySum.machine
noncomputable def program2 := RecoveryFocus.machine slots2 ClockUnarySum.machine
noncomputable def program3 := RecoveryFocus.machine slots3 ClockUnarySum.machine
noncomputable def program4 := RecoveryFocus.machine slots4 ClockUnarySum.machine
noncomputable def program5 := RecoveryFocus.machine slots5 ClockUnarySum.machine
noncomputable def program6 := RecoveryFocus.machine slots6 ClockUnarySum.machine
noncomputable def machine := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine program0 program1) program2) program3) program4) program5) program6)
def budget (R Q N stride Lq Lc : ℕ) := 10+1+(2*(R+Q)+6)+1+(2*(N+stride)+6)+1+(2*(Lq+Lc)+6)+1+(2*((R+Q)+(N+stride))+6)+1+(2*((Lq+Lc)+4)+6)+1+(2*(value R Q N stride Lq Lc)+6)

private theorem bounded {t s b : ℕ} {p : Machine t s} {a z : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p b a z) : ClockJoin.ReadyRun p b a z := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem stage0_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program0 (10) (data R Q N stride Lq Lc 0) (data R Q N stride Lq Lc 1) := by
  have h := (bounded (HierarchyFixedWord.word_ready (List.replicate 4 true))).focus slots0 (by decide) (data R Q N stride Lq Lc 0)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots0 (by decide) _ (data R Q N stride Lq Lc 1) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 0; have hb := hi 1;
        fin_cases i <;> simp_all [data,slots0])] at h
  exact h

theorem stage1_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program1 (2*(R+Q)+6) (data R Q N stride Lq Lc 1) (data R Q N stride Lq Lc 2) := by
  have h := (ClockUnarySum.sum_ready R Q).focus slots1 (by decide) (data R Q N stride Lq Lc 1)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots1 (by decide) _ (data R Q N stride Lq Lc 2) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots1])] at h
  exact h

theorem stage2_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program2 (2*(N+stride)+6) (data R Q N stride Lq Lc 2) (data R Q N stride Lq Lc 3) := by
  have h := (ClockUnarySum.sum_ready N stride).focus slots2 (by decide) (data R Q N stride Lq Lc 2)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots2 (by decide) _ (data R Q N stride Lq Lc 3) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots2])] at h
  exact h

theorem stage3_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program3 (2*(Lq+Lc)+6) (data R Q N stride Lq Lc 3) (data R Q N stride Lq Lc 4) := by
  have h := (ClockUnarySum.sum_ready Lq Lc).focus slots3 (by decide) (data R Q N stride Lq Lc 3)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots3 (by decide) _ (data R Q N stride Lq Lc 4) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots3])] at h
  exact h

theorem stage4_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program4 (2*((R+Q)+(N+stride))+6) (data R Q N stride Lq Lc 4) (data R Q N stride Lq Lc 5) := by
  have h := (ClockUnarySum.sum_ready (R+Q) (N+stride)).focus slots4 (by decide) (data R Q N stride Lq Lc 4)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots4 (by decide) _ (data R Q N stride Lq Lc 5) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots4])] at h
  exact h

theorem stage5_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program5 (2*((Lq+Lc)+4)+6) (data R Q N stride Lq Lc 5) (data R Q N stride Lq Lc 6) := by
  have h := (ClockUnarySum.sum_ready (Lq+Lc) 4).focus slots5 (by decide) (data R Q N stride Lq Lc 5)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots5 (by decide) _ (data R Q N stride Lq Lc 6) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots5])] at h
  exact h

theorem stage6_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun program6 (2*(value R Q N stride Lq Lc)+6) (data R Q N stride Lq Lc 6) (data R Q N stride Lq Lc 7) := by
  have h := (ClockUnarySum.sum_ready ((R+Q)+(N+stride)) ((Lq+Lc)+4)).focus slots6 (by decide) (data R Q N stride Lq Lc 6)
    (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq slots6 (by decide) _ (data R Q N stride Lq Lc 7) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have ha := hi 2; have hb := hi 3;
        fin_cases i <;> simp_all [data,slots6])] at h
  exact h

theorem envelope_run (R Q N stride Lq Lc : ℕ) :
    ClockJoin.ReadyRun machine (budget R Q N stride Lq Lc) (data R Q N stride Lq Lc 0) (data R Q N stride Lq Lc 7) := by
  exact (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (stage0_run R Q N stride Lq Lc) (stage1_run R Q N stride Lq Lc)) (stage2_run R Q N stride Lq Lc)) (stage3_run R Q N stride Lq Lc)) (stage4_run R Q N stride Lq Lc)) (stage5_run R Q N stride Lq Lc)) (stage6_run R Q N stride Lq Lc))

theorem fields (R Q N stride Lq Lc : ℕ) :
    (∀ i : Fin 6,data R Q N stride Lq Lc 7 (i.castAdd 14)=data R Q N stride Lq Lc 0 (i.castAdd 14)) ∧
    data R Q N stride Lq Lc 7 18=List.replicate (value R Q N stride Lq Lc) true := by
  constructor
  · intro i
    fin_cases i <;> simp [data]
  · simp [data]

theorem bounds (R Q N stride Lq Lc : ℕ) :
    4≤value R Q N stride Lq Lc ∧ R≤value R Q N stride Lq Lc ∧ Q≤value R Q N stride Lq Lc ∧
    N≤value R Q N stride Lq Lc ∧ stride≤value R Q N stride Lq Lc ∧ Lq≤value R Q N stride Lq Lc ∧ Lc≤value R Q N stride Lq Lc ∧
    budget R Q N stride Lq Lc≤12*value R Q N stride Lq Lc+52 := by
  unfold budget value
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeEnvelope
