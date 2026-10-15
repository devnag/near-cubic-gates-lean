import Proof.MachineModel.OrdinaryMatrixPacketCapacityDimensions

/-! Actual capacity polynomial: source-fixed C*q^E followed by two
multiplications with the physically supplied U+1 sentinel. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityPower
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (E : ℕ) := DimensionPower.tapes E+5
def extras (u : ℕ) (i : Fin 5) : List Bool := if i=0 then UnaryTemplate.tape u else []
def input (E q u : ℕ) : Fin (tapes E) → List Bool := Fin.addCases (DimensionPower.input E q) (extras u)
def slots1 (E : ℕ) : Fin 4 → Fin (tapes E) :=
  ![(DimensionPower.valueSlot E E le_rfl).castAdd 5,(0 : Fin 5).natAdd (DimensionPower.tapes E),
    (1 : Fin 5).natAdd (DimensionPower.tapes E),(2 : Fin 5).natAdd (DimensionPower.tapes E)]
def slots2 (E : ℕ) : Fin 4 → Fin (tapes E) :=
  ![(1 : Fin 5).natAdd (DimensionPower.tapes E),(0 : Fin 5).natAdd (DimensionPower.tapes E),
    (3 : Fin 5).natAdd (DimensionPower.tapes E),(4 : Fin 5).natAdd (DimensionPower.tapes E)]
theorem inj1 (E : ℕ) : Function.Injective (slots1 E) := by
  intro a b he
  have hv := congrArg Fin.val he
  fin_cases a <;> fin_cases b <;> simp [slots1,DimensionPower.valueSlot,DimensionPower.tapes] at hv ⊢ <;> omega
theorem inj2 (E : ℕ) : Function.Injective (slots2 E) := by
  intro a b he
  have hv := congrArg Fin.val he
  fin_cases a <;> fin_cases b <;> simp [slots2] at hv ⊢
theorem pick_fresh (E : ℕ) (j : Fin 5) (hj : 3≤j.val) :
    RecoveryFocus.pick (slots1 E) (j.natAdd (DimensionPower.tapes E))=none := by
  have hn : ¬∃ k,slots1 E k=j.natAdd (DimensionPower.tapes E) := by
    rintro ⟨k,he⟩
    have hv := congrArg Fin.val he
    fin_cases k <;> simp [slots1,DimensionPower.valueSlot,DimensionPower.tapes] at hv <;> omega
  simp only [RecoveryFocus.pick,dif_neg hn]

noncomputable def first (E C : ℕ) := TapeEmbedding.machine 5 (DimensionPower.machine E C)
noncomputable def second (E : ℕ) := RecoveryFocus.machine (slots1 E) ClockUnaryProduct.machine
noncomputable def third (E : ℕ) := RecoveryFocus.machine (slots2 E) ClockUnaryProduct.machine
noncomputable def machine (E C : ℕ) := Composition.machine (Composition.machine (first E C) (second E)) (third E)
def budget (E C q u : ℕ) := DimensionPower.cost C q E+1+WilliamsUnaryProduct.budget (C*q^E) u+1+
  WilliamsUnaryProduct.budget (C*q^E*u) u

theorem power_ready (E C q u : ℕ) : ∃ out,ClockJoin.ReadyRun (machine E C) (budget E C q u) (input E q u) out ∧
    out ((3 : Fin 5).natAdd (DimensionPower.tapes E))=List.replicate (C*q^E*u*u) true ∧
    out ((0 : Fin 5).natAdd (DimensionPower.tapes E))=UnaryTemplate.tape u := by
  obtain ⟨values,⟨base,hb,bt,bh,bs⟩,hq,hvalue⟩ := DimensionPower.power_run E C q
  let data := Fin.addCases (motive := fun _ => List Bool) values (extras u)
  have he := TapeEmbedding.run_embed (DimensionPower.machine E C) (fun _ : Fin 5 => 0) (extras u) _ _ base hb
  let embedded := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (extras u) base
  have hin : TapeEmbedding.config (fun _ : Fin 5 => 0) (extras u)
      (initialConfiguration (DimensionPower.machine E C) (DimensionPower.input E q))=
      initialConfiguration (first E C) (input E q u) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := DimensionPower.tapes E) (n := 5) (fun j => ?_) (fun j => ?_) i
      all_goals simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at he
  have h0 : ClockJoin.ReadyRun (first E C) (DimensionPower.cost C q E) (input E q u) data := by
    refine ⟨embedded,he,?_,?_,bs⟩
    · change Fin.addCases base.final.tapes (extras u)=data
      rw [bt]
    · intro i
      refine Fin.addCases (m := DimensionPower.tapes E) (n := 5) (fun j => ?_) (fun j => ?_) i
      · change (Fin.addCases (m := DimensionPower.tapes E) (n := 5) (motive := fun _ => ℕ)
          base.final.heads (fun _ => 0)) (j.castAdd 5)=0
        rw [Fin.addCases_left,bh]
      · change (Fin.addCases (m := DimensionPower.tapes E) (n := 5) (motive := fun _ => ℕ)
          base.final.heads (fun _ => 0)) (j.natAdd (DimensionPower.tapes E))=0
        rw [Fin.addCases_right]
  have data_old (j : Fin (DimensionPower.tapes E)) : data (j.castAdd 5)=values j := Fin.addCases_left j
  have data_extra (j : Fin 5) : data (j.natAdd (DimensionPower.tapes E))=extras u j := Fin.addCases_right j
  have r1 : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (C*q^E) u)
      (WilliamsUnaryProduct.input (C*q^E) u) (WilliamsUnaryProduct.output (C*q^E) u) := by
    obtain ⟨r,hr,rt,rh,rs⟩ := WilliamsUnaryProduct.product_ready (C*q^E) u
    exact ⟨r,hr,rt,rh,rs.le⟩
  have h1 := r1.focus (slots1 E) (inj1 E) data (by
    intro j; fin_cases j
    · exact (data_old _).trans hvalue
    · exact data_extra 0
    · exact data_extra 1
    · exact data_extra 2)
  let middle := install (slots1 E) data (WilliamsUnaryProduct.output (C*q^E) u)
  have r2 : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (C*q^E*u) u)
      (WilliamsUnaryProduct.input (C*q^E*u) u) (WilliamsUnaryProduct.output (C*q^E*u) u) := by
    obtain ⟨r,hr,rt,rh,rs⟩ := WilliamsUnaryProduct.product_ready (C*q^E*u) u
    exact ⟨r,hr,rt,rh,rs.le⟩
  have h2 := r2.focus (slots2 E) (inj2 E) middle (by
    intro j; fin_cases j
    · change middle (slots1 E 2)=_
      simp only [middle,install,RecoveryFocus.pick_slot (slots1 E) (inj1 E)]
      rfl
    · change middle (slots1 E 1)=_
      simp only [middle,install,RecoveryFocus.pick_slot (slots1 E) (inj1 E)]
      rfl
    · change middle ((3 : Fin 5).natAdd (DimensionPower.tapes E))=_
      rw [show middle _=data ((3 : Fin 5).natAdd (DimensionPower.tapes E)) by
        simp only [middle,install,pick_fresh E 3 (by decide)]]
      exact data_extra 3
    · change middle ((4 : Fin 5).natAdd (DimensionPower.tapes E))=_
      rw [show middle _=data ((4 : Fin 5).natAdd (DimensionPower.tapes E)) by
        simp only [middle,install,pick_fresh E 4 (by decide)]]
      exact data_extra 4)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ h0 h1) h2,?_,?_⟩
  · change (install (slots2 E) middle (WilliamsUnaryProduct.output (C*q^E*u) u)) (slots2 E 2)=_
    simp only [install,RecoveryFocus.pick_slot (slots2 E) (inj2 E)]
    rfl
  · change (install (slots2 E) middle (WilliamsUnaryProduct.output (C*q^E*u) u)) (slots2 E 1)=_
    simp only [install,RecoveryFocus.pick_slot (slots2 E) (inj2 E)]
    rfl

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityPower
