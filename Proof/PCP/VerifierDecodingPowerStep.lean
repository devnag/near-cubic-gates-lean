import Proof.PCP.VerifierDecodingPowerKernel

/-! Complete paid doubling at the guarded decoder's actual tape boundary. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem success_iteration (cap total pos value : ℕ)
    (ht : total ≤ cap) (hp : pos < total) (hv : value+value ≤ cap) :
    Prefix machine (4*(cap+2)) (8*value+9)
      (boundary cap total pos value) (boundary cap total (pos+1) (value+value)) := by
  have hvc : value ≤ cap := by omega
  obtain ⟨r,hr,hf,hs,hpeak⟩ := CapMachine.capped_add_run cap value value hvc hvc
  have hc : min value (cap-value) = value := Nat.min_eq_left (by omega)
  simp only [hc, if_pos hv, min_eq_right hv] at hr hf hs
  have hbody := add_prefix (prefix_of_run _ _ _ _
    (TapeEmbedding.run_embed CapMachine.machine (fun _ : Fin 1 => pos+2)
      (fun _ => CapMachine.counter cap total) _ _ r hr)).1
  simp only [TapeEmbedding.receipt, TapeEmbedding.extraCells, Fin.sum_univ_one,
    CapMachine.counter_length _ _ ht, hs, hf] at hbody
  have hbody' := hbody.enlarge (large := 4*(cap+2)) (by omega)

  obtain ⟨ra,hra,hfa,hsa,hpa⟩ := CapMachine.reset_run cap value value hvc (Nat.le_refl _)
  let ah : Fin 3 → ℕ := ![value+value+1,value+value+1,pos+2]
  let atp : Fin 3 → List Bool := ![CapMachine.counter cap (value+value),
    CapMachine.counter cap cap, CapMachine.counter cap total]
  have hfirst := first_reset_prefix (prefix_of_run _ _ _ _
    (TapeEmbedding.run_embed UnaryTemplate.machine ah atp _ _ ra hra)).1
  simp only [TapeEmbedding.receipt, hfa, hsa] at hfirst
  have hfirst' := hfirst.enlarge (large := 4*(cap+2)) (by
    simp [TapeEmbedding.extraCells, atp, Fin.sum_univ_succ,
      CapMachine.counter_length _ _ hv, CapMachine.counter_length _ _ ht,
      CapMachine.counter_length cap cap (Nat.le_refl _)]
    omega)

  obtain ⟨rb,hrb,hfb,hsb,hpb⟩ := CapMachine.reset_run cap (value+value) (value+value) hv (Nat.le_refl _)
  let bh : Fin 3 → ℕ := ![1,value+value+1,pos+2]
  let btp : Fin 3 → List Bool := ![CapMachine.counter cap value,
    CapMachine.counter cap cap, CapMachine.counter cap total]
  have hsecond := second_reset_prefix (prefix_of_run _ _ _ _
    (TapeRenaming.run_rename swap resetA _ _ _
      (TapeEmbedding.run_embed UnaryTemplate.machine bh btp _ _ rb hrb))).1
  simp only [TapeRenaming.receipt, TapeEmbedding.receipt, hfb, hsb] at hsecond
  have hsecond' := hsecond.enlarge (large := 4*(cap+2)) (by
    simp [TapeEmbedding.extraCells, btp, Fin.sum_univ_succ,
      CapMachine.counter_length _ _ hvc, CapMachine.counter_length _ _ ht,
      CapMachine.counter_length cap cap (Nat.le_refl _)]
    omega)

  obtain ⟨rc,hrc,hfc,hsc,hpc⟩ := CopyMachine.copy_run cap (value+value) value hv (by omega)
  let ch : Fin 2 → ℕ := ![value+value+1,pos+2]
  let ctp : Fin 2 → List Bool := ![CapMachine.counter cap cap,CapMachine.counter cap total]
  have hcopy := copy_prefix (prefix_of_run _ _ _ _
    (TapeRenaming.run_rename swap (TapeEmbedding.machine 2 CopyMachine.machine) _ _ _
      (TapeEmbedding.run_embed CopyMachine.machine ch ctp _ _ rc hrc))).1
  simp only [TapeRenaming.receipt, TapeEmbedding.receipt, hfc, hsc] at hcopy
  have hcopy' := hcopy.enlarge (large := 4*(cap+2)) (by
    simp [TapeEmbedding.extraCells, ctp, Fin.sum_univ_succ,
      CapMachine.counter_length _ _ ht, CapMachine.counter_length cap cap (Nat.le_refl _)]
    omega)

  have hlast := final_reset_prefix (prefix_of_run _ _ _ _
    (TapeEmbedding.run_embed UnaryTemplate.machine ah atp _ _ rb hrb)).1
  simp only [TapeEmbedding.receipt, hfb, hsb] at hlast
  have hlast' := hlast.enlarge (large := 4*(cap+2)) (by
    simp [TapeEmbedding.extraCells, atp, Fin.sum_univ_succ,
      CapMachine.counter_length _ _ hv, CapMachine.counter_length _ _ ht,
      CapMachine.counter_length cap cap (Nat.le_refl _)]
    omega)

  have hm1 : controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
      (fun _ => CapMachine.counter cap total) (CapMachine.cfg 1 cap value (value+value) value)) =
      controlConfig firstResetCode (TapeEmbedding.config ah atp
        (UnaryTemplate.config 0 (CapMachine.counter cap value) (value+1))) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, CapMachine.cfg,
        UnaryTemplate.config, ah, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, CapMachine.cfg,
        UnaryTemplate.config, atp, Fin.addCases]
  have hm2 : controlConfig firstResetCode (TapeEmbedding.config ah atp
      (UnaryTemplate.config 2 (CapMachine.counter cap value) 1)) =
      controlConfig secondResetCode (TapeRenaming.config swap (TapeEmbedding.config bh btp
        (UnaryTemplate.config 0 (CapMachine.counter cap (value+value)) (value+value+1)))) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, ah, bh, swap, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, atp, btp, swap, Fin.addCases]
  have hm3 : controlConfig secondResetCode (TapeRenaming.config swap (TapeEmbedding.config bh btp
      (UnaryTemplate.config 2 (CapMachine.counter cap (value+value)) 1))) =
      controlConfig copyCode (TapeRenaming.config swap (TapeEmbedding.config ch ctp
        (CopyMachine.cfg 0 cap (value+value) value 0))) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, CopyMachine.cfg, bh, ch, swap, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, CopyMachine.cfg, btp, ctp, swap, Fin.addCases]
  have hm4 : controlConfig copyCode (TapeRenaming.config swap (TapeEmbedding.config ch ctp
      (CopyMachine.cfg 1 cap (value+value) value (value+value)))) =
      controlConfig finalResetCode (TapeEmbedding.config ah atp
        (UnaryTemplate.config 0 (CapMachine.counter cap (value+value)) (value+value+1))) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, CopyMachine.cfg, ch, ah, swap, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, TapeRenaming.config,
        UnaryTemplate.config, CopyMachine.cfg, ctp, atp, swap, Fin.addCases]
  have hend : controlConfig finalResetCode (TapeEmbedding.config ah atp
      (UnaryTemplate.config 2 (CapMachine.counter cap (value+value)) 1)) =
      boundary cap total (pos+1) (value+value) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, UnaryTemplate.config,
        ah, boundary, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, UnaryTemplate.config,
        atp, boundary, Fin.addCases]
  rw [hm1] at hbody'
  rw [hm2] at hfirst'
  rw [hm3] at hsecond'
  rw [hm4] at hcopy'
  rw [hend] at hlast'
  have htail := hbody'.trans (hfirst'.trans (hsecond'.trans (hcopy'.trans hlast')))
  have hj := Prefix.step (by rw [boundary_cells _ _ _ _ ht hvc]) (by rfl)
    (enter_step cap total pos value hp) htail
  convert hj using 1
  omega

end NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
