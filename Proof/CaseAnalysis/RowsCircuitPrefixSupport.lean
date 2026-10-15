import Proof.CaseAnalysis.RowsCircuitBottomDock

/-! Preserve the original prefix worker's receipt at the cold circuit
join. This bounds its private tapes by its own parsing work, separately
from the paid C allocation and copy sweeps on other tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem together {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H : Fin t → ℕ) (A B D : Fin t → List Bool) (hp : ReadyAt p fp H A B) (hq : ReadyAt q fq H B D) :
    ReadyAt (Composition.machine p q) (fp+1+fq) H A D:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=hp
  obtain ⟨s,hs,st,sh,ss⟩:=hq
  have he:Composition.restart r.final q.start=RecoveryCalls.restarted q H B:=configuration_ext rfl rh rt
  rw [←he] at hs
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q _ _ _ r s hr hs,st,sh,?_⟩
  change r.steps+1+s.steps ≤ fp+1+fq
  omega

theorem from_prefix (threshold : Bool) (C core W L : ℕ) (bits out : List Bool)
    (bank : Fin 639 → List Bool) (hin : 2*bits.length+1 ≤ C)
    (hp : ClockJoin.ReadyRun (CloseoutRowsCircuitPrefix.machine threshold)
      (CloseoutRowsCircuitPrefix.budget bits) (CloseoutRowsCircuitPrefix.input bits) bank)
    (htop : bank 158=frame (CloseoutRowsCircuitHeader.codeWord bits 3)) :
    ReadyAt (machine threshold) (budget C bits) (heads out) (input C core W L bits out)
      (output C core W L bits out bank):=by
  have initial:=together CloseoutRowsCircuitAllocate.machine seed _ _ (heads out) _ _ _
    (allocated_run C core W L bits out) (seed_run C core W L bits out)
  obtain ⟨r,hr,rh,rt,rs⟩:=hp.focus_at prefixSlots prefix_injective (heads out)
    (seeded C core W L bits out) (seeded_prefix C core W L bits out) (by
      intro i
      change (if (prefixSlots i)=1688 then out.length else if (prefixSlots i).val=1674 then 1 else 0)=0
      have hi:i.val < 639:=i.isLt
      simp only [prefixSlots,Fin.val_castAdd]
      split_ifs <;> first | rfl | (rename_i he;have hv:=congrArg (fun k : Fin 1703=>k.val) he;change i.val=1688 at hv;omega) | omega)
  have pr:ReadyAt (prefixMachine threshold) (CloseoutRowsCircuitPrefix.budget bits) (heads out)
      (seeded C core W L bits out) (framed C core W L bits out bank):=⟨r,hr,rt,rh,rs⟩
  have joined:=together first (prefixMachine threshold) _ _ (heads out) _ _ _ initial pr
  have all:=together (second threshold) load _ _ (heads out) _ _ _ joined
    (load_run C core W L bits out bank htop hin)
  have hf:((2*C+4+1+1)+1+CloseoutRowsCircuitPrefix.budget bits)+1+(2*C+4)=budget C bits:=by
    unfold budget;omega
  rw [hf] at all
  exact all

theorem prefix_support (threshold : Bool) (C : ℕ) (bits : List Bool)
    (bank : Fin 639 → List Bool) (hin : 2*bits.length+1 ≤ C)
    (hp : ClockJoin.ReadyRun (CloseoutRowsCircuitPrefix.machine threshold)
      (CloseoutRowsCircuitPrefix.budget bits) (CloseoutRowsCircuitPrefix.input bits) bank)
    (hc : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C) : ∀ i,(bank i).length ≤ C:=by
  obtain ⟨r,hr,rt,_rh,rs⟩:=hp
  intro i
  rw [←rt]
  apply CloseoutRowsProjectionReset.scratch_support (CloseoutRowsCircuitPrefix.machine threshold)
    _ C _ r hr i rfl
  · change (CloseoutRowsCircuitPrefix.input bits i).length ≤ C
    rw [prefix_input]
    split_ifs
    · change 1 ≤ C;omega
    · rw [frame_length];exact hin
    · exact Nat.zero_le _
  · omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
