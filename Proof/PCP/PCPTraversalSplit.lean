import Proof.PCP.PCPTraversalLeaf

/-! Executed midpoint division in the fixed internal-node branch. The input
is the actual retained unary count; no midpoint driver is supplied. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def splitClearSlots : Fin 3 → Fin 128 := ![85,86,87]
def splitSlots : Fin 4 → Fin 128 := ![79,85,86,87]
theorem splitClearSlots_injective : Function.Injective splitClearSlots := by decide
theorem splitSlots_injective : Function.Injective splitSlots := by decide

def splitLocal (n cap countCap : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad countCap (List.replicate n true),
    ZeroPadding.pad cap (List.replicate ((n+1)/2) true),
    ZeroPadding.pad cap (List.replicate (n/2) true),List.replicate cap false]
noncomputable def splitOutput (n cap countCap log : ℕ) (ambient : Fin 128 → List Bool) :=
  install splitSlots (cleared splitClearSlots cap log ambient) (splitLocal n cap countCap)

theorem padded_split_ready (n cap countCap : ℕ) (hc : n+1≤cap) :
    ClockJoin.ReadyRun PCPUnarySplit.machine (2*n+4)
      ![ZeroPadding.pad countCap (List.replicate n true),List.replicate cap false,
        List.replicate cap false,List.replicate cap false]
      (splitLocal n cap countCap) := by
  have h := PCPPairReusable.padded_ready _ _ _ (PCPUnarySplit.split_run n)
    (![countCap,cap,cap,cap] : Fin 4 → ℕ)
  have hin : (fun i => ZeroPadding.pad ((![countCap,cap,cap,cap] : Fin 4 → ℕ) i)
      ((![List.replicate n true,[],[],[]] : Fin 4 → List Bool) i))=
      ![ZeroPadding.pad countCap (List.replicate n true),List.replicate cap false,
        List.replicate cap false,List.replicate cap false] := by
    funext i; fin_cases i <;> rfl
  have hout : (fun i => ZeroPadding.pad ((![countCap,cap,cap,cap] : Fin 4 → ℕ) i)
      ((![List.replicate n true,List.replicate ((n+1)/2) true,List.replicate (n/2) true,
        List.replicate (n+1) false] : Fin 4 → List Bool) i))=splitLocal n cap countCap := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change ZeroPadding.pad cap (List.replicate (n+1) false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  rw [hin,hout] at h
  exact h

theorem split_path (n cap countCap log : ℕ) (heads : Fin 128 → ℕ)
    (ambient : Fin 128 → List Bool) (hc : n+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hcount : ambient 79=ZeroPadding.pad countCap (List.replicate n true))
    (hhd : heads 28=0) :
    Path 14 16 (2*cap+2*n+10) heads ambient heads (splitOutput n cap countCap log ambient) := by
  have hclear := clear_path 14 15 splitClearSlots rfl (by intro q scanned; simp [next])
    splitClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨r,hr,hrh,hrt,_⟩ := (padded_split_ready n cap countCap hc).focus_at splitSlots
    splitSlots_injective heads (cleared splitClearSlots cap log ambient)
    (by intro i; fin_cases i
        · exact (cleared_other splitClearSlots cap log ambient 79 (by decide) (by decide) (by decide)).trans hcount
        · exact cleared_slot splitClearSlots splitClearSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot splitClearSlots splitClearSlots_injective (by decide) (by decide) cap log ambient 1
        · exact cleared_slot splitClearSlots splitClearSlots_injective (by decide) (by decide) cap log ambient 2)
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
  have hsplit := packed_path 15 16 (focused splitSlots PCPUnarySplit.machine) rfl (2*n+4)
    heads (cleared splitClearSlots cap log ambient) _ ⟨r,hr,hrh,hrt⟩ (by intro q scanned; simp [next])
  have hpath := hclear.trans hsplit
  have he : (2*cap+5)+(2*n+4+1)=2*cap+2*n+10 := by omega
  rw [he] at hpath
  exact hpath

theorem split_output_halves (n cap countCap log : ℕ) (ambient : Fin 128 → List Bool) :
    splitOutput n cap countCap log ambient 85=ZeroPadding.pad cap (List.replicate ((n+1)/2) true) ∧
    splitOutput n cap countCap log ambient 86=ZeroPadding.pad cap (List.replicate (n/2) true) :=
  ⟨install_slot splitSlots splitSlots_injective _ (splitLocal n cap countCap) 1,
    install_slot splitSlots splitSlots_injective _ (splitLocal n cap countCap) 2⟩

theorem WorkBound.splitOutput {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (n countCap : ℕ) (hn : n+1≤cap) (hcountCap : countCap≤cap) :
    WorkBound cap (splitOutput n cap countCap log ambient) := by
  apply (hb.clear splitClearSlots splitClearSlots_injective (by decide) (by decide)).install splitSlots
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad countCap (List.replicate n true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le hcountCap (by omega)
  · change (ZeroPadding.pad cap (List.replicate ((n+1)/2) true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl (by omega)
  · change (ZeroPadding.pad cap (List.replicate (n/2) true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

end NearCubicWires.RepairOrdinary.PCPTraversal
