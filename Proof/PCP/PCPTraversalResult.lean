import Proof.PCP.PCPTraversalPair

/-! The three physical result-copy tails in the fixed serializer controller.
The result and copy log are swept before copying the canonical pair field. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resultSlots : Fin 2 → Fin 128 := ![77,91]
def resultCopySlots : Fin 3 → Fin 128 := ![65,77,91]
theorem resultSlots_injective : Function.Injective resultSlots := by decide
theorem resultCopySlots_injective : Function.Injective resultCopySlots := by decide

def resultLocal (cap : ℕ) (bits : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame bits),ZeroPadding.pad cap (frame bits),
    List.replicate cap false]
noncomputable def copiedResult (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) : Fin 128 → List Bool :=
  install resultCopySlots (cleared resultSlots cap log ambient) (resultLocal cap bits)

theorem padded_field_ready (bits : List Bool) (cap : ℕ) (hcap : 2*bits.length+1≤cap) :
    ReadyRun PCPFieldMoves.readyMachine (4*bits.length+4)
      ![ZeroPadding.pad cap (frame bits),List.replicate cap false,List.replicate cap false]
      (resultLocal cap bits) := by
  have h := PCPFieldMoves.ready_run bits
    (List.replicate (cap-(frame bits).length) false) cap cap
  have he : PCPFieldMoves.output [] bits
      (List.replicate (cap-(frame bits).length) false) cap cap=resultLocal cap bits := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change List.replicate (max cap (2*bits.length+1)) false=List.replicate cap false
      rw [max_eq_left hcap]
  rw [he] at h
  exact h

theorem result_clear_calls (j k l : Fin 39)
    (hj : call j=clear resultSlots) (hk : call k=copyField 65 77 91)
    (hjk : ∀ q scanned,next j q scanned=some k)
    (hkl : ∀ q scanned,next k q scanned=some l)
    (cap log : ℕ) (bits : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hcap : 2*bits.length+1≤cap)
    (hb : ∀ i,(ambient (resultSlots i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hsource : ambient 65=ZeroPadding.pad cap (frame bits))
    (hh : ∀ i,heads (resultCopySlots i)=0) (hhd : heads 28=0) (hhl : heads 127=0) :
    Path j l (2*cap+4*bits.length+10) heads ambient heads (copiedResult cap log bits ambient) := by
  have hclear := clear_path j k resultSlots hj hjk resultSlots_injective
    (by decide) (by decide) cap log heads ambient hb hdriver hlog
    (by intro i; fin_cases i; exact hh 1; exact hh 2) hhd hhl
  have hin : ∀ i,cleared resultSlots cap log ambient (resultCopySlots i)=
      (![ZeroPadding.pad cap (frame bits),List.replicate cap false,
        List.replicate cap false] : Fin 3 → List Bool) i := by
    intro i
    fin_cases i
    · exact (cleared_other resultSlots cap log ambient 65 (by decide)
        (by decide) (by decide)).trans hsource
    · exact cleared_slot resultSlots resultSlots_injective (by decide) (by decide)
        cap log ambient 0
    · exact cleared_slot resultSlots resultSlots_injective (by decide) (by decide)
        cap log ambient 1
  obtain ⟨r,hr,hrh,hrt,_⟩ := (padded_field_ready bits cap hcap).focus_at resultCopySlots
    resultCopySlots_injective heads (cleared resultSlots cap log ambient) hin hh
  have hcopy := packed_path k l (copyField 65 77 91) hk (4*bits.length+4)
    heads (cleared resultSlots cap log ambient) _ ⟨r,hr,hrh,hrt⟩ hkl
  have hpath := hclear.trans hcopy
  have he : (2*cap+5)+(4*bits.length+4+1)=2*cap+4*bits.length+10 := by omega
  rw [he] at hpath
  exact hpath

theorem copiedResult_source (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) :
    copiedResult cap log bits ambient 65=ZeroPadding.pad cap (frame bits) :=
  install_slot resultCopySlots resultCopySlots_injective _ (resultLocal cap bits) 0
theorem copiedResult_result (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) :
    copiedResult cap log bits ambient 77=ZeroPadding.pad cap (frame bits) :=
  install_slot resultCopySlots resultCopySlots_injective _ (resultLocal cap bits) 1
theorem copiedResult_other (cap log : ℕ) (bits : List Bool)
    (ambient : Fin 128 → List Bool) (i : Fin 128)
    (h65 : 65≠i) (h77 : 77≠i) (h91 : 91≠i) (h28 : 28≠i) (h127 : 127≠i) :
    copiedResult cap log bits ambient i=ambient i := by
  apply Eq.trans (install_other resultCopySlots _ _ i ?_)
    (cleared_other resultSlots cap log ambient i ?_ h28 h127)
  · intro j; fin_cases j
    · exact h65
    · exact h77
    · exact h91
  · intro j; fin_cases j
    · exact h77
    · exact h91

theorem result_leaf_path (cap log : ℕ) (bits : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hcap : 2*bits.length+1≤cap)
    (hb : ∀ i,(ambient (resultSlots i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hsource : ambient 65=ZeroPadding.pad cap (frame bits))
    (hh : ∀ i,heads (resultCopySlots i)=0) (hhd : heads 28=0) (hhl : heads 127=0) :
    Path 7 9 (2*cap+4*bits.length+10) heads ambient heads (copiedResult cap log bits ambient) :=
  result_clear_calls 7 8 9 rfl rfl (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) cap log bits heads ambient hcap hb hdriver hlog hsource hh hhd hhl

end NearCubicWires.RepairOrdinary.PCPTraversal
