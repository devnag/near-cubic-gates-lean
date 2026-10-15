import Proof.Amplification.RecoveryRowStreamRead

/-! Prior-row lookup needs equality of padded binary codes, retaining both
words. Two paid comparisons give this equality with reusable scratch. The
semantic uniqueness lemma justifies keeping the first matching checked row. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
open CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem meaning_count_unique (left right : Row) (hl : Meaning left)
    (hr : Meaning right) (hc : left.code=right.code) : left.count=right.count := by
  obtain ⟨xs,hx,hn⟩ := hl
  obtain ⟨ys,hy,hm⟩ := hr
  have he : encodeBalancedList xs=encodeBalancedList ys := hx.trans (hc.trans hy.symm)
  have hd := congrArg decodeBalancedList he
  simp only [decodeBalancedList_encode,Option.some.injEq] at hd
  exact hn.symm.trans ((congrArg List.length hd).trans hm)

theorem checked_count_unique (rows : List Row) (hrows : checkFrom [] rows=true)
    (left right : Row) (hl : left∈rows) (hr : right∈rows)
    (hc : left.code=right.code) : left.count=right.count := by
  have hs := check_sound [] rows (by simp) hrows
  exact meaning_count_unique left right (hs left hl) (hs right hr) hc

end NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate

namespace NearCubicWires.RepairOrdinary.RecoveryRowComparison
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (left right : List Bool) (flags : Fin 2→Bool) (capacity : Nat) : Fin 5→List Bool :=
  ![frame left,frame right,[flags 0],[flags 1],List.replicate capacity false]
def slots (reverse : Bool) : Fin 4→Fin 5 :=
  if reverse then ![1,0,3,4] else ![0,1,2,4]
theorem slots_injective (reverse : Bool) : Function.Injective (slots reverse) := by
  cases reverse <;> decide
noncomputable def compare (reverse : Bool) := RecoveryFocus.machine (slots reverse) RecoveryPrefixCompare.machine

theorem comparison_ready (left right : List Bool) (flags : Fin 2→Bool) (capacity : Nat)
    (hw : left.length=right.length) (reverse : Bool) :
    ReadyRun (compare reverse) (4*left.length+8) (tapes left right flags capacity)
      (tapes left right (Function.update flags (if reverse then 1 else 0)
        (if reverse then decide (value right≤value left) else decide (value left≤value right)))
        (max capacity (2*left.length+3))) := by
  cases reverse
  · have h := (RecoveryPrefixCompare.compare_ready left right (flags 0) capacity hw).focus
      (slots false) (slots_injective false) (tapes left right flags capacity) (by
        intro i; fin_cases i <;> rfl)
    convert h using 1 <;> try rfl
    funext i
    fin_cases i
    · symm
      change install _ _ _ (slots false 0)=_
      rw [install_slot (slots false) (slots_injective false)]
      rfl
    · symm
      change install _ _ _ (slots false 1)=_
      rw [install_slot (slots false) (slots_injective false)]
      rfl
    · symm
      change install _ _ _ (slots false 2)=_
      rw [install_slot (slots false) (slots_injective false)]
      rfl
    · exact (install_other (slots false) (tapes left right flags capacity)
        ![frame left,frame right,[decide (value left≤value right)],
          List.replicate (max capacity (2*left.length+3)) false] 3
        (by intro j; fin_cases j <;> decide)).symm
    · symm
      change install _ _ _ (slots false 3)=_
      rw [install_slot (slots false) (slots_injective false)]
      rfl
  · have h := (RecoveryPrefixCompare.compare_ready right left (flags 1) capacity hw.symm).focus
      (slots true) (slots_injective true) (tapes left right flags capacity) (by
        intro i; fin_cases i <;> rfl)
    rw [←hw] at h
    convert h using 1 <;> try rfl
    funext i
    fin_cases i
    · symm
      change install _ _ _ (slots true 1)=_
      rw [install_slot (slots true) (slots_injective true)]
      rfl
    · symm
      change install _ _ _ (slots true 0)=_
      rw [install_slot (slots true) (slots_injective true)]
      rfl
    · exact (install_other (slots true) (tapes left right flags capacity)
        ![frame right,frame left,[decide (value right≤value left)],
          List.replicate (max capacity (2*left.length+3)) false] 2
        (by intro j; fin_cases j <;> decide)).symm
    · symm
      change install _ _ _ (slots true 2)=_
      rw [install_slot (slots true) (slots_injective true)]
      rfl
    · symm
      change install _ _ _ (slots true 3)=_
      rw [install_slot (slots true) (slots_injective true)]
      rfl

def gate : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    ![none,none,some (scanned 2 && scanned 3),none,none],fun _=>.stay⟩ else none

theorem gate_ready (left right : List Bool) (flags : Fin 2→Bool) (capacity : Nat) :
    ReadyRun gate 1 (tapes left right flags capacity)
      (tapes left right (Function.update flags 0 (flags 0 && flags 1)) capacity) := by
  let final : Configuration 5 2 := ⟨1,fun _=>0,
    tapes left right (Function.update flags 0 (flags 0 && flags 1)) capacity⟩
  have hs : step gate (initialConfiguration gate (tapes left right flags capacity))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

def sizes : Fin 3→Nat := ![9,9,2]
noncomputable def programs : (j : Fin 3)→Machine 5 (sizes j)
  | ⟨0,_⟩=>compare false
  | ⟨1,_⟩=>compare true
  | ⟨2,_⟩=>gate
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (_ : Fin 5→Bool) : Option (Fin 3) :=
  ![some 1,some 2,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem equal_ready (left right : List Bool) (flags : Fin 2→Bool) (capacity : Nat)
    (hw : left.length=right.length) :
    ReadyRun machine (8*left.length+20) (tapes left right flags capacity)
      (tapes left right ![decide (value left=value right),decide (value right≤value left)]
        (max capacity (2*left.length+3))) := by
  let f0 := Function.update flags 0 (decide (value left≤value right))
  let f1 := Function.update f0 1 (decide (value right≤value left))
  let cap := max capacity (2*left.length+3)
  have h0 := (comparison_ready left right flags capacity hw false).call
    sizes programs 0 next 0 1 (by intro q; rfl)
  have hsecond := comparison_ready left right f0 cap hw true
  simp only [cap,max_assoc,max_self] at hsecond
  have h1 := hsecond.call sizes programs 0 next 1 2 (by intro q; rfl)
  have h2 := (gate_ready left right f1 cap).stop sizes programs 0 next 2 (by intro q; rfl)
  have h := (h0.trans h1).trans h2
  have ht : ((4*left.length+8+1)+(4*left.length+8+1))+(1+1)=8*left.length+20 := by omega
  rw [ht] at h
  obtain ⟨r,hr,hf,hn⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨r,hr,?_,by intro i; simp [hf,RecoveryCalls.stopped],hn⟩
  rw [hf]
  change tapes left right (Function.update f1 0 (f1 0 && f1 1)) cap=_
  have he : Function.update f1 0 (f1 0 && f1 1)=
      ![decide (value left=value right),decide (value right≤value left)] := by
    funext i
    fin_cases i
    · apply Bool.eq_iff_iff.mpr
      simp [f1,f0,Nat.le_antisymm_iff]
    · simp [f1]
  rw [he]

end NearCubicWires.RepairOrdinary.RecoveryRowComparison
