import Proof.CaseAnalysis.CaseTwoFixedFoldLayout

/-! Execute each fixed ordinary block exactly once in a fresh bank. The
only shared mutable field is the XOR accumulator; every call is charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem run {t : ℕ} (sizes : ℕ→ℕ) (workers : (n : ℕ)→Machine t (sizes n))
    (acc : Fin t) (ha : 3≤acc.val) (words : Fin 3→List Bool) (cost : ℕ→ℕ) (bit : ℕ→Bool)
    (copies : ℕ)
    (hworkers : ∀ n<copies,∀ parity,∃ out,
      ClockJoin.ReadyRun (workers n) (cost n) (bodyInput acc words parity) out ∧
      (∀ i : Fin 3,out (ports acc ha i)=words i) ∧ out acc=[xor parity (bit n)]) :
    ∃ out,ClockJoin.ReadyRun (machine sizes workers acc copies) (budget cost copies)
      (initial t copies words) out ∧ Result t copies words (value bit copies) out:=by
  induction copies with
  | zero=>
    have hi : initial t 0 words=XorInit.input words:=by
      funext i;fin_cases i <;>rfl
    refine ⟨XorInit.output words,?_,?_,?_⟩
    · rw [hi]
      exact XorInit.ready words
    · intro i;fin_cases i <;>rfl
    · rfl
  | succ n ih=>
    obtain ⟨previous,hprevious,hfields⟩:=ih (fun j hj=>hworkers j (by omega))
    have firstReady:=hprevious.focus (previousSlots t n) (prefix_injective t n) (initial t (n+1) words)
      (by intro i;rfl)
    let middle:=install (previousSlots t n) (initial t (n+1) words) previous
    obtain ⟨body,hbody,hwords,hbit⟩:=hworkers n (by omega) (value bit n)
    have lastReady:=hbody.focus (slots acc n) (slots_injective acc n) middle (by
      intro j
      by_cases h3 : j.val<3
      · let i : Fin 3:=⟨j.val,h3⟩
        have he : j=ports acc ha i:=Fin.ext rfl
        rw [he,slots_port,←prefix_low]
        change install (previousSlots t n) (initial t (n+1) words) previous (previousSlots t n (low t n (i.castAdd 1)))=_
        rw [install_slot (previousSlots t n) (prefix_injective t n),hfields.words i]
        change words i=(if h : i.val<3 then words ⟨i.val,h⟩ else _)
        rw [dif_pos i.isLt]
      by_cases hac : j.val=acc.val
      · have he : j=acc:=Fin.ext hac
        subst j
        rw [slots_acc acc ha,←prefix_low]
        change install (previousSlots t n) (initial t (n+1) words) previous (previousSlots t n (low t n 3))=_
        rw [install_slot (previousSlots t n) (prefix_injective t n),hfields.parity]
        unfold bodyInput
        rw [dif_neg (by omega),if_pos rfl]
      · rw [slots_fresh acc n j h3 hac]
        change install (previousSlots t n) (initial t (n+1) words) previous (fresh t n j)=_
        rw [install_other (previousSlots t n) _ _ _ (fresh_outside t n j)]
        have hb:=tapes_lower t n
        simp only [initial,fresh,Fin.val_natAdd,bodyInput,dif_neg h3,if_neg hac]
        rw [dif_neg (by omega)])
    have whole:=ClockJoin.join (RecoveryFocus.machine (previousSlots t n) (machine sizes workers acc n))
      (RecoveryFocus.machine (slots acc n) (workers n)) _ _ _ _ _ firstReady lastReady
    refine ⟨_,whole,?_,?_⟩
    · intro i
      rw [←slots_port acc ha n i]
      exact (install_slot (slots acc n) (slots_injective acc n) _ _ (ports acc ha i)).trans (hwords i)
    · rw [←slots_acc acc ha n]
      exact (install_slot (slots acc n) (slots_injective acc n) _ _ acc).trans hbit

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FixedFold
