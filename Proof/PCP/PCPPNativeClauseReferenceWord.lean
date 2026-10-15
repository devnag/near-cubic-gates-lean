import Proof.PCP.PCPPNativeClauseReference

/-! The same literal-reference machine accepts the actual shorter sentinel
word from the binary reader. Inverse padding transports the real trace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wordInput (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) :=
  if i=0 then CompareMachine.word (2*index+sign.toNat) else input index sign stride p n i
def wordCaps (index : ℕ) (sign : Bool) (i : Fin 13) := if i=0 then 2*index+sign.toNat+2 else 0

theorem word_run (index : ℕ) (sign : Bool) (stride p n : ℕ) : ∃ r,
    run machine (budget index sign stride p n) (wordInput index sign stride p n)=some r ∧
      (∀ i : Fin 13,i≠0 → r.final.tapes i=output index sign stride p n i) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget index sign stride p n := by
  obtain ⟨base,hb,bt,bh,bs⟩:=ready_run index sign stride p n
  have hi : ZeroPadding.config (wordCaps index sign)
      (initialConfiguration machine (wordInput index sign stride p n))=
      initialConfiguration machine (input index sign stride p n) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases h : i=0
      · rw [h]
        simp [ZeroPadding.config,initialConfiguration,wordCaps,wordInput,input,
          ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
      · simp [ZeroPadding.config,initialConfiguration,wordCaps,wordInput,h,ZeroPadding.pad_zero]
  change runFrom machine _ _=some base at hb
  rw [←hi] at hb
  obtain ⟨r,hr,hf,hs,_⟩:=ZeroPadding.run_unpad machine (wordCaps index sign) _ _ base hb
  refine ⟨r,hr,?_,?_,hs.le.trans bs⟩
  · intro i h
    have ht:=congrArg (fun c=>c.tapes i) hf
    rw [bt] at ht
    simpa only [ZeroPadding.config,wordCaps,h,ite_false,ZeroPadding.pad_zero] using ht
  · intro i
    have hh:=congrArg (fun c=>c.heads i) hf
    exact hh.trans (bh i)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
