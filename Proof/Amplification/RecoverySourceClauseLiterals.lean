import Proof.Amplification.RecoverySourceLiteralRetained

/-! Three actual original-CNF literal computations share the same retained
address stream. Each fixed bank starts blank except for its original source
literal field; all three executions and their composition steps are paid. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseLiterals
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (k : Fin 3) (i : Fin 53) : Fin 160 :=
  if i.val=11 then 159 else ⟨53*k.val+i.val,by have hk:=k.isLt; have hi:=i.isLt; omega⟩
theorem bank_injective (k : Fin 3) : Function.Injective (bank k) := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h; have ha:=a.isLt; have hb:=b.isLt; have hk:=k.isLt
  dsimp only [bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem bank_cross (k l : Fin 3) (hk : k≠l) (i : Fin 53) (hi : i.val≠11) :
    ∀ j,bank k j≠bank l i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hn : k.val≠l.val := fun he=>hk (Fin.ext he)
  have hj:=j.isLt; have hik:=i.isLt; have hkk:=k.isLt; have hll:=l.isLt
  dsimp only [bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (codes : Fin 3→List Bool) (source : List Bool) (i : Fin 160) :=
  if i.val=159 then source else if i.val=0 then RepairOrdinary.frame (codes 0)
  else if i.val=53 then RepairOrdinary.frame (codes 1)
  else if i.val=106 then RepairOrdinary.frame (codes 2) else []

theorem bank_input (codes : Fin 3→List Bool) (source : List Bool) (k : Fin 3) (i : Fin 53) :
    input codes source (bank k i)=RecoverySourceLiteralCode.input (codes k) source i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem carry_input (k l : Fin 3) (hk : k≠l) (ambient : Fin 160→List Bool) (out : Fin 53→List Bool)
    (code source : List Bool) (hsource : out 11=source)
    (ht : ∀ i,ambient (bank l i)=RecoverySourceLiteralCode.input code source i) :
    ∀ i,install (bank k) ambient out (bank l i)=RecoverySourceLiteralCode.input code source i := by
  intro i
  by_cases hi : i.val=11
  · have he : i=11 := Fin.ext hi
    subst i
    change install (bank k) _ _ (bank k 11)=_
    rw [install_slot _ (bank_injective k)]
    exact hsource
  · rw [install_other _ _ _ _ (bank_cross k l hk i hi)]
    exact ht i

noncomputable def phase (k : Fin 3) := RecoveryFocus.machine (bank k) RecoverySourceLiteralCode.machine
noncomputable def machine := Composition.machine (Composition.machine (phase 0) (phase 1)) (phase 2)

private theorem retained_literal {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun RecoverySourceLiteralCode.machine
      (RecoverySourceLiteralMeaning.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
      (RecoverySourceLiteralCode.input (literalCode literal).bits
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))) out ∧
      out 44=RepairOrdinary.frame (RecoverySourceLiteralMeaning.word pcp x randomness literal) ∧
      out 11=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) := by
  have hc : 2*(RecoverySourceLiteralMeaning.skipped pcp x randomness literal).length+
      (RecoverySourceLiteral.negative literal).toNat=literalCode literal := by
    rw [RecoverySourceLiteralMeaning.skipped_length]
    cases literal <;> rfl
  have hs := RecoverySourceLiteralMeaning.stream_index (RecoverySourceLiteralMeaning.addressBits pcp x randomness)
    (RecoverySourceLiteralMeaning.query literal)
  change FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)=
    FieldList.stream (RecoverySourceLiteralMeaning.skipped pcp x randomness literal)++
      RepairOrdinary.frame (RecoverySourceLiteralMeaning.addressBits pcp x randomness (RecoverySourceLiteralMeaning.query literal))++
        FieldList.stream ((RecoverySourceLiteralMeaning.fields pcp x randomness).drop ((RecoverySourceLiteralMeaning.query literal).val+1)) at hs
  have h := RecoverySourceLiteralCode.retained_code_run (RecoverySourceLiteral.negative literal)
    (RecoverySourceLiteralMeaning.skipped pcp x randomness literal)
    (RecoverySourceLiteralMeaning.addressBits pcp x randomness (RecoverySourceLiteralMeaning.query literal))
    (FieldList.stream ((RecoverySourceLiteralMeaning.fields pcp x randomness).drop ((RecoverySourceLiteralMeaning.query literal).val+1)))
  rw [hc,←hs] at h
  obtain ⟨out,hr,hword,hsource⟩ := h
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (RecoverySourceLiteralMeaning.budget_bound pcp x randomness literal),hword,hsource⟩

theorem literals_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (clause : Fin 3→Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun machine (3*RecoverySourceLiteralMeaning.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)+2)
      (input (fun i=>(literalCode (clause i)).bits) (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))) out ∧
      (∀ i,out (bank i 44)=RepairOrdinary.frame (RecoverySourceLiteralMeaning.word pcp x randomness (clause i))) ∧
      out 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) := by
  let codes : Fin 3→List Bool := fun i=>(literalCode (clause i)).bits
  let source := FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)
  obtain ⟨a,ha,aw,asource⟩ := retained_literal pcp x randomness (clause 0)
  obtain ⟨b,hb,bw,bsource⟩ := retained_literal pcp x randomness (clause 1)
  obtain ⟨c,hc,cw,csource⟩ := retained_literal pcp x randomness (clause 2)
  have first := ha.focus (bank 0) (bank_injective 0) (input codes source) (bank_input codes source 0)
  let stage1 := install (bank 0) (input codes source) a
  have second := hb.focus (bank 1) (bank_injective 1) stage1
    (carry_input 0 1 (by decide) _ a _ source asource (bank_input codes source 1))
  let stage2 := install (bank 1) stage1 b
  have third := hc.focus (bank 2) (bank_injective 2) stage2
    (carry_input 1 2 (by decide) _ b _ source bsource
      (carry_input 0 2 (by decide) _ a _ source asource (bank_input codes source 2)))
  have hall := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ first second) third
  have ht (B : Nat) : (B+1+B)+1+B=3*B+2 := by omega
  rw [ht] at hall
  refine ⟨_,hall,?_,?_⟩
  · intro i; fin_cases i
    · change install (bank 2) stage2 c (bank 0 44)=RepairOrdinary.frame (RecoverySourceLiteralMeaning.word pcp x randomness (clause 0))
      rw [install_other _ _ _ _ (bank_cross 2 0 (by decide) 44 (by decide))]
      dsimp only [stage2, stage1]
      rw [install_other _ _ _ _ (bank_cross 1 0 (by decide) 44 (by decide))]
      rw [install_slot _ (bank_injective 0)]
      exact aw
    · change install (bank 2) stage2 c (bank 1 44)=RepairOrdinary.frame (RecoverySourceLiteralMeaning.word pcp x randomness (clause 1))
      rw [install_other _ _ _ _ (bank_cross 2 1 (by decide) 44 (by decide))]
      dsimp only [stage2]
      rw [install_slot _ (bank_injective 1)]
      exact bw
    · change install (bank 2) stage2 c (bank 2 44)=RepairOrdinary.frame (RecoverySourceLiteralMeaning.word pcp x randomness (clause 2))
      rw [install_slot _ (bank_injective 2)]
      exact cw
  · change install (bank 2) _ _ (bank 2 11)=_
    rw [install_slot _ (bank_injective 2)]
    exact csource

end NearCubicWires.RepairSource.RecoverySourceClauseLiterals
