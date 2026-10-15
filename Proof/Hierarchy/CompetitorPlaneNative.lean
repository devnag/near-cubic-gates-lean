import Proof.Hierarchy.CompetitorPlaneFields

/-! The 18-tape arithmetic/append kernel at the actual 27-tape plane-cell
boundary. Both input cursors are retained and the output cursor streams. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nativeProgram (sign : Bool) := TapeEmbedding.machine 9 (CompetitorPlane.kernelProgram sign)
def extraHeads (countPos oldPos : ℕ) : Fin 9 → ℕ := ![countPos,oldPos,0,0,0,0,0,0,0]

theorem kernel_input_cases (w count positive negative : ℕ) (bits output : List Bool) (i : Fin 18) :
    CompetitorPlane.kernelInput w count positive negative bits output i=
      if i.val=0 then frame bits else if i.val=9 then List.replicate w true else if i.val=17 then output
      else if i.val=8 then ZeroPadding.pad (CompetitorPlane.capacity w) (frame (binary w count))
      else if i.val=14 then ZeroPadding.pad (CompetitorPlane.capacity w) (frame (binary w positive))
      else if i.val=15 then ZeroPadding.pad (CompetitorPlane.capacity w) (frame (binary w negative))
      else List.replicate (CompetitorPlane.capacity w) false := by
  fin_cases i <;> simp [CompetitorPlane.kernelInput,CompetitorPlane.paddedArithmeticInput,
    CompetitorPlane.arithmeticPadding,CompetitorPlane.arithmeticInput,
    CompetitorRationalProducts.input14_cases,Fin.addCases,ZeroPadding.pad]

theorem loaded_keep (w count positive negative : ℕ) (ambient : Fin 27 → List Bool)
    (i : Fin 27) (hi : retainedSlot i) : loadedFields w count positive negative ambient i=ambient i := by
  have h8 : i≠8 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have h14 : i≠14 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have h15 : i≠15 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [loadedFields,loadField,Function.update_of_ne h8,Function.update_of_ne h14,Function.update_of_ne h15]
  exact width_keep w ambient i hi

theorem loaded_native (b w count positive negative : ℕ) (bits counts old output : List Bool)
    (ambient : Fin 27 → List Bool) (h : Store b w bits counts old output ambient) (i : Fin 18) :
    loadedFields w count positive negative ambient (i.castAdd 9)=
      CompetitorPlane.kernelInput w count positive negative bits output i := by
  rw [kernel_input_cases]
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simp only [show (0 : Fin 18).val=0 by rfl,if_true]
    exact (loaded_keep w count positive negative ambient 0 (by simp [retainedSlot])).trans h.factor
  · by_cases h9 : i.val=9
    · have hi : i=9 := Fin.ext h9
      subst i
      change loadedFields w count positive negative ambient 9=List.replicate w true
      exact (loaded_keep w count positive negative ambient 9 (by simp [retainedSlot])).trans h.width
    · by_cases h17 : i.val=17
      · have hi : i=17 := Fin.ext h17
        subst i
        change loadedFields w count positive negative ambient 17=output
        exact (loaded_keep w count positive negative ambient 17 (by simp [retainedSlot])).trans h.output
      · simp only [h0,h9,h17,if_false]
        by_cases h8 : i.val=8
        · have hi : i=8 := Fin.ext h8
          subst i
          simp [loadedFields,loadField]
        · by_cases h14 : i.val=14
          · have hi : i=14 := Fin.ext h14
            subst i
            simp [loadedFields,loadField]
          · by_cases h15 : i.val=15
            · have hi : i=15 := Fin.ext h15
              subst i
              simp [loadedFields,loadField]
            · have hn8 : i.castAdd 9≠(8 : Fin 27) := fun he => h8 (congrArg (fun a : Fin 27 => a.val) he)
              have hn14 : i.castAdd 9≠(14 : Fin 27) := fun he => h14 (congrArg (fun a : Fin 27 => a.val) he)
              have hn15 : i.castAdd 9≠(15 : Fin 27) := fun he => h15 (congrArg (fun a : Fin 27 => a.val) he)
              have hn24 : i.castAdd 9≠(24 : Fin 27) := by intro he; have hv:=congrArg (fun a : Fin 27 => a.val) he; change i.val=24 at hv; omega
              simp only [h8,h14,h15,if_false,loadedFields,loadField,Function.update_of_ne hn8,
                Function.update_of_ne hn14,Function.update_of_ne hn15]
              apply width_work w ambient (i.castAdd 9) _ hn24
              left
              exact ⟨by simp; omega,fun he => h0 (congrArg (fun a : Fin 27 => a.val) he),
                fun he => h9 (congrArg (fun a : Fin 27 => a.val) he)⟩

theorem native_run (sign : Bool) (b w count positive negative countPos oldPos : ℕ)
    (bits counts old output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store b w bits counts old output ambient) (hbits : bits.length≤w)
    (hshift : count*2^bits.length<2^w)
    (hadd : count*value bits+(if sign then negative else positive)<2^w) :
    ∃ r out,runFrom (nativeProgram sign) (CompetitorPlane.kernelBudget w bits)
        (cfg (nativeProgram sign).start countPos oldPos output.length (loadedFields w count positive negative ambient))=some r ∧
      r.steps≤CompetitorPlane.kernelBudget w bits ∧
      r.final.heads=heads countPos oldPos (output++CompetitorPlane.nextWord sign w positive negative count bits).length ∧
      r.final.tapes=out ∧ Store b w bits counts old
        (output++CompetitorPlane.nextWord sign w positive negative count bits) out := by
  obtain ⟨base,produced,hr,hs,hh,ht,hout,h0,h9,hsupp⟩ :=
    CompetitorPlane.kernel_run sign w count positive negative bits output hbits hshift hadd
  let extra : Fin 9 → List Bool := fun i => loadedFields w count positive negative ambient (i.natAdd 18)
  have hrun := TapeEmbedding.run_embed (CompetitorPlane.kernelProgram sign) (extraHeads countPos oldPos) extra _ _ base hr
  have hin : TapeEmbedding.config (extraHeads countPos oldPos) extra
      (RecoveryCalls.restarted (CompetitorPlane.kernelProgram sign) (CompetitorPlane.kernelHeads output)
        (CompetitorPlane.kernelInput w count positive negative bits output))=
      cfg (nativeProgram sign).start countPos oldPos output.length (loadedFields w count positive negative ambient) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (m := 18) (n := 9) ?_ ?_ i
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,cfg,Fin.addCases_left]
        exact (loaded_native b w count positive negative bits counts old output ambient h j).symm
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,cfg,Fin.addCases_right,extra]
  rw [hin] at hrun
  let out := Fin.addCases (m := 18) (n := 9) (motive := fun _ => List Bool) produced extra
  refine ⟨TapeEmbedding.receipt (extraHeads countPos oldPos) extra base,out,hrun,hs,?_,?_,?_⟩
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,hh]
    funext i
    fin_cases i <;> rfl
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,ht]
    rfl
  · constructor
    · exact h0
    · exact h9
    · exact hout
    · exact (loaded_keep w count positive negative ambient 18 (by simp [retainedSlot])).trans h.counts
    · exact (loaded_keep w count positive negative ambient 19 (by simp [retainedSlot])).trans h.old
    · exact (loaded_keep w count positive negative ambient 20 (by simp [retainedSlot])).trans h.nativeWidth
    · exact (loaded_keep w count positive negative ambient 21 (by simp [retainedSlot])).trans h.erase
    · exact (loaded_keep w count positive negative ambient 22 (by simp [retainedSlot])).trans h.reset
    · intro j
      have hcap : w≤CompetitorPlane.capacity w := by unfold CompetitorPlane.capacity; nlinarith
      fin_cases j
      all_goals first
        | exact hsupp 1
        | exact hsupp 2
        | exact hsupp 3
        | exact hsupp 4
        | exact hsupp 5
        | exact hsupp 6
        | exact hsupp 7
        | exact hsupp 8
        | exact hsupp 10
        | exact hsupp 11
        | exact hsupp 12
        | exact hsupp 13
        | exact hsupp 14
        | exact hsupp 15
        | exact hsupp 16
        | skip
      all_goals simp only [out,workSlot,extra,loadedFields,loadField,
        widthPrepared,Function.update_apply]
      all_goals simp [Fin.addCases,Fin.ext_iff,clean_work w ambient 23 (by simp [working]),
        clean_work w ambient 25 (by simp [working]),clean_work w ambient 26 (by simp [working]),
        ZeroPadding.pad_length,max_eq_left hcap]

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream
