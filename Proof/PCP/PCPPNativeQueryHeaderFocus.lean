import Proof.PCP.PCPPNativeQueryLoopFocus

/-! Dock the actual original header reader without disturbing the prepared
node bank, live output, or work reserved for the original output footer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reserved (i : Fin 168) : Prop := i=124 ∨ 155 ≤ i.val
theorem reserved_high (i : Fin 168) (hi : reserved i) : 123 ≤ i.val := by
  rcases hi with rfl|hi <;> omega
theorem reserved_header (i : Fin 168) (hi : reserved i) (j : Fin 31) : headerSlots j≠i := by
  intro h
  have hv := congrArg Fin.val h
  rcases hi with rfl|hi
  · simp only [headerSlots] at hv
    split_ifs at hv <;> simp_all only [Fin.ext_iff]
    all_goals omega
  · have hlt : (headerSlots j).val < 155 := by
      fin_cases j <;> decide
    omega
theorem cold_high (bits queries : List Bool) (cursor base position C F : ℕ) (out : List Bool)
    (i : Fin 168) (hi : 122 ≤ i.val) :
    heads cursor out i=0 ∧ data bits queries base position C F out i=[] := by
  let k : Fin 46 := ⟨i.val-122,by omega⟩
  have he : i=k.natAdd 122 := by apply Fin.ext; simp only [Fin.val_natAdd]; dsimp only [k]; omega
  rw [he]
  simp only [heads,data,Fin.addCases_right,and_self]
theorem header_low_away (i : Fin 122) (hi : i≠0) (j : Fin 31) : headerSlots j≠i.castAdd 46 := by
  by_cases hj : j=0
  · subst j
    intro h
    apply hi
    apply Fin.ext
    exact (congrArg (fun k : Fin 168 => k.val) h).symm
  · have hl := header_away j hj
    apply Fin.ne_of_val_ne
    change (headerSlots j).val≠i.val
    omega

theorem header_focus_run (pre suffix queries : List Bool) (arity size base position C F : ℕ) (out : List Bool) :
    ∃ result,runFrom header (PCPPNativeQueryHeader.budget arity size)
      ⟨header.start,heads pre.length out,data (PCPPNativeQueryHeader.source pre suffix arity size) queries base position C F out⟩=some result ∧
      result.steps ≤ PCPPNativeQueryHeader.budget arity size ∧
      lowFrame (PCPPNativeQueryHeader.source pre suffix arity size) queries
        (pre.length+(natWord arity).length+(natWord size).length) base position C F out result.final.heads result.final.tapes ∧
      result.final.tapes 123=UnaryTemplate.tape arity ∧ result.final.heads 123=1 ∧
      result.final.tapes 122=UnaryTemplate.tape size ∧ result.final.heads 122=1 ∧
      (∀ i,reserved i → result.final.heads i=0 ∧ result.final.tapes i=[]) := by
  obtain ⟨raw,hr,rs,r0,rh0,ra,rha,rsize,rhs⟩ := PCPPNativeQueryHeader.header_run pre suffix arity size
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock headerSlots header_injective
    PCPPNativeQueryHeader.machine _ (heads pre.length out)
    (data (PCPPNativeQueryHeader.source pre suffix arity size) queries base position C F out) _
    (by intro j
        by_cases hj : j=0
        · subst j; rfl
        · simpa only [PCPPNativeQueryHeader.entry,hj,ite_false] using
            (cold_high (PCPPNativeQueryHeader.source pre suffix arity size) queries pre.length
              base position C F out (headerSlots j) (header_away j hj)).1)
    (by intro j
        by_cases hj : j=0
        · subst j; rfl
        · simpa only [PCPPNativeQueryHeader.entry,hj,ite_false] using
            (cold_high (PCPPNativeQueryHeader.source pre suffix arity size) queries pre.length
              base position C F out (headerSlots j) (header_away j hj)).2) raw hr
  refine ⟨result,run,by omega,?_,(ht 10).trans ra,(hh 10).trans rha,
    (ht 20).trans rsize,(hh 20).trans rhs,?_⟩
  · intro i
    by_cases hi : i=0
    · subst i; exact ⟨(hh 0).trans rh0,(ht 0).trans r0⟩
    · have hk := keep (i.castAdd 46) (header_low_away i hi)
      constructor
      · simpa only [heads,Fin.addCases_left,PCPPNativeNodeReusable.heads,hi,ite_false] using hk.1
      · simpa only [data,Fin.addCases_left] using hk.2
  · intro i hi
    have hk := keep i (reserved_header i hi)
    have hc := cold_high (PCPPNativeQueryHeader.source pre suffix arity size) queries pre.length base position C F out i
      (by have := reserved_high i hi; omega)
    exact ⟨hk.1.trans hc.1,hk.2.trans hc.2⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
