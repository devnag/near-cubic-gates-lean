import Proof.CaseAnalysis.CaseTwoUnaryLookup

/-! The raw lookup is specialized to an actual auxiliary assignment table.
Its index is a paid unary value; no binary lookup or table re-encoding is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.UnaryLookup
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bit_ready (bits : List Bool) (i : Fin bits.length) : ∃ out,
    ClockJoin.ReadyRun machine (2*i.val+4) ![List.replicate i.val true,bits,[],[]] out ∧
      out 2=[bits[i.val]]:=by
  obtain ⟨out,hr,ht,_,_⟩:=lookup_run (bits.take i.val) (bits.drop (i.val+1)) bits[i.val]
  have hl:(bits.take i.val).length=i.val:=by simp
  rw [hl] at hr
  have hi:input (bits.take i.val) (bits.drop (i.val+1)) bits[i.val]=
      ![List.replicate i.val true,bits,[],[]]:=by
    funext j;fin_cases j <;>simp [input,hl]
  rw [hi] at hr
  exact ⟨out,hr,ht⟩

theorem auxiliary_ready {n : ℕ} (u : BitInput n) (i : Fin n) : ∃ out,
    ClockJoin.ReadyRun machine (2*i.val+4) ![List.replicate i.val true,List.ofFn u,[],[]] out ∧
      out 2=[u i]:=by
  obtain ⟨out,hr,ht⟩:=bit_ready (List.ofFn u) ⟨i.val,by simp⟩
  refine ⟨out,hr,?_⟩
  simpa only [List.getElem_ofFn] using ht

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.UnaryLookup
