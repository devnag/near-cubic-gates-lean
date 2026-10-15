import Proof.CaseAnalysis.RowsCircuitPrefix

/-! The measured gate already restores its heads. Its SAME run therefore
uses one reusable zero bank directly, without a second masked rewind. The
actual core template is retained outside the local capacity bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateBank
open LocalBitMultitape CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads (cap : ℕ) (i : Fin 1049) : ℕ:=if i.val=1035 then 0 else cap
def padded (cap : ℕ) (bank : Fin 1049→List Bool) (i : Fin 1049):=ZeroPadding.pad (pads cap i) (bank i)
def input (cap core : ℕ) (bits : List Bool):=padded cap (CloseoutRowsGateMeasured.input core bits)

theorem heads_eq (i : Fin 1049) : CloseoutRowsGateMeasured.heads i=if i.val=1035 then 1 else 0:=by
  refine Fin.addCases (m:=1038) (n:=11) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsGateMeasured.heads,Fin.addCases_left,Fin.val_castAdd]
    refine Fin.addCases (m:=1035) (n:=3) ?_ ?_ j
    · intro k
      simp only [CloseoutRowsGateGuard.heads,Fin.addCases_left,Fin.val_castAdd,if_neg (show k.val≠1035 by omega)]
    · intro k;fin_cases k <;> rfl
  · intro j
    simp only [CloseoutRowsGateMeasured.heads,Fin.addCases_right,Fin.val_natAdd,
      if_neg (show 1038+j.val≠1035 by omega)]

theorem input_eq (core : ℕ) (bits : List Bool) (i : Fin 1049) :
    CloseoutRowsGateMeasured.input core bits i=
      if i.val=1035 then UnaryTemplate.tape core else if i.val=1 then frame bits else []:=by
  refine Fin.addCases (m:=1038) (n:=11) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsGateMeasured.input,CloseoutRowsGateMeasured.extend,Fin.addCases_left,Fin.val_castAdd]
    refine Fin.addCases (m:=1035) (n:=3) ?_ ?_ j
    · intro k
      simp only [CloseoutRowsGateGuard.input,CloseoutRowsGateGuard.extend,Fin.addCases_left,Fin.val_castAdd,
        if_neg (show k.val≠1035 by omega)]
      refine Fin.addCases (m:=998) (n:=37) ?_ ?_ k
      · intro z
        simp only [CloseoutRowsGateCold.input,Fin.addCases_left,Fin.val_castAdd,CloseoutRowsGateFields.input]
        rfl
      · intro z
        simp only [CloseoutRowsGateCold.input,Fin.addCases_right,Fin.val_natAdd,
          if_neg (show 998+z.val≠1 by omega)]
    · intro k;fin_cases k <;> rfl
  · intro j
    simp only [CloseoutRowsGateMeasured.input,CloseoutRowsGateMeasured.extend,Fin.addCases_right,Fin.val_natAdd,
      if_neg (show 1038+j.val≠1035 by omega),if_neg (show 1038+j.val≠1 by omega)]

theorem gate_run (compressed : Bool) (cap core : ℕ) (bits : List Bool)
    (hinput:2*bits.length+1 ≤ cap) (htime:CloseoutRowsGateMeasured.budget bits+1 ≤ cap) : ∃ bank,
    ReadyAt (CloseoutRowsGateMeasured.machine compressed) (CloseoutRowsGateMeasured.budget bits)
      CloseoutRowsGateMeasured.heads (input cap core bits) (padded cap bank) ∧
      CloseoutRowsGateMeasured.Output compressed core bits bank ∧
      ∀ i : Fin 1049,i.val≠1035 → (padded cap bank i).length ≤ cap := by
  obtain ⟨bank,⟨base,hbase,bt,bh,bs⟩,meaning⟩:=CloseoutRowsGateMeasured.allraw compressed core bits
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config (CloseoutRowsGateMeasured.machine compressed)
    (pads cap) _ _ base hbase
  refine ⟨bank,⟨r,hr,?_,?_,rs ▸ bs⟩,meaning,?_⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad (pads cap i) (base.final.tapes i))=padded cap bank
    rw [bt];rfl
  · rw [rf];exact bh
  · intro i hi
    have hb:=PCPSerializerReuse.tape_support (CloseoutRowsGateMeasured.machine compressed) _ _ r hr i cap 0
      (by change CloseoutRowsGateMeasured.heads i ≤ 0;rw [heads_eq,if_neg hi])
      (by
        change (ZeroPadding.pad (pads cap i) (CloseoutRowsGateMeasured.input core bits i)).length ≤ max cap (0+1)
        rw [ZeroPadding.pad_length,input_eq]
        simp only [pads,if_neg hi]
        apply max_le
        · exact Nat.le_max_left _ _
        · split_ifs
          · exact (frame_length bits ▸ hinput).trans (Nat.le_max_left _ _)
          · exact Nat.zero_le _)
    rw [rf] at hb
    change (ZeroPadding.pad (pads cap i) (base.final.tapes i)).length ≤ _ at hb
    rw [bt,rs] at hb
    have hc:0+base.steps+1 ≤ cap:=by omega
    simpa only [Nat.max_eq_left hc,padded] using hb

end NearCubicWires.RepairOrdinary.CloseoutRowsGateBank
