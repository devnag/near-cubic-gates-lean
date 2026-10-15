import Proof.CaseAnalysis.RowsPacketBranch

/-! One enclosing polynomial packet, including the physical zero-monomial
skip, has a uniform receipt for the outer live-family loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketOptional
open LocalBitMultitape CloseoutRowsBankPacket CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def packet {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) : List Bool :=
  if rows=[] then [false] else
    true::word (CloseoutRowsPacketPolynomial.data gs p F Q w C rows [])
noncomputable def machine :=
  CloseoutRowsPacketBranch.machine (113 : Fin 114) CloseoutRowsPacketPolynomial.machine
def cost (Q C : ℕ) := CloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+6

theorem cuts_nil {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ) :
    CloseoutRowsSharedDigits.cuts gs Q w []=[] := by
  have hd : ∀ j,CloseoutRowsCutMeaning.degreeCuts gs w j []=[] := fun j=>
    CloseoutRowsDegreeRange.degree_nil gs w j [] (by simp) (by simp)
  simp [CloseoutRowsSharedDigits.cuts,hd]

theorem optional_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out pre tail : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length<2^w)
    (hQp : Q≤p) (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let pkt:=packet gs p F Q w C rows
    let result:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (cost Q C)
      ⟨machine.start,heads out pre.length,tapes C out (pre++pkt++tail)⟩=some actual ∧
      actual.final.heads=heads result (pre.length+pkt.length) ∧
      actual.final.tapes=tapes C result (pre++pkt++tail) ∧ actual.steps≤cost Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  by_cases he : rows=[]
  · subst rows
    obtain ⟨a,ha,ah,atape,asteps⟩ := CloseoutRowsPacketBranch.absent_run (113 : Fin 114)
      CloseoutRowsPacketPolynomial.machine (heads out pre.length)
      (tapes C out (pre++[false]++tail))
      (by change readTapeBit ((pre++[false])++tail) pre.length=false; simp [List.append_assoc,Streaming.read_append])
    have hb : 2≤cost Q C := by unfold cost; omega
    have more:=runFrom_moreFuel machine 2 (cost Q C-2) _ a ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨a,?_,?_,?_,?_⟩
    · simpa only [machine,packet,↓reduceIte,C] using more
    · rw [ah]
      change Function.update (heads out pre.length) (113 : Fin 114) (pre.length+1)=_
      rw [CloseoutRowsPacketFlag.advanced]
      simp only [cuts_nil,List.flatMap_nil,List.append_nil,packet,↓reduceIte,List.length_singleton]
    · simpa only [cuts_nil,List.flatMap_nil,List.append_nil,packet,↓reduceIte,C] using atape
    · change a.steps≤cost Q C
      omega
  · have hM : 0<rows.length := List.length_pos_iff.mpr he
    let raw:=word (CloseoutRowsPacketPolynomial.data gs p F Q w C rows [])
    let tt:=tapes C out (pre++true::(raw++tail))
    obtain ⟨base,hbase,bh,bt,_⟩ := CloseoutRowsPacketPolynomial.packet_run gs p F Q w rows out
      (pre++[true]) tail hl hM hw hQp hp hF
    have hwrd:=CloseoutRowsPacketIndependent.word_out gs p F Q w C rows out
    rw [hwrd] at hbase bh bt
    have hsource :
        (⟨CloseoutRowsPacketPolynomial.machine.start,
          Function.update (heads out pre.length) (113 : Fin 114) (heads out pre.length 113+1),tt⟩ :
          Configuration 114 _)=
        ⟨CloseoutRowsPacketPolynomial.machine.start,heads out (pre++[true]).length,
          tapes C out ((pre++[true])++raw++tail)⟩ := by
      apply configuration_ext
      · rfl
      · change Function.update (heads out pre.length) (113 : Fin 114) (pre.length+1)=_
        rw [CloseoutRowsPacketFlag.advanced]
        simp only [List.length_append,List.length_singleton]
      · simp only [tt,List.append_assoc,List.cons_append,List.nil_append]
    rw [←hsource] at hbase
    obtain ⟨a,ha,ah,atape,asteps⟩:=CloseoutRowsPacketBranch.present_run (113 : Fin 114)
      CloseoutRowsPacketPolynomial.machine (heads out pre.length) tt _
      (by change readTapeBit (pre++true::(raw++tail)) pre.length=true; simp [Streaming.read_append]) base hbase
    have db:=CloseoutRowsPacketPolynomial.data_bound gs p F Q w rows out hl hw.le hF
    have hb:=CloseoutRowsBankPacket.budget_bound C
      (CloseoutRowsPacketPolynomial.data gs p F Q w C rows out) db
    have hcost : CloseoutRowsPacketPolynomial.budget gs p F Q w C rows out+3≤cost Q C := by
      unfold CloseoutRowsPacketPolynomial.budget CloseoutRowsPacketPolynomial.nativeBudget cost
      omega
    have more:=runFrom_moreFuel machine _ (cost Q C-(CloseoutRowsPacketPolynomial.budget gs p F Q w C rows out+3)) _ a ha
    rw [Nat.add_sub_of_le hcost] at more
    refine ⟨a,?_,?_,?_,asteps.trans hcost⟩
    · simpa only [machine,tt,raw,C,packet,he,↓reduceIte,List.cons_append,List.append_assoc] using more
    · rw [ah,bh]
      simp only [packet,he,↓reduceIte,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm 1,C]
    · rw [atape,bt]
      simp only [packet,he,↓reduceIte,List.append_assoc,List.cons_append,List.nil_append,C]

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketOptional
