import Proof.Amplification.RecoveryAllCodeBanks

/-! One injective physical embedding of the complete348-tape all-code
checker into the493-tape cold producer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem join_injective {m n r : Nat} (f : Fin m→Fin r) (g : Fin n→Fin r)
    (hf : Function.Injective f) (hg : Function.Injective g) (hd : ∀ i j,f i≠g j) :
    Function.Injective (Fin.addCases (m:=m) (n:=n) (motive:=fun _=>Fin r) f g) := by
  let J : Fin (m+n)→Fin r := Fin.addCases (m:=m) (n:=n) (motive:=fun _=>Fin r) f g
  have h : ∀ i j,J i=J j→i=j := by
    intro i
    refine Fin.addCases (m:=m) (n:=n) (motive:=fun i=>∀ j,J i=J j→i=j) ?_ ?_ i
    · intro a j
      refine Fin.addCases (m:=m) (n:=n) (motive:=fun j=>J (a.castAdd n)=J j→a.castAdd n=j) ?_ ?_ j
      · intro b he
        simp only [J,Fin.addCases_left] at he
        exact congrArg (Fin.castAdd n) (hf he)
      · intro b he
        simp only [J,Fin.addCases_left,Fin.addCases_right] at he
        exact False.elim (hd a b he)
    · intro a j
      refine Fin.addCases (m:=m) (n:=n) (motive:=fun j=>J (a.natAdd m)=J j→a.natAdd m=j) ?_ ?_ j
      · intro b he
        simp only [J,Fin.addCases_left,Fin.addCases_right] at he
        exact False.elim (hd b a he.symm)
      · intro b he
        simp only [J,Fin.addCases_right] at he
        exact congrArg (Fin.natAdd m) (hg he)
  exact fun {i j}=>h i j

def rawSlots : Fin 136→Fin 493 := Fin.addCases (m:=66) (n:=70) (motive:=fun _=>Fin 493) rawViewSlots rawSATSlots
def compactSlots : Fin 212→Fin 493 := Fin.addCases (m:=57) (n:=155) (motive:=fun _=>Fin 493) markerSlots RecoveryColdCompact.bankSlots
def slots : Fin 348→Fin 493 := Fin.addCases (m:=136) (n:=212) (motive:=fun _=>Fin 493) rawSlots compactSlots
def caps (bits word : List Bool) : Fin 348→Nat :=
  Fin.addCases (m:=136) (n:=212) (motive:=fun _=>Nat)
    (Fin.addCases (m:=66) (n:=70) (motive:=fun _=>Nat)
      (RecoveryColdView.nativeCaps bits) (RecoveryColdSAT.caps bits word))
    (Fin.addCases (m:=57) (n:=155) (motive:=fun _=>Nat)
      (RecoveryColdMarker.caps bits) (RecoveryColdCompact.caps bits word))

theorem rawSlots_lt (i : Fin 136) : (rawSlots i).val<170 := by
  refine Fin.addCases (m:=66) (n:=70) (motive:=fun j=>(rawSlots j).val<170) ?_ ?_ i
  · intro j
    simp only [rawSlots,Fin.addCases_left]
    change (viewSlots j).val<170
    exact (viewSlots j).isLt.trans (by decide)
  · intro j
    simp only [rawSlots,Fin.addCases_right]
    change 100+j.val<170
    omega

theorem compactSlots_ge (i : Fin 212) : 279≤(compactSlots i).val := by
  refine Fin.addCases (m:=57) (n:=155) (motive:=fun j=>279≤(compactSlots j).val) ?_ ?_ i
  · intro j
    simp only [compactSlots,Fin.addCases_left]
    change 279≤279+j.val
    omega
  · intro j
    simp only [compactSlots,Fin.addCases_right]
    change 279≤338+j.val
    omega

theorem slots_injective : Function.Injective slots := by
  have hv : Function.Injective rawViewSlots := by
    intro i j he
    apply viewSlots_injective
    have hval := congrArg Fin.val he
    exact Fin.ext hval
  have hs : Function.Injective rawSATSlots := by
    intro i j he
    apply RecoveryColdSAT.satSlots_injective
    have hval := congrArg Fin.val he
    exact Fin.ext hval
  have hm : Function.Injective markerSlots := by
    intro i j he
    apply RecoveryColdMarker.markerSlots_injective
    have hval := congrArg Fin.val he
    exact Fin.ext hval
  have hraw : Function.Injective rawSlots := join_injective rawViewSlots rawSATSlots hv hs (by
    intro i j he
    have hval := congrArg Fin.val he
    change (viewSlots i).val=100+j.val at hval
    have hlt := (viewSlots i).isLt
    omega)
  have hcompact : Function.Injective compactSlots := join_injective markerSlots RecoveryColdCompact.bankSlots
    hm RecoveryColdCompact.bankSlots_injective (by
      intro i j he
      have hval := congrArg Fin.val he
      change 279+i.val=338+j.val at hval
      omega)
  exact join_injective rawSlots compactSlots hraw hcompact (by
    intro i j he
    have ha := rawSlots_lt i
    have hb := compactSlots_ge j
    have hval := congrArg Fin.val he
    omega)

theorem native_layout {s : Nat} (bits word ib ob : List Bool) (count n m : Nat)
    (H : Fin 493→Nat) (A : Fin 493→List Bool) (q : Fin s)
    (hv : ZeroPadding.config (RecoveryColdView.nativeCaps bits)
      ⟨q,(fun j=>H (rawViewSlots j)),(fun j=>A (rawViewSlots j))⟩=
      RecoveryRawViewEnd.cfg (view bits word (2*(count*(width bits+2)+1))) 0 q)
    (hs : ZeroPadding.config (RecoveryColdSAT.caps bits word)
      ⟨q,(fun j=>H (rawSATSlots j)),(fun j=>A (rawSATSlots j))⟩=
      (RecoveryColdSAT.state bits word).cfg q)
    (hm : ZeroPadding.config (RecoveryColdMarker.caps bits)
      ⟨q,(fun j=>H (markerSlots j)),(fun j=>A (markerSlots j))⟩=
      (RecoveryColdMarker.state bits).cfg q)
    (hc : ZeroPadding.config (RecoveryColdCompact.caps bits word)
      ⟨q,(fun j=>H (RecoveryColdCompact.bankSlots j)),(fun j=>A (RecoveryColdCompact.bankSlots j))⟩=
      (RecoveryColdCompact.state bits word ib ob n m).cfg q) :
    ZeroPadding.config (caps bits word) ⟨q,(fun j=>H (slots j)),(fun j=>A (slots j))⟩=
      RecoveryAllCode.cfg (state bits word ib ob count n m) q := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=136) (n:=212) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=66) (n:=70) ?_ ?_ j
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.heads hv) k
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.heads hs) k
    · intro j
      refine Fin.addCases (m:=57) (n:=155) ?_ ?_ j
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.heads hm) k
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.heads hc) k
  · funext i
    refine Fin.addCases (m:=136) (n:=212) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=66) (n:=70) ?_ ?_ j
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.tapes hv) k
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.tapes hs) k
    · intro j
      refine Fin.addCases (m:=57) (n:=155) ?_ ?_ j
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.tapes hm) k
      · intro k
        simpa only [ZeroPadding.config,slots,rawSlots,compactSlots,caps,
          RecoveryAllCode.cfg,RecoveryBankPair.cfg,RecoveryRawBranch.cfg,
          RecoveryMarkerHandoff.heads,RecoveryMarkerHandoff.tapes,state,
          RecoveryRawViewEnd.cfg,TapeEmbedding.config,RecoveryRawView.State.cfg,
          RecoveryRawView.State.innerCfg,RecoveryRawLiteralBound.State.cfg,
          RecoveryRawLiteralStream.State.cfg,RecoveryRawSAT.State.cfg,
          RecoveryMarkerClause.State.cfg,RecoveryNestedTable.State.cfg,
          RecoveryNestedTable.State.innerCfg,RecoveryRowTable.tableCfg,
          Fin.addCases_left,Fin.addCases_right] using
          congrFun (congrArg Configuration.tapes hc) k

end NearCubicWires.RepairOrdinary.RecoveryColdAllCode
