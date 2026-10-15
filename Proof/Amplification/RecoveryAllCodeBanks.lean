import Proof.Amplification.RecoveryColdAllCodeState

/-! The actual493-tape cold endpoint retains the earlier raw banks and
supplies both new banks at their literal native positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RecoveryColdCompact
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawViewSlots (j : Fin 66) : Fin 493 := (viewSlots j).castAdd 393
def rawSATSlots (j : Fin 70) : Fin 493 := (RecoveryColdSAT.satSlots j).castAdd 321
def markerSlots (j : Fin 57) : Fin 493 := (RecoveryColdMarker.markerSlots j).castAdd 155

theorem retained_head (h : Fin 338→Nat) (i : Fin 336) (ha : i.val≠270) (hb : i.val≠274) :
    finishHeads (RecoveryColdCompact.bankHeads h) (i.castAdd 157)=h (i.castAdd 2) := by
  have hf : ¬finishing (i.castAdd 157) := by
    unfold finishing
    simp only [Fin.ext_iff]
    change ¬(i.val=387 ∨ i.val=406 ∨ i.val=456 ∨ i.val=491)
    omega
  have hn : ¬(i.castAdd 157=(270 : Fin 493) ∨ i.castAdd 157=(274 : Fin 493)) := by
    simp only [Fin.ext_iff,Fin.val_castAdd]
    exact not_or.mpr ⟨ha,hb⟩
  simp only [finishHeads,if_neg hf,RecoveryColdCompact.bankHeads,if_neg hn,liftedHeads]
  have hi : i.castAdd 157=(i.castAdd 2).castAdd 155 := Fin.ext rfl
  rw [hi,Fin.addCases_left]

theorem ready_sat (bits word : List Bool) (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : RecoveryColdCompact.Ready bits word H A) :
    RecoveryColdSAT.Ready bits word (fun j=>H (j.castAdd 321)) (fun j=>A (j.castAdd 321)) := by
  obtain ⟨h,a,n,ib,m,ob,hmarker,_,_,_,hh,ht⟩ := hr
  obtain ⟨g,b,hfront,hg,hb⟩ := hmarker
  obtain ⟨k,u,v,hs,hp,hsat,hcode⟩ := hfront
  have heh : (fun j : Fin 172=>H (j.castAdd 321))=(fun j=>g (j.castAdd 107)) := by
    funext j
    rw [hh]
    have he : j.castAdd 321=(j.castAdd 164).castAdd 157 := Fin.ext rfl
    rw [he,retained_head h (j.castAdd 164) (by simp; omega) (by simp; omega),hg]
    change RecoveryColdMarker.heads g ((j.castAdd 107).castAdd 59)=g (j.castAdd 107)
    simp only [RecoveryColdMarker.heads,Fin.addCases_left]
  have het : (fun j : Fin 172=>A (j.castAdd 321))=(fun j=>b (j.castAdd 107)) := by
    funext j
    rw [ht]
    have he : j.castAdd 321=(j.castAdd 164).castAdd 157 := Fin.ext rfl
    rw [he,retained,hb]
    change RecoveryColdMarker.stage6 bits b ((j.castAdd 107).castAdd 59)=b (j.castAdd 107)
    exact RecoveryColdMarker.retained bits b _
  rw [heh,het]
  exact hsat

theorem ready_marker {s : Nat} (bits word : List Bool) (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : RecoveryColdCompact.Ready bits word H A) (q : Fin s) :
    ZeroPadding.config (RecoveryColdMarker.caps bits)
      ⟨q,(fun j=>H (markerSlots j)),(fun j=>A (markerSlots j))⟩=
      (RecoveryColdMarker.state bits).cfg q := by
  obtain ⟨h,a,n,ib,m,ob,hmarker,_,_,_,hh,ht⟩ := hr
  obtain ⟨g,b,_,hg,hb⟩ := hmarker
  have heh : (fun j=>H (markerSlots j))=(fun j=>RecoveryColdMarker.heads g (RecoveryColdMarker.markerSlots j)) := by
    funext j
    rw [hh]
    let i : Fin 336 := ⟨279+j.val,by omega⟩
    change finishHeads (RecoveryColdCompact.bankHeads h) (i.castAdd 157)=_
    rw [retained_head h i (by dsimp [i]; omega) (by dsimp [i]; omega),hg]
    rfl
  have het : (fun j=>A (markerSlots j))=(fun j=>RecoveryColdMarker.stage6 bits b (RecoveryColdMarker.markerSlots j)) := by
    funext j
    rw [ht]
    let i : Fin 336 := ⟨279+j.val,by omega⟩
    change finishTapes (stage34 bits word ib ob n m (bankInput a)) (i.castAdd 157)=_
    rw [retained,hb]
    rfl
  rw [heh,het]
  exact RecoveryColdMarker.bank_native bits g b q

theorem ready_compact {s : Nat} (bits word : List Bool) (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : RecoveryColdCompact.Ready bits word H A) (q : Fin s) :
    ∃ n ib m ob,n≤limit bits ∧ m≤limit bits ∧
      ZeroPadding.config (RecoveryColdCompact.caps bits word)
        ⟨q,(fun j=>H (bankSlots j)),(fun j=>A (bankSlots j))⟩=
        (RecoveryColdCompact.state bits word (buffer ib word) (buffer ob word) n m).cfg q := by
  obtain ⟨h,a,n,ib,m,ob,_,hn,hm,_,hh,ht⟩ := hr
  refine ⟨n,ib,m,ob,hn,hm,?_⟩
  rw [hh,ht]
  apply bank_native bits word ib ob n m (RecoveryColdCompact.bankHeads h) (bankInput a) q
  · intro i hi
    have hn : ¬(i=(270 : Fin 493) ∨ i=(274 : Fin 493)) := by
      simp only [Fin.ext_iff]
      omega
    simp only [RecoveryColdCompact.bankHeads,if_neg hn,liftedHeads]
    simp [Fin.addCases,Nat.not_lt.mpr hi]
  · intro i hi
    simp [bankInput,Fin.addCases,Nat.not_lt.mpr hi]

end NearCubicWires.RepairOrdinary.RecoveryColdAllCode
