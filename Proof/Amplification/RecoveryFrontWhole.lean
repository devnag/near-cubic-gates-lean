import Proof.Amplification.RecoveryFrontGraph

/-! The entire cold certificate front executes from the two original
inputs and blank workspace. Every success supplies its actual prepared
raw banks/table buffers; each earlier rejected gate retains false277. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem front_run (bits word : List Bool) :
    ∃ bit r,run machine (budget bits word) (input bits word)=some r ∧
      r.steps ≤ budget bits word ∧ r.final.heads 277=0 ∧ r.final.tapes 277=[bit] ∧
      (bit=true → Prepared bits word r.final.heads r.final.tapes) := by
  obtain ⟨base,hbase,hbh,hbt,hready,first,hfirst,_,hfh,hft⟩ := prefix_run bits word
  have hflag : first.final.scanned 30=(readList (limit bits) (readEntry (width bits)) word).isSome := by
    change readTapeBit (first.final.tapes 30) (first.final.heads 30)=_
    rw [hfh,hft]
    change readTapeBit (base.final.tapes 30) (base.final.heads 30)=_
    rw [hbh,hbt]
    rfl
  cases hp : readList (limit bits) (readEntry (width bits)) word with
  | none=>
    obtain ⟨used,hused,h⟩ := stop_receipt sizes programs 0 next 0 _ _ first hfirst
      (by
        change (if first.final.scanned 30 then some (1 : Fin 3) else none)=none
        rw [hflag,hp]; rfl)
    obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hb : used ≤ budget bits word := by unfold budget; omega
    have hm := runFrom_moreFuel machine used (budget bits word-used) _ r hr
    rw [Nat.add_sub_of_le hb] at hm
    refine ⟨false,r,hm,by omega,?_,?_,?_⟩
    · rw [hfinal]
      change first.final.heads 277=0
      rw [hfh]; rfl
    · rw [hfinal]
      change first.final.tapes 277=[false]
      rw [hft]; rfl
    · intro hf; contradiction
  | some pair=>
    rcases pair with ⟨table,tail⟩
    have hsat := hready (by simp only [hp,Option.isSome_some])
    have hcode := RecoveryColdSAT.cold_original bits word base hbase table tail hp
    obtain ⟨a,ha,hA⟩ := call_receipt sizes programs 0 next 0 1 _ _ first hfirst
      (by
        change (if first.final.scanned 30 then some (1 : Fin 3) else none)=some 1
        rw [hflag,hp]; rfl)
    rw [hfh,hft] at hA
    obtain ⟨bit,g,b,second,hsecond,_,hsh,hst,hgh,hgt,hkeepH,hkeepT,hgood⟩ :=
      scan_run bits word base.final.heads base.final.tapes hsat hcode table tail hp
    have hsecondFlag : second.final.scanned 230=bit := by
      change readTapeBit (second.final.tapes 230) (second.final.heads 230)=_
      rw [hsh,hst]
      change readTapeBit (b 230) (g 230)=_
      rw [hgh,hgt]
      rfl
    cases hbit : bit with
    | false=>
      obtain ⟨bUsed,hb,hB⟩ := stop_receipt sizes programs 0 next 1 _ _ second hsecond
        (by
          change (if second.final.scanned 230 then some (2 : Fin 3) else none)=none
          rw [hsecondFlag,hbit]; rfl)
      have h := hA.trans hB
      obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
      have hbound : a+bUsed ≤ budget bits word := by unfold budget; omega
      have hm := runFrom_moreFuel machine (a+bUsed) (budget bits word-(a+bUsed)) _ r hr
      rw [Nat.add_sub_of_le hbound] at hm
      refine ⟨false,r,hm,by omega,?_,?_,?_⟩
      · rw [hfinal]
        change second.final.heads 277=0
        rw [hsh]; rfl
      · rw [hfinal]
        change second.final.tapes 277=[false]
        rw [hst]; rfl
      · intro hf; contradiction
    | true=>
      obtain ⟨k,hsources⟩ := hgood hbit
      obtain ⟨bUsed,hb,hB⟩ := call_receipt sizes programs 0 next 1 2 _ _ second hsecond
        (by
          change (if second.final.scanned 230 then some (2 : Fin 3) else none)=some 2
          rw [hsecondFlag,hbit]; rfl)
      rw [hsh,hst] at hB
      obtain ⟨last,hlast,_,hlh,hlt,hlready⟩ := RecoveryColdTablesAmbient.ambient_run
        word k (width bits) (limit bits) g b hsources
      obtain ⟨c,hc,hC⟩ := stop_receipt sizes programs 0 next 2 _ _ last hlast (by rfl)
      have h := hA.trans (hB.trans hC)
      obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
      have hbound : a+(bUsed+c) ≤ budget bits word := by unfold budget; omega
      have hm := runFrom_moreFuel machine (a+(bUsed+c)) (budget bits word-(a+(bUsed+c))) _ r hr
      rw [Nat.add_sub_of_le hbound] at hm
      refine ⟨RecoveryColdTables.answer (width bits) (limit bits) word k,r,hm,by omega,?_,?_,?_⟩
      · rw [hfinal]; exact hlh
      · rw [hfinal]; exact hlt
      · intro htrue
        rw [hfinal]
        exact prepared_of_produced bits word base.final.heads base.final.tapes hsat hcode
          g b hkeepH hkeepT k hsources last.final.heads last.final.tapes (hlready htrue)

end NearCubicWires.RepairOrdinary.RecoveryColdFront
