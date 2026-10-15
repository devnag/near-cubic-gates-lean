import Proof.Amplification.RecoveryCanonicalFrontScan

/-! Canonical positive execution of the entire279-tape cold front. It
retains both the full prepared entry and the exact table-start production
relation needed to identify the materialized row buffers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
open RecoveryColdFront
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem front_run (code : Nat) (c : Certificate) (hc : Fits code c) :
    ∃ r,run RecoveryColdFront.machine
      (RecoveryColdFront.budget code.bits (TableFirst.pack (Serialization.width code) c))
      (RecoveryColdFront.input code.bits (TableFirst.pack (Serialization.width code) c))=some r ∧
      r.final.heads 277=0 ∧ r.final.tapes 277=[true] ∧
      RecoveryColdFront.Prepared code.bits (TableFirst.pack (Serialization.width code) c) r.final.heads r.final.tapes ∧
      ∃ (g : Fin 270→Nat) (b : Fin 270→List Bool),
        RecoveryColdTablesAmbient.Sources (TableFirst.pack (Serialization.width code) c)
          (tablePosition code c) (RecoveryColdView.width code.bits) (RecoveryColdView.limit code.bits) g b ∧
        RecoveryColdTablesAmbient.Produced (RecoveryColdView.width code.bits) (RecoveryColdView.limit code.bits)
          (TableFirst.pack (Serialization.width code) c) (tablePosition code c) g b r.final.heads r.final.tapes := by
  let word := TableFirst.pack (Serialization.width code) c
  have hp : readList (RecoveryColdView.limit code.bits)
      (readEntry (RecoveryColdView.width code.bits)) word = some (c.table,suffix code c) :=
    valuation_parse code c hc
  obtain ⟨base,hbase,hbh,hbt,hready,first,hfirst,_,hfh,hft⟩ := RecoveryColdFront.prefix_run code.bits word
  have hsat := hready (by rw [hp]; rfl)
  have hcode := RecoveryColdSAT.cold_original code.bits word base hbase c.table (suffix code c) hp
  have hflag : first.final.scanned 30=true := by
    change readTapeBit (first.final.tapes 30) (first.final.heads 30)=true
    rw [hfh,hft]
    change readTapeBit (base.final.tapes 30) (base.final.heads 30)=true
    rw [hbh,hbt,hp]
    rfl
  obtain ⟨usedA,hA,hfirstCall⟩ := call_receipt RecoveryColdFront.sizes RecoveryColdFront.programs 0 RecoveryColdFront.next 0 1 _ _ first hfirst
    (by change (if first.final.scanned 30 then some (1 : Fin 3) else none)=some 1; rw [hflag]; rfl)
  rw [hfh,hft] at hfirstCall
  obtain ⟨g,b,second,hsecond,hsh,hst,hgh,hgt,hkeepH,hkeepT,hsources⟩ :=
    front_scan code c hc base.final.heads base.final.tapes hsat hcode
  have hsecondFlag : second.final.scanned 230=true := by
    change readTapeBit (second.final.tapes 230) (second.final.heads 230)=true
    rw [hsh,hst]
    change readTapeBit (b 230) (g 230)=true
    rw [hgh,hgt]
    rfl
  obtain ⟨usedB,hB,hsecondCall⟩ := call_receipt RecoveryColdFront.sizes RecoveryColdFront.programs 0 RecoveryColdFront.next 1 2 _ _ second hsecond
    (by change (if second.final.scanned 230 then some (2 : Fin 3) else none)=some 2; rw [hsecondFlag]; rfl)
  rw [hsh,hst] at hsecondCall
  obtain ⟨last,hlast,_,hlh,hlt,hlready⟩ := RecoveryColdTablesAmbient.ambient_run word
    (tablePosition code c) (RecoveryColdView.width code.bits) (RecoveryColdView.limit code.bits) g b hsources
  have hprod := hlready (table_answer code c hc)
  obtain ⟨usedC,hC,hlastCall⟩ := stop_receipt RecoveryColdFront.sizes RecoveryColdFront.programs 0 RecoveryColdFront.next 2 _ _ last hlast (by rfl)
  have hwhole := hfirstCall.trans (hsecondCall.trans hlastCall)
  obtain ⟨r,hr,hfinal,_⟩ := hwhole.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  change usedB ≤ RecoveryColdScanner.scanBudget code.bits word+1 at hB
  have hbound : usedA+(usedB+usedC)≤RecoveryColdFront.budget code.bits word := by
    unfold RecoveryColdFront.budget
    omega
  have hm := runFrom_moreFuel RecoveryColdFront.machine (usedA+(usedB+usedC))
    (RecoveryColdFront.budget code.bits word-(usedA+(usedB+usedC))) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,?_,?_,?_,g,b,hsources,?_⟩
  · rw [hfinal]; exact hlh
  · rw [hfinal]
    change last.final.tapes 277=[true]
    exact hlt.trans (congrArg (fun b=>[b]) (table_answer code c hc))
  · rw [hfinal]
    exact RecoveryColdFront.prepared_of_produced code.bits word base.final.heads base.final.tapes hsat hcode
      g b hkeepH hkeepT (tablePosition code c) hsources last.final.heads last.final.tapes hprod
  · rw [hfinal]
    exact hprod

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
