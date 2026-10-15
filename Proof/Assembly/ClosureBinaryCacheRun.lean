import Proof.Assembly.ClosureBinaryCacheJoin

/-! Complete cold native hardwired-cache producer, including construction of
all repeat drivers/templates, all repeated working/master banks, enumeration,
and a paid final rewind. The only input words are the original native cache,
unary domain/live sizes, and membership bits. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdRun
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource SupplierPipeline SupplierEstimator RepairSource.CloseoutFinal RepairSource.VerifierDecoding SignedSortKey
open BinaryCacheColdJoin
variable {q : Nat}

theorem private_avoids {n : Nat} (slots : Fin n→Fin 372)
    (hslots : ∀ j,224≤(slots j).val ∨ slots j=34 ∨ slots j=98 ∨ slots j=104 ∨ slots j=223)
    (i : Fin 224) (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) (h223 : i≠223) :
    ∀ j,slots j≠i.castAdd 148 := by
  intro j he
  have h := hslots j
  rw [he] at h
  rcases h with h|h|h|h|h <;>
    norm_num [Fin.ext_iff,Fin.val_castAdd] at * <;>omega

theorem data_private (r : Args q) (i : Fin 224)
    (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) (h223 : i≠223) :
    data9 r (i.castAdd 148)=[] := by
  rw [data9_other r (i.castAdd 148) (private_avoids slots9 (by decide) i h34 h98 h104 h223)]
  rw [data8_other r (i.castAdd 148) (private_avoids slots8 (by decide) i h34 h98 h104 h223)]
  rw [data7_other r (i.castAdd 148) (private_avoids slots7 (by decide) i h34 h98 h104 h223)]
  rw [data6_other r (i.castAdd 148) (private_avoids slots6 (by decide) i h34 h98 h104 h223)]
  rw [data5_other r (i.castAdd 148) (private_avoids slots5 (by decide) i h34 h98 h104 h223)]
  rw [data4_other r (i.castAdd 148) (private_avoids slots4 (by decide) i h34 h98 h104 h223)]
  rw [data3_other r (i.castAdd 148) (private_avoids slots3 (by decide) i h34 h98 h104 h223)]
  rw [data2_other r (i.castAdd 148) (private_avoids slots2 (by decide) i h34 h98 h104 h223)]
  rw [data1_other r (i.castAdd 148) (private_avoids slots1 (by decide) i h34 h98 h104 h223)]
  simp only [data0]
  split_ifs <;>first | rfl | (exfalso;norm_num [Fin.ext_iff,Fin.val_castAdd] at *;omega)

theorem heads_private (r : Args q) (i : Fin 224)
    (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) (h223 : i≠223) :
    heads9 r (i.castAdd 148)=0 := by
  rw [heads9_other r (i.castAdd 148) (private_avoids slots9 (by decide) i h34 h98 h104 h223)]
  rw [heads8_other r (i.castAdd 148) (private_avoids slots8 (by decide) i h34 h98 h104 h223)]
  rw [heads7_other r (i.castAdd 148) (private_avoids slots7 (by decide) i h34 h98 h104 h223)]
  rw [heads6_other r (i.castAdd 148) (private_avoids slots6 (by decide) i h34 h98 h104 h223)]
  rw [heads5_other r (i.castAdd 148) (private_avoids slots5 (by decide) i h34 h98 h104 h223)]
  rw [heads4_other r (i.castAdd 148) (private_avoids slots4 (by decide) i h34 h98 h104 h223)]
  rw [heads3_other r (i.castAdd 148) (private_avoids slots3 (by decide) i h34 h98 h104 h223)]
  rw [heads2_other r (i.castAdd 148) (private_avoids slots2 (by decide) i h34 h98 h104 h223)]
  rw [heads1_other r (i.castAdd 148) (private_avoids slots1 (by decide) i h34 h98 h104 h223)]
  simp only [heads0]

theorem data_main (r : Args q) (i : Fin 224) : data9 r (i.castAdd 148)=BinaryCacheColdInitialize.oldInput r.live r.gs r.prefix i := by
  by_cases h34 : i=34
  · subst i
    change data9 r 34=BinaryCacheColdInitialize.oldInput r.live r.gs r.prefix 34
    rw [show data9 r 34=localOutput9 r 17 from data9_slot r 17]
    rw [projection9_17]
    rfl
  by_cases h98 : i=98
  · subst i
    change data9 r 98=BinaryCacheColdInitialize.oldInput r.live r.gs r.prefix 98
    rw [data9_other r 98 (by decide)]
    rw [data8_other r 98 (by decide)]
    rw [data7_other r 98 (by decide)]
    rw [data6_other r 98 (by decide)]
    rw [data5_other r 98 (by decide)]
    rw [data4_other r 98 (by decide)]
    rw [data3_other r 98 (by decide)]
    rw [show data2 r 98=localOutput2 r 0 from data2_slot r 0]
    rw [projection2_0]
    rfl
  by_cases h104 : i=104
  · subst i
    change data9 r 104=BinaryCacheColdInitialize.oldInput r.live r.gs r.prefix 104
    rw [data9_other r 104 (by decide)]
    rw [data8_other r 104 (by decide)]
    rw [data7_other r 104 (by decide)]
    rw [data6_other r 104 (by decide)]
    rw [data5_other r 104 (by decide)]
    rw [show data4 r 104=localOutput4 r 8 from data4_slot r 8]
    rw [projection4_8]
    rfl
  by_cases h223 : i=223
  · subst i
    change data9 r 223=BinaryCacheColdInitialize.oldInput r.live r.gs r.prefix 223
    rw [data9_other r 223 (by decide)]
    rw [show data8 r 223=localOutput8 r 0 from data8_slot r 0]
    rw [projection8_0]
    rfl
  rw [data_private r i h34 h98 h104 h223]
  simp only [BinaryCacheColdInitialize.oldInput,h34,h98,h104,h223,↓reduceIte]

theorem heads_main (r : Args q) (i : Fin 224) : heads9 r (i.castAdd 148)=BinaryCacheColdFanout.heads r.prefix i := by
  by_cases h34 : i=34
  · subst i
    change heads9 r 34=BinaryCacheColdFanout.heads r.prefix 34
    rw [show heads9 r 34=localHeadsOut9 r 17 from heads9_slot r 17]
    rfl
  by_cases h98 : i=98
  · subst i
    change heads9 r 98=BinaryCacheColdFanout.heads r.prefix 98
    rw [heads9_other r 98 (by decide)]
    rw [heads8_other r 98 (by decide)]
    rw [heads7_other r 98 (by decide)]
    rw [heads6_other r 98 (by decide)]
    rw [heads5_other r 98 (by decide)]
    rw [heads4_other r 98 (by decide)]
    rw [heads3_other r 98 (by decide)]
    rw [show heads2 r 98=localHeadsOut2 r 0 from heads2_slot r 0]
    rfl
  by_cases h104 : i=104
  · subst i
    change heads9 r 104=BinaryCacheColdFanout.heads r.prefix 104
    rw [heads9_other r 104 (by decide)]
    rw [heads8_other r 104 (by decide)]
    rw [heads7_other r 104 (by decide)]
    rw [heads6_other r 104 (by decide)]
    rw [heads5_other r 104 (by decide)]
    rw [show heads4 r 104=localHeadsOut4 r 8 from heads4_slot r 8]
    rfl
  by_cases h223 : i=223
  · subst i
    change heads9 r 223=BinaryCacheColdFanout.heads r.prefix 223
    rw [heads9_other r 223 (by decide)]
    rw [show heads8 r 223=localHeadsOut8 r 0 from heads8_slot r 0]
    rfl
  rw [heads_private r i h34 h98 h104 h223]
  simp only [BinaryCacheColdFanout.heads,h34,h223,↓reduceIte]

def slots : Fin 235→Fin 372 := fun i=>Fin.addCases
  (fun j : Fin 224=>j.castAdd 148) (![250,327,284,258,226,276,252,260,322,324,371] : Fin 11→Fin 372) i
theorem slots_inj : Function.Injective slots := by decide
noncomputable def phase := RecoveryFocus.machine slots BinaryCacheColdInitialize.machine
noncomputable def raw := Composition.machine joined9 phase
def rawBudget (r : Args q) := budget9 r+1+localBudget10 r
noncomputable def finalData (r : Args q) := install slots (data9 r) (localOutput10 r)
noncomputable def finalHeads (r : Args q) := dockH slots (heads9 r) (localHeadsOut10 r)

theorem heads_input (r : Args q) : ∀ j,heads9 r (slots j)=localHeadsIn10 r j := by
  intro j
  refine Fin.addCases (m:=224) (n:=11) (fun i=>?_) (fun i=>?_) j
  · simpa only [slots,localHeadsIn10,BinaryCacheColdInitialize.heads,Fin.addCases_left] using heads_main r i
  · fin_cases i
    · change heads9 r 250=localHeadsIn10 r 224
      rw [heads9_other r 250 (by decide)]
      rw [heads8_other r 250 (by decide)]
      rw [heads7_other r 250 (by decide)]
      rw [heads6_other r 250 (by decide)]
      rw [heads5_other r 250 (by decide)]
      rw [heads4_other r 250 (by decide)]
      rw [show heads3 r 250=localHeadsOut3 r 8 from heads3_slot r 8]
      rfl
    · change heads9 r 327=localHeadsIn10 r 225
      rw [heads9_other r 327 (by decide)]
      rw [heads8_other r 327 (by decide)]
      rw [heads7_other r 327 (by decide)]
      rw [heads6_other r 327 (by decide)]
      rw [heads5_other r 327 (by decide)]
      rw [heads4_other r 327 (by decide)]
      rw [show heads3 r 327=localHeadsOut3 r 85 from heads3_slot r 85]
      rfl
    · change heads9 r 284=localHeadsIn10 r 226
      rw [heads9_other r 284 (by decide)]
      rw [heads8_other r 284 (by decide)]
      rw [heads7_other r 284 (by decide)]
      rw [heads6_other r 284 (by decide)]
      rw [heads5_other r 284 (by decide)]
      rw [heads4_other r 284 (by decide)]
      rw [show heads3 r 284=localHeadsOut3 r 42 from heads3_slot r 42]
      rfl
    · change heads9 r 258=localHeadsIn10 r 227
      rw [heads9_other r 258 (by decide)]
      rw [heads8_other r 258 (by decide)]
      rw [heads7_other r 258 (by decide)]
      rw [heads6_other r 258 (by decide)]
      rw [heads5_other r 258 (by decide)]
      rw [heads4_other r 258 (by decide)]
      rw [show heads3 r 258=localHeadsOut3 r 16 from heads3_slot r 16]
      rfl
    · change heads9 r 226=localHeadsIn10 r 228
      rw [heads9_other r 226 (by decide)]
      rw [heads8_other r 226 (by decide)]
      rw [heads7_other r 226 (by decide)]
      rw [heads6_other r 226 (by decide)]
      rw [heads5_other r 226 (by decide)]
      rw [heads4_other r 226 (by decide)]
      rw [show heads3 r 226=localHeadsOut3 r 5 from heads3_slot r 5]
      rfl
    · change heads9 r 276=localHeadsIn10 r 229
      rw [heads9_other r 276 (by decide)]
      rw [heads8_other r 276 (by decide)]
      rw [heads7_other r 276 (by decide)]
      rw [heads6_other r 276 (by decide)]
      rw [heads5_other r 276 (by decide)]
      rw [heads4_other r 276 (by decide)]
      rw [show heads3 r 276=localHeadsOut3 r 34 from heads3_slot r 34]
      rfl
    · change heads9 r 252=localHeadsIn10 r 230
      rw [heads9_other r 252 (by decide)]
      rw [heads8_other r 252 (by decide)]
      rw [heads7_other r 252 (by decide)]
      rw [heads6_other r 252 (by decide)]
      rw [heads5_other r 252 (by decide)]
      rw [heads4_other r 252 (by decide)]
      rw [show heads3 r 252=localHeadsOut3 r 10 from heads3_slot r 10]
      rfl
    · change heads9 r 260=localHeadsIn10 r 231
      rw [heads9_other r 260 (by decide)]
      rw [heads8_other r 260 (by decide)]
      rw [heads7_other r 260 (by decide)]
      rw [heads6_other r 260 (by decide)]
      rw [heads5_other r 260 (by decide)]
      rw [heads4_other r 260 (by decide)]
      rw [show heads3 r 260=localHeadsOut3 r 18 from heads3_slot r 18]
      rfl
    · change heads9 r 322=localHeadsIn10 r 232
      rw [heads9_other r 322 (by decide)]
      rw [heads8_other r 322 (by decide)]
      rw [heads7_other r 322 (by decide)]
      rw [heads6_other r 322 (by decide)]
      rw [heads5_other r 322 (by decide)]
      rw [heads4_other r 322 (by decide)]
      rw [show heads3 r 322=localHeadsOut3 r 80 from heads3_slot r 80]
      rfl
    · change heads9 r 324=localHeadsIn10 r 233
      rw [heads9_other r 324 (by decide)]
      rw [heads8_other r 324 (by decide)]
      rw [heads7_other r 324 (by decide)]
      rw [heads6_other r 324 (by decide)]
      rw [heads5_other r 324 (by decide)]
      rw [heads4_other r 324 (by decide)]
      rw [show heads3 r 324=localHeadsOut3 r 82 from heads3_slot r 82]
      rfl
    · change heads9 r 371=localHeadsIn10 r 234
      rw [heads9_other r 371 (by decide)]
      rw [heads8_other r 371 (by decide)]
      rw [heads7_other r 371 (by decide)]
      rw [heads6_other r 371 (by decide)]
      rw [heads5_other r 371 (by decide)]
      rw [heads4_other r 371 (by decide)]
      rw [heads3_other r 371 (by decide)]
      rw [heads2_other r 371 (by decide)]
      rw [heads1_other r 371 (by decide)]
      rfl

theorem data_input (r : Args q) : ∀ j,data9 r (slots j)=localInput10 r j := by
  intro j
  refine Fin.addCases (m:=224) (n:=11) (fun i=>?_) (fun i=>?_) j
  · simpa only [slots,localInput10,BinaryCacheColdInitialize.input,Fin.addCases_left] using data_main r i
  · fin_cases i
    · change data9 r 250=localInput10 r 224
      rw [data9_other r 250 (by decide)]
      rw [data8_other r 250 (by decide)]
      rw [data7_other r 250 (by decide)]
      rw [data6_other r 250 (by decide)]
      rw [data5_other r 250 (by decide)]
      rw [data4_other r 250 (by decide)]
      rw [show data3 r 250=localOutput3 r 8 from data3_slot r 8]
      rw [projection3_8]
      rfl
    · change data9 r 327=localInput10 r 225
      rw [data9_other r 327 (by decide)]
      rw [data8_other r 327 (by decide)]
      rw [data7_other r 327 (by decide)]
      rw [data6_other r 327 (by decide)]
      rw [data5_other r 327 (by decide)]
      rw [data4_other r 327 (by decide)]
      rw [show data3 r 327=localOutput3 r 85 from data3_slot r 85]
      rw [projection3_85]
      rfl
    · change data9 r 284=localInput10 r 226
      rw [data9_other r 284 (by decide)]
      rw [data8_other r 284 (by decide)]
      rw [data7_other r 284 (by decide)]
      rw [data6_other r 284 (by decide)]
      rw [data5_other r 284 (by decide)]
      rw [data4_other r 284 (by decide)]
      rw [show data3 r 284=localOutput3 r 42 from data3_slot r 42]
      rw [projection3_42]
      rfl
    · change data9 r 258=localInput10 r 227
      rw [data9_other r 258 (by decide)]
      rw [data8_other r 258 (by decide)]
      rw [data7_other r 258 (by decide)]
      rw [data6_other r 258 (by decide)]
      rw [data5_other r 258 (by decide)]
      rw [data4_other r 258 (by decide)]
      rw [show data3 r 258=localOutput3 r 16 from data3_slot r 16]
      rw [projection3_16]
      rfl
    · change data9 r 226=localInput10 r 228
      rw [data9_other r 226 (by decide)]
      rw [data8_other r 226 (by decide)]
      rw [data7_other r 226 (by decide)]
      rw [data6_other r 226 (by decide)]
      rw [data5_other r 226 (by decide)]
      rw [data4_other r 226 (by decide)]
      rw [show data3 r 226=localOutput3 r 5 from data3_slot r 5]
      rw [projection3_5]
      rfl
    · change data9 r 276=localInput10 r 229
      rw [data9_other r 276 (by decide)]
      rw [data8_other r 276 (by decide)]
      rw [data7_other r 276 (by decide)]
      rw [data6_other r 276 (by decide)]
      rw [data5_other r 276 (by decide)]
      rw [data4_other r 276 (by decide)]
      rw [show data3 r 276=localOutput3 r 34 from data3_slot r 34]
      rw [projection3_34]
      rfl
    · change data9 r 252=localInput10 r 230
      rw [data9_other r 252 (by decide)]
      rw [data8_other r 252 (by decide)]
      rw [data7_other r 252 (by decide)]
      rw [data6_other r 252 (by decide)]
      rw [data5_other r 252 (by decide)]
      rw [data4_other r 252 (by decide)]
      rw [show data3 r 252=localOutput3 r 10 from data3_slot r 10]
      rw [projection3_10]
      rfl
    · change data9 r 260=localInput10 r 231
      rw [data9_other r 260 (by decide)]
      rw [data8_other r 260 (by decide)]
      rw [data7_other r 260 (by decide)]
      rw [data6_other r 260 (by decide)]
      rw [data5_other r 260 (by decide)]
      rw [data4_other r 260 (by decide)]
      rw [show data3 r 260=localOutput3 r 18 from data3_slot r 18]
      rw [projection3_18]
      rfl
    · change data9 r 322=localInput10 r 232
      rw [data9_other r 322 (by decide)]
      rw [data8_other r 322 (by decide)]
      rw [data7_other r 322 (by decide)]
      rw [data6_other r 322 (by decide)]
      rw [data5_other r 322 (by decide)]
      rw [data4_other r 322 (by decide)]
      rw [show data3 r 322=localOutput3 r 80 from data3_slot r 80]
      rw [projection3_80]
      rfl
    · change data9 r 324=localInput10 r 233
      rw [data9_other r 324 (by decide)]
      rw [data8_other r 324 (by decide)]
      rw [data7_other r 324 (by decide)]
      rw [data6_other r 324 (by decide)]
      rw [data5_other r 324 (by decide)]
      rw [data4_other r 324 (by decide)]
      rw [show data3 r 324=localOutput3 r 82 from data3_slot r 82]
      rw [projection3_82]
      rfl
    · change data9 r 371=localInput10 r 234
      rw [data9_other r 371 (by decide)]
      rw [data8_other r 371 (by decide)]
      rw [data7_other r 371 (by decide)]
      rw [data6_other r 371 (by decide)]
      rw [data5_other r 371 (by decide)]
      rw [data4_other r 371 (by decide)]
      rw [data3_other r 371 (by decide)]
      rw [data2_other r 371 (by decide)]
      rw [data1_other r 371 (by decide)]
      rfl

theorem raw_run (r : Args q) :
    Step raw (rawBudget r) (heads0 r) (data0 r) (finalHeads r) (finalData r) :=
  (joined9_run r).seq ((localStep10 r).dock slots slots_inj (heads9 r) (data9 r)
    (heads_input r) (data_input r))

noncomputable def rawReceipt (r : Args q) := Classical.choose (raw_run r)
noncomputable def machine := Rewind.machine raw
def input (r : Args q) : Fin 373→List Bool := fun i=>Fin.addCases (data0 r) (fun _ : Fin 1=>[]) i
noncomputable def output (r : Args q) : Fin 373→List Bool := fun i=>
  Fin.addCases (finalData r) (fun _ : Fin 1=>List.replicate (rawReceipt r).steps false) i
def budget (r : Args q) := 2*rawBudget r+2

theorem run (r : Args q) : Step machine (budget r) (fun _=>0) (input r) (fun _=>0) (output r) := by
  have h := Classical.choose_spec (raw_run r)
  obtain ⟨actual,hr,ht,hlog,hh,_,_⟩ :=
    Rewind.Workspace.reset_workspace raw (rawBudget r) (data0 r) (rawReceipt r) h.1 0
  have hb : 2*(rawReceipt r).steps+2≤budget r := by
    have bound := h.2.2.2
    change (rawReceipt r).steps≤rawBudget r at bound
    unfold budget;omega
  apply ((Step.of_run hr (funext hh) rfl).enlarge hb).congr rfl
  funext i
  refine Fin.addCases (m:=372) (n:=1) (fun i=>?_) (fun i=>?_) i
  · simpa only [output,Fin.addCases_left] using (ht i).trans (congrFun h.2.2.1 i)
  · fin_cases i
    change actual.final.tapes 372=List.replicate (rawReceipt r).steps false
    change actual.final.tapes 372=List.replicate (max 0 (rawReceipt r).steps) false at hlog
    simpa only [Nat.zero_max] using hlog

theorem output_cache (r : Args q) :
    output r 34=r.prefix++HardwireAssignments.emitted r.live r.gs := by
  exact (install_slot slots slots_inj (data9 r) (localOutput10 r) 34).trans (projection10_34 r)
theorem output_original (r : Args q) : output r 98=exactListWord r.gs := by
  exact (install_slot slots slots_inj (data9 r) (localOutput10 r) 98).trans (projection10_98 r)

theorem c10_output (a : RepairRepresentation.DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) :
    output (Args.mk live (C10SupplierRowInput.childList a live occ)) 34=
      exactListWord (BinaryPool.pool a live occ s harity) := by
  rw [output_cache,BinarySerialization.exactListWord_eq_native]
  have hcard : q-live.card=liveᶜ.card := by
    have h := Finset.card_add_card_compl live
    simp only [Fintype.card_fin] at h
    omega
  simp only [Args.prefix,Args.poolCount,Args.K,Args.N,BinaryCachePrefix.prefixWord,HardwireAssignments.emitted]
  have hword := congrArg (fun n=>exactWord (C10SupplierRowInput.falseGate n)) (hcard.trans harity.symm)
  rw [hword]

/-- Full parent application: fixed program, four original source words, exact
complete final store at zero heads, and the exact native BinaryPool cache. -/
theorem c10_run (a : RepairRepresentation.DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) :
    let r : Args q := ⟨live,C10SupplierRowInput.childList a live occ⟩
    Step machine (budget r) (fun _=>0) (input r) (fun _=>0) (output r) ∧
      output r 34=exactListWord (BinaryPool.pool a live occ s harity) ∧
      output r 98=exactListWord r.gs :=
  ⟨run _,c10_output a live occ s harity,output_original _⟩

end NearCubicWires.P1Closure.BinaryCacheColdRun
