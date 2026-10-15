import Proof.SourceAssembly.SourceRefill
import Proof.SourceAssembly.PoolColdCompatible

/- Actual paired decomposition outputs, aliased into the binary pool consumer.
Only two supplied public words remain on the disjoint bank: the already paid
mask bitmap and the retained live-count template.  No child cache is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyCache
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PoolColdSource
noncomputable section

abbrev tapes (a : DecompositionAlgorithm) := 132+Cold.tapes a
def cachePort (a : DecompositionAlgorithm) : Fin (tapes a) :=
  PoolCold.slots a (Cold.port a (cch a))
def domainPort (a : DecompositionAlgorithm) : Fin (tapes a) :=
  PoolCold.slots a (Cold.port a (dom a))

theorem cache_ne_domain (a : DecompositionAlgorithm) : cachePort a ≠ domainPort a := by
  intro h
  have he := PoolCold.slots_injective a h
  have hv := congrArg Fin.val he
  simp only [Cold.port,Cold.old,live,cch,dom,ex,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def directions (a : DecompositionAlgorithm) (i : Fin (tapes a)) : HeadMove :=
  if i=domainPort a then .left else .stay

def readyMachine (a : DecompositionAlgorithm) := Composition.machine (PoolCold.machine a)
  (DecompositionCountPosition.move (directions a))

def budget {q : Nat} (a : DecompositionAlgorithm) (occ : List (SupportedNormalizedGate q))
    (B w P : Nat) := PoolEntryLoop.budget occ.length B q w+1+
      Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a+2

theorem ready_run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ (H : Fin (tapes a) → Nat) (A : Fin (tapes a) → List Bool),
      Step (readyMachine a) (budget a occ B w P)
        (Fin.addCases (PoolCold.start live occ B w top).heads (PoolCold.coldHeads a))
        (Fin.addCases (PoolCold.start live occ B w top).tapes (PoolCold.coldData a P q)) H A ∧
      H (cachePort a)=0 ∧
      A (cachePort a)=exactListWord (C10SupplierRowInput.childList a live occ) ∧
      H (domainPort a)=0 ∧ A (domainPort a)=UnaryTemplate.tape q := by
  obtain ⟨H,O,run,hcache,hcacheH,hcount,hcountH,hsource,hsourceH,htotal,htotalH,hq,hqH,_⟩ :=
    PoolCold.run a live occ B w P top hw hqw hb hm hqP hi
  let endH := dockH (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).heads (PoolCold.coldHeads a)) H
  let endA := install (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).tapes (PoolCold.coldData a P q)) O
  obtain ⟨r,hr,hfinal,_⟩ := DecompositionCountPosition.move_run (directions a) endH endA
  have move : Step (DecompositionCountPosition.move (directions a)) 1 endH endA
      (fun i => (directions a i).apply (endH i)) endA :=
    Step.of_run hr (by rw [hfinal]) (by rw [hfinal])
  refine ⟨(fun i => (directions a i).apply (endH i)),endA,?_,?_,?_,?_,?_⟩
  · simpa only [readyMachine,budget,show ∀ n : Nat,n+1+1=n+2 from by omega] using run.seq move
  · have hd : directions a (cachePort a) = .stay := by
      simp [directions,cache_ne_domain a]
    change (directions a (cachePort a)).apply (endH (cachePort a))=0
    rw [hd]
    change endH (cachePort a)=0
    simpa only [endH,cachePort,dockH_slot _ (PoolCold.slots_injective a)] using hcacheH
  · simpa only [endA,cachePort,install_slot _ (PoolCold.slots_injective a),
      C10SupplierRowInput.childList] using hcache
  · have hd : directions a (domainPort a) = .left := by simp [directions]
    change (directions a (domainPort a)).apply (endH (domainPort a))=0
    rw [hd]
    change endH (domainPort a)-1=0
    have he : endH (domainPort a)=1 := by
      simpa only [endH,domainPort,dockH_slot _ (PoolCold.slots_injective a)] using hqH
    rw [he]
  · simpa only [endA,domainPort,install_slot _ (PoolCold.slots_injective a)] using hq

def poolSlots (a : DecompositionAlgorithm) (i : Fin 373) : Fin (tapes a+373) :=
  if i=98 then (cachePort a).castAdd 373 else
  if i=224 then (domainPort a).castAdd 373 else i.natAdd (tapes a)

theorem poolSlots_injective (a : DecompositionAlgorithm) : Function.Injective (poolSlots a) := by
  intro i j h
  have hc := (cachePort a).isLt
  have hd := (domainPort a).isLt
  have hv := congrArg Fin.val h
  simp only [poolSlots] at h hv
  split_ifs at h hv with hi hj hj hji hji hji hji
  all_goals simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals first
    | exact hi.trans hj.symm
    | exact False.elim ((cache_ne_domain a) (Fin.ext hv))
    | exact False.elim ((cache_ne_domain a) (Fin.ext hv.symm))
    | (apply Fin.ext; omega)

def extra {q : Nat} (live : Finset (Fin q)) (i : Fin 373) : List Bool :=
  if i=225 then UnaryTemplate.tape live.card else
  if i=226 then CloseoutRowsGateSupport.gateMembers live else []

def args {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) : BinaryCacheColdJoin.Args q :=
  ⟨live,C10SupplierRowInput.childList a live occ⟩

theorem input_eq {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) :
    BinaryCacheColdRun.input c i =
      if i=98 then exactListWord c.gs else if i=224 then UnaryTemplate.tape q
      else extra c.live i := by
  fin_cases i <;> rfl

def machine (a : DecompositionAlgorithm) := TapeEmbedding.machine 373 (readyMachine a)

/-- The exact binary-cache input bank is physically reached from native input,
through the actual paired writer and decomposition constructor.  Its child
cache and domain template are produced by this Step, not input hypotheses. -/
theorem pool_entry {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ (H : Fin (tapes a+373) → Nat) (A : Fin (tapes a+373) → List Bool),
      Step (machine a) (budget a occ B w P)
        (Fin.addCases
          (Fin.addCases (PoolCold.start live occ B w top).heads (PoolCold.coldHeads a))
          (fun _ : Fin 373 => 0))
        (Fin.addCases
          (Fin.addCases (PoolCold.start live occ B w top).tapes (PoolCold.coldData a P q))
          (extra live))
        (dockH (poolSlots a) H (fun _ => 0))
        (install (poolSlots a) A (BinaryCacheColdRun.input (args a live occ))) := by
  obtain ⟨H,A,run,hcacheH,hcache,hqH,hq⟩ := ready_run a live occ B w P top hw hqw hb hm hqP hi
  let finalH : Fin (tapes a+373) → Nat := Fin.addCases H (fun _ : Fin 373 => 0)
  let finalA : Fin (tapes a+373) → List Bool := Fin.addCases A (extra live)
  have heH : dockH (poolSlots a) finalH (fun _ => 0) = finalH := by
    apply SourceAssemblyReuse.dockH_existing
    intro i
    simp only [poolSlots]
    split_ifs <;> simp [finalH,hcacheH,hqH]
  have heA : install (poolSlots a) finalA (BinaryCacheColdRun.input (args a live occ)) = finalA := by
    apply install_existing
    intro i
    rw [input_eq]
    simp only [poolSlots]
    split_ifs <;> simp [finalA,args,hcache,hq]
  refine ⟨finalH,finalA,?_⟩
  rw [heH,heA]
  exact run.embed (fun _ : Fin 373 => 0) (extra live)

end
end SourceAssemblyCache
