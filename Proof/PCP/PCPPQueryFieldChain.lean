import Proof.PCP.PCPPQueryField

/-! Constant-sized natural-field chains used by the PCPP metadata reader
and the counted clause-pair scan. All cursors are those produced by the
preceding physical field parser. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryField
open LocalBitMultitape StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def store {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) : Configuration 3 s := ⟨q,![pos,0,out.length],![source,backing,out]⟩
def saved (n : ℕ) (backing : List Bool) := overlay (UnaryTemplate.tape (natBitLength n)) backing
def fieldBits (n : ℕ) := RepairRepresentation.natWord n
def fieldCost (n : ℕ) := 2*natBitLength n+3
def pair (keep : Bool) := Composition.machine (machine keep) (machine keep)
def pairBits (a b : ℕ) := fieldBits a++fieldBits b
def pairCost (a b : ℕ) := fieldCost a+1+fieldCost b

@[simp] theorem fieldBits_length (n : ℕ) : (fieldBits n).length=2*natBitLength n+1 := by
  simp [fieldBits,WilliamsInputHeader.natWord_eq,SignedSortKey.binary_length]; omega

theorem pair_run (keep : Bool) (pre tail backing out : List Bool) (a b : ℕ) :
    ∃ r : ExecutionReceipt 3 8,
      runFrom (pair keep) (pairCost a b)
        (store 0 (pre++pairBits a b++tail) pre.length backing out)=some r ∧
      r.final=store 7 (pre++pairBits a b++tail) (pre.length+(pairBits a b).length)
        (saved b (saved a backing)) (out++selected keep (pairBits a b)) ∧
      r.steps=pairCost a b := by
  let source := pre++pairBits a b++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := nat_run keep pre (fieldBits b++tail) backing out a
  have hsource : pre++fieldBits a++(fieldBits b++tail)=source := by simp [source,pairBits,List.append_assoc]
  change runFrom (machine keep) (fieldCost a) (cfg 0 (pre++fieldBits a++(fieldBits b++tail)) pre.length backing 0 out)=some first at hfirst
  rw [hsource] at hfirst
  change first.final=payload 3 (pre++fieldBits a++(fieldBits b++tail))
    (pre.length+2*natBitLength a+1) (natBitLength a) 0 backing (out++selected keep (fieldBits a)) at hff
  rw [hsource] at hff
  obtain ⟨last,hl,hlf,hls⟩ := nat_run keep (pre++fieldBits a) tail (saved a backing)
    (out++selected keep (fieldBits a)) b
  have hsource2 : (pre++fieldBits a)++fieldBits b++tail=source := by simp [source,pairBits,List.append_assoc]
  change runFrom (machine keep) (fieldCost b)
    (cfg 0 ((pre++fieldBits a)++fieldBits b++tail) (pre++fieldBits a).length
      (saved a backing) 0 (out++selected keep (fieldBits a)))=some last at hl
  rw [hsource2] at hl
  have hi : Composition.restart first.final (machine keep).start=
      cfg 0 source (pre++fieldBits a).length (saved a backing) 0 (out++selected keep (fieldBits a)) := by
    rw [hff]
    simp only [List.length_append,fieldBits_length]
    simp only [Composition.restart,payload,cfg,saved,machine,Nat.add_assoc]
  rw [← hi] at hl
  have hj := Composition.run_join (machine keep) (machine keep) (fieldCost a) (fieldCost b) _ first last hfirst hl
  have hentry : Composition.leftConfig 4 (cfg 0 source pre.length backing 0 out)=
      store 0 source pre.length backing out := rfl
  rw [hentry] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 4 last.final=_
    rw [hlf]
    have hp : (pre++fieldBits a).length+2*natBitLength b+1=pre.length+(pairBits a b).length := by
      simp [pairBits]; omega
    have hout : (out++selected keep (fieldBits a))++selected keep (fieldBits b)=out++selected keep (pairBits a b) := by
      cases keep <;> simp [selected,pairBits,List.append_assoc]
    change Composition.rightConfig 4 (payload 3 ((pre++fieldBits a)++fieldBits b++tail)
      ((pre++fieldBits a).length+2*natBitLength b+1) (natBitLength b) 0 (saved a backing)
      ((out++selected keep (fieldBits a))++selected keep (fieldBits b)))=_
    rw [hsource2,hp,hout]
    rfl
  · change first.steps+1+last.steps=_
    rw [hfs,hls]
    rfl

def four (keep : Bool) := Composition.machine (pair keep) (pair keep)
def fourBits (a b c d : ℕ) := pairBits a b++pairBits c d
def fourCost (a b c d : ℕ) := pairCost a b+1+pairCost c d

theorem four_run (keep : Bool) (pre tail backing out : List Bool) (a b c d : ℕ) :
    ∃ r : ExecutionReceipt 3 16,
      runFrom (four keep) (fourCost a b c d)
        (store 0 (pre++fourBits a b c d++tail) pre.length backing out)=some r ∧
      r.final=store 15 (pre++fourBits a b c d++tail) (pre.length+(fourBits a b c d).length)
        (saved d (saved c (saved b (saved a backing))))
        (out++selected keep (fourBits a b c d)) ∧ r.steps=fourCost a b c d := by
  let source := pre++fourBits a b c d++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := pair_run keep pre (pairBits c d++tail) backing out a b
  have hsource : pre++pairBits a b++(pairBits c d++tail)=source := by simp [source,fourBits,List.append_assoc]
  rw [hsource] at hfirst hff
  obtain ⟨last,hl,hlf,hls⟩ := pair_run keep (pre++pairBits a b) tail (saved b (saved a backing))
    (out++selected keep (pairBits a b)) c d
  have hsource2 : (pre++pairBits a b)++pairBits c d++tail=source := by simp [source,fourBits,List.append_assoc]
  rw [hsource2] at hl hlf
  have hi : Composition.restart first.final (pair keep).start=
      store 0 source (pre++pairBits a b).length (saved b (saved a backing))
        (out++selected keep (pairBits a b)) := by
    rw [hff,List.length_append]
    rfl
  rw [← hi] at hl
  have hj := Composition.run_join (pair keep) (pair keep) (pairCost a b) (pairCost c d) _ first last hfirst hl
  have hentry : Composition.leftConfig 8 (store (s:=8) 0 source pre.length backing out)=
      store (s:=16) 0 source pre.length backing out := rfl
  rw [hentry] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 8 last.final=_
    rw [hlf]
    have hp : (pre++pairBits a b).length+(pairBits c d).length=pre.length+(fourBits a b c d).length := by
      simp [fourBits,Nat.add_assoc]
    have hout : (out++selected keep (pairBits a b))++selected keep (pairBits c d)=
        out++selected keep (fourBits a b c d) := by
      cases keep <;> simp [selected,fourBits,List.append_assoc]
    rw [hp,hout]
    rfl
  · change first.steps+1+last.steps=_
    rw [hfs,hls]
    rfl

end NearCubicWires.RepairOrdinary.PCPPQueryField
