import Proof.MachineModel.OrdinaryMatrixRightAdvance

/-! One repeatable right bucket on a fixed 25-tape bank. It computes its
interval complement, emits keyed right cells, restores the source cursor,
and advances the actual boundary and inner-coordinate scalars. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightBucket
open LocalBitMultitape SignedSortKey
open MatrixRightAdvance (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Params where
  S : ℕ
  K : ℕ
  I : ℕ
  B : ℕ
  keyCap : ℕ
  resetCap : ℕ
  records : List KeyLoop.Record
  rankFit : ∀ r ∈ records,r.2.2<2^(K+S+1)-1
  keyI : 2*I ≤ keyCap
  keyK : 2*K ≤ keyCap
  resetFit : records.length*(68*(K+S+1)+4*(I+K)+63)+1 ≤ resetCap

def width (p : Params) := p.K+p.S+1
def fuel (p : Params) := p.records.length*(68*width p+4*(p.I+p.K)+63)+1
def advanceParams (p : Params) : MatrixRightAdvance.Params :=
  ⟨width p,p.K,p.I,p.keyCap,p.resetCap,p.B,KeyLoop.stream p.S p.K p.records⟩
def cfg {s : ℕ} (q : Fin s) (p : Params) (v : Store) := MatrixRightAdvance.cfg q (advanceParams p) v
def output (p : Params) (a inner : ℕ) :=
  p.records.flatMap (fun e => frame (decide (a≤e.2.2)::(binary p.I inner++binary p.K e.2.1)))

def request (p : Params) (v : Store) (ha : v.a<2^width p)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) : MatrixRightScan.Request where
  S := p.S
  K := p.K
  I := p.I
  inner := v.inner
  keyCap := p.keyCap
  resetCap := p.resetCap
  a := v.a
  initialRank := v.rank
  records := p.records
  upper := v.upper
  recordBack := v.record
  cloneBack := v.clone
  out := v.out
  backing := frame (binary (width p) v.b)
  aFit := ha
  rankFit := p.rankFit
  upperFit := hu
  recordFit := hr
  cloneFit := hc
  backingFit := by simp [width]
  keyI := p.keyI
  keyK := p.keyK
  resetFit := p.resetFit

def extras (p : Params) : Fin 3 → List Bool :=
  ![frame (binary (width p) p.B),List.replicate (2*width p+1) false,List.replicate (4*width p+3) false]
noncomputable def scan : Machine 25 62 := TapeEmbedding.machine 3 MatrixRightScan.machine
noncomputable def machine : Machine 25 86 := Composition.machine scan MatrixRightAdvance.machine

theorem input_config (p : Params) (v : Store) (ha : v.a<2^width p)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) :
    TapeEmbedding.config (fun _ : Fin 3 => 0) (extras p)
      (Composition.leftConfig 57 (MatrixRightScan.entry (request p v ha hu hr hc)))=cfg scan.start p v := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp only [TapeEmbedding.config,Fin.addCases,MatrixRightScan.entry]
    all_goals rfl

def afterScan (p : Params) (v : Store) (rank : ℕ) (upper record clone : List Bool) : Store :=
  {v with
    b := MatrixComplement.difference (width p) v.a
    rank := rank
    upper := upper
    record := record
    clone := clone
    out := v.out++output p v.a v.inner}

theorem output_config (p : Params) (v : Store) (rank : ℕ) (upper record clone : List Bool) :
    TapeEmbedding.config (fun _ : Fin 3 => 0) (extras p)
      (Composition.rightConfig 5 (TapeEmbedding.config (fun _ : Fin 1 => 0)
        (fun _ : Fin 1 => List.replicate (2*width p+1) false)
        (KeyReset.config (56 : Fin 57) (width p) v.a (MatrixComplement.difference (width p) v.a) rank
          upper record clone true (KeyLoop.stream p.S p.K p.records) (v.out++output p v.a v.inner)
          p.K p.I v.inner p.keyCap p.resetCap)))=cfg (61 : Fin 62) p (afterScan p v rank upper record clone) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem bucket_run (p : Params) (v : Store) (ha : v.a+p.B<2^width p) (hi : v.inner+1<2^p.I)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) :
    ∃ rank record clone,record.length ≤ 4*width p+1 ∧ clone.length ≤ 4*width p+1 ∧
      ∃ actual : ExecutionReceipt 25 86,runFrom machine (2*fuel p+24*width p+4*p.I+33)
        (cfg machine.start p v)=some actual ∧
        actual.final=cfg 85 p
          {v with
            a := v.a+p.B
            b := p.B
            inner := v.inner+1
            rank := rank
            upper := frame (binary (width p) (v.a+p.B))
            record := record
            clone := clone
            out := v.out++output p v.a v.inner} ∧ actual.steps ≤ 2*fuel p+24*width p+4*p.I+33 := by
  have ha0 : v.a<2^width p := by omega
  let req := request p v ha0 hu hr hc
  obtain ⟨rank,upper,record,clone,hupper,hrecord,hclone,base,hb,hbf,hbs⟩ := MatrixRightScan.scan_run req
  have he := TapeEmbedding.run_embed MatrixRightScan.machine (fun _ : Fin 3 => 0) (extras p) _ _ base hb
  rw [input_config] at he
  let first := TapeEmbedding.receipt (fun _ : Fin 3 => 0) (extras p) base
  let state := afterScan p v rank upper record clone
  have hf : first.final=cfg (61 : Fin 62) p state := by
    change TapeEmbedding.config _ _ base.final=_
    rw [hbf]
    exact output_config p v rank upper record clone
  obtain ⟨last,hl,hlf,hls⟩ := MatrixRightAdvance.advance_run (advanceParams p) state hi p.keyI ha hupper
  have hentry : Composition.restart first.final MatrixRightAdvance.machine.start=
      MatrixRightAdvance.cfg MatrixRightAdvance.machine.start (advanceParams p) state := by
    rw [hf]
    rfl
  have hl' : runFrom MatrixRightAdvance.machine (20*width p+4*p.I+25)
      (Composition.restart first.final MatrixRightAdvance.machine.start)=some last := by
    rw [hentry]
    exact hl
  have hj := Composition.run_join scan MatrixRightAdvance.machine (2*fuel p+4*width p+7)
    (20*width p+4*p.I+25) (cfg scan.start p v) first last he hl'
  have htime : (2*fuel p+4*width p+7)+1+(20*width p+4*p.I+25)=2*fuel p+24*width p+4*p.I+33 := by omega
  rw [htime] at hj
  refine ⟨rank,record,clone,hrecord,hclone,Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 62 last.final=_
    rw [hlf]
    rfl
  · change base.steps+1+last.steps ≤ _
    change base.steps ≤ 2*fuel p+4*width p+7 at hbs
    change last.steps ≤ 20*width p+4*p.I+25 at hls
    omega

end NearCubicWires.RepairOrdinary.MatrixRightBucket
