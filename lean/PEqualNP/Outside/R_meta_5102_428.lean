import PEqualNP.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5102_428
    (factors :
      let edges : List (Fin 13 × Fin 13) :=
        [(0,6),(2,6),(1,7),(5,7),(0,8),(4,8),(5,8),(3,9),(4,9),
         (2,10),(3,10),(5,10),(1,11),(2,11),(4,11),(0,12),(1,12),(3,12)]
      let bank := fun (x : Fin 13 → Bool) =>
        List.ofFn x ++ [x 6 || x 7, x 6 || x 7 || x 9]
      let run := fun (s : List Bool) (p : List (Bool × ℕ × ℕ)) =>
        p.foldl (fun (w : List Bool) g =>
          let r := fun i => w.getD i (s.headD false)
          w ++ [cond g.1 (r g.2.1 || r g.2.2) (r g.2.1 && r g.2.2)]) s
      ∃ p : List (Bool × ℕ × ℕ), p.length ≤ 21 ∧
        ∃ a b : ℕ, 15 ≤ a ∧ a < b ∧ b < 15 + p.length ∧
          ∃ op : Bool, ∀ x : Fin 13 → Bool,
            let w := run (bank x) p
            let u := w.getD a (x 0)
            let v := w.getD b (x 0)
            cond op (u || v) (u && v) = edges.any (fun e => x e.1 && x e.2))
    (bitRun :
      ∀ (s : List ℕ) (p : List (Bool × ℕ × ℕ)) (d k : ℕ),
      let numberWires := p.foldl (fun (w : List ℕ) g =>
        let r := fun i => w.getD i d
        w ++ [cond g.1 (r g.2.1 ||| r g.2.2) (r g.2.1 &&& r g.2.2)]) s
      let boolWires := p.foldl (fun (w : List Bool) g =>
        let r := fun i => w.getD i (d.testBit k)
        w ++ [cond g.1 (r g.2.1 || r g.2.2) (r g.2.1 && r g.2.2)])
        (s.map fun n => n.testBit k)
      (numberWires.map fun n => n.testBit k) = boolWires) :
have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; ∃ (x3 : List (Bool × ℕ × ℕ)), x3.length ≤ (22 : ℕ) ∧ ∃ (x4 : ℕ), x1 x2 x3 x4 = (262143 : ℕ) := by
  simp only [Bool.cond_eq_ite] at factors bitRun
  let seeds : List ℕ :=
    [917681504273,14878052356,31886295704066,257731462272,42884715528480,
     82789891049544,248671168364547,198670308868108,158476001083504,
     238332533539200,176488259259904,212188564320256,280375465312256,
     271282175737871,280357743624591]
  let edges : List (Fin 13 × Fin 13) :=
    [(0,6),(2,6),(1,7),(5,7),(0,8),(4,8),(5,8),(3,9),(4,9),
     (2,10),(3,10),(5,10),(1,11),(2,11),(4,11),(0,12),(1,12),(3,12)]
  let bank := fun (x : Fin 13 → Bool) =>
    List.ofFn x ++ [x 6 || x 7, x 6 || x 7 || x 9]
  let xs := fun (i : ℕ) (j : Fin 13) => (seeds.getD j.val 0).testBit i
  have packedBank (i : ℕ) : bank (xs i) = seeds.map (fun n => n.testBit i) := by
    have pooled : (271282175737871 : ℕ) = 248671168364547 ||| 198670308868108 :=
      by decide
    have pooledExtra : (280357743624591 : ℕ) = (248671168364547 ||| 198670308868108) |||
        238332533539200 := by decide
    have h13 := congrArg (fun n : ℕ => n.testBit i) pooled
    have h14 := congrArg (fun n : ℕ => n.testBit i) pooledExtra
    simp only [Nat.testBit_lor] at h13 h14
    simp [bank, xs, seeds, List.ofFn_succ, List.getD, h13, h14]
  have bound : ∀ j : Fin 13, seeds.getD j.val 0 < 2 ^ 48 := by decide
  have graphTable : ∀ i : Fin 48,
      edges.any (fun e => xs i.val e.1 && xs i.val e.2) = (262143 : ℕ).testBit i.val := by
    decide +kernel
  have graphBits (i : ℕ) :
      edges.any (fun e => xs i e.1 && xs i e.2) = (262143 : ℕ).testBit i := by
    by_cases hi : i < 48
    · exact graphTable ⟨i,hi⟩
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 48 ≤ i)
    have zeroBits (j : Fin 13) : xs i j = false :=
      Nat.testBit_eq_false_of_lt ((bound j).trans_le hpow)
    rw [Nat.testBit_eq_false_of_lt ((by decide : 262143 < 2 ^ 48).trans_le hpow)]
    simp [edges, zeroBits]
  let stepB := fun (d : Bool) (w : List Bool) (g : Bool × ℕ × ℕ) =>
    let r := fun i => w.getD i d
    w ++ [if g.1 then r g.2.1 || r g.2.2 else r g.2.1 && r g.2.2]
  let stepN := fun (d : ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) =>
    let r := fun i => w.getD i d
    w ++ [if g.1 then r g.2.1 ||| r g.2.2 else r g.2.1 &&& r g.2.2]
  let d := seeds.headD 0
  have lenStep (d : Bool) (s : List Bool) (p : List (Bool × ℕ × ℕ)) :
      (p.foldl (stepB d) s).length = s.length + p.length := by
    induction p generalizing s with
    | nil => simp
    | cons g p ih =>
      simp only [List.foldl_cons, ih, List.length_cons]
      simp only [stepB, List.length_append, List.length_singleton]
      omega
  change ∃ p : List (Bool × ℕ × ℕ), p.length ≤ 22 ∧
    ∃ o : ℕ, (p.foldl (stepN d) seeds).getD o d = 262143
  obtain ⟨p, hp, a, b, _, _, _, op, h⟩ := factors
  refine ⟨p ++ [(op,a,b)], by simpa using Nat.succ_le_succ hp, 15 + p.length, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  let bit := fun n : ℕ => n.testBit i
  have getBit (w : List ℕ) (o : ℕ) : bit (w.getD o d) = (w.map bit).getD o (bit d) := by
    simp [List.getD, List.getElem?_map, Option.getD_map]
  have proj := bitRun seeds (p ++ [(op,a,b)]) d i
  change (((p ++ [(op,a,b)]).foldl (stepN d) seeds).map bit) =
    (p ++ [(op,a,b)]).foldl (stepB (bit d)) (seeds.map bit) at proj
  change bit (((p ++ [(op,a,b)]).foldl (stepN d) seeds).getD (15 + p.length) d) = _
  rw [getBit, proj, ← packedBank i, List.foldl_append, List.foldl_cons, List.foldl_nil]
  let w := p.foldl (stepB (xs i 0)) (bank (xs i))
  change (stepB (xs i 0) w (op,a,b)).getD (15 + p.length) (xs i 0) = _
  have hw : w.length = 15 + p.length := by
    rw [lenStep]
    simp [bank]
  rw [← hw]
  have hrow := h (xs i)
  change (if op then w.getD a (xs i 0) || w.getD b (xs i 0)
    else w.getD a (xs i 0) && w.getD b (xs i 0)) = _ at hrow
  simpa [stepB, List.getD, List.getElem?_append_right] using hrow.trans (graphBits i)
