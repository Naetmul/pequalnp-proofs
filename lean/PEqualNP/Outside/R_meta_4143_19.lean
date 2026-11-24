import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

-- Keep one representative of each inclusion-maximal projected negative row.
set_option synthInstance.maxSize 256 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
theorem PEqualNP.Outside.R_meta_4143_19
  (monoEval : ∀ (C : Circuit), Monotone2 C → ∀ a b : List Bool, a.length = b.length →
    (∀ i : ℕ, a.getD i false = true → b.getD i false = true) →
    C.eval a = true → C.eval b = true)
  (search :
    let R : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
    let slope (m : Fin 3) := ([1,3,9] : List (Fin 13)).getD m.val 0
    let I := (List.finRange 26).filter fun i => i.val ∉ ([0,1,3,9,13] : List ℕ)
    let bit := fun (a i : ℕ) => a.testBit i
    let row (r : Fin 8) (m : Fin 3) (t : Fin 13) (dual : Bool) :=
      let z := R.getD r.val (0,0)
      let f (a b : ℕ) (i : Fin 13) :=
        if dual then bit b (-(slope m * i + t)).val else bit a (slope m * i + t).val
      Fin.append (f z.1 z.2) (f z.2 z.1)
    let id (r : Fin 8) (m : Fin 3) (t : Fin 13) (b : Bool) :=
      78 * r.val + 26 * m.val + 2 * t.val + b.toNat
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 43 ∧
      (∀ p l : Fin 13, p ∉ singerLines3 0 → p ∈ singerLines3 l →
        C.eval (I.map fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
      ∀ r m t b, bit 7011143044986635921097714193007014598871001440475200211071138856852336165733130736051031088810532323307102984947221566105176172108787210502487496978059865145642979448812919 (id r m t b) = true → C.eval (I.map (row r m t b)) = false) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.output < (21 : ℕ) + x5.size ∧ x5.size ≤ (43 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∉ x1 → x6 - x7 ∈ x1 → x5.eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧ ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool), x5.eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false := by
  intro D R raw I
  let slope (m : Fin 3) := ([1,3,9] : List (Fin 13)).getD m.val 0
  let row (r : Fin 8) (m : Fin 3) (t : Fin 13) (dual : Bool) :=
    raw (R.getD r.val (0,0)) (slope m) t dual
  let code (r : Fin 8) (m : Fin 3) (t : Fin 13) (b : Bool) :=
    78 * r.val + 26 * m.val + 2 * t.val + b.toNat
  let kept (i : ℕ) := ( 7011143044986635921097714193007014598871001440475200211071138856852336165733130736051031088810532323307102984947221566105176172108787210502487496978059865145642979448812919 : ℕ).testBit i
  let larger := ([0, 1, 2, 20, 4, 5, 6, 514, 8, 124, 10, 500, 12, 13, 14, 6, 16, 17, 18, 454, 20, 504, 22, 23, 24, 25, 26, 27, 28, 46, 30, 31, 32, 540, 34, 390, 36, 526, 38, 39, 40, 32, 42, 43, 44, 402, 46, 530, 48, 49, 50, 51, 52, 53, 54, 72, 56, 57, 58, 92, 60, 416, 62, 474, 64, 65, 66, 58, 68, 69, 70, 428, 72, 478, 74, 75, 76, 77, 78, 79, 80, 60, 82, 178, 84, 70, 86, 452, 88, 84, 90, 91, 92, 88, 94, 56, 69, 97, 98, 99, 100, 101, 102, 172, 104, 105, 106, 8, 108, 180, 110, 18, 112, 10, 114, 110, 116, 117, 118, 114, 120, 116, 17, 123, 124, 125, 126, 127, 128, 124, 130, 131, 132, 166, 134, 416, 136, 44, 138, 426, 140, 136, 142, 143, 144, 140, 146, 142, 43, 149, 150, 151, 152, 153, 154, 180, 156, 157, 158, 126, 91, 100, 162, 142, 164, 546, 166, 152, 168, 550, 143, 171, 172, 116, 117, 175, 176, 90, 178, 92, 180, 181, 164, 175, 156, 152, 117, 126, 166, 90, 158, 550, 176, 100, 168, 92, 91, 171, 178, 142, 143, 181, 162, 116, 180, 546, 172, 157, 158, 181, 164, 100, 143, 152, 176, 116, 156, 92, 162, 126, 168, 546, 117, 171, 180, 90, 91, 157, 166, 142, 172, 550, 178, 175, 234, 235, 236, 254, 238, 239, 240, 544, 242, 243, 244, 240, 246, 462, 248, 244, 250, 530, 252, 253, 254, 255, 239, 257, 258, 250, 260, 261, 262, 482, 264, 265, 266, 492, 268, 269, 270, 266, 272, 264, 274, 270, 276, 478, 278, 279, 280, 281, 265, 283, 284, 276, 286, 287, 288, 306, 290, 291, 292, 518, 294, 295, 296, 418, 298, 290, 300, 296, 302, 504, 304, 305, 306, 307, 291, 309, 310, 302, 312, 313, 314, 332, 316, 317, 318, 319, 320, 452, 322, 323, 324, 462, 326, 454, 328, 426, 330, 331, 332, 333, 317, 335, 336, 328, 318, 333, 336, 462, 328, 317, 320, 335, 312, 454, 330, 319, 322, 328, 314, 426, 332, 452, 324, 313, 316, 331, 317, 323, 326, 332, 320, 331, 326, 328, 332, 317, 312, 323, 318, 426, 324, 335, 330, 332, 336, 452, 316, 454, 322, 333, 328, 313, 317, 319, 314, 462, 390, 391, 392, 336, 394, 30, 323, 274, 398, 42, 400, 260, 402, 110, 281, 322, 31, 407, 408, 46, 410, 264, 123, 413, 414, 120, 416, 417, 418, 326, 420, 56, 319, 300, 424, 68, 426, 74, 428, 136, 307, 330, 57, 433, 434, 72, 436, 290, 149, 439, 440, 146, 442, 443, 444, 314, 446, 86, 335, 248, 450, 16, 452, 234, 454, 240, 255, 324, 5, 459, 460, 336, 462, 316, 97, 465, 466, 94, 468, 469, 470, 471, 472, 260, 474, 470, 476, 272, 478, 278, 65, 74, 482, 66, 269, 485, 486, 482, 488, 489, 490, 486, 492, 560, 494, 495, 496, 497, 498, 286, 500, 496, 502, 12, 504, 304, 13, 568, 508, 14, 295, 511, 512, 302, 514, 515, 516, 8, 518, 546, 520, 521, 522, 523, 524, 234, 526, 522, 528, 246, 530, 252, 39, 48, 534, 40, 243, 537, 538, 250, 540, 541, 542, 34, 544, 550, 546, 547, 548, 486, 550, 542, 171, 490, 554, 526, 497, 500, 558, 559, 560, 162, 523, 518, 471, 166, 566, 168, 568, 569, 570, 516, 550, 569, 568, 162, 560, 490, 171, 516, 570, 518, 523, 526, 554, 547, 546, 166, 471, 500, 497, 486, 548, 168, 566, 559, 558, 542, 560, 559, 566, 166, 546, 516, 171, 542, 558, 500, 471, 518, 570, 569, 550, 486, 497, 526, 523, 162, 568, 168, 548, 547, 554, 490] : List ℕ)
  let dest (r : Fin 8) (m : Fin 3) (t : Fin 13) (b : Bool) := larger.getD (code r m t b) 0
  let ri (v : ℕ) : Fin 8 := Fin.ofNat 8 (v / 78)
  let mi (v : ℕ) : Fin 3 := Fin.ofNat 3 (v / 26)
  let ti (v : ℕ) : Fin 13 := Fin.ofNat 13 (v / 2)
  let bi (v : ℕ) := v.testBit 0
  have dominated : ∀ (r : Fin 8) (m : Fin 3) (t : Fin 13) (b : Bool),
      let v := dest r m t b
      kept (code (ri v) (mi v) (ti v) (bi v)) = true ∧
        ∀ i ∈ I, row r m t b i = true → row (ri v) (mi v) (ti v) (bi v) i = true := by
    decide +kernel
  have membership : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ singerLines3 l := by decide +kernel
  have deleted : ∀ p : Fin 13, p ∈ D ↔ p ∈ singerLines3 0 := by decide +kernel
  obtain ⟨C,hC,count,pos,neg⟩ := search
  have neg' : ∀ r m t b, kept (code r m t b) = true → C.eval (I.map (row r m t b)) = false := neg
  have validOutput : C.output < 21 + C.size := by
    let read := fun (i : Fin 26) => decide (i = Fin.castAdd 13 (2 : Fin 13) ∨ i = Fin.natAdd 13 (1 : Fin 13))
    have u : C.eval (I.map read) = true := pos 2 1 (by decide +kernel) (by decide +kernel)
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
    have size : (C.wires (I.map read)).length = 21 + C.size := by
      change (C.gates.foldl step (I.map read)).length = 21 + C.gates.length
      rw [len, List.length_map, show I.length = 21 by decide +kernel]
    by_contra bad
    change ((C.wires (I.map read)).getD C.output false) = true at u
    rw [List.getD_eq_default _ _ (by rw [size]; omega)] at u
    contradiction
  refine ⟨C,hC,validOutput,count,?_,?_⟩
  · intro p l hp hl
    exact pos p l (fun h => hp ((deleted p).mpr h)) ((membership p l).mp hl)
  · intro z hz m hm t b
    obtain ⟨r,hr,rEq⟩ := List.mem_iff_getElem.mp hz
    let r' : Fin 8 := ⟨r, hr⟩
    have rep : R.getD r'.val (0,0) = z := by
      rw [List.getD_eq_getElem _ _ hr, rEq]
    obtain ⟨j,hj,jEq⟩ := List.mem_iff_getElem.mp hm
    let j' : Fin 3 := ⟨j,hj⟩
    have s : slope j' = m := by
      change ([1,3,9] : List (Fin 13)).getD j 0 = m
      rw [List.getD_eq_getElem _ _ hj, jEq]
    have eq : raw z m t b = row r' j' t b := by
      change raw z m t b = raw (R.getD r'.val (0,0)) (slope j') t b
      rw [rep,s]
    rw [eq]
    let v := dest r' j' t b
    have hDom := dominated r' j' t b
    have hFalse := neg' (ri v) (mi v) (ti v) (bi v) hDom.1
    cases h : C.eval (I.map (row r' j' t b))
    · rfl
    · have compare (i : ℕ) :
          (I.map (row r' j' t b)).getD i false = true →
          (I.map (row (ri v) (mi v) (ti v) (bi v))).getD i false = true := by
        by_cases hi : i < I.length
        · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
            List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
            List.getElem_map, List.getElem_map]
          exact hDom.2 _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by simpa only [List.length_map] using Nat.le_of_not_gt hi)]
          exact fun e => Bool.noConfusion e
      have hTrue := monoEval C hC _ _ (by simp only [List.length_map]) compare h
      rw [hFalse] at hTrue
      contradiction
