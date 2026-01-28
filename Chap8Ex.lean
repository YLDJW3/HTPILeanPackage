import HTPILib.Chap8Part2
namespace HTPI.Exercises

open Classical

/- Section 8.1 -/
-- 1.
--Hint:  Use Exercise_6_1_16a2 from the exercises of Section 6.1
theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := sorry
-- can't import from Chap6Ex.lean for unknown reason, paste it here temporarily

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := by
    have h1: ¬2 ∣ 2 * k + 1 := by
      by_contra h
      obtain x hx from h
      have h_even: nat_even (2 * k + 1) := by
        exists x
      have h_odd: nat_odd (2 * k + 1) := by
        exists k
      contradict Exercise_6_1_16a2
      rw [Classical.not_forall_not]
      exists 2 * k + 1
      done
    have h2: 0 < 2 := by linarith
    calc fnz (2 * k + 1)
      _ = -↑((2 * k + 1 + 1) / 2) := if_neg h1
      _ = -↑(2 * (k + 1) / 2) := by ring
      _ = -↑(k + 1) := by rw[Nat.mul_div_cancel_left _ h2]
    done

-- 2.
lemma fnz_fzn : fnz ∘ fzn = id  := by
  apply funext
  intros x
  rw [comp_def]
  by_cases h: x ≥ 0
  · -- x ≥ 0
    rw [fzn, if_pos h]
    rw [fnz_even, id]
    rw [Int.natCast_toNat_eq_self]
    apply h
  · -- x < 0
    rw [fzn, if_neg h]
    have h2 : 1 ≤ (-x).toNat := by
        have g1: 1 = (↑1: Int).toNat := by decide
        nth_rw 1 [g1]
        apply Int.toNat_le_toNat
        linarith
    have h1: 1 ≤ 2 * (-x).toNat - 1 := by
        have g1: 2 ≤ 2 * (-x).toNat := by linarith
        apply Nat.sub_le_sub_right at g1
        apply g1 1
        done
    have h3 : 0 ≤ -x := by linarith
    rw [← Int.natCast_toNat_eq_self] at h3
    rw [id]
    calc fnz (2 * (-x).toNat - 1)
      _ = fnz (2 * (-x).toNat -1 -1 + 1) := by rw[Nat.sub_add_cancel h1]
      _ = fnz (2 * (-x).toNat - (1 + 1) + 1) := by rw[Nat.sub_add_eq]
      _ = fnz (2 * (-x).toNat - 2 * 1 + 1) := by linarith
      _ = fnz (2 * ((-x).toNat - 1) + 1) := by rw[← Nat.mul_sub_left_distrib]
      _ = -↑((-x).toNat - 1 + 1) := by rw[fnz_odd]
      _ = -(-x).toNat := by rw[Nat.sub_add_cancel h2]
      _ = -(-x) := by rw [h3]
      _ = x := by ring
    done

-- 3.
lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := by
    rw [tri, tri]
    have h1: (k + 1) * 2 % 2 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exists (k + 1)
      ring
    show (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + k + 1 from
      calc (k + 1) * (k + 1 + 1) / 2
        _ = (k + 1) * (k + 2) / 2 := by ring
        _ = ((k + 1) * k + (k + 1) * 2) / 2 := by ring
        _ = (k * (k + 1) + (k + 1) * 2) / 2 := by ring
        _ = k * (k + 1) / 2 + (k + 1) * 2 / 2 := by
          rw [Nat.add_div_eq_of_add_mod_lt]
          rw [h1]; ring
          apply mod_nonzero_lt; linarith
        _ = k * (k + 1) / 2 + (k + 1) := by
          rw [Nat.mul_div_cancel]
          linarith
    done

-- 4.
lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := by
    rw [tri, tri]
    have h2: j + 1 ≤ k + 1 := by linarith
    have h3 : j * (j + 1) ≤ k * (k + 1) := by
      apply Nat.mul_le_mul h1 h2
    have h4: 2 ≤ 2 := by linarith
    have h5: 2 ≠ 0 := by linarith
    apply Nat.div_le_div h3 h4 h5
    done

-- 5.
example {U V : Type} (f : U → V) : range f = Ran (graph f) := by
  apply Set.ext; fix y ; apply Iff.intro
  · --y ∈ range f → y ∈ Ran (graph f)
    intros h1; define at h1
    obtain x h2 from h1; clear h1
    define; exists x
  · --y ∈ Ran (graph f) → y ∈ range f
    intros h1; define at h1
    obtain x h2 from h1; clear h1
    define; exists x
  done

-- 6.
lemma onto_iff_range_eq_univ {U V : Type} (f : U → V) :
    onto f ↔ range f = Univ V := by
    apply Iff.intro
    · --onto f → range f = Univ V
      intros h1
      apply Set.ext; fix y; apply Iff.intro
      · --y ∈ range f → y ∈ Univ V
        intros h2
        define; trivial
      · --y ∈ Univ V → y ∈ range f
        intros h2
        apply h1
    · --range f = Univ V → onto f
      intros h1
      intros y
      rw [Set.ext_iff] at h1
      have h2 := by apply h1 y
      have h3 : y ∈ Univ V := by define; trivial
      rw [← h2] at h3; define at h3
      apply h3
    done

-- 7.
-- Don't use ctble_iff_set_nat_equinum to prove this lemma
lemma ctble_of_ctble_equinum {U V : Type}
    (h1 : U ∼ V) (h2 : ctble U) : ctble V := by
    define
    by_cases on h2
    · --finite U
      apply Or.inl
      define at h2; obtain n h3 from h2; clear h2
      define; exists n
      apply Theorem_8_1_3_3 h3 h1
    · --denum U
      apply Or.inr
      define at h2; obtain f h3 from h2; clear h2
      obtain g h2 from h1; clear h1
      exists (g ∘ f)
      apply And.intro
      · --one_to_one (g ∘ f)
        apply Theorem_5_2_5_1 f g h3.left h2.left
      · --onto (g ∘ f)
        apply Theorem_5_2_5_2 f g h3.right h2.right
    done

-- 8.
theorem Exercise_8_1_1_b : denum {n : Int | even n} := by
    define
    -- Define a bijection from Nat to even integers
    -- Map: 0→0, 1→-2, 2→2, 3→-4, 4→4, 5→-6, ...
    let V := {n : Int | even n}
    have g1 (n: Nat)(h: nat_even n): (↑n: Int) ∈ V := by
      define; define at h
      obtain x hx from h
      exists x
      rw [hx, Nat.cast_mul]
      rfl
      done
    -- let f : (Nat → {n : Int | even n}) := fun n =>
    --   if h: nat_even n
    --   then ⟨↑n, by
    --     apply g1
    --     apply h
    --     ⟩
    --   else ⟨-↑(n + 1), by
    --     define
    --     have g
    --     ⟩
    sorry

-- 9.
theorem equinum_iff_inverse_pair (U V : Type) :
    U ∼ V ↔ ∃ (f : U → V) (g : V → U), f ∘ g = id ∧ g ∘ f = id := by
    apply Iff.intro
    · --U ∼ V → ∃ (f : U → V) (g : V → U), f ∘ g = id ∧ g ∘ f = id
      intros h1
      obtain f h2 from h1
      have h3 := by apply Theorem_5_3_1 f h2.left h2.right
      obtain finv h4 from h3; clear h3
      exists f
      exists finv
      apply And.intro
      · --f ∘ finv = id
        apply Theorem_5_3_2_2 f finv h4
      · --finv ∘ f = id
        apply Theorem_5_3_2_1 f finv h4
    · --(∃ (f : U → V) (g : V → U), f ∘ g = id ∧ g ∘ f = id) → U ∼ V
      intros h1
      obtain f tmp from h1; clear h1
      obtain g h2 from tmp; clear tmp
      exists f
      apply And.intro
      · --one_to_one f
        apply Theorem_5_3_3_1 f g
        apply h2.right
      · --onto f
        apply Theorem_5_3_3_2 f g
        apply h2.left
    done

-- 10.
lemma image_comp_id {U V : Type} {f : U → V} {g : V → U}
    (h : g ∘ f = id) : (image g) ∘ (image f) = id := by
    rw [funext_iff] at h
    apply funext
    intros A
    apply Set.ext
    intros a
    apply Iff.intro
    · -- a ∈ (image g ∘ image f) A → a ∈ id A
      intros h1
      rw [id]
      have h2 := by apply h a
      rw [id] at h2
      define at h1
      obtain x hx from h1; clear h1
      have h3 := hx.left; define at h3
      obtain y hy from h3; clear h3
      rw [← hy.right] at hx
      have h1 := by apply h y
      rw [comp_def, id, hx.right] at h1
      rw [h1]
      apply hy.left
    · --a ∈ id A → a ∈ (image g ∘ image f) A
      intros h1; define at h1
      define; exists f a
      apply And.intro
      · --f a ∈ image f A
        define; exists a
      · apply h a
    done

-- 11.
theorem Exercise_8_1_5_1 {U V : Type}
    (h : U ∼ V) : Set U ∼ Set V := by
    define; define at h
    obtain f h1 from h; clear h
    exists image f
    apply And.intro
    · --one_to_one (image f)
      define
      intros X1 X2 heq
      rw [Set.ext_iff] at heq
      apply Set.ext
      intros x
      have h2 := by apply heq (f x)
      apply Iff.intro
      · -- x ∈ X1 → x ∈ X2
        intros h3
        have h4 : f x ∈ image f X1 := by
          define; exists x
        rw [h2] at h4
        obtain y h5 from h4
        have g1:= h1.left
        define at g1
        have g2 := h5.right
        apply g1 at g2
        rw [← g2]; apply h5.left
      · --x ∈ X2 → x ∈ X1
        intros h3
        have h4: f x ∈ image f X2 := by
          define; exists x
        rw [← h2] at h4
        obtain y h5 from h4
        have g1 := h1.left; define at g1
        have g2 := h5.right
        apply g1 at g2
        rw [← g2]; apply h5.left
    · --onto (image f)
      define; fix Y
      exists inverse_image f Y
      apply Set.ext
      intros y
      apply Iff.intro
      · -- y ∈ image f (inverse_image f Y) → y ∈ Y
        intros h2; define at h2
        obtain x h3 from h2; clear h2
        have h4 := h3.left; define at h4
        rw [← h3.right]
        apply h4
      · --y ∈ Y → y ∈ image f (inverse_image f Y)
        intros h2
        define
        have h3 := h1.right y
        obtain x h4 from h3; clear h3
        exists x
        apply And.intro
        · --x ∈ inverse_image f Y
          define; rw [h4]; apply h2
        · apply h4
    done

-- Definition for next three exercises
def val_image {U : Type} (A : Set U) (X : Set A) : Set U :=
  {y : U | ∃ x ∈ X, x.val = y}
  -- {y: Set ↑A | ∃ x ∈ B, y.val = x}

-- 12.
lemma subset_of_val_image_eq {U : Type} {A : Set U} {X1 X2 : Set A}
    (h : val_image A X1 = val_image A X2) : X1 ⊆ X2 := by
    rw [Set.ext_iff] at h
    define; intros x h1
    have h2: x.val ∈ val_image A X1 := by
      define; exists x
    rw [h] at h2
    define at h2
    obtain y h3 from h2
    have h4 := h3.right
    rw [← Subtype.ext_iff] at h4
    rw [← h4]
    apply h3.left
    done

-- 13.
lemma val_image_one_one {U : Type} (A : Set U) :
    one_to_one (val_image A) := by
    define
    intros X1 X2 h1
    rw [Set.ext_iff] at h1
    apply Set.ext
    intros x; apply Iff.intro
    · --x ∈ X1 → x ∈ X2
      intros h2
      have h3: x.val ∈ val_image A X1 := by
        define; exists x
      rw [h1] at h3
      define at h3
      obtain y h4 from h3; clear h3
      have h5 := h4.right; rw [← Subtype.ext_iff] at h5
      rw [h5] at h4; apply h4.left
    · --x ∈ X2 → x ∈ X1
      intros h2
      have h3: x.val ∈ val_image A X2 := by
        define; exists x
      rw [← h1] at h3
      define at h3
      obtain y h4 from h3; clear h3
      have h5 := h4.right; rw [← Subtype.ext_iff] at h5
      rw [h5] at h4; apply h4.left
    done

-- 14.
lemma range_val_image {U : Type} (A : Set U) :
    range (val_image A) = 𝒫 A := by
    apply Set.ext
    intros B; apply Iff.intro
    · --B ∈ range (val_image A) → B ∈ 𝒫 A
      intros h1; define at h1
      obtain X h2 from h1; clear h1
      intros x h1
      rw [val_image] at h2
      rw [← h2] at h1; define at h1
      obtain y h3 from h1; clear h1
      have h4 := y.property
      rw [←h3.right]
      apply h4
    · --B ∈ 𝒫 A → B ∈ range (val_image A)
      intros h1; define at h1
      define
      exists {y: ↑A | ∃ x ∈ B, y.val = x}
      apply Set.ext; fix x
      apply Iff.intro
      · --x ∈ val_image A {y : ↑A | ∃ x ∈ B, ↑y = x} → x ∈ B
        intros h2; define at h2
        obtain y h3 from h2; clear h2
        have h2 := h3.left; define at h2
        obtain z h4 from h2; clear h2
        rw [← h3.right, h4.right]
        apply h4.left
      · --x ∈ B → x ∈ val_image A {y : ↑A | ∃ x ∈ B, ↑y = x}
        intros h2
        define
        have h3 := h2; apply h1 at h3
        exists Subtype_elt h3
        apply And.intro
        · -- Subtype_elt h3 ∈ {y : ↑A | ∃ x ∈ B, ↑y = x}
          define; exists x
        · --↑(Subtype_elt h3) = x
          rfl
      done

-- 15.
lemma Set_equinum_powerset {U : Type} (A : Set U) :
    Set A ∼ 𝒫 A := by
    rw [← range_val_image A]
    exists func_to_range (val_image A)
    apply And.intro
    · --one_to_one (func_to_range (val_image A))
      apply ftr_one_one_of_one_one
      apply val_image_one_one
    · --onto (func_to_range (val_image A))
      apply ftr_onto
    done

-- 16.
--Hint:  Use Exercise_8_1_5_1 and Set_equinum_powerset.
theorem Exercise_8_1_5_2 {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) : 𝒫 A ∼ 𝒫 B := by
    have h1: Set A ∼ 𝒫 A := by apply Set_equinum_powerset A
    have h2: Set B ∼ 𝒫 B := by apply Set_equinum_powerset B
    apply Exercise_8_1_5_1 at h
    apply Theorem_8_1_3_2 at h1
    have h3 := by apply Theorem_8_1_3_3 h h2
    apply Theorem_8_1_3_3 h1 h3
    done

-- 17.
example (U V : Type) (A : Set U) (f : A → V) (v : V) :
    func_restrict (func_extend f v) A = f := by
    apply funext
    fix a
    rw [fr_def, fe_elt]
    done

-- 18.
theorem Theorem_8_1_5_3_type {U : Type} :
    ctble U ↔ ∃ (f : U → Nat), one_to_one f := by
    apply Iff.intro
    · --ctble U → ∃ (f : U → ℕ), one_to_one f
      intros h1
      rw [ctble_iff_set_nat_equinum] at h1
      obtain X h2 from h1; clear h1
      apply Theorem_8_1_3_2 at h2
      define at h2
      obtain f h3 from h2; clear h2
      exists func_to_type f
      apply ftt_one_one_of_one_one h3.left
    · --(∃ (f : U → ℕ), one_to_one f) → ctble U
      intros h1
      obtain f h2 from h1; clear h1
      rw [ctble_iff_set_nat_equinum]
      exists range f
      apply Theorem_8_1_3_2
      define
      exists func_to_range f
      apply And.intro
      · apply ftr_one_one_of_one_one h2
      · apply ftr_onto
    done

-- 19.
theorem ctble_set_of_ctble_type {U : Type}
    (h : ctble U) (A : Set U) : ctble A := by
    rw [ctble_iff_set_nat_equinum] at h
    obtain V h1 from h; clear h
    apply Theorem_8_1_3_2 at h1
    define at h1; obtain f h2 from h1; clear h1
    rw [Theorem_8_1_5_3_type]

    exists func_to_type (func_restrict f A)
    apply ftt_one_one_of_one_one
    apply fr_one_one_of_one_one_on
    define; intros x1 x2 hx1 hx2 heq
    apply h2.left at heq
    apply heq
    done

-- 20.
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := by
    rw [Theorem_8_1_5_3_type] at h2
    obtain f h3 from h2; clear h2
    rw [Theorem_8_1_5_3_type]
    define at h1

    set fba: ↑B → ↑A := fun b => ⟨b.val, h1 b.property⟩
    exists f ∘ fba
    define
    intros b1 b2 h4
    rw [comp_def, comp_def] at h4
    apply h3 at h4
    simp [fba] at h4
    rw [Subtype.ext_iff]
    apply h4
    done

/- Section 8.1½ -/
-- 1.
lemma image_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : image f A = I 0 := by
    define at h
    apply Set.ext
    intros x; apply Iff.intro
    · --x ∈ image f A → x ∈ I 0
      intros h1; define at h1
      obtain y h2 from h1
      contradict h; exists y
      apply h2.left
    · --x ∈ I 0 → x ∈ image f A
      intros h1; define at h1
      linarith
    done

-- 2.
lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := by

    have g: range (func_restrict f (A \ {a})) = B \ {b} := by
      rw [fr_range]
      apply Set.ext; intros y; apply Iff.intro
      · intros g1; define at g1
        obtain x g2 from g1; clear g1
        apply And.intro
        rw [Set.ext_iff] at h2
        have g3 := by apply h2 y
        rw [← g3]
        define; exists x
        have g1 := g2.left; define at g1
        apply And.intro g1.left g2.right
        have g3 := g2.left.right; define at g3
        define; contradict g3 with g4
        rw [← g2.right, ← h4] at g4
        apply h1 at g4
        apply g4
        apply g2.left.left
        apply h3
        done
      · intros g1; define at g1
        define
        rw [Set.ext_iff] at h2
        have g2 := by apply h2 y
        have g3 := g1.left
        rw [← g2] at g3; define at g3
        obtain x g4 from g3; clear g3
        exists x
        apply And.intro _ g4.right
        apply And.intro g4.left
        define
        contradict g1.right with g3
        define; rw [← h4, ← g4.right, g3]
        done

    set f' := func_to_range (func_restrict f (A \ {a}))
    have g1: one_to_one f' := by
      apply ftr_one_one_of_one_one
      apply fr_one_one_of_one_one_on
      define; intros x1 x2 g1 g2 geq
      apply h1 at geq
      apply geq
      apply g1.left
      apply g2.left
    have g2: onto f' := by
      apply ftr_onto
      done
    define; rw [← g]
    exists f'
    done

-- 3.
lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := by
    define at h2
    apply Set.ext; intros x; apply Iff.intro
    · --x ∈ A → x ∈ {a}
      intros g1
      contradict h2 with g2
      exists x
    · --x ∈ {a} → x ∈ A
      intros g1; define at g1
      rw [g1]; apply h1
    done

-- 4.
lemma eq_zero_of_I_zero_equinum {n : Nat} (h : I 0 ∼ I n) : n = 0 := by
  rw [← numElts_def] at h
  rw [zero_elts_iff_empty] at h
  define at h
  contradict h with h1
  exists 0
  have h2: n > 0 := by apply Nat.pos_of_ne_zero h1
  define
  apply h2
  done

-- 5.
--Hint: use mathematical induction
theorem Exercise_8_1_6a : ∀ ⦃m n : Nat⦄, (I m ∼ I n) → m = n := by
  by_induc
  · --base case
    intros n h1
    apply eq_zero_of_I_zero_equinum at h1
    rw [h1]
  · --induction case
    intros m h1 n h2
    by_cases h3: n = 0
    · -- n = 0
      rw [h3] at h2
      apply Theorem_8_1_3_2 at h2
      apply eq_zero_of_I_zero_equinum at h2
      rw [h3]
      apply h2
    · -- n > 0
      have h5 := by apply exists_eq_add_one_of_ne_zero h3
      obtain n' h4 from h5; clear h5
      rw [h4] at h2
      rw [h4]
      have g1: n' < n' + 1 := by linarith
      have g2 := by apply I_equinum_I_remove_one g1
      rw [← numElts_def] at h2
      have g3: n' ∈ I (n' + 1) := by
        define; apply g1
      have g4 := by apply remove_one_numElts h2 g3
      rw [numElts_def] at g4
      apply Theorem_8_1_3_2 at g2
      have g5 := by apply Theorem_8_1_3_3 g4 g2
      apply h1 at g5
      rw [g5]
    done

-- 6.
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := by
    rw [numElts_def] at h1
    rw [numElts_def] at h2
    apply Theorem_8_1_3_2 at h2
    have h3 := by apply Theorem_8_1_3_3 h1 h2
    apply Exercise_8_1_6a at h3
    apply h3
    done

-- 7.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := by
    by_induc
    · intros h1
      rfl
    · intros n h1 h2
      by_cases h3: rel_prime m n
      · --rel_prime m n
        rw [num_rp_below_step_rp h3]
        have g1: n ∈ set_rp_below m := by
          define; apply And.intro h3
          linarith
        rw [neb_step_elt g1]
        have g2 : n ≤ m := by linarith
        apply h1 at g2
        rw [g2]
      · --not rel_prime m n
        rw [num_rp_below_step_not_rp h3]
        have g2: n ∉ set_rp_below m := by
          contradict h3 with h4
          define at h4
          apply h4.left
        rw [neb_step_not_elt g2]
        apply h1
        linarith
      done

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := sorry

--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := by
    apply Set.ext
    fix (q, r)
    apply Iff.intro
    · --(q, r) ∈ image (qr n) (I (m * n)) → (q, r) ∈ I m ×ₛ I n
      by_cases h : n = 0
      · -- n = 0
        rw [h]; ring
        intros h1
        define at h1
        obtain x h2 from h1; clear h1
        have h3 := h2.left
        define at h3
        linarith
      · -- n > 0
        intros h1; define at h1; define
        obtain x h2 from h1; clear h1
        have h3 := h2.right; unfold qr at h3
        rw [Prod.eq_iff_fst_eq_snd_eq] at h3
        have h4 : x / n = q := by linarith
        have h5 : x % n = r := by linarith
        clear h3
        have h3 := h2.left; define at h3
        apply And.intro
        · define -- q < m
          rw [← h4]
          rw [Nat.div_lt_iff_lt_mul]
          apply h3
          apply Nat.pos_of_ne_zero h
        · define -- r < n
          rw [← h5]
          apply Nat.mod_lt
          apply Nat.pos_of_ne_zero h
    · --(q, r) ∈ I m ×ₛ I n → (q, r) ∈ image (qr n) (I (m * n))
      intros h1
      define at h1
      have h2 := h1.left; define at h2
      have h3 := h1.right; define at h3
      clear h1
      define
      exists q * n + r
      apply And.intro
      · --q * n + r ∈ I (m * n)
        define
        have h1 : m > 0 := by linarith
        rw [← Nat.le_sub_one_iff_lt h1] at h2
        have h4: q * n ≤ (m - 1) * n := by
          apply Nat.mul_le_mul_right n h2
        have g1 : m ≥ 1 := by linarith
        calc q * n + r
          _ ≤ (m - 1) * n + r := by linarith
          _ < (m - 1) * n + n := by linarith
          _ = (m - 1) * n + 1 * n := by ring
          _ = m * n := by rw [← right_distrib, Nat.sub_add_cancel g1]
        done
      · --qr n (q * n + r) = (q, r)
        unfold qr
        set x := n * q + r
        have h4: x = n * q + r := by rfl
        have g1 := by apply div_mod_char n x q r h4 h3
        rw [h4, mul_comm] at g1
        rw [← g1.left, ← g1.right]
      done

-- Definitions for next two exercises
lemma is_elt_snd_of_not_fst {U : Type} {A C : Set U} {x : U}
    (h1 : x ∈ A ∪ C) (h2 : x ∉ A) : x ∈ C := by
  disj_syll h1 h2
  show x ∈ C from h1
  done

def elt_snd_of_not_fst {U : Type} {A C : Set U} {x : ↑(A ∪ C)}
  (h : x.val ∉ A) : C :=
  Subtype_elt (is_elt_snd_of_not_fst x.property h)

noncomputable def func_union {U V : Type} {A C : Set U}
  (f : A → V) (g : C → V) (x : ↑(A ∪ C)) : V :=
  if test : x.val ∈ A then f (Subtype_elt test)
    else g (elt_snd_of_not_fst test)

-- 9.
lemma func_union_one_one {U V : Type} {A C : Set U}
    {f : A → V} {g : C → V} (h1 : empty (range f ∩ range g))
    (h2 : one_to_one f) (h3 : one_to_one g) :
    one_to_one (func_union f g) := by
    define; intros x1 x2 heq
    by_cases g1: x1.val ∈ A
    · by_cases g2: x2.val ∈ A
      · --x1.val ∈ A and x2.val ∈ A
        rw [func_union, dif_pos g1, func_union, dif_pos g2] at heq
        apply h2 at heq
        rw [Subtype_elt, Subtype_elt] at heq
        injection heq with hvaleq
        apply Subtype.ext at hvaleq
        apply hvaleq
      · --x1.val ∈ A and x2.val ∉ A
        rw [func_union, dif_pos g1, func_union, dif_neg g2] at heq
        contradict h1
        exists f (Subtype_elt g1)
        define
        apply And.intro
        · define; exists Subtype_elt g1
        · rw [heq]; define; exists elt_snd_of_not_fst g2
        done
    · by_cases g2: x2.val ∈ A
      · --x1.val ∉ A and x2.val ∈ A
        rw [func_union, dif_neg g1, func_union, dif_pos g2] at heq
        contradict h1
        exists f (Subtype_elt g2)
        apply And.intro
        · define; exists Subtype_elt g2
        · rw [← heq]; define; exists elt_snd_of_not_fst g1
      · --x1.val ∉ A and x2.val ∉ A
        rw [func_union, dif_neg g1, func_union, dif_neg g2] at heq
        apply h3 at heq
        rw [elt_snd_of_not_fst, elt_snd_of_not_fst, Subtype_elt, Subtype_elt] at heq
        injection heq with heqval
        apply Subtype.ext at heqval
        apply heqval
    done

-- 10.
lemma func_union_range {U V : Type} {A C : Set U}
    (f : A → V) (g : C → V) (h : empty (A ∩ C)) :
    range (func_union f g) = range f ∪ range g := by
    apply Set.ext; intros y; apply Iff.intro
    · --y ∈ range (func_union f g) → y ∈ range f ∪ range g
      intros h1; define at h1; obtain x h2 from h1; clear h1
      by_cases h1: x.val ∈ A
      · -- x.val ∈ A
        rw [func_union, dif_pos h1] at h2
        apply Or.inl
        exists Subtype_elt h1
        done
      · --x.val ∉ A
        rw [func_union, dif_neg h1] at h2
        apply Or.inr
        exists elt_snd_of_not_fst h1
    · --y ∈ range f ∪ range g → y ∈ range (func_union f g)
      intros h1; define at h1
      by_cases on h1
      · -- y ∈ range f
        obtain x h2 from h1
        have h3: x.val ∈ A ∪ C := by
          apply Or.inl x.property
        exists Subtype_elt h3
        have h4: ↑(Subtype_elt h3) ∈ A := by
          rw [Subtype_elt]
          apply x.property
          done
        have h5 : Subtype_elt h4 = x := by
          rfl
        rw [func_union, dif_pos h4, h5]
        apply h2
      · --y ∈ range g
        obtain x h2 from h1
        have h3: x.val ∈ A ∪ C := by
          apply Or.inr x.property
        exists Subtype_elt h3
        have h4: ↑(Subtype_elt h3) ∈ C := by
          rw [Subtype_elt]
          apply x.property
          done
        have h6: ↑(Subtype_elt h3) ∉ A := by
          contradict h with g1
          exists Subtype_elt h3
        have h5 : elt_snd_of_not_fst h6 = x := by
          rfl
        rw [func_union, dif_neg h6, h5]
        apply h2
    done

-- 11.
--Hint:  Use the last two exercises.
theorem Theorem_8_1_2_2
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : empty (A ∩ C)) (h2 : empty (B ∩ D))
    (h3 : A ∼ B) (h4 : C ∼ D) : ↑(A ∪ C) ∼ ↑(B ∪ D) := by
    obtain f g1 from h3
    obtain g g2 from h4
    define
    set f': ↑A → ↑(B ∪ D) := fun a => ⟨(f a).val, Or.inl (f a).property⟩
    set g': ↑C → ↑(B ∪ D) := fun c => ⟨(g c).val, Or.inr (g c).property⟩
    exists (func_union f' g')
    apply And.intro
    · --one_to_one (func_union f' g')
      apply func_union_one_one
      · --empty (range f' ∩ range g')
        define
        contradict h2 with h5
        obtain x h6 from h5; clear h5
        define at h6; have hleft := h6.left; define at hleft
        obtain a h7 from hleft; clear hleft
        unfold f' at h7
        rw [Subtype.mk_eq_mk] at h7
        have hright := h6.right; define at hright
        obtain c h8 from hright; clear hright
        unfold g' at h8
        rw [Subtype.mk_eq_mk] at h8
        exists x
        apply And.intro
        · rw [← h7]; apply (f a).property
        · rw [← h8]; apply (g c).property
        done
      · --one_to_one f'
        define; intros x1 x2 heq
        unfold f' at heq
        rw [Subtype.mk_eq_mk] at heq
        apply Subtype.ext at heq
        apply g1.left at heq
        apply heq
      · --one_to_one g'
        define; intros x1 x2 heq
        unfold g' at heq
        rw [Subtype.mk_eq_mk] at heq
        apply Subtype.ext at heq
        apply g2.left at heq
        apply heq
    · --onto (func_union f' g')
      have g3 := by apply func_union_range f' g' h1
      define; fix y
      by_cases g4: y.val ∈ B
      · -- y.val ∈ B
        have g5 := g1.right; define at g5
        obtain a g6 from g5 (Subtype_elt g4); clear g5
        exists ⟨a, by apply Or.inl a.property⟩
        rw [func_union, dif_pos a.property]
        unfold f'; rw[Subtype_elt]; simp
        rw [Subtype.mk_eq_mk, g6, Subtype_elt]
        done
      · --y.val ∉ B
        have h5: ↑y ∈ D := by
          disj_syll y.property g4
          apply this
        have g5 := g2.right; define at g5
        obtain c g6 from g5 (Subtype_elt h5)
        exists ⟨c, by apply Or.inr c.property⟩
        have g7: ↑c ∉ A := by
          contradict h1 with g8
          exists c
          apply And.intro g8 c.property
        rw [func_union, dif_neg g7]
        unfold g'; unfold elt_snd_of_not_fst
        rw [Subtype_elt]; simp
        rw [Subtype.mk_eq_mk, g6]
        rfl
    done

-- 12.
lemma shift_I_equinum (n m : Nat) : I m ∼ ↑(I (n + m) \ I n) := by
  define
  set f: ↑(I m) → ↑(I (n + m) \ I n) := fun x => ⟨x.val + n, by
    define; apply And.intro
    · --↑x + n ∈ I (n + m)
      define
      have h1 := x.property; define at h1
      calc x + n
        _ < m + n := by linarith
        _ = n + m := by linarith
    · --↑x + n ∉ I n
      define; linarith
    ⟩
  exists f
  apply And.intro
  · --one_to_one
    define; intros x1 x2 heq
    unfold f at heq
    rw [Subtype.mk_eq_mk] at heq
    apply Nat.add_right_cancel at heq
    apply Subtype.ext at heq
    apply heq
  · --onto
    define; intros y
    have h1 := y.property.right; define at h1
    apply Nat.ge_of_not_lt at h1
    apply exists_add_of_le at h1
    obtain n' h2 from h1; clear h1
    have h3 := y.property.left; define at h3
    rw [h2] at h3
    apply lt_of_add_lt_add_left at h3
    exists ⟨n', h3⟩
    unfold f
    rw [Subtype.mk_eq_mk]; simp
    rw [h2, add_comm]
    done

-- 13.
theorem Theorem_8_1_7 {U : Type} {A B : Set U} {n m : Nat}
    (h1 : empty (A ∩ B)) (h2 : numElts A n) (h3 : numElts B m) :
    numElts (A ∪ B) (n + m) := by
    rw [numElts_def] at h2
    rw [numElts_def] at h3
    rw [numElts_def]
    have h4 := by apply shift_I_equinum n m
    have h5: I (n + m) = I n ∪ I (n + m) \ I n := by
      apply Set.ext; intros x; apply Iff.intro
      · intros g1; define at g1
        by_cases g2: x < n
        · apply Or.inl g2
        · apply Or.inr
          define; apply And.intro g1 g2
      · intros g1
        by_cases on g1
        · define; define at g1; linarith
        · define at g1; apply g1.left
      done
    have h6: empty (I n ∩ (I (n + m) \ I n)) := by
      define; by_contra h6
      obtain x h7 from h6; clear h6
      have h8 := h7.right; define at h8
      contradict h8.right
      apply h7.left
      done
    have h7: ↑(I (n + m) \ I n) ∼ ↑B := by
      apply Theorem_8_1_3_2 at h4
      apply Theorem_8_1_3_3 h4 h3
    rw [h5]
    apply Theorem_8_1_2_2 h6 h1 h2 h7
    done

-- 14.
theorem equinum_sub {U V : Type} {A C : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : C ⊆ A) : ∃ (D : Set V), D ⊆ B ∧ C ∼ D := by
    obtain f h3 from h1
    set D := {v: V | ∃(x: ↑A), x.val ∈ C ∧ (f x).val = v}
    exists D
    apply And.intro
    · -- D ⊆ B
      define; intros y h4
      define at h4
      obtain x h5 from h4; clear h4
      rw [← h5.right]
      apply (f x).property
    · -- ↑C ∼ ↑D
      define
      set f': ↑C → ↑D := fun x => ⟨(f ⟨x, by apply h2 x.property⟩).val, by
        define
        exists ⟨x, by apply h2 x.property⟩
        apply And.intro
        · apply x.property
        · rfl
        ⟩
      exists f'
      apply And.intro
      · --one_to_one f'
        define; intros x1 x2 heq
        unfold f' at heq; simp at heq
        apply Subtype.ext at heq
        apply h3.left at heq
        rw [Subtype.mk_eq_mk] at heq
        apply Subtype.ext at heq
        apply heq
      · --onto f'
        define; intros y
        have h4:= y.property
        define at h4; obtain x h5 from h4
        exists  ⟨x.val, h5.left⟩
        unfold f'; simp
        rw [Subtype.mk_eq_mk]
        apply h5.right
    done

lemma Lemma_8_1_8b: ∀ (n: Nat), ∀ D ⊆ I n, finite D := by
  by_induc
  · --base
    intros D h1
    define at h1
    have h2: empty D := by
      by_contra h3; define at h3; double_neg at h3
      obtain x h2 from h3; clear h3
      apply h1 at h2
      define at h2; linarith
      done
    rw [← zero_elts_iff_empty] at h2
    exists 0
  · --induction
    intros n h1 D h2
    by_cases h3: n ∈ D
    · --n ∈ D
      have h4: D \ {n} ⊆ I n := by
        define
        intros a g1
        have g2 := g1.left; apply h2 at g2
        define at g2
        have g3 := g1.right; define at g3
        define
        apply Nat.le_of_lt_add_one at g2
        apply Nat.lt_of_le_of_ne g2 g3
        done
      apply h1 at h4
      obtain m h5 from h4
      obtain f h6 from h5
      exists m + 1
      set f' : ↑(I (m + 1)) → ↑D := fun x =>
        if test: x.val < m
        then ⟨f ⟨x.val, by define; apply test⟩, by
          have h7 := ↑(f ⟨↑x, by define; apply test⟩).property
          apply h7.left
          ⟩
        else Subtype_elt h3
      exists f'
      apply And.intro
      · --one_to_one
        define; intros x1 x2 heq
        unfold f' at heq
        by_cases g1: x1 < m
        · by_cases g2: x2 < m
          · --x1 < m and x2 < m
            rw [dif_pos g1, dif_pos g2] at heq
            simp at heq
            apply Subtype.ext at heq
            apply h6.left at heq
            rw [Subtype.mk_eq_mk] at heq
            apply Subtype.ext at heq
            apply heq
          · --x1 < m and x2 >= m
            rw [dif_pos g1, dif_neg g2, Subtype_elt] at heq
            rw [Subtype.mk_eq_mk] at heq
            have g3 := (f ⟨x1, by define; apply g1⟩).property
            rw [heq] at g3
            have g4 := g3.right
            contradict g4; rfl
        · by_cases g2: x2 < m
          · --x1 >= m and x2 < m
            rw [dif_neg g1, dif_pos g2, Subtype_elt] at heq
            rw [Subtype.mk_eq_mk] at heq
            have g3 := (f ⟨x2, by define; apply g2⟩).property
            rw [← heq] at g3
            have g4 := g3.right
            contradict g4; rfl
          · --x1 >= m and x2 >= m
            have g3 := x1.property; define at g3
            have g4 := x2.property; define at g4
            have g5 : x1 = m := by
              linarith
            have g6 : x2 = m := by
              linarith
            apply Subtype.ext
            rw [g5, g6]
      · --onto
        define; intros y
        by_cases g1: y = n
        · -- y = n
          exists ⟨m, by define; linarith⟩
          unfold f'
          rw [dif_neg, Subtype_elt, Subtype.mk_eq_mk]
          rw [g1]
          linarith
        · -- y ≠ n
          have g2 := h6.right
          define at g2
          have g3 := by apply g2 ⟨y, by
            define
            apply And.intro y.property
            apply g1
            ⟩
          obtain x g4 from g3
          exists ⟨x, by define; have g5 := x.property; define at g5; linarith⟩
          unfold f'
          have g6 := x.property; define at g6
          rw [dif_pos g6]; simp
          rw [Subtype.mk_eq_mk, g4]
    · -- n ∉ D
      have h4: D ⊆ I n := by
        define; intros a h4
        have g1 := h4
        apply h2 at h4; define at h4
        have h5 := by apply Nat.le_of_lt_add_one h4
        have h6 : a ≠ n := by
          contradict h3 with g2
          rw [←g2]; apply g1
        define; apply Nat.lt_of_le_of_ne h5 h6
        done
      apply h1
      apply h4
    done

-- 15.
theorem Exercise_8_1_8b {U : Type} {A B : Set U}
    (h1 : finite A) (h2 : B ⊆ A) : finite B := by
    define at h1
    obtain n h3 from h1; clear h1
    apply Theorem_8_1_3_2 at h3
    have h4:= by apply equinum_sub h3 h2
    obtain D h5 from h4; clear h4
    have h6 := h5.left
    have h7 := h5.right
    clear h5
    have h8 := by apply Lemma_8_1_8b n D h6
    obtain m h9 from h8; clear h8
    apply Theorem_8_1_3_2 at h7
    exists m
    apply Theorem_8_1_3_3 h9 h7
    done

-- 16.
lemma finite_bdd_aux : ∀ (n : Nat) (A : Set Nat), numElts A n →
    ∃ (m : Nat), ∀ k ∈ A, k < m := by
  by_induc
  · -- Base case: numElts A 0
    intros A h1
    exists 0
    intros n h2
    have h3 : empty A := by
      rw [← zero_elts_iff_empty, numElts_def]
      apply h1
    define at h3
    contradict h3 with h4
    exact ⟨n, h2⟩
  · -- Inductive step
    intros k ih A h1
    by_cases h2 : empty A
    · -- A is empty
      exists 0
      intros n h3
      define at h2
      contradict h2 with h4
      exact ⟨n, h3⟩
    · -- A is nonempty
      define at h2
      push_neg at h2
      obtain a h3 from h2
      have h4 : numElts (A \ {a}) k := remove_one_numElts h1 h3
      have h5 := ih (A \ {a}) h4
      obtain m' h6 from h5
      exists max m' (a + 1)
      intros n h7
      by_cases h8 : n = a
      · -- n = a
        rw [h8]
        have : a < a + 1 := by linarith
        have : a + 1 ≤ max m' (a + 1) := Nat.le_max_right m' (a + 1)
        linarith
      · -- n ≠ a
        have h9 : n ∈ A \ {a} := by
          define
          apply And.intro h7
          define
          apply h8
        apply h6 at h9
        have : m' ≤ max m' (a + 1) := Nat.le_max_left m' (a + 1)
        linarith
  done

theorem finite_bdd {A : Set Nat} (h : finite A) :
    ∃ (m : Nat), ∀ n ∈ A, n < m := by
  obtain n h1 from h
  apply finite_bdd_aux n A h1
  done

-- 17.
lemma N_not_finite : ¬finite Nat := by
  by_contra h
  -- h : finite Nat
  define at h
  obtain n h1 from h
  -- h1 : I n ∼ Nat
  have h2 : Univ Nat ∼ Nat := univ_equinum_type Nat
  apply Theorem_8_1_3_2 at h2
  -- h2 : Nat ∼ Univ Nat
  have h3 : I n ∼ Univ Nat := Theorem_8_1_3_3 h1 h2
  -- Now Univ Nat has n elements
  have h4 : finite ↑(Univ Nat) := ⟨n, h3⟩
  have h5 := finite_bdd h4
  obtain m h6 from h5
  -- h6 : ∀ n ∈ Univ Nat, n < m
  have h7 : m ∈ Univ Nat := by
    define
    trivial
  have h8 := h6 m h7
  -- h8 : m < m
  linarith
  done

-- 18.
theorem denum_not_finite (U : Type)
    (h : denum U) : ¬finite U := by
    rw [denum_def] at h
    have h1 := N_not_finite
    contradict h1 with h2; clear h1
    obtain n h3 from h2
    apply Theorem_8_1_3_2 at h
    exists n
    apply Theorem_8_1_3_3 h3 h
    done

-- 19.
--Hint:  Use Like_Exercise_6_2_16 from the exercises of Section 6.2.
theorem Like_Exercise_6_2_16 {A : Type} (f : A → A)
    (h : one_to_one f) : ∀ (n : Nat) (B : Set A), numElts B n →
    closed f B → ∀ y ∈ B, ∃ x ∈ B, f x = y := sorry

theorem Exercise_6_2_16 {U : Type} {f : U → U}
    (h1 : one_to_one f) (h2 : finite U) : onto f := by
    obtain n h3 from h2
    have h4 : Univ U ∼ U := univ_equinum_type U
    apply Theorem_8_1_3_2 at h4
    have h5 := by apply Theorem_8_1_3_3 h3 h4
    rw [← numElts_def] at h5
    have h6: closed f (Univ U) := by
      define
      intros x g1
      define
      trivial
    have h7: ∀ y ∈ (Univ U), ∃ x ∈ (Univ U), f x = y := by
      apply Like_Exercise_6_2_16 f h1 n (Univ U) h5 h6
    define; intros y
    have h8 := by apply h7 y; define; trivial
    obtain x h9 from h8
    exists x; apply h9.right
    done

/- Section 8.2 -/
-- 1.
lemma pair_ctble {U : Type}
    (a b : U) : ctble ↑({a, b} : Set U) := by
    define
    apply Or.inl
    by_cases h: a = b
    · -- a = b
      exists 1
      rw [h]
      simp
      rw [← numElts_def]
      apply singleton_one_elt
    · -- a ≠ b
      exists 2
      apply Theorem_8_1_3_2
      define
      set f: ↑({a, b}: Set U) → ↑(I 2) := fun x =>
        if x.val = a
        then ⟨0, by define; linarith⟩
        else ⟨1, by define; linarith⟩
      exists f
      apply And.intro
      · --one_to_one
        define; intros x1 x2 heq
        unfold f at heq
        by_cases hx1: x1.val = a
        · by_cases hx2: x2.val = a
          · --x1 = a, x2 = a
            apply Subtype.ext
            rw [hx1, hx2]
          · --x1 = a, not x2 = a
            rw [if_pos hx1, if_neg hx2, Subtype.mk_eq_mk] at heq
            linarith
        · by_cases hx2: x2.val = a
          · --not x1 = a, x2 = a
            rw [if_neg hx1, if_pos hx2, Subtype.mk_eq_mk] at heq
            linarith
          · --not x1 = a, not x2 = a
            apply Subtype.ext
            have h1: x1 = b := by
              have g1:= x1.property
              define at g1
              disj_syll g1 hx1
              apply g1
            have h2: x2 = b := by
              have g2:= x2.property
              define at g2
              disj_syll g2 hx2
              apply g2
            rw [h1, h2]
      · --onto
        define
        intros y
        by_cases h1: y.val = 0
        · --y = 0
          exists ⟨a, by define; apply Or.inl; rfl⟩
          unfold f
          rw [if_pos, Subtype.mk_eq_mk, h1]
          rfl
        · --y = 1
          have h2: y.val = 1 := by
            have h3:= y.property
            define at h3
            have h4 := by apply Nat.le_of_lt_add_one h3
            have h5 := by apply Nat.pos_of_ne_zero h1
            linarith
          exists ⟨b, by define; apply Or.inr; rfl⟩
          unfold f
          have h3 : ¬b = a := by
            contradict h with h3
            rw [h3]
          rw [if_neg h3, Subtype.mk_eq_mk, h2]
    done

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {U : Type} {A B : Set U}
    (h1 : ctble A) (h2 : ctble B) : ctble ↑(A ∪ B) := by
    set F := {A, B}
    have g1 : ctble F := by apply pair_ctble A B
    have g2 : ctble (⋃₀F) := by
      apply Theorem_8_2_2
      apply g1
      intros X h3; define at h3
      by_cases on h3
      · rw [h3]; apply h1
      · define at h3; rw [h3]; apply h2
      done
    have g3: ⋃₀ F = A ∪ B := by
      apply Set.ext
      intros x; apply Iff.intro
      · intros h3; define at h3
        obtain X h4 from h3; clear h3
        have h5 := h4.left; define at h5
        by_cases on h5
        apply Or.inl
        rw [← h5]; apply h4.right
        apply Or.inr; define at h5
        rw [← h5]; apply h4.right
      · intros h3; by_cases on h3
        define; exists A
        apply And.intro _ h3
        define; apply Or.inl
        rfl
        define; exists B
        apply And.intro _ h3
        define; apply Or.inr
        rfl
      done
    rw [g3] at g2
    apply g2
    done

-- 3.
lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := by
    apply Set.ext; intros x; apply Iff.intro
    · --x ∈ ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} → x ∈ ⋃₀ F
      intros h1; define at h1
      obtain X h2 from h1; clear h1
      have h3 := h2.left; define at h3
      exists X
      apply And.intro h3.left h2.right
    · --x ∈ ⋃₀ F → x ∈ ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A}
      intros h1
      obtain X h2 from h1
      define; exists X
      apply And.intro _ h2.right
      define
      apply And.intro h2.left
      define; double_neg
      exists x; apply h2.right
    done

-- 4.
lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := by
    apply Set.ext; intros L; apply Iff.intro
    · --l ∈ image (seq_cons U) (A ×ₛ seq_by_length A n) → l ∈ seq_by_length A (n + 1)
      intros h1; define at h1
      obtain l h2 from h1; clear h1
      have h3 := h2.left; define at h3
      have h4 := h2.right
      have h5 := h3.right; define at h5
      have h6 := h5.left; define at h6
      define; apply And.intro
      · --l ∈ seq A
        rw [← h2.right]
        define
        intros x g1
        rw [seq_cons_def] at g1
        rw [List.mem_cons] at g1
        by_cases on g1
        · rw [g1]; apply h3.left
        · apply h6; apply g1
      · --L.length = n + 1
        rw [← h4]
        rw [seq_cons, List.length_cons]
        rw [h5.right]
    · --L ∈ seq_by_length A (n + 1) → L ∈ image (seq_cons U) (A ×ₛ seq_by_length A n)
      intros h1; define at h1
      have h2 := h1.left; define at h2
      have h3 := h1.right; clear h1
      define
      have t1 := h3
      apply List.exists_cons_of_length_eq_add_one at t1
      obtain h t2 from t1
      obtain l t3 from t2
      clear t1; clear t2
      exists (h, l)
      apply And.intro
      · --(h, l) ∈ A ×ₛ seq_by_length A n
        define; apply And.intro
        · --h ∈ A
          apply h2; rw [t3]
          apply List.head_mem
          rw [List.ne_nil_iff_exists_cons]
          exists h; exists l
        · --l ∈ seq_by_length A n
          define; apply And.intro
          · --l ∈ seq A
            define; intros x h4
            apply h2; rw [t3]
            apply List.mem_cons_of_mem
            apply h4
          · --l.length = n
            rw [t3] at h3
            rw [List.length_cons] at h3
            linarith
      · --seq_cons U (h, l) = L
        rw [t3]
        rfl
    done

-- 5.
--Hint:  Apply Theorem_8_2_4 to the set Univ U
theorem Theorem_8_2_4_type {U : Type}
    (h : ctble U) : ctble (List U) := by
    have h1 := by apply univ_equinum_type U
    have h2: ctble (Univ U) := by
      apply ctble_set_of_ctble_type h (Univ U)
    have h3 := by apply Theorem_8_2_4 h2
    have h5 : Univ (List U) ∼ List U := by apply univ_equinum_type (List U)
    have h6 : seq (Univ U) = Univ (List U) := by
      nth_rw 2 [Univ]
      rw [seq]
      apply Set.ext; intros l; apply Iff.intro
      · --(->)
        intros g1; define at g1
        define; trivial
      · --(<-)
        intros g1
        define; intros x g2
        define; trivial
      done
    have h4 : seq (Univ U) ∼ List U := by
      rw [h6]
      apply h5
    apply ctble_of_ctble_equinum h4 h3
    done

-- 6.
def list_to_set (U : Type) (l : List U) : Set U := {x : U | x ∈ l}

lemma list_to_set_def (U : Type) (l : List U) (x : U) :
    x ∈ list_to_set U l ↔ x ∈ l := by rfl

--Hint:  Use induction on the size of A
lemma set_from_list_aux {U: Type}: ∀ n: Nat, ∀ A: Set U,
    finite A → numElts A n → ∃ (l : List U), list_to_set U l = A := by
    by_induc
    · -- n = 0
      intros A h1 h2
      exists []
      apply Set.ext; intros x; apply Iff.intro
      · intros h3
        have h4 : x ∈ [] := by apply h3
        rw [List.mem_nil_iff] at h4
        absurd h4
        trivial
      · intros h3
        rw [zero_elts_iff_empty] at h2
        contradict h2
        exists x
    · --induction case
      intros n ih A h1 h2
      -- obtain some element x from A
      -- remove x to get a N-element set, and apply ih to get list tail
      -- concat x::tail to obtain the required list
      have tmp: n + 1 > 0 := by linarith
      have h3:= by apply nonempty_of_pos_numElts h2 tmp
      obtain h h4 from h3; clear tmp; clear h3
      have g1:= by apply remove_one_numElts h2 h4
      have g2: finite ↑(A \ {h}) := by
        exists n
      have h5 := by apply ih (A \ {h}) g2 g1
      obtain l h6 from h5; clear h5
      exists h::l
      apply Set.ext; intros x; apply Iff.intro
      · --x ∈ list_to_set U (h :: l) → x ∈ A
        intros h7
        have h8: x ∈ h::l := by apply h7
        rw [List.mem_cons] at h8
        by_cases on h8
        · rw [h8]; apply h4
        · rw [← list_to_set_def] at h8
          rw [h6] at h8
          apply h8.left
      · --x ∈ A → x ∈ list_to_set U (h :: l)
        intros h7
        rw [list_to_set_def]
        rw [List.mem_cons]
        by_cases h8: x = h
        · apply Or.inl h8
        · apply Or.inr
          rw [← list_to_set_def]
          rw [h6]
          apply And.intro h7 h8
      done

lemma set_from_list {U : Type} {A : Set U} (h : finite A) :
    ∃ (l : List U), list_to_set U l = A := by
    obtain n h1 from h
    rw [← numElts_def] at h1
    apply set_from_list_aux n
    apply h; apply h1
    done

-- 7.
--Hint:  Use the previous exercise and Theorem_8_2_4_type
theorem Like_Exercise_8_2_4 (U : Type) (h : ctble U) :
    ctble {X : Set U | finite X} := by
    have h1 := by apply Theorem_8_2_4_type h
    have h2 : ∀ (A : Set (List U)), ctble ↑A := by
      apply ctble_set_of_ctble_type h1
    set g : {X : Set U | finite X} → List U := fun X =>
      Classical.choose (set_from_list X.property)
    have hg : ∀ (X : {X : Set U | finite X}), list_to_set U (g X) = X.val := by
      intro X
      exact Classical.choose_spec (set_from_list X.property)
    have h3: one_to_one g := by
      define; intros x1 x2 heq
      apply Subtype.ext
      have g1 := hg x1
      have g2 := hg x2
      rw [← g1, ← g2, heq]
    rw [Theorem_8_1_5_3_type] at h1
    obtain f hf from h1
    rw [Theorem_8_1_5_3_type]
    exists f ∘ g
    apply Theorem_5_2_5_1
    apply h3; apply hf
    done

-- 8.
theorem Exercise_8_2_6b (U V W : Type) :
     ((U × V) → W) ∼ (U → V → W) := by
    exists fun f u v => f (u, v)
    apply And.intro
    · --one_to_one
      define; intros f1 f2 heq
      apply funext
      intros x
      rw [funext_iff] at heq
      have h1 := by apply heq x.1
      rw [funext_iff] at h1
      have h2 := by apply h1 x.2
      clear heq; clear h1
      simp at h2
      apply h2
    · --onto
      define; intros f
      set g : U × V → W := fun x => f x.1 x.2
      exists g
    done

-- 9.
theorem Like_Exercise_8_2_7 : ∃ (P : Set (Set Nat)),
    partition P ∧ denum P ∧ ∀ X ∈ P, denum X := sorry

-- 10.
theorem unctbly_many_inf_set_nat :
    ¬ctble {X : Set Nat | ¬finite X} := sorry

-- 11.
theorem Exercise_8_2_8 {U : Type} {A B : Set U}
    (h : empty (A ∩ B)) : 𝒫 (A ∪ B) ∼ 𝒫 A ×ₛ 𝒫 B := sorry

/- Section 8.3 -/
-- 1.
lemma csb_func_graph_not_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∉ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ g y = x := sorry

-- 2.
theorem intervals_equinum :
    {x : Real | 0 < x ∧ x < 1} ∼ {x : Real | 0 < x ∧ x ≤ 1} := sorry

-- 3.
--Hint for proof:  First show that `extension R = extension S`, and then use the fact
--that `R` and `S` can be determined from `extension R` and `extension S` (see Section 4.3).
theorem relext {U V : Type} {R S : Rel U V}
    (h : ∀ (u : U) (v : V), R u v ↔ S u v) : R = S := sorry

-- Definitions for next six exercises
def EqRel (U : Type) : Set (BinRel U) :=
  {R : BinRel U | equiv_rel R}

def Part (U : Type) : Set (Set (Set U)) :=
  {P : Set (Set U) | partition P}

def EqRelExt (U : Type) : Set (Set (U × U)) :=
  {E : Set (U × U) | ∃ (R : BinRel U), equiv_rel R ∧ extension R = E}

def shift_and_zero (X : Set Nat) : Set Nat :=
  {x + 2 | x ∈ X} ∪ {0}

def shift_and_zero_comp (X : Set Nat) : Set Nat :=
  {n : Nat | n ∉ shift_and_zero X}

def saz_pair (X : Set Nat) : Set (Set Nat) :=
  {shift_and_zero X, shift_and_zero_comp X}

-- 4.
theorem EqRel_equinum_Part (U : Type) : EqRel U ∼ Part U := sorry

-- 5.
theorem EqRel_equinum_EqRelExt (U : Type) :
    EqRel U ∼ EqRelExt U := sorry

-- 6.
theorem EqRel_Nat_to_Set_Nat :
    ∃ (f : EqRel Nat → Set Nat), one_to_one f := sorry

-- 7.
theorem saz_pair_part (X : Set Nat) : saz_pair X ∈ Part Nat := sorry

-- 8.
theorem Set_Nat_to_EqRel_Nat :
    ∃ (f : Set Nat → EqRel Nat), one_to_one f := sorry

-- 9.
theorem EqRel_Nat_equinum_Set_Nat : EqRel Nat ∼ Set Nat := sorry
