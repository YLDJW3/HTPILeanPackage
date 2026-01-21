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
    (f : U → Nat) (h : empty A) : image f A = I 0 := sorry

-- 2.
lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := sorry

-- 3.
lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := sorry

-- 4.
lemma eq_zero_of_I_zero_equinum {n : Nat} (h : I 0 ∼ I n) : n = 0 := sorry

-- 5.
--Hint: use mathematical induction
theorem Exercise_8_1_6a : ∀ ⦃m n : Nat⦄, (I m ∼ I n) → m = n := sorry

-- 6.
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := sorry

-- 7.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := sorry

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

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
    one_to_one (func_union f g) := sorry

-- 10.
lemma func_union_range {U V : Type} {A C : Set U}
    (f : A → V) (g : C → V) (h : empty (A ∩ C)) :
    range (func_union f g) = range f ∪ range g := sorry

-- 11.
--Hint:  Use the last two exercises.
theorem Theorem_8_1_2_2
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : empty (A ∩ C)) (h2 : empty (B ∩ D))
    (h3 : A ∼ B) (h4 : C ∼ D) : ↑(A ∪ C) ∼ ↑(B ∪ D) := sorry

-- 12.
lemma shift_I_equinum (n m : Nat) : I m ∼ ↑(I (n + m) \ I n) := sorry

-- 13.
theorem Theorem_8_1_7 {U : Type} {A B : Set U} {n m : Nat}
    (h1 : empty (A ∩ B)) (h2 : numElts A n) (h3 : numElts B m) :
    numElts (A ∪ B) (n + m) := sorry

-- 14.
theorem equinum_sub {U V : Type} {A C : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : C ⊆ A) : ∃ (D : Set V), D ⊆ B ∧ C ∼ D := sorry

-- 15.
theorem Exercise_8_1_8b {U : Type} {A B : Set U}
    (h1 : finite A) (h2 : B ⊆ A) : finite B := sorry

-- 16.
theorem finite_bdd {A : Set Nat} (h : finite A) :
    ∃ (m : Nat), ∀ n ∈ A, n < m := sorry

-- 17.
lemma N_not_finite : ¬finite Nat := sorry

-- 18.
theorem denum_not_finite (U : Type)
    (h : denum U) : ¬finite U := sorry

-- 19.
--Hint:  Use Like_Exercise_6_2_16 from the exercises of Section 6.2.
theorem Exercise_6_2_16 {U : Type} {f : U → U}
    (h1 : one_to_one f) (h2 : finite U) : onto f := sorry

/- Section 8.2 -/
-- 1.
lemma pair_ctble {U : Type}
    (a b : U) : ctble ↑({a, b} : Set U) := sorry

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {U : Type} {A B : Set U}
    (h1 : ctble A) (h2 : ctble B) : ctble ↑(A ∪ B) := sorry

-- 3.
lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := sorry

-- 4.
lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

-- 5.
--Hint:  Apply Theorem_8_2_4 to the set Univ U
theorem Theorem_8_2_4_type {U : Type}
    (h : ctble U) : ctble (List U) := sorry

-- 6.
def list_to_set (U : Type) (l : List U) : Set U := {x : U | x ∈ l}

lemma list_to_set_def (U : Type) (l : List U) (x : U) :
    x ∈ list_to_set U l ↔ x ∈ l := by rfl

--Hint:  Use induction on the size of A
lemma set_from_list {U : Type} {A : Set U} (h : finite A) :
    ∃ (l : List U), list_to_set U l = A := sorry

-- 7.
--Hint:  Use the previous exercise and Theorem_8_2_4_type
theorem Like_Exercise_8_2_4 (U : Type) (h : ctble U) :
    ctble {X : Set U | finite X} := sorry

-- 8.
theorem Exercise_8_2_6b (U V W : Type) :
     ((U × V) → W) ∼ (U → V → W) := sorry

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
